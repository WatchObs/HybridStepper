/*
  Hybrid stepper (float integration) with loss-of-pulses safety and 2 Hz logging
  - External STEP on pin 21 used only for measurement (period + count)
  - ISR integrates published host rate (indices per ISR) into a float phase accumulator
  - If no STEP edges seen for LOSS_TIMEOUT_MS, published rate is forced to zero
  - PIN_RATE_PWM (pin 11) configured once at 220 Hz and left untouched
  - Debug logging prints countRate, periodRate, chosenRate, source, usSinceLastEdge, phaseStepPerIsr every 500 ms
*/

#include <Arduino.h>
#include <IntervalTimer.h>
#include <stdint.h>
#include <math.h>
#include <FreqCount.h>
#include <FreqMeasure.h>

// --- Configuration ---
const bool ENABLE_DEBUG = true;            // enable 2 Hz serial debug prints

// Loss-of-pulses timeout (milliseconds)
const unsigned long LOSS_TIMEOUT_MS = 1000UL; // 1 second

// Pins
const int PIN_AEN   = 4;
const int PIN_AENB  = 3;
const int PIN_APWM1 = 1;
const int PIN_APWM2 = 2;
const int PIN_BEN   = 8;
const int PIN_BENB  = 7;
const int PIN_BPWM1 = 6;
const int PIN_BPWM2 = 5;
const int PIN_LED   = 13;

const int PIN_OCM1 = A1;
const int PIN_OCM2 = A2;

const int PIN_HOST_ENABLE = 20;
const int PIN_HOST_DIR    = 21;
//const int PIN_HOST_STEP   = 21; // external STEP input (measurement only)
const int PIN_HOST_FREQCNT = 9;   // FreqCount API
const int PIN_HOST_FREQMSR = 22;  // FreqMeasure API

const int PIN_RATE_PWM = 11;    // fixed hardware PWM test source
const uint32_t RATE_PWM_FREQ_HZ = 1000;
const uint32_t RATE_PWM_DUTY_16 = 32768; // 50% duty (0..65535)

const int PIN_ISR_TOGGLE = 10;  // scope probe

// Waveform / motor geometry
const int angles = 1024;            // table entries per electrical cycle
const int cycles_per_turn = 50;     // electrical cycles per mechanical revolution

// ISR timing
const uint32_t ISR_FREQ_HZ = 1000UL; // ISR ticks per second
const uint32_t ISR_PERIOD_US = 1000000UL / ISR_FREQ_HZ;

// Host rate steps/sec conversion to sine table in ISR
const float hostRTconv = 1.0/(ISR_FREQ_HZ); // * cycles_per_turn);
// ADC
const int ADC_BITS = 12;

// --- Sine table ---
static int32_t tbl[angles];
static void setupSineTable() {
  for (int n = 0; n < angles; ++n) {
    double a = (double)n * 2.0 * M_PI / (double)angles;
    tbl[n] = (int32_t)round(sin(a) * 65535.0);
  }
}

// Interpolated lookup using float index
static inline int32_t lookupInterpolatedFloat(float idx) {
  if (idx >= (float)angles) idx -= floorf(idx / (float)angles) * (float)angles;
  if (idx < 0.0f) idx += ceilf(-idx / (float)angles) * (float)angles;
  int i = (int)floorf(idx);
  float frac = idx - (float)i;
  int j = (i + 1 >= angles) ? 0 : i + 1;
  int32_t v0 = tbl[i];
  int32_t v1 = tbl[j];
  float interp = (float)v0 + ((float)(v1 - v0)) * frac;
  return (int32_t)roundf(interp);
}

// --- Shared state (volatile for ISR/main) ---
volatile float phaseA_f = 0.0f;             // floating index into table [0..angles)
volatile float phaseStepPerIsr_f = 0.0f;    // indices to advance per ISR tick (published by loop)
volatile float latestRatePps_f = 0.0f;      // latest chosen rate in pulses/sec (for diagnostics)
volatile int8_t dirSign = 1;                // +1 forward, -1 reverse
volatile int8_t enable = LOW;               // Host enable
volatile int8_t enable_ = HIGH;             // Host enable inverse (bar)
volatile unsigned long freqCount = 0;
volatile unsigned long freqMeasure = 0;
volatile float freqMeasureHz = 0.0;

// PWM outputs (written by ISR)
volatile uint16_t pwmA_pos = 0, pwmA_neg = 0, pwmB_pos = 0, pwmB_neg = 0;
volatile int8_t lastSignA = 0, lastSignB = 0;

// Diagnostics / housekeeping
volatile uint32_t stepsSinceLastSample = 0;
volatile uint16_t latestRaw1 = 0, latestRaw2 = 0;
volatile uint32_t isrHeartbeat = 0;

// IntervalTimer
IntervalTimer stepTimer;

// --- DWT cycle counter (raw registers) ---
static inline void enableCycleCounter() {
  *(volatile uint32_t *)0xE000EDFC |= (1UL << 24); // DEMCR TRCENA
  *(volatile uint32_t *)0xE0001004 = 0;            // DWT_CYCCNT = 0
  *(volatile uint32_t *)0xE0001000 |= 1UL;         // DWT_CTRL CYCCNTENA
}
static inline uint32_t readCycleCounter() {
  return *(volatile uint32_t *)0xE0001004;
}

// --- Hardware measurement state ---
volatile uint32_t hw_lastEdgeCapture = 0;   // last capture timer value (GPT capture)
volatile uint32_t hw_lastPeriodTicks = 0;   // ticks between last two captures (timer ticks)
volatile uint32_t hw_countLatched = 0;      // latched count from hardware counter (gated)
volatile uint32_t hw_lastEdgeTimeCycles = 0; // DWT cycles of last edge (for timeout)

// --- Teensy 4.x: Use GPT1 for input capture and period measurement ---
#ifndef CCM_CCGR1_GPT1
#define CCM_CCGR1_GPT1(x) ((x) << 20)
#endif

// --- API: publish host microsteps/sec (host unit = pulses/sec where 1 pulse = 1 table index) ---
void setMicrostepsPerSec(double microstepsPerSec) {
  if (microstepsPerSec < 0.0) microstepsPerSec = -microstepsPerSec;
  double stepPerIsr = microstepsPerSec / (double)ISR_FREQ_HZ; // indices per ISR
  noInterrupts();
  phaseStepPerIsr_f = (float)stepPerIsr;
  latestRatePps_f = (float)microstepsPerSec;
  interrupts();
}

// --- ISR: measurement + integration (no per-edge phase changes) ---
void stepISR() {
  digitalWriteFast(PIN_ISR_TOGGLE, HIGH);
  isrHeartbeat++;

  dirSign = digitalReadFast(PIN_HOST_DIR) ? 1 : -1;

   if (FreqCount.available()) {
    freqCount = FreqCount.read();
  }

  if (FreqMeasure.available()) {
    freqMeasure = FreqMeasure.read();
    freqMeasureHz = FreqMeasure.countToFrequency(freqMeasure);
  }

  // 2) Phase integration from published host rate (float read is atomic on 32-bit)
  float inc = freqMeasureHz * hostRTconv;
  if (inc != 0.0f) {
    phaseA_f += (float)dirSign * inc;
    if (phaseA_f >= (float)angles) phaseA_f -= (float)angles * floorf(phaseA_f / (float)angles);
    else if (phaseA_f < 0.0f) phaseA_f += (float)angles * ceilf(-phaseA_f / (float)angles);
  }

  // 3) Compute channel B (quarter period ahead) and lookup
  float phaseB_f = phaseA_f + ((float)angles / 4.0f);
  if (phaseB_f >= (float)angles) phaseB_f -= (float)angles;

  
  int32_t valA = lookupInterpolatedFloat(phaseA_f);
  int32_t valB = lookupInterpolatedFloat(phaseB_f);

  int8_t signA = (valA < 0) ? -1 : ((valA > 0) ? 1 : 0);
  int8_t signB = (valB < 0) ? -1 : ((valB > 0) ? 1 : 0);

  if ((lastSignA != 0 && signA != lastSignA) || (lastSignB != 0 && signB != lastSignB)) {
    if (valA < 0) { pwmA_pos = 0; pwmA_neg = (uint16_t)(-valA); } else { pwmA_pos = (uint16_t)valA; pwmA_neg = 0; }
    if (valB < 0) { pwmB_pos = 0; pwmB_neg = (uint16_t)(-valB); } else { pwmB_pos = (uint16_t)valB; pwmB_neg = 0; }
    lastSignA = signA; lastSignB = signB;
  } else {
  if (valA < 0) { pwmA_pos = 0; pwmA_neg = (uint16_t)(-valA); } else { pwmA_pos = (uint16_t)valA; pwmA_neg = 0; }
    if (valB < 0) { pwmB_pos = 0; pwmB_neg = (uint16_t)(-valB); } else { pwmB_pos = (uint16_t)valB; pwmB_neg = 0; }
    lastSignA = signA; lastSignB = signB;
  }

  // 4) Write PWM outputs
  analogWrite(PIN_APWM1, pwmA_pos);
  analogWrite(PIN_APWM2, pwmA_neg);
  analogWrite(PIN_BPWM1, pwmB_pos);
  analogWrite(PIN_BPWM2, pwmB_neg);

  // 5) ADC reads and housekeeping
  latestRaw1 = (uint16_t)analogRead(PIN_OCM1);
  latestRaw2 = (uint16_t)analogRead(PIN_OCM2);
  stepsSinceLastSample++;
  digitalWriteFast(PIN_ISR_TOGGLE, LOW);
}

// --- Loop: choose period vs count estimator, detect loss-of-pulses, publish chosen rate ---
// Also prints debug info at 2 Hz when ENABLE_DEBUG is true.
void publishChosenRateFromMeasurement(double chosenRatePps) {
  setMicrostepsPerSec(chosenRatePps);
}

void setup() {
  Serial.begin(115200);
  while (!Serial && millis() < 2000) {}
  Serial.println("Hybrid stepper");

  // pins
  pinMode(PIN_AEN, OUTPUT); pinMode(PIN_AENB, OUTPUT);
  pinMode(PIN_APWM1, OUTPUT); pinMode(PIN_APWM2, OUTPUT);
  pinMode(PIN_BEN, OUTPUT); pinMode(PIN_BENB, OUTPUT);
  pinMode(PIN_BPWM1, OUTPUT); pinMode(PIN_BPWM2, OUTPUT);
  pinMode(PIN_LED, OUTPUT);

  pinMode(PIN_HOST_ENABLE, INPUT_PULLUP);
  pinMode(PIN_HOST_DIR, INPUT_PULLUP);
  //pinMode(PIN_HOST_STEP, INPUT_PULLUP); // STEP input (measurement only)

  pinMode(PIN_ISR_TOGGLE, OUTPUT);
  digitalWriteFast(PIN_ISR_TOGGLE, LOW);

  // Configure fixed hardware PWM on PIN_RATE_PWM once and never touch it again
  pinMode(PIN_RATE_PWM, OUTPUT);
  analogWriteResolution(16); // 0..65535
  analogWriteFrequency(PIN_RATE_PWM, RATE_PWM_FREQ_HZ);
  analogWrite(PIN_RATE_PWM, (int)RATE_PWM_DUTY_16); // set and leave

  // Configure other PWM outputs
  analogWriteFrequency(PIN_APWM1, 2000);
  analogWriteFrequency(PIN_APWM2, 2000);
  analogWriteFrequency(PIN_BPWM1, 2000);
  analogWriteFrequency(PIN_BPWM2, 2000);

  analogReadResolution(ADC_BITS);

  analogWrite(PIN_APWM1, 0); analogWrite(PIN_APWM2, 0);
  analogWrite(PIN_BPWM1, 0); analogWrite(PIN_BPWM2, 0);

  setupSineTable();

  digitalWrite(PIN_AEN, LOW); digitalWrite(PIN_AENB, HIGH);
  digitalWrite(PIN_BEN, LOW); digitalWrite(PIN_BENB, HIGH);
  digitalWrite(PIN_LED, LOW);

  // Direction sign
  dirSign = 1;

  // Setup frequency counter/measure
  FreqCount.begin(1);  // Milliseconds gate interval
  FreqMeasure.begin();

  // Start with zero host rate (no continuous stepping until host publishes)
  setMicrostepsPerSec(0.0);

  // enable DWT cycle counter
  enableCycleCounter();

  // start ISR timer
  stepTimer.begin(stepISR, ISR_PERIOD_US);
}

void loop() {
  static unsigned long lastDebugMs = 0;

  enable  = digitalReadFast(PIN_HOST_ENABLE) ? HIGH : LOW;
  enable_ = (enable == HIGH) ? LOW : HIGH;
  digitalWrite(PIN_AEN, enable); digitalWrite(PIN_AENB, enable_);
  digitalWrite(PIN_BEN, enable); digitalWrite(PIN_BENB, enable_);
  digitalWrite(PIN_LED, enable);

  // 2 Hz debug printing
  if (ENABLE_DEBUG && (millis() - lastDebugMs >= 500)) {
    Serial.print("freqCount="); Serial.print(freqCount);
    Serial.print(" freqMeasure="); Serial.print(freqMeasure);
    Serial.print(" freqMeasureHz="); Serial.print(freqMeasureHz);
    Serial.print(" OCM1="); Serial.print(latestRaw1);
    Serial.print(" OCM2="); Serial.print(latestRaw2);
    Serial.println(" ");

    lastDebugMs = millis();
  }

  delay(1);
}

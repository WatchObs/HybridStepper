/*
  Sinusoidal micro stepper with loss-of-pulses safety
  - External STEP on pin 21 used only for measurement (freq)
  - ISR integrates published host rate (indices per ISR) into a float phase accumulator
  - If no STEP edges seen for LOSS_TIMEOUT_MS, published rate is forced to zero
*/

#include <Arduino.h>
#include <stdint.h>
#include <math.h>
#include <FreqMeasure.h>

// Loss-of-pulses timeout (milliseconds)
const unsigned long LOSS_TIMEOUT_MS = 1000UL; // 1 second  TODO

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

const int BPWM_FREQ = 2000;

const int PIN_OCM1 = A1;
const int PIN_OCM2 = A2;

const int PIN_HOST_ENABLE  = 20;
const int PIN_HOST_DIR     = 21;
const int PIN_HOST_FREQMSR = 22;  // FreqMeasure API

const int PIN_RATE_PWM = 11;             // fixed hardware PWM test source
const uint32_t RATE_PWM_FREQ_HZ = 51200/240;

const int PIN_ISR_TOGGLE = 10;  // scope probe

// Waveform / motor geometry
const int cntLUT = 1024;                               // Table entries per electrical cycle
const float cyclesPerRev = 50;                         // Electrical cycles per mechanical revolution
const float phaseConv = cntLUT / 360.f;                // Convert magnetic phase angle to LUT index
const float microStepsPerRev = cntLUT * cyclesPerRev;  // Microsteps per motor revolution
const int PWM_BITS = 10;                               // PWM resolution
const float PWM_MAG = (float)(pow(2, PWM_BITS)-1);     // PWM magnitude

// ISR timing
const uint32_t ISR_FREQ_HZ   = 10000UL; // ISR ticks per second
const uint32_t ISR_PERIOD_US = 1000000UL / ISR_FREQ_HZ;

// Host rate steps/sec conversion to magnetic phase
const float hostRTconv = 360.0/(ISR_FREQ_HZ * cntLUT);

// ADC
const int ADC_BITS = 12;

// --- Shared state (volatile for ISR/main) ---
volatile float phaseA_f = 0.0f;             // Magnetic angle
volatile float dirSign = 1;                 // +1 CW, -1 CCW
volatile int8_t enableDrv = HIGH;           // Host enableDrv
volatile int8_t enableDrv_ = LOW;           // Host enableDrv inverse (bar)
volatile unsigned long freqMeasure = 0;     // Host step counts per second (rate)
volatile float freqMeasureHz = 0.f;         // Host step frequency
volatile float pwmGain = 0.3f;              // Gain on PWM amplitude

// PWM outputs (written by ISR)
volatile uint16_t pwmA_pos = 0, pwmA_neg = 0, pwmB_pos = 0, pwmB_neg = 0;

// Driver motor currents
volatile uint16_t rawOCM1 = 0, rawOCM2 = 0;
volatile float    avgOCM1Cur = 0, avgOCM2Cur = 0;
const int avgAdcCnt = 10;
const float convOCM2Cur = 2.f*(3.3f/(float)pow(2,ADC_BITS))/(float)avgAdcCnt;

// --- Look Up Tables (fast + Sine) ---
const float thres = sin(22.5 / 360.f * 2.0 * M_PI);
static float fastLUT[cntLUT];
static float sineLUT[cntLUT];
static void setupLUTs() 
{
  for (int n = 0; n < cntLUT; ++n) 
  {
    float a = sinf((float)n * 2.0 * M_PI / (float)cntLUT);
    sineLUT[n] = a * PWM_MAG;
    if      (a >=  thres) fastLUT[n] =  PWM_MAG;
    else if (a <  -thres) fastLUT[n] = -PWM_MAG;
    else                  fastLUT[n] =      0.;
    Serial.print("Angle="); Serial.print(n*360/cntLUT);
    Serial.print(" Sine="); Serial.print(sineLUT[n]);
    Serial.print(" Fast="); Serial.println(fastLUT[n]);
  }
}

// Interpolated lookup using float index
static inline float lookupInterpolatedFloat(float phase) 
{
  float idx = phase * phaseConv;
  if (idx >= (float)cntLUT) idx -= floorf(idx / (float)cntLUT) * (float)cntLUT;
  if (idx < 0.0f) idx += ceilf(-idx / (float)cntLUT) * (float)cntLUT;
  int i = (int)floorf(idx);
  float frac = idx - (float)i;
  int j = (i + 1 >= cntLUT) ? 0 : i + 1;
  float v0 = sineLUT[i];
  float v1 = sineLUT[j];
  float interp = v0 + (v1 - v0) * frac;
  return interp;
}

// IntervalTimer
IntervalTimer stepTimer;

// --- ISR: measurement + integration ---
void stepISR() 
{
  static int subBandAdc = 0;
  static int avgCntAdc  = 0;

  digitalWriteFast(PIN_ISR_TOGGLE, HIGH);  // Debug

  // 1) Sample host step frequency, direction and enable
  enableDrv  = digitalReadFast(PIN_HOST_ENABLE) ? LOW : HIGH;
  enableDrv_ = (enableDrv == HIGH) ? LOW : HIGH;
  dirSign    = digitalReadFast(PIN_HOST_DIR) ? 1.0f : -1.0f;

  if (FreqMeasure.available()) 
  {
    freqMeasure   = FreqMeasure.read();
    freqMeasureHz = FreqMeasure.countToFrequency(freqMeasure);
  }

  // 2) Phase integration from host rate (float read is atomic on 32-bit)
  float magRate = freqMeasureHz * hostRTconv;  // Magnetic degrees/sec
  if (enableDrv == HIGH)
  {
    phaseA_f += dirSign * magRate;
    if      (phaseA_f >= 360.f) phaseA_f -= 360.f;
    else if (phaseA_f <  0.0f)  phaseA_f += 360.f;
  }

  // 3) Compute channel B (quarter period ahead) and lookup
  float phaseB_f = phaseA_f + 90.f;
  if (phaseB_f >= 360.f) phaseB_f -= 360.f;
  
//float valA = lookupInterpolatedFloat(phaseA_f);
//float valB = lookupInterpolatedFloat(phaseB_f);

  float valA = 0.;
  float valB = 0.;
  
  if (freqMeasureHz < 100000)
  {
    valA = sineLUT[(int)(phaseA_f * phaseConv)];
    valB = sineLUT[(int)(phaseB_f * phaseConv)];
  }
  else
  {
    valA = fastLUT[(int)(phaseA_f * phaseConv)];
    valB = fastLUT[(int)(phaseB_f * phaseConv)];
  }

  // Fade PWM levels to control current
  valA *= pwmGain;
  valB *= pwmGain;
  
  if (valA < 0.) { pwmA_pos = 0; pwmA_neg = (uint16_t)(-valA); } else { pwmA_pos = (uint16_t)valA; pwmA_neg = 0; }
  if (valB < 0.) { pwmB_pos = 0; pwmB_neg = (uint16_t)(-valB); } else { pwmB_pos = (uint16_t)valB; pwmB_neg = 0; }

  // 4) Write PWM, enable and direction outputs
  digitalWrite(PIN_AEN,  enableDrv); 
  digitalWrite(PIN_AENB, enableDrv_);
  digitalWrite(PIN_BEN,  enableDrv); 
  digitalWrite(PIN_BENB, enableDrv_);
  analogWrite(PIN_APWM1, pwmA_pos);
  analogWrite(PIN_APWM2, pwmA_neg);
  analogWrite(PIN_BPWM1, pwmB_pos);
  analogWrite(PIN_BPWM2, pwmB_neg);

  // 5) ADC
  if (subBandAdc == 0)
  {
    rawOCM1 += analogRead(PIN_OCM1);
    subBandAdc = 1;
  }
  else
  {
    rawOCM2 += analogRead(PIN_OCM2);
    subBandAdc = 0;
    avgCntAdc++;  // do once per sub band cycle
  }

  if (avgCntAdc > avgAdcCnt)
  {
    avgOCM1Cur = rawOCM1 * convOCM2Cur;
    avgOCM2Cur = rawOCM2 * convOCM2Cur;
    rawOCM1 = 0;
    rawOCM2 = 0;
    avgCntAdc = 0;
  }

  digitalWrite(PIN_LED, enableDrv);       // Debug
  digitalWriteFast(PIN_ISR_TOGGLE, LOW);  // Debug
}

void setup() 
{
  Serial.begin(115200);
  while (!Serial && millis() < 2000) {}
  Serial.println("Sinusoidal micro-stepper");

  // pins
  pinMode(PIN_AEN, OUTPUT); 
  pinMode(PIN_AENB, OUTPUT);
  pinMode(PIN_APWM1, OUTPUT); 
  pinMode(PIN_APWM2, OUTPUT);
  pinMode(PIN_BEN, OUTPUT); 
  pinMode(PIN_BENB, OUTPUT);
  pinMode(PIN_BPWM1, OUTPUT); 
  pinMode(PIN_BPWM2, OUTPUT);
  pinMode(PIN_LED, OUTPUT);

  pinMode(PIN_HOST_ENABLE, INPUT_PULLUP);
  pinMode(PIN_HOST_DIR, INPUT_PULLUP);

  pinMode(PIN_ISR_TOGGLE, OUTPUT);
  digitalWriteFast(PIN_ISR_TOGGLE, LOW);

  // Common to all PWMs
  analogWriteResolution(PWM_BITS); 

  // TEST - Configure fixed hardware PWM on PIN_RATE_PWM once and never touch it again
  pinMode(PIN_RATE_PWM, OUTPUT);
  analogWriteFrequency(PIN_RATE_PWM, RATE_PWM_FREQ_HZ);
  analogWrite(PIN_RATE_PWM, (int)100); // set and leave

  // Configure other PWM outputs
  analogWriteFrequency(PIN_APWM1, BPWM_FREQ);
  analogWriteFrequency(PIN_APWM2, BPWM_FREQ);
  analogWriteFrequency(PIN_BPWM1, BPWM_FREQ);
  analogWriteFrequency(PIN_BPWM2, BPWM_FREQ);

  analogReadResolution(ADC_BITS);
  analogReadAveraging(1);  // No averaging to speed up

  // Direction sign
  dirSign = 1;

  setupLUTs();

  // Setup frequency counter/measure
  FreqMeasure.begin();

  // start ISR timer
  stepTimer.begin(stepISR, ISR_PERIOD_US);
}

void loop() {
  static unsigned long lastDebugMs = 0;

  // 2 Hz debug printing
  if (1 && (millis() - lastDebugMs >= 500))
  {
    Serial.print(" freqMeasure="); Serial.print(freqMeasure);
    Serial.print(" freqMeasureHz="); Serial.print(freqMeasureHz);
    Serial.print(" phaseA_f="); Serial.print(phaseA_f);
    Serial.print(" OCM1="); Serial.print(avgOCM1Cur);
    Serial.print(" OCM2="); Serial.print(avgOCM2Cur);
    Serial.println(" ");

    lastDebugMs = millis();
  }

  delay(1);
}

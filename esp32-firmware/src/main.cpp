#include <Arduino.h>
#include <Wire.h>
#include <DHT.h>
#include <WiFi.h>
#include <esp_wifi.h>
#include <Firebase_ESP_Client.h>
#include <addons/TokenHelper.h>
#include <addons/RTDBHelper.h>
#include <hd44780.h>
#include <hd44780ioClass/hd44780_I2Cexp.h>
#include <NTPClient.h>
#include <WiFiUdp.h>
#include <time.h>
#include <EEPROM.h>
#include <WiFiManager.h>  

//  DEVICE / FIREBASE PATH 
const char* DEVICE_ID = "ESP_001";
String fbBase;
//  FIREBASE 
#define API_KEY      "YOUR_API_KEY"
#define DATABASE_URL "https://your-project-id.firebaseio.com"

FirebaseData fbdo;
FirebaseAuth auth;
FirebaseConfig config;

bool firebaseStarted = false;
unsigned long lastFirebaseTry = 0;
constexpr unsigned long FIREBASE_RETRY_MS = 5000;

//  LCD I2C 
hd44780_I2Cexp lcd;
constexpr uint8_t I2C_SDA = 21;
constexpr uint8_t I2C_SCL = 22;

//  DHT 
constexpr uint8_t DHTPIN  = 14;
constexpr uint8_t DHTTYPE = DHT22;
DHT dht(DHTPIN, DHTTYPE);
float h = 0, t = 0;
bool dhtOK = true;

//  RELAYS 
constexpr uint8_t RELAY1_PIN = 23;
constexpr uint8_t RELAY2_PIN = 19;
constexpr uint8_t RELAY_ACTIVE_LEVEL = HIGH;

static inline void relayWrite(uint8_t pin, bool on) {
  digitalWrite(pin, on ? RELAY_ACTIVE_LEVEL : (uint8_t)!RELAY_ACTIVE_LEVEL);
}
static inline bool relayRead(uint8_t pin) {
  return (digitalRead(pin) == RELAY_ACTIVE_LEVEL);
}

//  LED HEARTBEAT 
constexpr uint8_t LED_PIN = 2; 
unsigned long lastLedToggle = 0;
bool ledState = false;
constexpr unsigned long LED_BLINK_MS = 500; 

//  TIMERS 
unsigned long lastLCD        = 0;
unsigned long lastFB         = 0;
unsigned long lastRelayPoll  = 0;
unsigned long lastTimeUpdate = 0;
unsigned long lastCfgPoll    = 0;
unsigned long lastDHT        = 0;

unsigned long lastWiFiCheck     = 0;
unsigned long wifiConnectStart  = 0;
unsigned long lastWifiRetry     = 0;

constexpr unsigned long LCD_UPDATE_MS   = 1000;
constexpr unsigned long FB_UPDATE_MS    = 5000;
constexpr unsigned long RELAY_POLL_MS   = 300;
constexpr unsigned long TIME_UPDATE_MS  = 10000;
constexpr unsigned long CFG_POLL_MS     = 2000;
constexpr unsigned long DHT_READ_MS     = 2000;

constexpr unsigned long WIFI_CHECK_MS          = 2000;
constexpr unsigned long WIFI_CONNECT_TIMEOUT   = 8000;
constexpr unsigned long WIFI_RETRY_INTERVAL    = 10000;



// WIFI PORTAL (Flutter RESET_WIFI) 
static constexpr const char* PORTAL_SSID = "ESP_001_SET";
static constexpr const char* PORTAL_PASS = "";        
constexpr unsigned long PORTAL_TIMEOUT_S = 180;       

String fbResetWifiPath; // "/DEVICES/ESP_001/COMMAND/RESET_WIFI"

//  NTP 
const long utcOffsetInSeconds = 7 * 3600;
WiFiUDP ntpUDP;
NTPClient timeClient(ntpUDP, "asia.pool.ntp.org", utcOffsetInSeconds);
char daysOfTheWeek[7][12] = {"Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"};

//  STATE 
bool wifiOK = false;
bool wifiConnecting = false;

bool autoMode       = false;
bool lastAutoMode   = false;
bool spChanged      = false;

bool lastRelayState1 = false;
bool lastRelayState2 = false;

float tempSetpoint     = 30.0;
float lastTempSetpoint = 30.0;
constexpr float TEMP_HYST = 0.5;

// STATS (MIN/MAX) 
// min/max theo NGÀY: reset khi đổi ngày (theo NTP local time)
float tMinStat =  9999.0f;
float tMaxStat = -9999.0f;
float hMinStat =  9999.0f;
float hMaxStat = -9999.0f;

int lastDateKey = -1; // yyyymmdd, -1 nghĩa là chưa có ngày

static inline void statsResetForNewDay(float tt, float hh) {
  tMinStat = tt;
  tMaxStat = tt;
  hMinStat = hh;
  hMaxStat = hh;
}

static inline void statsUpdate(float tt, float hh) {
  if (tt < tMinStat) tMinStat = tt;
  if (tt > tMaxStat) tMaxStat = tt;
  if (hh < hMinStat) hMinStat = hh;
  if (hh > hMaxStat) hMaxStat = hh;
}

//  LCD MODE 
enum LcdMode { LCD_MAIN, LCD_INFO };
LcdMode lcdMode = LCD_MAIN;
unsigned long lcdInfoExpire = 0;
String lcdInfoL1, lcdInfoL2;

//  EEPROM 
#define EEPROM_SIZE          64
const uint32_t EEPROM_MAGIC = 0xDEADBEEF;
#define EEPROM_ADDR_MAGIC        0
#define EEPROM_ADDR_SETPOINT     4
#define EEPROM_ADDR_AUTOMODE     8

//  CUSTOM ICONS 
byte iconThermo[8] = {B00100,B01010,B01010,B01010,B01010,B01110,B01110,B00100};
byte iconDrop[8]   = {B00100,B00100,B01010,B01010,B10001,B10001,B10001,B01110};
byte iconWifi[8]   = {B00000,B00000,B10001,B01010,B00100,B00000,B00000,B00000};
byte iconWifiErr[8]= {B00000,B10001,B01010,B00100,B00100,B01010,B10001,B00000};

// FAST RECONNECT (EVENT-DRIVEN) + DEBOUNCE POPUP
volatile bool wifiEventDisconnected = false;
volatile bool wifiEventGotIP        = false;

unsigned long lastFastReconnectTry  = 0;
constexpr unsigned long FAST_RECONNECT_GUARD_MS = 1500;

unsigned long wifiDownSince = 0;
unsigned long wifiUpSince   = 0;

// debounce popup
constexpr unsigned long WIFI_DOWN_DEBOUNCE_MS = 500; // mất >2s mới popup
constexpr unsigned long WIFI_UP_DEBOUNCE_MS   = 1000; // ổn định >1.5s mới popup

bool shownWifiDown = false;
bool shownWifiUp   = false;

void WiFiEventHandler(WiFiEvent_t event) {
  switch (event) {
    case ARDUINO_EVENT_WIFI_STA_DISCONNECTED:
      wifiEventDisconnected = true;
      wifiEventGotIP = false;
      break;

    case ARDUINO_EVENT_WIFI_STA_GOT_IP:
      wifiEventGotIP = true;
      wifiEventDisconnected = false;
      break;

    default:
      break;
  }
}

// EEPROM CONFIG
void saveConfigToEEPROM() {
  EEPROM.put(EEPROM_ADDR_MAGIC, EEPROM_MAGIC);
  EEPROM.put(EEPROM_ADDR_SETPOINT, tempSetpoint);
  EEPROM.put(EEPROM_ADDR_AUTOMODE, autoMode);
  EEPROM.commit();
}

void loadConfigFromEEPROM() {
  uint32_t magic = 0;
  EEPROM.get(EEPROM_ADDR_MAGIC, magic);

  if (magic == EEPROM_MAGIC) {
    EEPROM.get(EEPROM_ADDR_SETPOINT, tempSetpoint);
    EEPROM.get(EEPROM_ADDR_AUTOMODE, autoMode);
    if (tempSetpoint <= 0 || tempSetpoint >= 60) tempSetpoint = 30.0;
  } else {
    tempSetpoint = 30.0;
    autoMode = false;
    saveConfigToEEPROM();
  }
}

// LCD
static String pad16(String s){
  if (s.length() > 16) return s.substring(0,16);
  while (s.length() < 16) s += ' ';
  return s;
}

void lcd_show_info(const String &l1, const String &l2, unsigned long ms) {
  lcdMode = LCD_INFO;
  lcdInfoExpire = millis() + ms;
  lcdInfoL1 = l1;
  lcdInfoL2 = l2;

  lcd.clear();
  lcd.setCursor(0, 0);
  lcd.print(pad16(lcdInfoL1));
  lcd.setCursor(0, 1);
  lcd.print(pad16(lcdInfoL2));
}

static int getLocalDateKey_yyyymmdd() {
  if (!timeClient.isTimeSet()) return -1;

  // NTPClient epoch đã cộng offset (local time)
  time_t localEpoch = (time_t)timeClient.getEpochTime();
  struct tm ti;
  gmtime_r(&localEpoch, &ti); // dùng gmtime vì epoch đã là local-time

  int y = ti.tm_year + 1900;
  int m = ti.tm_mon + 1;
  int d = ti.tm_mday;
  return y * 10000 + m * 100 + d;
}

void lcd_show_main() {
  if (!wifiOK) {
    lcd.setCursor(0, 0);
    lcd.print(pad16("NO WIFI"));
    lcd.setCursor(15, 0);
    lcd.write((uint8_t)3);
    lcd.setCursor(0, 1);
    lcd.print(pad16("ESP_001_SET 192.168.4.1"));
    return;
  }

  String dayStr  = daysOfTheWeek[timeClient.getDay()];
  String timeStr = timeClient.getFormattedTime().substring(0, 5);

  time_t raw = (time_t)timeClient.getEpochTime(); // local epoch
  struct tm ti;
  gmtime_r(&raw, &ti);

  char datebuf[6];
  snprintf(datebuf, sizeof(datebuf), "%02d/%02d", ti.tm_mday, ti.tm_mon + 1);

  String line1 = dayStr + " " + String(datebuf) + " " + timeStr;
  lcd.setCursor(0, 0);
  lcd.print(pad16(line1));
  lcd.setCursor(15, 0);
  lcd.write((uint8_t)2);

  lcd.setCursor(0, 1);
  if (!dhtOK) {
    lcd.print(pad16("DHT ERR"));
  } else {
    const char DEG = char(223);
    String s;
    s += char(0); s += ":"; s += String(t,1); s += DEG;
    s += " ";
    s += char(1); s += ":"; s += String(h,1); s += "%";
    lcd.print(pad16(s));
  }
}

void lcd_show_relay_status(bool r1, bool r2) {
  if (!autoMode) {
    String l1 = String("BUZZER:") + (r1 ? "ON" : "OFF");
    String l2 = String("LIGHT :") + (r2 ? "ON" : "OFF");
    lcd_show_info(l1, l2, 1500);
  } else {
    String l1 = String("RELAY2:") + (r2 ? "ON" : "OFF");
    lcd_show_info(l1, "AUTO MODE", 1200);
  }
}

void lcd_task() {
  if (lcdMode == LCD_INFO) {
    if ((long)(millis() - lcdInfoExpire) >= 0) {
      lcdMode = LCD_MAIN;
      lcd.clear();
      lcd_show_main();
    }
  } else {
    lcd_show_main();
  }
}

// DHT
void read_dht22() {
  float hh = dht.readHumidity();
  float tt = dht.readTemperature();

  if (isnan(hh) || isnan(tt)) {
    dhtOK = false;
    return;
  }

  h = hh;
  t = tt;
  dhtOK = true;

  // reset min/max khi đổi ngày (theo NTP)
  int key = getLocalDateKey_yyyymmdd();
  if (key != -1 && key != lastDateKey) {
    lastDateKey = key;
    statsResetForNewDay(t, h);
  } else {
    statsUpdate(t, h);
  }
}

// WiFi helpers
static bool connectSavedWiFi(uint32_t timeoutMs = 15000) {
  WiFi.mode(WIFI_STA);
  WiFi.setAutoReconnect(true);
  WiFi.setSleep(false);

  WiFi.disconnect(false, false);
  delay(100);

  Serial.println("[WiFi] Trying connect using saved credentials (WiFi.begin())...");
  WiFi.begin();

  uint32_t start = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - start < timeoutMs) {
    delay(200);
    yield();
  }

  if (WiFi.status() == WL_CONNECTED) {
    Serial.printf("[WiFi] Connected. SSID='%s' IP=%s\n",
                  WiFi.SSID().c_str(),
                  WiFi.localIP().toString().c_str());
    return true;
  }

  Serial.println("[WiFi] Connect saved failed.");
  return false;
}

// WiFiManager Portal
void startWiFiPortal(bool resetSettingsFirst) {
  Serial.println("[Portal] Start WiFiManager portal: ESP_001_SET");

  WiFi.disconnect(true, true);
  delay(300);
  WiFi.mode(WIFI_STA);
  WiFi.setSleep(false);

  WiFiManager wm;
  wm.setDebugOutput(true);

  if (resetSettingsFirst) {
    Serial.println("[Portal] resetSettings (clear saved WiFi) ...");
    wm.resetSettings();
    delay(300);
  }

  wm.setConfigPortalTimeout((int)PORTAL_TIMEOUT_S);
  wm.setConnectTimeout(25);
  wm.setBreakAfterConfig(true);

  lcd_show_info("AP: ESP_001_SET", "192.168.4.1", 2000);

  bool ok = wm.startConfigPortal(PORTAL_SSID, PORTAL_PASS);

  Serial.println(ok ? "[Portal] Got WiFi -> reboot" : "[Portal] Timeout -> reboot");
  lcd_show_info(ok ? "WIFI SAVED" : "PORTAL TIMEOUT", "Reboot...", 1500);
  delay(800);
  ESP.restart();
}

// checkWiFi (polling backup)
void checkWiFi() {
  wl_status_t s = WiFi.status();

  if (s == WL_CONNECTED) {
    wifiOK = true;
    wifiConnecting = false;
    return;
  }

  wifiOK = false;

  unsigned long now = millis();

  if (wifiConnecting) {
    if (now - wifiConnectStart > WIFI_CONNECT_TIMEOUT) {
      wifiConnecting = false;
      lastWifiRetry = now;
    }
    return;
  }

  if (now - lastWifiRetry >= WIFI_RETRY_INTERVAL) {
    WiFi.reconnect();

    wifiConnecting   = true;
    wifiConnectStart = now;
    lastWifiRetry    = now;
  }
}

// Firebase
void firebaseInit() {
  config.api_key      = API_KEY;
  config.database_url = DATABASE_URL;
  config.token_status_callback = tokenStatusCallback;

  fbdo.setResponseSize(4096);
  config.timeout.serverResponse = 5000;

  if (Firebase.signUp(&config, &auth, "", "")) {
    Serial.println(F("[FB] SignUp OK"));
  } else {
    Serial.printf("[FB] SignUp failed: %s\n",
                  config.signer.signupError.message.c_str());
    firebaseStarted = false;
    return;
  }

  Firebase.begin(&config, &auth);
  Firebase.reconnectWiFi(true);
  firebaseStarted = true;
}

void ensureResetWifiNodeExists() {
  if (!Firebase.ready()) return;
  bool v;
  if (!Firebase.RTDB.getBool(&fbdo, fbResetWifiPath.c_str(), &v)) {
    Firebase.RTDB.setBool(&fbdo, fbResetWifiPath.c_str(), false);
  }
}

void readConfigFromFirebase() {
  if (!Firebase.ready()) return;

  bool modeChanged = false;
  spChanged        = false;
  lastAutoMode     = autoMode;
  lastTempSetpoint = tempSetpoint;

  int modeVal;
  if (Firebase.RTDB.getInt(&fbdo, fbBase + "/CONFIG/MODE", &modeVal)) {
    autoMode = (modeVal != 0);
    if (autoMode != lastAutoMode) modeChanged = true;
  }

  float sp;
  if (Firebase.RTDB.getFloat(&fbdo, fbBase + "/CONFIG/SETPOINT", &sp)) {
    if (sp > 0 && sp < 60) {
      if (sp != tempSetpoint) spChanged = true;
      tempSetpoint = sp;
    }
  }

  if (modeChanged) {
    if (autoMode) {
      String spLine = "SET:" + String(tempSetpoint, 1) + String(char(223)) + "C";
      lcd_show_info("MODE: AUTO", spLine, 2000);
    } else {
      lcd_show_info("MODE: MANUAL", "FB RELAY CMD", 2000);
    }
  }

  if (spChanged) {
    String spLine2 = String(tempSetpoint, 1) + String(char(223)) + "C";
    lcd_show_info("SETPOINT", spLine2, 2000);
  }

  if (modeChanged || spChanged) saveConfigToEEPROM();
}

void autoControlRelay() {
  if (!autoMode || !dhtOK) return;

  bool state = relayRead(RELAY2_PIN);
  if (t > tempSetpoint + TEMP_HYST) state = true;
  else if (t < tempSetpoint - TEMP_HYST) state = false;

  relayWrite(RELAY2_PIN, state);
  lastRelayState2 = state;
}

void uploadToFirebase() {
  if (!Firebase.ready()) return;

  timeClient.update();

  // epoch UTC 
  time_t nowEpochUtc = (time_t)timeClient.getEpochTime() - utcOffsetInSeconds;

  String dayStr  = daysOfTheWeek[timeClient.getDay()];
  String timeStr = timeClient.getFormattedTime();
  String formattedDayTime = dayStr + String(",") + timeStr;

  String tempLog = formattedDayTime + " T:" + String(t, 1) + "C";
  String humiLog = formattedDayTime + " H:" + String(h, 1) + "%";

  bool r1 = relayRead(RELAY1_PIN);
  bool r2 = relayRead(RELAY2_PIN);

  FirebaseJson json;
  if (dhtOK) {
    json.set("TEMP", t);
    json.set("HUMI", h);
    json.set("DHT_OK", true);
    json.set("LOG/TEMP_LAST", tempLog);
    json.set("LOG/HUMI_LAST", humiLog);

    // STATS: min/max theo ngày
    json.set("STATS/TMAX", tMaxStat);
    json.set("STATS/TMIN", tMinStat);
    json.set("STATS/HMAX", hMaxStat);
    json.set("STATS/HMIN", hMinStat);
    json.set("STATS/DATEKEY", lastDateKey); // để app biết stats thuộc ngày nào (yyyymmdd)
  } else {
    json.set("DHT_OK", false);
  }

  json.set("STATE/RELAY1", r1);
  json.set("STATE/RELAY2", r2);
  json.set("LAST_UPDATE", (int)nowEpochUtc);

  if (!Firebase.RTDB.updateNode(&fbdo, fbBase, &json)) {
    Serial.printf("[FB] updateNode failed: %s\n", fbdo.errorReason().c_str());
  }
}

// RESET_WIFI handler (Flutter)
void handleResetWifiPortalFromFirebase() {
  Serial.println("[WiFi] RESET_WIFI=true -> open portal");

  if (Firebase.ready()) {
    Firebase.RTDB.setBool(&fbdo, fbResetWifiPath.c_str(), false);
  }

  wifiOK = false;
  wifiConnecting = false;

  startWiFiPortal(true);
}

void clearResetWifiFlagAtBoot() {
  if (!Firebase.ready()) return;

  bool v = false;
  if (Firebase.RTDB.getBool(&fbdo, fbResetWifiPath.c_str(), &v)) {
    if (v) {
      Serial.println("[BOOT] RESET_WIFI was TRUE -> clear to FALSE");
      Firebase.RTDB.setBool(&fbdo, fbResetWifiPath.c_str(), false);
      delay(200);
    }
  } else {
    Firebase.RTDB.setBool(&fbdo, fbResetWifiPath.c_str(), false);
  }
}

// WIFI EVENT PROCESS + DEBOUNCE POPUP
void wifiEventTask() {
  unsigned long now = millis();

  // DISCONNECTED event
  if (wifiEventDisconnected) {
    wifiEventDisconnected = false;

    wifiOK = false;
    wifiConnecting = false;

    if (wifiDownSince == 0) wifiDownSince = now;
    wifiUpSince = 0;

    shownWifiUp = false; // cho phép hiện WiFi OK lần sau

    // thử reconnect nhanh (guard)
    if (now - lastFastReconnectTry >= FAST_RECONNECT_GUARD_MS) {
      lastFastReconnectTry = now;
      Serial.println(F("[WiFi][EV] Fast reconnect..."));
      WiFi.mode(WIFI_STA);
      WiFi.reconnect();
    }
  }

  // GOT_IP event
  if (wifiEventGotIP) {
    wifiEventGotIP = false;

    wifiOK = true;
    wifiConnecting = false;

    if (wifiUpSince == 0) wifiUpSince = now;
    wifiDownSince = 0;

    shownWifiDown = false; // cho phép hiện Mất kết nối lần sau

    if (!timeClient.isTimeSet()) timeClient.begin();
    timeClient.update();
  }

  // Debounce popup DOWN
  if (!wifiOK) {
    if (wifiDownSince == 0) wifiDownSince = now;

    if (!shownWifiDown && (now - wifiDownSince >= WIFI_DOWN_DEBOUNCE_MS)) {
      shownWifiDown = true;
      Serial.println(F("[WiFi] Lost (debounced)"));
      lcd_show_info("Mat ket noi", "Dang thu lai...", 2000);
    }
  }

  // Debounce popup UP
  if (wifiOK) {
    if (wifiUpSince == 0) wifiUpSince = now;

    if (!shownWifiUp && (now - wifiUpSince >= WIFI_UP_DEBOUNCE_MS)) {
      shownWifiUp = true;
      Serial.print(F("[WiFi] OK (debounced) IP="));
      Serial.println(WiFi.localIP());
      lcd_show_info("WiFi OK", WiFi.localIP().toString(), 2000);
    }
  }
}

// LED blink task
void ledTask() {
  unsigned long now = millis();
  if (now - lastLedToggle >= LED_BLINK_MS) {
    lastLedToggle = now;
    ledState = !ledState;
    digitalWrite(LED_PIN, ledState ? HIGH : LOW);
  }
}

// SETUP
void setup() {
  Serial.begin(115200);
  delay(200);

  WiFi.onEvent(WiFiEventHandler);

  Serial.printf("Reset reason: %d\n", (int)esp_reset_reason());
  fbBase = "/DEVICES/" + String(DEVICE_ID);
  fbResetWifiPath = fbBase + "/COMMAND/RESET_WIFI";

  Serial.print("Firebase base path: ");
  Serial.println(fbBase);

  pinMode(LED_PIN, OUTPUT);
  digitalWrite(LED_PIN, HIGH); // bật ngay khi cấp nguồn

  EEPROM.begin(EEPROM_SIZE);
  loadConfigFromEEPROM();

  pinMode(RELAY1_PIN, OUTPUT);
  pinMode(RELAY2_PIN, OUTPUT);
  relayWrite(RELAY1_PIN, false);
  relayWrite(RELAY2_PIN, false);
  lastRelayState1 = false;
  lastRelayState2 = false;

  dht.begin();
  Wire.begin(I2C_SDA, I2C_SCL);

  lcd.begin(16, 2);
  lcd.clear();
  lcd.createChar(0, iconThermo);
  lcd.createChar(1, iconDrop);
  lcd.createChar(2, iconWifi);
  lcd.createChar(3, iconWifiErr);

  lcd_show_info("BOOT", "Connecting...", 1200);

  // Nếu chưa có Wi-Fi saved -> mở portal ngay
  bool ok = connectSavedWiFi(15000);
  if (!ok) {
    Serial.println("[WiFi] No saved WiFi -> open ESP_001_SET portal");
    startWiFiPortal(false);
    return;
  }

  wifiOK = true;
  wifiUpSince = millis(); // để debounce WiFi OK
  lcd_show_info("WiFi OK", WiFi.localIP().toString(), 2000);

  timeClient.begin();
  timeClient.update();

  // init datekey ngay khi có time
  lastDateKey = getLocalDateKey_yyyymmdd();

  firebaseInit();
  if (firebaseStarted) {
    ensureResetWifiNodeExists();
    clearResetWifiFlagAtBoot();
    delay(800);
    readConfigFromFirebase();
  }

  lcd_show_main();
}

// LOOP
void loop() {
  unsigned long now = millis();
  ledTask();
  wifiEventTask();
  if (now - lastWiFiCheck >= WIFI_CHECK_MS) {
    checkWiFi();
    lastWiFiCheck = now;
  }
  if (wifiOK && !firebaseStarted && (now - lastFirebaseTry >= FIREBASE_RETRY_MS)) {
    lastFirebaseTry = now;
    firebaseInit();
    if (firebaseStarted) ensureResetWifiNodeExists();
  }
  if (!wifiOK) {
    if (now - lastLCD >= LCD_UPDATE_MS) {
      lcd_task();
      lastLCD = now;
    }
    return;
  }
  if (now - lastTimeUpdate >= TIME_UPDATE_MS) {
    timeClient.update();
    lastTimeUpdate = now;
  }
  if (now - lastCfgPoll >= CFG_POLL_MS) {
    if (wifiOK && WiFi.status() == WL_CONNECTED && Firebase.ready()) readConfigFromFirebase();
    lastCfgPoll = now;
  }
  if (now - lastDHT >= DHT_READ_MS) {
    read_dht22();
    autoControlRelay();
    lastDHT = now;
  }
  if (now - lastLCD >= LCD_UPDATE_MS) {
    lcd_task();
    lastLCD = now;
  }
  if (now - lastFB >= FB_UPDATE_MS) {
    if (wifiOK && WiFi.status() == WL_CONNECTED && Firebase.ready()) uploadToFirebase();
  lastFB = now;
  }
  if (wifiOK && WiFi.status() == WL_CONNECTED && Firebase.ready() && (now - lastRelayPoll >= RELAY_POLL_MS)) {
    lastRelayPoll = now;
    static uint8_t rstCnt = 0;
    bool rstWifi = false;

    if (Firebase.RTDB.getBool(&fbdo, fbResetWifiPath.c_str(), &rstWifi)) {
      if (rstWifi) {
        rstCnt++;
        Serial.printf("[CMD] RESET_WIFI true cnt=%u\n", rstCnt);
        if (rstCnt >= 3) {
          handleResetWifiPortalFromFirebase();
          return;
        }
      } else {
        rstCnt = 0;
      }
    }
    bool cmd1 = lastRelayState1;
    if (Firebase.RTDB.getBool(&fbdo, fbBase + "/COMMAND/RELAY1", &cmd1)) {
      if (cmd1 != lastRelayState1) {
        relayWrite(RELAY1_PIN, cmd1);
        lastRelayState1 = cmd1;
        lcd_show_relay_status(lastRelayState1, lastRelayState2);
        Firebase.RTDB.setBool(&fbdo, fbBase + "/STATE/RELAY1", cmd1);
      }
    }
    if (!autoMode) {
      bool cmd2 = lastRelayState2;
      if (Firebase.RTDB.getBool(&fbdo, fbBase + "/COMMAND/RELAY2", &cmd2)) {
        if (cmd2 != lastRelayState2) {
          relayWrite(RELAY2_PIN, cmd2);
          lastRelayState2 = cmd2;
          lcd_show_relay_status(lastRelayState1, lastRelayState2);
          Firebase.RTDB.setBool(&fbdo, fbBase + "/STATE/RELAY2", cmd2);
        }
      }
    }
  }
}

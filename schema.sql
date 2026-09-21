-- Driver Dashboard v46 — SQL persistence schema
-- Records are retained indefinitely unless an explicit cleanup policy is added.
CREATE TABLE IF NOT EXISTS drivers (
  name TEXT PRIMARY KEY,
  driver_id TEXT,
  email TEXT,
  phone TEXT,
  password_hash TEXT,
  password_salt TEXT,
  self_registered INTEGER NOT NULL DEFAULT 0,
  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);
CREATE TABLE IF NOT EXISTS work_days (
  driver_name TEXT NOT NULL,
  work_date TEXT NOT NULL,
  selected INTEGER NOT NULL DEFAULT 1,
  selected_at TEXT,
  stores_json TEXT,
  PRIMARY KEY (driver_name, work_date)
);
CREATE INDEX IF NOT EXISTS idx_work_days_date ON work_days(work_date);
CREATE TABLE IF NOT EXISTS attendance (
  driver_name TEXT NOT NULL,
  attendance_date TEXT NOT NULL,
  am INTEGER NOT NULL DEFAULT 0,
  pm INTEGER NOT NULL DEFAULT 0,
  am_photo_json TEXT,
  pm_photo_json TEXT,
  photo_verified INTEGER NOT NULL DEFAULT 0,
  photo_time TEXT,
  admin_override INTEGER NOT NULL DEFAULT 0,
  override_reason TEXT,
  override_by TEXT,
  override_type TEXT,
  override_proof_json TEXT,
  no_photo_reason TEXT,
  no_photo_note TEXT,
  late_proof_json TEXT,
  pending_approval INTEGER NOT NULL DEFAULT 0,
  approval_status TEXT,
  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (driver_name, attendance_date)
);
CREATE INDEX IF NOT EXISTS idx_attendance_date ON attendance(attendance_date);
CREATE INDEX IF NOT EXISTS idx_attendance_driver_date ON attendance(driver_name, attendance_date);

CREATE UNIQUE INDEX IF NOT EXISTS idx_drivers_email ON drivers(email) WHERE email IS NOT NULL AND email <> '';

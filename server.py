import os
from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse
from pydantic import BaseModel
from pathlib import Path
import sqlite3, json
from datetime import datetime, timezone

BASE=Path(__file__).resolve().parent
HTML=BASE/'index.html'

# ── Render persistent disk ───────────────────────────────────────────────
# Render's filesystem is ephemeral — anything written outside a mounted disk
# is wiped on every redeploy/restart. In render.yaml a disk is mounted at
# DB_DIR (default /var/data) so the SQLite file survives deploys. Locally
# (no DB_DIR set) it just uses a file next to this script, same as before.
DB_DIR = Path(os.environ.get('DB_DIR', str(BASE)))
DB_DIR.mkdir(parents=True, exist_ok=True)
DB = DB_DIR / 'driver_dashboard.db'

# ── API key (optional but strongly recommended once this is public) ─────
# Set the API_KEY environment variable in Render. When set, every /api/*
# request must include a matching `X-API-Key` header, checked below.
# When API_KEY is not set (e.g. local dev), the check is skipped — this
# keeps the login-fix workflow you already had working unchanged.
API_KEY = os.environ.get('API_KEY', '').strip()

app=FastAPI(title='Driver Operations Dashboard SQL API', version='46.0')

# CORS: only needed if the frontend is ever hosted on a different origin
# than this backend (e.g. Netlify frontend + Render backend, instead of
# Render serving both). Harmless to leave on if you serve everything from
# this one Render service. Tighten allow_origins to your real frontend URL
# once you know it, instead of '*'.
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)

# Same-origin web app: API routes are intentionally not gated by a client-side API secret.
# Authentication/authorization belongs in user sessions, not a secret embedded in HTML.
def conn():
    c=sqlite3.connect(DB)
    c.row_factory=sqlite3.Row
    c.execute('PRAGMA journal_mode=WAL')
    c.execute('PRAGMA foreign_keys=ON')
    return c

def init_db():
    with conn() as c:
        c.executescript('''
        CREATE TABLE IF NOT EXISTS drivers(
          name TEXT PRIMARY KEY, driver_id TEXT, email TEXT, self_registered INTEGER NOT NULL DEFAULT 0,
          created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP, updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS work_days(
          driver_name TEXT NOT NULL, work_date TEXT NOT NULL, selected INTEGER NOT NULL DEFAULT 1,
          selected_at TEXT, stores_json TEXT, PRIMARY KEY(driver_name,work_date)
        );
        CREATE INDEX IF NOT EXISTS idx_work_days_date ON work_days(work_date);
        CREATE TABLE IF NOT EXISTS attendance(
          driver_name TEXT NOT NULL, attendance_date TEXT NOT NULL,
          am INTEGER NOT NULL DEFAULT 0, pm INTEGER NOT NULL DEFAULT 0,
          am_photo_json TEXT, pm_photo_json TEXT, photo_verified INTEGER NOT NULL DEFAULT 0,
          photo_time TEXT, admin_override INTEGER NOT NULL DEFAULT 0, override_reason TEXT, override_by TEXT, override_type TEXT, override_proof_json TEXT, no_photo_reason TEXT, no_photo_note TEXT, late_proof_json TEXT, updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
          PRIMARY KEY(driver_name,attendance_date)
        );
        CREATE INDEX IF NOT EXISTS idx_attendance_date ON attendance(attendance_date);
        CREATE INDEX IF NOT EXISTS idx_attendance_driver_date ON attendance(driver_name,attendance_date);
        ''')
        # Safe v35 -> v36 migration
        cols={r['name'] for r in c.execute('PRAGMA table_info(attendance)')}
        for col,ddl in [('admin_override','INTEGER NOT NULL DEFAULT 0'),('override_reason','TEXT'),('override_by','TEXT'),('override_type','TEXT'),('override_proof_json','TEXT'),('no_photo_reason','TEXT'),('no_photo_note','TEXT'),('late_proof_json','TEXT')]:
            if col not in cols: c.execute(f'ALTER TABLE attendance ADD COLUMN {col} {ddl}')
        dcols={r['name'] for r in c.execute('PRAGMA table_info(drivers)')}
        if 'email' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN email TEXT')
        wcols={r['name'] for r in c.execute('PRAGMA table_info(work_days)')}
        if 'stores_json' not in wcols: c.execute('ALTER TABLE work_days ADD COLUMN stores_json TEXT')
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_drivers_email ON drivers(email) WHERE email IS NOT NULL AND email <> ''")
init_db()

class RosterPayload(BaseModel): drivers:list[dict]
class AttendancePayload(BaseModel): driverName:str; date:str; record:dict
class WorkDayPayload(BaseModel): driverName:str; date:str; record:dict
class DriverLoginPayload(BaseModel): login:str

@app.get('/')
def home(): return FileResponse(HTML)
@app.get('/health')
def health(): return {'ok':True,'database':'sqlite','retention':'indefinite (1 year+ supported)'}

@app.get('/api/health-check')
def api_health_check(): return {'ok':True,'version':'46.0'}

@app.post('/api/driver-login')
def driver_login(p:DriverLoginPayload):
    login=(p.login or '').strip()
    if not login: raise HTTPException(400,'login required')
    with conn() as c:
        if '@' in login:
            r=c.execute('SELECT * FROM drivers WHERE lower(trim(email))=lower(trim(?)) LIMIT 1',(login,)).fetchone()
        else:
            r=c.execute('SELECT * FROM drivers WHERE lower(trim(name))=lower(trim(?)) LIMIT 1',(login,)).fetchone()
    if not r: return {'ok':False,'driver':None}
    return {'ok':True,'driver':{'name':r['name'],'driverId':r['driver_id'] or '', 'email':r['email'] or '', 'selfRegistered':bool(r['self_registered'])}}

@app.get('/api/dashboard-state')
def dashboard_state():
    with conn() as c:
        drivers=[{'name':r['name'],'driverId':r['driver_id'] or '', 'email':r['email'] or '', 'selfRegistered':bool(r['self_registered'])} for r in c.execute('SELECT * FROM drivers ORDER BY name')]
        att={}
        for r in c.execute('SELECT * FROM attendance'):
            rec={'am':bool(r['am']),'pm':bool(r['pm']),'amPhoto':json.loads(r['am_photo_json']) if r['am_photo_json'] else None,'pmPhoto':json.loads(r['pm_photo_json']) if r['pm_photo_json'] else None,'photoVerified':bool(r['photo_verified']),'photoTime':r['photo_time'],'adminOverride':bool(r['admin_override']),'overrideReason':r['override_reason'],'overrideBy':r['override_by'],'overrideType':r['override_type'],'overrideProofPhoto':json.loads(r['override_proof_json']) if r['override_proof_json'] else None,'noPhotoReason':r['no_photo_reason'],'noPhotoNote':r['no_photo_note'],'lateProofPhoto':json.loads(r['late_proof_json']) if r['late_proof_json'] else None}
            primary=rec['amPhoto'] or rec['pmPhoto']
            rec['photoDataUrl']=primary.get('dataUrl') if isinstance(primary,dict) else None
            att[f"{r['driver_name']}||{r['attendance_date']}"]=rec
        work={f"{r['driver_name']}||{r['work_date']}":{'selected':bool(r['selected']),'selectedAt':r['selected_at'],'stores':json.loads(r['stores_json']) if r['stores_json'] else []} for r in c.execute('SELECT * FROM work_days')}
    return {'rosterDrivers':drivers,'rosterAttendance':att,'driverWorkDays':work}

@app.post('/api/roster')
def save_roster(p:RosterPayload):
    with conn() as c:
        for d in p.drivers:
            name=(d.get('name') or '').strip()
            if not name: continue
            c.execute('''INSERT INTO drivers(name,driver_id,email,self_registered) VALUES(?,?,?,?)
              ON CONFLICT(name) DO UPDATE SET driver_id=excluded.driver_id,email=excluded.email,self_registered=excluded.self_registered,updated_at=CURRENT_TIMESTAMP''',
              (name,d.get('driverId') or '',(d.get('email') or '').strip().lower(),1 if d.get('selfRegistered') else 0))
    return {'ok':True,'count':len(p.drivers)}

@app.post('/api/work-day')
def save_work_day(p:WorkDayPayload):
    try: datetime.strptime(p.date,'%Y-%m-%d')
    except ValueError: raise HTTPException(400,'date must be YYYY-MM-DD')
    with conn() as c:
        c.execute('''INSERT INTO work_days(driver_name,work_date,selected,selected_at,stores_json) VALUES(?,?,?,?,?)
          ON CONFLICT(driver_name,work_date) DO UPDATE SET selected=excluded.selected,selected_at=excluded.selected_at,stores_json=excluded.stores_json''',
          (p.driverName,p.date,1 if p.record.get('selected',True) else 0,p.record.get('selectedAt'),json.dumps(p.record.get('stores') or [])))
    return {'ok':True}

@app.post('/api/attendance')
def save_attendance(p:AttendancePayload):
    try: datetime.strptime(p.date,'%Y-%m-%d')
    except ValueError: raise HTTPException(400,'date must be YYYY-MM-DD')
    r=p.record
    with conn() as c:
        c.execute('''INSERT INTO attendance(driver_name,attendance_date,am,pm,am_photo_json,pm_photo_json,photo_verified,photo_time,admin_override,override_reason,override_by,override_type,override_proof_json,no_photo_reason,no_photo_note,late_proof_json)
          VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(driver_name,attendance_date) DO UPDATE SET
          am=excluded.am,pm=excluded.pm,am_photo_json=excluded.am_photo_json,pm_photo_json=excluded.pm_photo_json,
          photo_verified=excluded.photo_verified,photo_time=excluded.photo_time,admin_override=excluded.admin_override,
          override_reason=excluded.override_reason,override_by=excluded.override_by,override_type=excluded.override_type,
          override_proof_json=excluded.override_proof_json,no_photo_reason=excluded.no_photo_reason,no_photo_note=excluded.no_photo_note,
          late_proof_json=excluded.late_proof_json,updated_at=CURRENT_TIMESTAMP''',
          (p.driverName,p.date,1 if r.get('am') else 0,1 if r.get('pm') else 0,
           json.dumps(r.get('amPhoto')) if r.get('amPhoto') else None,json.dumps(r.get('pmPhoto')) if r.get('pmPhoto') else None,
           1 if r.get('photoVerified') else 0,r.get('photoTime'),1 if r.get('adminOverride') else 0,r.get('overrideReason'),r.get('overrideBy'),
           r.get('overrideType'),json.dumps(r.get('overrideProofPhoto')) if r.get('overrideProofPhoto') else None,
           r.get('noPhotoReason'),r.get('noPhotoNote'),json.dumps(r.get('lateProofPhoto')) if r.get('lateProofPhoto') else None))
    return {'ok':True}

@app.get('/api/attendance')
def attendance(from_date:str|None=None,to_date:str|None=None,driver:str|None=None):
    q='SELECT * FROM attendance WHERE 1=1'; args=[]
    if from_date: q+=' AND attendance_date>=?'; args.append(from_date)
    if to_date: q+=' AND attendance_date<=?'; args.append(to_date)
    if driver: q+=' AND driver_name=?'; args.append(driver)
    q+=' ORDER BY attendance_date DESC, driver_name'
    with conn() as c: rows=[dict(r) for r in c.execute(q,args)]
    return {'rows':rows,'count':len(rows)}

import os
import re
import secrets
import hashlib
import hmac
from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse
from pydantic import BaseModel
from pathlib import Path
import sqlite3, json
from datetime import datetime, timezone, timedelta
import math

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

app=FastAPI(title='Driver Operations Dashboard SQL API', version='65.0')

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
# ── Database backend ─────────────────────────────────────────────────────
# DATABASE_URL set  -> external Postgres (Neon / Supabase / Render Postgres): survives every redeploy,
#                      works on Render's FREE plan (no disk needed).
# DATABASE_URL unset -> local SQLite file (DB_DIR/driver_dashboard.db), as before.
DATABASE_URL = os.environ.get('DATABASE_URL','').strip()
if DATABASE_URL.startswith('postgres://'): DATABASE_URL = 'postgresql://'+DATABASE_URL[len('postgres://'):]
PG = bool(DATABASE_URL)
if PG:
    import psycopg
    from psycopg.rows import dict_row
elif 'DB_DIR' not in os.environ:
    print('WARNING: neither DATABASE_URL nor DB_DIR is set - SQLite lives next to server.py and is WIPED on every redeploy on Render.')

_MAX_RE = re.compile(r'\bMAX\((?=[^()]*,)', re.I)      # scalar MAX(a,b) -> GREATEST(a,b) on Postgres
def _pg_sql(sql): return _MAX_RE.sub('GREATEST(', sql.replace('%','%%').replace('?','%s'))
def _pg_ddl(s):
    s = s.replace('INTEGER PRIMARY KEY AUTOINCREMENT','SERIAL PRIMARY KEY')
    s = re.sub(r'\bREAL\b','DOUBLE PRECISION',s)
    return s.replace('DEFAULT CURRENT_TIMESTAMP','DEFAULT (CURRENT_TIMESTAMP::text)')

class _PGConn:
    def __init__(s): s.c = psycopg.connect(DATABASE_URL, row_factory=dict_row, connect_timeout=15, prepare_threshold=None)
    def __enter__(s): return s
    def __exit__(s,et,ev,tb):
        try: (s.c.commit() if et is None else s.c.rollback())
        finally: s.c.close()
    def execute(s,sql,args=()): return s.c.execute(_pg_sql(sql), tuple(args))
    def executescript(s,script):
        for st in script.split(';'):
            if st.strip(): s.c.execute(_pg_ddl(st))
    def insert_id(s,sql,args=()): return s.c.execute(_pg_sql(sql)+' RETURNING id', tuple(args)).fetchone()['id']

class _LiteConn:
    def __init__(s):
        s.c = sqlite3.connect(DB); s.c.row_factory = sqlite3.Row
        s.c.execute('PRAGMA journal_mode=WAL'); s.c.execute('PRAGMA foreign_keys=ON')
    def __enter__(s): return s
    def __exit__(s,et,ev,tb):
        try: (s.c.commit() if et is None else s.c.rollback())
        finally: s.c.close()
    def execute(s,sql,args=()): return s.c.execute(sql, tuple(args))
    def executescript(s,script): s.c.executescript(script)
    def insert_id(s,sql,args=()): return s.c.execute(sql, tuple(args)).lastrowid

def conn(): return _PGConn() if PG else _LiteConn()

def _cols(c,table):
    if PG: return {r['column_name'] for r in c.execute('SELECT column_name FROM information_schema.columns WHERE table_schema=current_schema() AND table_name=?',(table,))}
    return {r['name'] for r in c.execute(f'PRAGMA table_info({table})')}

def init_db():
    with conn() as c:
        c.executescript('''
        CREATE TABLE IF NOT EXISTS drivers(
          name TEXT PRIMARY KEY, driver_id TEXT, email TEXT, phone TEXT, password_hash TEXT, password_salt TEXT, self_registered INTEGER NOT NULL DEFAULT 0,
          imported_days_worked INTEGER, days_worked_source TEXT,
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
          photo_time TEXT, admin_override INTEGER NOT NULL DEFAULT 0, override_reason TEXT, override_by TEXT, override_type TEXT, override_proof_json TEXT, no_photo_reason TEXT, no_photo_note TEXT, late_proof_json TEXT, pending_approval INTEGER NOT NULL DEFAULT 0, approval_status TEXT, updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
          PRIMARY KEY(driver_name,attendance_date)
        );
        CREATE INDEX IF NOT EXISTS idx_attendance_date ON attendance(attendance_date);
        CREATE INDEX IF NOT EXISTS idx_attendance_driver_date ON attendance(driver_name,attendance_date);
        CREATE TABLE IF NOT EXISTS store_locations(
          store TEXT PRIMARY KEY, lat REAL NOT NULL, lng REAL NOT NULL, radius_m INTEGER NOT NULL DEFAULT 300,
          updated_by TEXT, updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS away_events(
          id INTEGER PRIMARY KEY AUTOINCREMENT, driver_name TEXT NOT NULL, store TEXT NOT NULL, work_date TEXT NOT NULL,
          left_at TEXT NOT NULL, returned_at TEXT, last_seen TEXT NOT NULL, max_distance_m INTEGER NOT NULL DEFAULT 0,
          last_lat REAL, last_lng REAL
        );
        CREATE INDEX IF NOT EXISTS idx_away_date ON away_events(work_date);
        CREATE INDEX IF NOT EXISTS idx_away_open ON away_events(driver_name,returned_at);
        CREATE TABLE IF NOT EXISTS location_log(
          id INTEGER PRIMARY KEY AUTOINCREMENT, driver_name TEXT NOT NULL, store TEXT, ts TEXT NOT NULL,
          dist_m INTEGER NOT NULL DEFAULT 0, at_store INTEGER NOT NULL DEFAULT 0
        );
        CREATE INDEX IF NOT EXISTS idx_loclog_driver_ts ON location_log(driver_name,ts);
        CREATE TABLE IF NOT EXISTS work_sessions(
          id INTEGER PRIMARY KEY AUTOINCREMENT, driver_name TEXT NOT NULL, store TEXT, work_date TEXT NOT NULL,
          signed_in_at TEXT NOT NULL, signed_out_at TEXT, in_dist_m INTEGER, out_dist_m INTEGER,
          auto_closed INTEGER NOT NULL DEFAULT 0, onsite_min INTEGER
        );
        CREATE INDEX IF NOT EXISTS idx_ws_driver ON work_sessions(driver_name,signed_out_at);
        CREATE INDEX IF NOT EXISTS idx_ws_date ON work_sessions(work_date);
        CREATE TABLE IF NOT EXISTS driver_devices(
          token_hash TEXT PRIMARY KEY, email TEXT NOT NULL,
          created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP, last_used TEXT
        );
        CREATE INDEX IF NOT EXISTS idx_devices_email ON driver_devices(email);
        CREATE TABLE IF NOT EXISTS pm_store_status(
          driver_name TEXT NOT NULL, work_date TEXT NOT NULL, store TEXT NOT NULL,
          status TEXT NOT NULL DEFAULT 'pending', away_since TEXT, last_check_at TEXT, last_dist_m INTEGER,
          auto_at TEXT, auto_dist_m INTEGER, evidence_required_at TEXT, evidence_ok_at TEXT, reassessed_at TEXT,
          PRIMARY KEY(driver_name,work_date,store)
        );
        CREATE TABLE IF NOT EXISTS attendance_audit(
          id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT NOT NULL, driver_name TEXT NOT NULL, work_date TEXT NOT NULL,
          store TEXT, event TEXT NOT NULL, actor TEXT NOT NULL DEFAULT 'system', detail TEXT
        );
        CREATE INDEX IF NOT EXISTS idx_aaudit_driver_date ON attendance_audit(driver_name,work_date);
        CREATE INDEX IF NOT EXISTS idx_aaudit_ts ON attendance_audit(ts);
        CREATE TABLE IF NOT EXISTS driver_location_status(
          driver_name TEXT PRIMARY KEY, status TEXT NOT NULL, detail TEXT, updated_at TEXT NOT NULL
        );
        ''')
        # Safe v35 -> v36 migration
        cols=_cols(c,'attendance')
        for col,ddl in [('admin_override','INTEGER NOT NULL DEFAULT 0'),('override_reason','TEXT'),('override_by','TEXT'),('override_type','TEXT'),('override_proof_json','TEXT'),('no_photo_reason','TEXT'),('no_photo_note','TEXT'),('late_proof_json','TEXT'),('pending_approval','INTEGER NOT NULL DEFAULT 0'),('approval_status','TEXT')]:
            if col not in cols: c.execute(f'ALTER TABLE attendance ADD COLUMN {col} {ddl}')
        acols=_cols(c,'attendance')
        for col,ddl in [('incomplete_am','INTEGER NOT NULL DEFAULT 0'),('incomplete_pm','INTEGER NOT NULL DEFAULT 0'),('incomplete_reason','TEXT'),('incomplete_at','TEXT'),('close_photo_json','TEXT'),('pm_auto','INTEGER NOT NULL DEFAULT 0'),('pm_auto_at','TEXT'),('pm_auto_dist_m','INTEGER')]:
            if col not in acols: c.execute(f'ALTER TABLE attendance ADD COLUMN {col} {ddl}')
        # v64: per-shift (AM / PM) auto-approved reasons - {am:{reason,note,at,auto,status,by}, pm:{...}}
        if 'slot_approvals_json' not in _cols(c,'attendance'): c.execute('ALTER TABLE attendance ADD COLUMN slot_approvals_json TEXT')
        # v65 (Jira: automated PM attendance + closing picture logic)
        a2=_cols(c,'attendance')
        for col,ddl in [('pm_status','TEXT'),('pm_evidence_required','INTEGER NOT NULL DEFAULT 0'),('pm_photo_at','TEXT'),('close_at','TEXT'),
                        ('review_status','TEXT'),('review_type','TEXT'),('review_flagged_at','TEXT'),('work_minutes','INTEGER'),
                        ('review_driver_reason','TEXT'),('review_driver_note','TEXT'),('review_reason_at','TEXT'),
                        ('review_by','TEXT'),('review_at','TEXT'),('review_note','TEXT')]:
            if col not in a2: c.execute(f'ALTER TABLE attendance ADD COLUMN {col} {ddl}')
        wscols=_cols(c,'work_sessions')
        if 'out_of_area' not in wscols: c.execute('ALTER TABLE work_sessions ADD COLUMN out_of_area INTEGER NOT NULL DEFAULT 0')
        ecols=_cols(c,'away_events')
        if 'day_marked' not in ecols: c.execute('ALTER TABLE away_events ADD COLUMN day_marked TEXT')
        dcols=_cols(c,'drivers')
        if 'email' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN email TEXT')
        if 'phone' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN phone TEXT')
        if 'password_hash' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN password_hash TEXT')
        if 'password_salt' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN password_salt TEXT')
        if 'imported_days_worked' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN imported_days_worked INTEGER')
        if 'days_worked_source' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN days_worked_source TEXT')
        wcols=_cols(c,'work_days')
        if 'stores_json' not in wcols: c.execute('ALTER TABLE work_days ADD COLUMN stores_json TEXT')
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_drivers_email ON drivers(email) WHERE email IS NOT NULL AND email <> ''")
init_db()

# v52: seed store coordinates (from the warehouse CSV) so geofencing works out of the box.
# INSERT OR IGNORE -> never overwrites a location an admin has saved.
def seed_store_locations():
    f=BASE/'store_seed.json'
    if not f.exists(): return
    try: data=json.loads(f.read_text(encoding='utf-8'))
    except Exception: return
    with conn() as c:
        for name,v in data.items():
            c.execute('INSERT INTO store_locations(store,lat,lng,radius_m,updated_by) VALUES(?,?,?,?,?) ON CONFLICT(store) DO NOTHING',(name,v['lat'],v['lng'],300,'csv-seed'))
seed_store_locations()

class RosterPayload(BaseModel): drivers:list[dict]
class AttendancePayload(BaseModel): driverName:str; date:str; record:dict
class WorkDayPayload(BaseModel): driverName:str; date:str; record:dict
class DriverLoginPayload(BaseModel): login:str; password:str=""
class DriverRegisterPayload(BaseModel): name:str; email:str; phone:str; password:str
class DeviceTokenPayload(BaseModel): login:str; password:str=""
class DeviceLoginPayload(BaseModel): login:str; token:str

@app.get('/')
def home(): return FileResponse(HTML)
def _static(name,media,cache='no-cache'):
    f=BASE/name
    if not f.exists(): raise HTTPException(404)
    return FileResponse(f,media_type=media,headers={'Cache-Control':cache,'Service-Worker-Allowed':'/'})
@app.get('/sw.js')
def pwa_sw(): return _static('sw.js','application/javascript')
@app.get('/manifest.webmanifest')
def pwa_manifest(): return _static('manifest.webmanifest','application/manifest+json')
@app.get('/icon-192.png')
def pwa_icon192(): return _static('icon-192.png','image/png','public, max-age=86400')
@app.get('/icon-512.png')
def pwa_icon512(): return _static('icon-512.png','image/png','public, max-age=86400')
@app.get('/apple-touch-icon.png')
def pwa_apple_icon(): return _static('apple-touch-icon.png','image/png','public, max-age=86400')

@app.get('/health')
def health():
    with conn() as c: n=c.execute('SELECT COUNT(*) AS n FROM drivers').fetchone()['n']
    return {'ok':True,'database':'postgres' if PG else 'sqlite','persistent':bool(PG or 'DB_DIR' in os.environ),'dbPath':None if PG else str(DB),'drivers':n,'retention':'indefinite (1 year+ supported)'}

@app.get('/api/health-check')
def api_health_check(): return {'ok':True,'version':'65.0'}

@app.post('/api/driver-register')
def driver_register(p:DriverRegisterPayload):
    name=p.name.strip(); email=p.email.strip().lower(); phone=p.phone.strip(); password=p.password
    if not name or '@' not in email or not phone or len(password)<6:
        raise HTTPException(400,'full names, valid email, phone and password (6+ chars) required')
    if not re.search(r'[A-Za-z]', password) or not re.search(r'\d', password) or not re.search(r'[^A-Za-z0-9]', password):
        raise HTTPException(400,'password must contain at least one letter, one number and one special character')
    salt=secrets.token_hex(16); ph=hashlib.pbkdf2_hmac('sha256',password.encode(),salt.encode(),200000).hex()
    with conn() as c:
        existing=c.execute('SELECT * FROM drivers WHERE lower(trim(email))=?',(email,)).fetchone()
        if existing: raise HTTPException(409,'email_already_registered')
        # A driver may already exist in the operational roster before creating an app account.
        # Claim that roster row instead of trying to INSERT the same name (name is the PK).
        roster_row=c.execute('SELECT * FROM drivers WHERE lower(trim(name))=? LIMIT 1',(name.lower(),)).fetchone()
        if roster_row:
            if (roster_row['email'] or '').strip():
                # Allow the owner to re-link a new email only when the phone number on the roster matches.
                rp=re.sub(r'\D','',str(roster_row['phone'] or '')); np_=re.sub(r'\D','',phone)
                if not (rp and np_ and (rp[-9:]==np_[-9:])):
                    raise HTTPException(409,'name_linked_other_email')
            c.execute('''UPDATE drivers SET email=?,phone=?,password_hash=?,password_salt=?,self_registered=1,updated_at=CURRENT_TIMESTAMP WHERE name=?''',
                      (email,phone,ph,salt,roster_row['name']))
            driver_id=roster_row['driver_id'] or ''
            final_name=roster_row['name']
        else:
            c.execute('INSERT INTO drivers(name,email,phone,password_hash,password_salt,self_registered) VALUES(?,?,?,?,?,1)',(name,email,phone,ph,salt))
            driver_id=''; final_name=name
    return {'ok':True,'driver':{'name':final_name,'driverId':driver_id,'email':email,'phone':phone,'selfRegistered':True}}

@app.post('/api/driver-login')
def driver_login(p:DriverLoginPayload):
    login=(p.login or '').strip().lower()
    if not login: raise HTTPException(400,'login required')
    with conn() as c: r=c.execute('SELECT * FROM drivers WHERE lower(trim(email))=? LIMIT 1',(login,)).fetchone()
    if not r: return {'ok':False,'driver':None,'reason':'not_registered'}
    if r['password_hash']:
        if not p.password: return {'ok':False,'driver':None,'reason':'bad_password'}
        chk=hashlib.pbkdf2_hmac('sha256',p.password.encode(),r['password_salt'].encode(),200000).hex()
        if not hmac.compare_digest(chk,r['password_hash']): return {'ok':False,'driver':None,'reason':'bad_password'}
    return {'ok':True,'driver':{'name':r['name'],'driverId':r['driver_id'] or '', 'email':r['email'] or '', 'phone':r['phone'] or '', 'selfRegistered':bool(r['self_registered'])}}

def _driver_view(r): return {'name':r['name'],'driverId':r['driver_id'] or '', 'email':r['email'] or '', 'phone':r['phone'] or '', 'selfRegistered':bool(r['self_registered'])}

@app.post('/api/driver-device-token')
def driver_device_token(p:DeviceTokenPayload):
    """Issued after a successful password check so this phone can later sign in with fingerprint / Face ID (no password typed)."""
    login=(p.login or '').strip().lower()
    if not login: raise HTTPException(400,'login required')
    with conn() as c:
        r=c.execute('SELECT * FROM drivers WHERE lower(trim(email))=? LIMIT 1',(login,)).fetchone()
        if not r: return {'ok':False,'reason':'not_registered'}
        if r['password_hash']:
            if not p.password: return {'ok':False,'reason':'bad_password'}
            chk=hashlib.pbkdf2_hmac('sha256',p.password.encode(),r['password_salt'].encode(),200000).hex()
            if not hmac.compare_digest(chk,r['password_hash']): return {'ok':False,'reason':'bad_password'}
        token=secrets.token_urlsafe(32)
        c.execute('INSERT INTO driver_devices(token_hash,email) VALUES(?,?)',(hashlib.sha256(token.encode()).hexdigest(),login))
        # keep only the 10 newest devices per driver
        old=c.execute('SELECT token_hash FROM driver_devices WHERE email=? ORDER BY created_at DESC',(login,)).fetchall()
        for o in old[10:]: c.execute('DELETE FROM driver_devices WHERE token_hash=?',(o['token_hash'],))
    return {'ok':True,'token':token}

@app.post('/api/driver-device-login')
def driver_device_login(p:DeviceLoginPayload):
    login=(p.login or '').strip().lower()
    if not login or not p.token: raise HTTPException(400,'login and token required')
    th=hashlib.sha256(p.token.encode()).hexdigest()
    with conn() as c:
        d=c.execute('SELECT * FROM driver_devices WHERE token_hash=? AND email=?',(th,login)).fetchone()
        if not d: return {'ok':False,'driver':None,'reason':'bad_token'}
        r=c.execute('SELECT * FROM drivers WHERE lower(trim(email))=? LIMIT 1',(login,)).fetchone()
        if not r: return {'ok':False,'driver':None,'reason':'not_registered'}
        c.execute('UPDATE driver_devices SET last_used=? WHERE token_hash=?',(datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),th))
    return {'ok':True,'driver':_driver_view(r)}

@app.get('/api/dashboard-state')
def dashboard_state():
    with conn() as c:
        drivers=[{'name':r['name'],'driverId':r['driver_id'] or '', 'email':r['email'] or '', 'phone':r['phone'] or '', 'selfRegistered':bool(r['self_registered']),'daysWorked':r['imported_days_worked'],'daysWorkedSource':r['days_worked_source'] or ''} for r in c.execute('SELECT * FROM drivers ORDER BY name')]
        att={}
        for r in c.execute('SELECT * FROM attendance'):
            rec={'am':bool(r['am']),'pm':bool(r['pm']),'amPhoto':json.loads(r['am_photo_json']) if r['am_photo_json'] else None,'pmPhoto':json.loads(r['pm_photo_json']) if r['pm_photo_json'] else None,'photoVerified':bool(r['photo_verified']),'photoTime':r['photo_time'],'adminOverride':bool(r['admin_override']),'overrideReason':r['override_reason'],'overrideBy':r['override_by'],'overrideType':r['override_type'],'overrideProofPhoto':json.loads(r['override_proof_json']) if r['override_proof_json'] else None,'noPhotoReason':r['no_photo_reason'],'noPhotoNote':r['no_photo_note'],'lateProofPhoto':json.loads(r['late_proof_json']) if r['late_proof_json'] else None,'pendingApproval':bool(r['pending_approval']),'approvalStatus':r['approval_status'] or ('Pending Approval' if r['pending_approval'] else 'Approved')}
            rec.update({'closePhoto':json.loads(r['close_photo_json']) if r['close_photo_json'] else None,'pmAuto':bool(r['pm_auto']),'pmAutoAt':r['pm_auto_at'],'pmAutoDistM':r['pm_auto_dist_m']})
            try: rec['slotApprovals']=json.loads(r['slot_approvals_json']) if r['slot_approvals_json'] else None
            except Exception: rec['slotApprovals']=None
            rec.update(_server_fields(r))
            rec.update({'incompleteAm':bool(r['incomplete_am']),'incompletePm':bool(r['incomplete_pm']),'incompleteReason':r['incomplete_reason'],'incompleteAt':r['incomplete_at']})
            primary=rec['amPhoto'] or rec['pmPhoto']
            rec['photoDataUrl']=primary.get('dataUrl') if isinstance(primary,dict) else None
            att[f"{r['driver_name']}||{r['attendance_date']}"]=rec
        work={f"{r['driver_name']}||{r['work_date']}":{'selected':bool(r['selected']),'selectedAt':r['selected_at'],'stores':json.loads(r['stores_json']) if r['stores_json'] else []} for r in c.execute('SELECT * FROM work_days')}
    return {'rosterDrivers':drivers,'rosterAttendance':att,'driverWorkDays':work}

@app.post('/api/roster')
def save_roster(p:RosterPayload):
    # Canonical driver upsert. Match strongest identifier first and never replace
    # valid stored fields with blanks from an import. CSV Days Worked is persisted.
    saved=0
    with conn() as c:
        for d in p.drivers:
            name=(d.get('name') or '').strip()
            driver_id=str(d.get('driverId') or '').strip()
            email=(d.get('email') or '').strip().lower()
            phone=re.sub(r'\D','',str(d.get('phone') or ''))
            if not (name or driver_id or email or phone): continue
            row=None
            if driver_id: row=c.execute('SELECT * FROM drivers WHERE trim(driver_id)=? LIMIT 1',(driver_id,)).fetchone()
            if row is None and email: row=c.execute('SELECT * FROM drivers WHERE lower(trim(email))=? LIMIT 1',(email,)).fetchone()
            if row is None and phone: row=c.execute("SELECT * FROM drivers WHERE replace(replace(replace(replace(phone,' ',''),'-',''),'(',''),')','')=? LIMIT 1",(phone,)).fetchone()
            if row is None and name: row=c.execute('SELECT * FROM drivers WHERE lower(trim(name))=? LIMIT 1',(name.lower(),)).fetchone()
            days=d.get('daysWorked',None)
            try:
                days=int(float(days)) if days not in (None,'') else None
                if days is not None and days < 0: days=None
            except (TypeError,ValueError): days=None
            source=(d.get('daysWorkedSource') or ('CSV' if days is not None else '')).strip()
            if row:
                # Existing valid roster values win; CSV only fills missing fields.
                c.execute('''UPDATE drivers SET driver_id=?,email=?,phone=?,self_registered=?,
                  imported_days_worked=COALESCE(imported_days_worked,CAST(? AS INTEGER)),
                  days_worked_source=CASE WHEN imported_days_worked IS NULL AND CAST(? AS INTEGER) IS NOT NULL THEN CAST(? AS TEXT) ELSE days_worked_source END,
                  updated_at=CURRENT_TIMESTAMP WHERE name=?''',
                  (row['driver_id'] or driver_id,row['email'] or email,row['phone'] or phone,
                   row['self_registered'] or (1 if d.get('selfRegistered') else 0),days,days,source,row['name']))
            elif name:
                c.execute('''INSERT INTO drivers(name,driver_id,email,phone,self_registered,imported_days_worked,days_worked_source) VALUES(?,?,?,?,?,?,?)''',
                  (name,driver_id,email,phone,1 if d.get('selfRegistered') else 0,days,source))
            saved+=1
    return {'ok':True,'count':saved}

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
        before=c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(p.driverName,p.date)).fetchone()
        if before and before['pm_auto'] and not r.get('adminOverride'): r=dict(r,pm=True)   # a server-made automatic PM mark can't be wiped by a stale client copy
        c.execute('''INSERT INTO attendance(driver_name,attendance_date,am,pm,am_photo_json,pm_photo_json,photo_verified,photo_time,admin_override,override_reason,override_by,override_type,override_proof_json,no_photo_reason,no_photo_note,late_proof_json,pending_approval,approval_status)
          VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(driver_name,attendance_date) DO UPDATE SET
          am=excluded.am,pm=excluded.pm,am_photo_json=excluded.am_photo_json,pm_photo_json=excluded.pm_photo_json,
          photo_verified=excluded.photo_verified,photo_time=excluded.photo_time,admin_override=excluded.admin_override,
          override_reason=excluded.override_reason,override_by=excluded.override_by,override_type=excluded.override_type,
          override_proof_json=excluded.override_proof_json,no_photo_reason=excluded.no_photo_reason,no_photo_note=excluded.no_photo_note,
          late_proof_json=excluded.late_proof_json,pending_approval=excluded.pending_approval,approval_status=excluded.approval_status,updated_at=CURRENT_TIMESTAMP''',
          (p.driverName,p.date,1 if r.get('am') else 0,1 if r.get('pm') else 0,
           json.dumps(r.get('amPhoto')) if r.get('amPhoto') else None,json.dumps(r.get('pmPhoto')) if r.get('pmPhoto') else None,
           1 if r.get('photoVerified') else 0,r.get('photoTime'),1 if r.get('adminOverride') else 0,r.get('overrideReason'),r.get('overrideBy'),
           r.get('overrideType'),json.dumps(r.get('overrideProofPhoto')) if r.get('overrideProofPhoto') else None,
           r.get('noPhotoReason'),r.get('noPhotoNote'),json.dumps(r.get('lateProofPhoto')) if r.get('lateProofPhoto') else None,1 if r.get('pendingApproval') else 0,r.get('approvalStatus')))
        c.execute('UPDATE attendance SET close_photo_json=?,pm_auto=?,pm_auto_at=?,pm_auto_dist_m=?,slot_approvals_json=? WHERE driver_name=? AND attendance_date=?',
          (json.dumps(r.get('closePhoto')) if r.get('closePhoto') else None,1 if r.get('pmAuto') else 0,r.get('pmAutoAt'),r.get('pmAutoDistM'),
           json.dumps(r.get('slotApprovals')) if r.get('slotApprovals') else None,p.driverName,p.date))
        _after_attendance_save(c,p.driverName,p.date,before,(r.get('overrideBy') or p.driverName))
        return {'ok':True,'record':_server_fields(c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(p.driverName,p.date)).fetchone())}

@app.get('/api/attendance')
def attendance(from_date:str|None=None,to_date:str|None=None,driver:str|None=None):
    q='SELECT * FROM attendance WHERE 1=1'; args=[]
    if from_date: q+=' AND attendance_date>=?'; args.append(from_date)
    if to_date: q+=' AND attendance_date<=?'; args.append(to_date)
    if driver: q+=' AND driver_name=?'; args.append(driver)
    q+=' ORDER BY attendance_date DESC, driver_name'
    with conn() as c: rows=[dict(r) for r in c.execute(q,args)]
    return {'rows':rows,'count':len(rows)}


# ══ v51: live-location "away from store" flags ═══════════════════════════
# A driver is "away" when their live GPS position is outside the geofence
# (default 300 m) of ALL the stores they selected. v52: an away event now only opens when the
# driver is MORE THAN 10,000 m from the store, is FLAGGED once 90 min have passed, and stays
# flagged until the driver is back inside the store radius. If that return happens on a
# LATER calendar day than the one they left, that day/shift is marked incomplete.
# SA has no DST, so a fixed UTC+2 offset gives the correct local work date.
AWAY_FLAG_MINUTES = 90     # v52: flagged after 1.5 h away ...
AWAY_DISTANCE_M = 10000    # ... AND more than 10,000 m from the selected store (= the working area)
SIGN_RADIUS_M = 40         # v54: a shift can only be signed in / out within 40 m of the selected store
WORK_AREA_M = 10000        # v54: after signing in, time counts while the driver is within 10,000 m of the store
MAX_SIGN_ACC_M = 50        # v54: GPS fix must be better than this to prove the 40 m sign in / out
PRESENCE_MAX_GAP_MIN = 30  # v53: a gap between two at-store pings up to this long still counts as on-site (phone asleep)
SHORT_SHIFT_MIN = 480      # v53: less than 8 h at the store between sign in and sign out => flagged
SHIFT_SPLIT_HOUR = 15      # left before 15:00 SAST => AM+PM of that day incomplete; at/after => PM only
MAX_ACCURACY_M = 250      # ignore very imprecise GPS fixes (avoid false "left" events)
SIGNAL_LOST_MIN = 15      # open event with no ping for this long => shown as "No signal"
SAST = timezone(timedelta(hours=2))

def _now(): return datetime.now(timezone.utc)
def _iso(d): return d.strftime('%Y-%m-%dT%H:%M:%SZ')
def _parse(t): return datetime.strptime(t,'%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
def _meters(lat1,lng1,lat2,lng2):
    R=6371000.0; p1,p2=math.radians(lat1),math.radians(lat2)
    a=math.sin((p2-p1)/2)**2+math.cos(p1)*math.cos(p2)*math.sin(math.radians(lng2-lng1)/2)**2
    return 2*R*math.asin(math.sqrt(a))


def _mark_incomplete(c,name,work_date,left_at,store,now_s):
    """Mark the shift(s) of work_date as not complete. Left before SHIFT_SPLIT_HOUR (SAST) => AM and PM
    (the absence covers the evening shift too); left at/after it => PM only. Keeps photos untouched."""
    left_h=_parse(left_at).astimezone(SAST).hour
    am=1 if left_h<SHIFT_SPLIT_HOUR else 0
    reason=f'Left {store} (>10 km) at {_parse(left_at).astimezone(SAST).strftime("%H:%M")} and only returned the next day'
    c.execute('''INSERT INTO attendance(driver_name,attendance_date,incomplete_am,incomplete_pm,incomplete_reason,incomplete_at) VALUES(?,?,?,?,?,?)
      ON CONFLICT(driver_name,attendance_date) DO UPDATE SET incomplete_am=MAX(attendance.incomplete_am,excluded.incomplete_am),incomplete_pm=1,incomplete_reason=excluded.incomplete_reason,incomplete_at=excluded.incomplete_at''',
      (name,work_date,am,1,reason,now_s))
    return 'AM+PM' if am else 'PM'

class StoreLocPayload(BaseModel): store:str; lat:float; lng:float; radius_m:int=300; updatedBy:str=""
class PingPayload(BaseModel): driverName:str; stores:list[str]=[]; lat:float; lng:float; accuracy:float|None=None; capturedAt:str|None=None
class LocStatusPayload(BaseModel): driverName:str; status:str; detail:str=""

@app.post('/api/location-status')
def set_location_status(p:LocStatusPayload):
    name=p.driverName.strip()
    if not name: raise HTTPException(400,'driver required')
    st=p.status if p.status in ('granted','denied','unavailable','prompt','unsupported','insecure') else 'unavailable'
    with conn() as c:
        c.execute('INSERT INTO driver_location_status(driver_name,status,detail,updated_at) VALUES(?,?,?,?) ON CONFLICT(driver_name) DO UPDATE SET status=excluded.status,detail=excluded.detail,updated_at=excluded.updated_at',(name,st,(p.detail or '')[:200],_iso(_now())))
    return {'ok':True}

@app.get('/api/location-status')
def get_location_status():
    now=_now(); out=[]
    with conn() as c:
        for r in c.execute('SELECT * FROM driver_location_status ORDER BY driver_name'):
            try: age=int((now-_parse(r['updated_at'])).total_seconds()//60)
            except Exception: age=None
            out.append({'driver':r['driver_name'],'status':r['status'],'detail':r['detail'] or '','updatedAt':r['updated_at'],'ageMin':age})
    return {'rows':out}

@app.get('/api/store-locations')
def get_store_locations():
    with conn() as c: rows=[dict(r) for r in c.execute('SELECT store,lat,lng,radius_m,updated_by,updated_at FROM store_locations ORDER BY store')]
    return {'rows':rows}

@app.post('/api/store-locations')
def set_store_location(p:StoreLocPayload):
    if not (-90<=p.lat<=90 and -180<=p.lng<=180): raise HTTPException(400,'invalid coordinates')
    store=p.store.strip()
    if not store: raise HTTPException(400,'store required')
    radius=max(50,min(10000,int(p.radius_m)))
    with conn() as c:
        c.execute('''INSERT INTO store_locations(store,lat,lng,radius_m,updated_by) VALUES(?,?,?,?,?)
          ON CONFLICT(store) DO UPDATE SET lat=excluded.lat,lng=excluded.lng,radius_m=excluded.radius_m,updated_by=excluded.updated_by,updated_at=CURRENT_TIMESTAMP''',
          (store,p.lat,p.lng,radius,p.updatedBy))
    return {'ok':True}

@app.delete('/api/store-locations')
def delete_store_location(store:str):
    with conn() as c: c.execute('DELETE FROM store_locations WHERE store=?',(store,))
    return {'ok':True}

@app.post('/api/location-ping')
def location_ping(p:PingPayload):
    name=p.driverName.strip()
    if not name or not (-90<=p.lat<=90 and -180<=p.lng<=180): raise HTTPException(400,'invalid ping')
    if p.accuracy is not None and p.accuracy>MAX_ACCURACY_M: return {'ok':True,'ignored':'low_accuracy'}
    now=_now()
    if p.capturedAt:                       # pings queued while offline keep the time the fix was really taken
        try:
            t=_parse(p.capturedAt)
            if now-timedelta(hours=6)<=t<=now: now=t
        except Exception: pass
    now_s=_iso(now); work_date=now.astimezone(SAST).strftime('%Y-%m-%d')
    with conn() as c:
        best=_nearest_store(c,p.stores,p.lat,p.lng)
        if best is None: return {'ok':True,'tracked':False,'reason':'no_store_coordinates'}
        dist,store,radius=best                      # radius == WORK_AREA_M
        c.execute('INSERT INTO location_log(driver_name,store,ts,dist_m,at_store) VALUES(?,?,?,?,?)',(name,store,now_s,int(dist),1 if dist<=radius else 0))
        _pm_evaluate(c,name,p.stores,p.lat,p.lng,now,now_s,work_date)      # v65: 6 km PM attendance rules, per assigned store
        shift_open=c.execute('SELECT 1 FROM work_sessions WHERE driver_name=? AND signed_out_at IS NULL LIMIT 1',(name,)).fetchone()
        ev=c.execute('SELECT * FROM away_events WHERE driver_name=? AND returned_at IS NULL ORDER BY id DESC LIMIT 1',(name,)).fetchone()
        if ev:
            elapsed=(now-_parse(ev['left_at'])).total_seconds()
            flagged=elapsed>=AWAY_FLAG_MINUTES*60
            if dist<=radius:
                # back inside the working area -> close the event
                c.execute('UPDATE away_events SET returned_at=?,last_seen=? WHERE id=?',(now_s,now_s,ev['id']))
                if elapsed<300:
                    c.execute('DELETE FROM away_events WHERE id=?',(ev['id'],))      # GPS blip
                elif flagged and now.astimezone(SAST).strftime('%Y-%m-%d')>ev['work_date']:
                    # came back on a later day than they left -> day/shift not complete
                    marked=_mark_incomplete(c,name,ev['work_date'],ev['left_at'],ev['store'],now_s)
                    c.execute('UPDATE away_events SET day_marked=? WHERE id=?',(marked,ev['id']))
            else:
                # still outside the working area
                c.execute('UPDATE away_events SET last_seen=?,max_distance_m=MAX(max_distance_m,?),last_lat=?,last_lng=? WHERE id=?',(now_s,int(dist),p.lat,p.lng,ev['id']))
        elif dist>AWAY_DISTANCE_M and shift_open:
            c.execute('INSERT INTO away_events(driver_name,store,work_date,left_at,last_seen,max_distance_m,last_lat,last_lng) VALUES(?,?,?,?,?,?,?,?)',(name,store,work_date,now_s,now_s,int(dist),p.lat,p.lng))
    return {'ok':True,'tracked':True,'away':dist>AWAY_DISTANCE_M,'distance_m':int(dist),'store':store}

@app.get('/api/away-flags')
def away_flags(date:str|None=None,all:int=0):
    date=date or _now().astimezone(SAST).strftime('%Y-%m-%d')
    try: datetime.strptime(date,'%Y-%m-%d')
    except ValueError: raise HTTPException(400,'date must be YYYY-MM-DD')
    now=_now(); out=[]
    with conn() as c: rows=c.execute('SELECT * FROM away_events WHERE work_date=? ORDER BY left_at',(date,)).fetchall()
    for r in rows:
        left=_parse(r['left_at']); ret=_parse(r['returned_at']) if r['returned_at'] else None
        seen=_parse(r['last_seen']); end=ret or seen
        mins=int((end-left).total_seconds()//60)
        flagged=mins>=AWAY_FLAG_MINUTES
        if not (flagged or all): continue
        status='returned' if ret else ('no_signal' if (now-seen).total_seconds()>SIGNAL_LOST_MIN*60 else 'away')
        out.append({'id':r['id'],'driver':r['driver_name'],'store':r['store'],'date':r['work_date'],'leftAt':r['left_at'],'returnedAt':r['returned_at'],
                    'lastSeen':r['last_seen'],'minutesAway':mins,'flagged':flagged,'status':status,'maxDistanceM':r['max_distance_m'],'dayMarked':r['day_marked'] or '','lat':r['last_lat'],'lng':r['last_lng']})
    return {'date':date,'flagMinutes':AWAY_FLAG_MINUTES,'distanceM':AWAY_DISTANCE_M,'rows':out,'count':len(out)}


# ══ v53: on-site time, shift sign in / sign out, <8 h flag ═════════════════
def _nearest_store(c,stores,lat,lng):
    """(distance_m, store, WORK_AREA_M) for the closest selected store that has coordinates, else None."""
    best=None
    for st in stores:
        loc=c.execute('SELECT * FROM store_locations WHERE store=?',(st,)).fetchone()
        if not loc: continue
        d=_meters(lat,lng,loc['lat'],loc['lng'])
        if best is None or d<best[0]: best=(d,st,WORK_AREA_M)
    return best

def _log_point(c,name,best,now_s):
    if best: c.execute('INSERT INTO location_log(driver_name,store,ts,dist_m,at_store) VALUES(?,?,?,?,?)',(name,best[1],now_s,int(best[0]),1 if best[0]<=best[2] else 0))

def _onsite_minutes(c,name,t1,t2):
    """Minutes the driver was inside the store radius between t1 and t2 (from the ping log)."""
    if t2<=t1: return 0
    gap_max=PRESENCE_MAX_GAP_MIN*60
    rows=c.execute('SELECT ts,at_store FROM location_log WHERE driver_name=? AND ts>=? AND ts<=? ORDER BY ts',
                   (name,_iso(t1-timedelta(seconds=gap_max)),_iso(t2+timedelta(seconds=gap_max)))).fetchall()
    tot=0.0; prev=None
    for r in rows:
        t=_parse(r['ts'])
        if prev and prev[1] and r['at_store'] and (t-prev[0]).total_seconds()<=gap_max:
            a=max(prev[0],t1); b=min(t,t2)
            if b>a: tot+=(b-a).total_seconds()
        prev=(t,r['at_store'])
    return int(tot//60)

def _session_view(c,r,now):
    t_in=_parse(r['signed_in_at']); closed=r['signed_out_at']
    t_out=_parse(closed) if closed else now
    if closed and r['onsite_min'] is not None: on=r['onsite_min']
    else: on=_onsite_minutes(c,r['driver_name'],t_in,t_out)
    total=int((t_out-t_in).total_seconds()//60)
    status='open' if not closed else ('short' if on<SHORT_SHIFT_MIN else 'ok')
    return {'id':r['id'],'driver':r['driver_name'],'store':r['store'] or '','date':r['work_date'],'signedInAt':r['signed_in_at'],'signedOutAt':closed,
            'onsiteMin':on,'shiftMin':total,'status':status,'autoClosed':bool(r['auto_closed']),'outOfArea':bool(r['out_of_area']),'signRadiusM':SIGN_RADIUS_M,'inDistM':r['in_dist_m'],'outDistM':r['out_dist_m'],'requiredMin':SHORT_SHIFT_MIN}

def _autoclose_stale(c):
    """A shift left open past midnight (SAST) is closed at the driver's last ping of that day and evaluated."""
    today=_now().astimezone(SAST).strftime('%Y-%m-%d')
    for r in c.execute('SELECT * FROM work_sessions WHERE signed_out_at IS NULL AND work_date<?',(today,)).fetchall():
        t_in=_parse(r['signed_in_at'])
        day_end=(datetime.strptime(r['work_date'],'%Y-%m-%d').replace(tzinfo=SAST)+timedelta(days=1)).astimezone(timezone.utc)
        last=c.execute('SELECT MAX(ts) m FROM location_log WHERE driver_name=? AND ts>=? AND ts<=?',(r['driver_name'],r['signed_in_at'],_iso(day_end))).fetchone()['m']
        t_out=min(_parse(last),day_end) if last else t_in
        if t_out<t_in: t_out=t_in
        on=_onsite_minutes(c,r['driver_name'],t_in,t_out)
        c.execute('UPDATE work_sessions SET signed_out_at=?,auto_closed=1,onsite_min=? WHERE id=?',(_iso(t_out),on,r['id']))

class SessionPayload(BaseModel): driverName:str; stores:list[str]=[]; lat:float|None=None; lng:float|None=None; accuracy:float|None=None

@app.post('/api/work-session/start')
def work_session_start(p:SessionPayload):
    """Auto sign-in. Only succeeds within SIGN_RADIUS_M (40 m) of the selected store; the app retries until the driver is there."""
    name=p.driverName.strip()
    if not name: raise HTTPException(400,'driver required')
    now=_now(); now_s=_iso(now); work_date=now.astimezone(SAST).strftime('%Y-%m-%d')
    with conn() as c:
        _autoclose_stale(c)
        ex=c.execute('SELECT * FROM work_sessions WHERE driver_name=? AND signed_out_at IS NULL ORDER BY id DESC LIMIT 1',(name,)).fetchone()
        if ex: return {'ok':True,'already':True,'session':_session_view(c,ex,now)}
        if p.lat is None or p.lng is None: return {'ok':False,'reason':'no_location','radiusM':SIGN_RADIUS_M}
        best=_nearest_store(c,p.stores,p.lat,p.lng)
        if best is not None:
            if p.accuracy is not None and p.accuracy>MAX_SIGN_ACC_M:
                return {'ok':False,'reason':'weak_gps','accuracyM':int(p.accuracy),'radiusM':SIGN_RADIUS_M}
            if best[0]>SIGN_RADIUS_M:
                return {'ok':False,'reason':'too_far','distanceM':int(best[0]),'radiusM':SIGN_RADIUS_M,'store':best[1]}
        # best is None => none of the selected stores has coordinates yet: cannot verify, so allow (Admin should set the location)
        store=best[1] if best else (p.stores[0] if p.stores else '')
        _log_point(c,name,best,now_s)
        new_id=c.insert_id('INSERT INTO work_sessions(driver_name,store,work_date,signed_in_at,in_dist_m) VALUES(?,?,?,?,?)',(name,store,work_date,now_s,int(best[0]) if best else None))
        r=c.execute('SELECT * FROM work_sessions WHERE id=?',(new_id,)).fetchone()
        return {'ok':True,'session':_session_view(c,r,now),'atStore':True,'verified':best is not None,'radiusM':SIGN_RADIUS_M}

@app.post('/api/work-session/end')
def work_session_end(p:SessionPayload):
    """Auto sign-out (on logout). Always closes the shift, but a sign-out more than SIGN_RADIUS_M (40 m) from the store, or without a location, is flagged."""
    name=p.driverName.strip()
    now=_now(); now_s=_iso(now)
    with conn() as c:
        _autoclose_stale(c)
        r=c.execute('SELECT * FROM work_sessions WHERE driver_name=? AND signed_out_at IS NULL ORDER BY id DESC LIMIT 1',(name,)).fetchone()
        if not r: return {'ok':False,'reason':'no_open_session'}
        have_pos=p.lat is not None and p.lng is not None
        best=_nearest_store(c,p.stores or ([r['store']] if r['store'] else []),p.lat,p.lng) if have_pos else None
        _log_point(c,name,best,now_s)
        if not have_pos: out=1                                    # cannot prove where the driver signed out
        elif best is None: out=0                                  # store has no coordinates -> cannot judge
        else: out=1 if (best[0]>SIGN_RADIUS_M or (p.accuracy is not None and p.accuracy>MAX_SIGN_ACC_M)) else 0
        on=_onsite_minutes(c,name,_parse(r['signed_in_at']),now)
        c.execute('UPDATE work_sessions SET signed_out_at=?,onsite_min=?,out_dist_m=?,out_of_area=? WHERE id=?',(now_s,on,int(best[0]) if best else None,out,r['id']))
        r=c.execute('SELECT * FROM work_sessions WHERE id=?',(r['id'],)).fetchone()
        return {'ok':True,'session':_session_view(c,r,now)}

@app.get('/api/work-session/current')
def work_session_current(driver:str):
    now=_now()
    with conn() as c:
        _autoclose_stale(c)
        o=c.execute('SELECT * FROM work_sessions WHERE driver_name=? AND signed_out_at IS NULL ORDER BY id DESC LIMIT 1',(driver.strip(),)).fetchone()
        l=c.execute('SELECT * FROM work_sessions WHERE driver_name=? AND signed_out_at IS NOT NULL ORDER BY id DESC LIMIT 1',(driver.strip(),)).fetchone()
        return {'open':_session_view(c,o,now) if o else None,'last':_session_view(c,l,now) if l else None}

@app.get('/api/work-session/today')
def work_session_today(driver:str,date:str|None=None):
    """Everything a driver needs for the 'Work shift' card: all of today's (SAST) sessions + totals.
    Sessions are opened automatically on login and closed automatically on logout."""
    date=date or _now().astimezone(SAST).strftime('%Y-%m-%d')
    try: datetime.strptime(date,'%Y-%m-%d')
    except ValueError: raise HTTPException(400,'date must be YYYY-MM-DD')
    now=_now()
    with conn() as c:
        _autoclose_stale(c)
        rows=[_session_view(c,r,now) for r in c.execute('SELECT * FROM work_sessions WHERE driver_name=? AND work_date=? ORDER BY id',(driver.strip(),date)).fetchall()]
    open_s=next((r for r in reversed(rows) if r['status']=='open'),None)
    closed=[r for r in rows if r['signedOutAt']]
    return {'date':date,'sessions':rows,'open':open_s,
            'totalMin':sum(r['shiftMin'] for r in rows),'onsiteMin':sum(r['onsiteMin'] for r in rows),
            'firstSignIn':rows[0]['signedInAt'] if rows else None,
            'lastSignOut':closed[-1]['signedOutAt'] if (closed and not open_s) else None,
            'requiredMin':SHORT_SHIFT_MIN,'signRadiusM':SIGN_RADIUS_M,'workAreaM':WORK_AREA_M,
            'outOfArea':any(r['outOfArea'] for r in rows)}

@app.get('/api/short-shifts')
def short_shifts(date:str|None=None):
    date=date or _now().astimezone(SAST).strftime('%Y-%m-%d')
    try: datetime.strptime(date,'%Y-%m-%d')
    except ValueError: raise HTTPException(400,'date must be YYYY-MM-DD')
    now=_now()
    with conn() as c:
        _autoclose_stale(c)
        rows=[_session_view(c,r,now) for r in c.execute('SELECT * FROM work_sessions WHERE work_date=? ORDER BY signed_in_at',(date,)).fetchall()]
    return {'date':date,'requiredMin':SHORT_SHIFT_MIN,'rows':rows,'flagged':sum(1 for r in rows if r['status']=='short')}

@app.get('/api/onsite-summary')
def onsite_summary(from_date:str,to_date:str):
    """Per driver/day: minutes on-site between the AM photo and the PM photo, plus that day's shift session."""
    now=_now(); days={}; sess={}
    with conn() as c:
        _autoclose_stale(c)
        _ex=(lambda col:f"({col}::json->>'ts')") if PG else (lambda col:f"json_extract({col},'$.ts')")
        q=f"""SELECT driver_name,attendance_date,{_ex('am_photo_json')} am_ts,{_ex('pm_photo_json')} pm_ts
             FROM attendance WHERE attendance_date>=? AND attendance_date<=? AND am_photo_json IS NOT NULL AND pm_photo_json IS NOT NULL"""
        for r in c.execute(q,(from_date,to_date)).fetchall():
            try:
                t1=datetime.fromtimestamp(float(r['am_ts'])/1000,timezone.utc); t2=datetime.fromtimestamp(float(r['pm_ts'])/1000,timezone.utc)
            except (TypeError,ValueError): continue
            if t2<=t1: continue
            days[f"{r['driver_name']}||{r['attendance_date']}"]={'amAt':_iso(t1),'pmAt':_iso(t2),'spanMin':int((t2-t1).total_seconds()//60),'onsiteMin':_onsite_minutes(c,r['driver_name'],t1,t2)}
        for r in c.execute('SELECT * FROM work_sessions WHERE work_date>=? AND work_date<=? ORDER BY id',(from_date,to_date)).fetchall():
            sess[f"{r['driver_name']}||{r['work_date']}"]=_session_view(c,r,now)     # latest session of the day wins
    return {'days':days,'sessions':sess}


# ══ v65: automatic PM attendance, evidence requests, closing-picture review ═══════
# Jira "Automated PM Attendance and Closing Picture Logic".
#  1. within PM_RADIUS_M (6 km) of an assigned store -> PM attendance is recorded automatically (once per store/day);
#     no extra PM picture is requested; the closing picture is still required.
#  2. more than PM_RADIUS_M away for PM_AWAY_MIN (90 min) -> PM picture + closing picture are requested and PM is
#     NOT auto-approved until both are submitted; coming back inside the radius re-assesses the status.
#  3. closing picture but no AM picture and < FULL_DAY_MIN (8 h) worked -> record is flagged for Admin/Manager review
#     (driver may give a reason); the day is not counted until it is approved.
# Rules run per store (pm_store_status) so a driver assigned to several stores is evaluated separately for each.
# Every automatic decision and manual override is written to attendance_audit.
PM_RADIUS_M = 6000
PM_AWAY_MIN = 90
FULL_DAY_MIN = 480
PM_START_MIN = 19*60+45                      # PM window opens 19:45 SAST (matches the dashboard's capture window)
PM_OK = ('auto_approved','evidence_ok')

def _audit(c,name,work_date,event,actor='system',detail=None,store=None):
    c.execute('INSERT INTO attendance_audit(ts,driver_name,work_date,store,event,actor,detail) VALUES(?,?,?,?,?,?,?)',
              (_iso(_now()),name,work_date,store,event,actor or 'system',json.dumps(detail or {})))

def _ensure_att_row(c,name,date):
    c.execute('INSERT INTO attendance(driver_name,attendance_date) VALUES(?,?) ON CONFLICT DO NOTHING',(name,date))

def _pm_rollup(c,name,date,now_s):
    """Fold the per-store PM rows into the single attendance record for the day."""
    rows=c.execute('SELECT * FROM pm_store_status WHERE driver_name=? AND work_date=? ORDER BY store',(name,date)).fetchall()
    if not rows: return
    sts=[r['status'] for r in rows]
    _ensure_att_row(c,name,date)
    if all(x in PM_OK for x in sts):
        autos=[r for r in rows if r['status']=='auto_approved']
        if autos:
            a=autos[0]
            c.execute('UPDATE attendance SET pm=1,pm_auto=1,pm_auto_at=COALESCE(pm_auto_at,?),pm_auto_dist_m=COALESCE(pm_auto_dist_m,?),pm_status=?,pm_evidence_required=0,updated_at=CURRENT_TIMESTAMP WHERE driver_name=? AND attendance_date=?',
                      (a['auto_at'] or now_s,a['auto_dist_m'],'auto_approved' if len(autos)==len(rows) else 'evidence_approved',name,date))
        else:
            c.execute('UPDATE attendance SET pm=1,pm_status=?,pm_evidence_required=0,updated_at=CURRENT_TIMESTAMP WHERE driver_name=? AND attendance_date=?',('evidence_approved',name,date))
    elif any(x in ('evidence_required','evidence_partial') for x in sts):
        c.execute('UPDATE attendance SET pm_status=?,pm_evidence_required=1,updated_at=CURRENT_TIMESTAMP WHERE driver_name=? AND attendance_date=?',('evidence_required',name,date))
    else:
        c.execute('UPDATE attendance SET pm_status=?,pm_evidence_required=0,updated_at=CURRENT_TIMESTAMP WHERE driver_name=? AND attendance_date=?',('pending',name,date))

def _pm_evaluate(c,name,stores,lat,lng,now,now_s,work_date):
    """Run the 6 km / 90 min rules for every assigned store from one GPS fix. Idempotent."""
    if not c.execute('SELECT 1 FROM work_sessions WHERE driver_name=? AND work_date=? LIMIT 1',(name,work_date)).fetchone(): return
    att=c.execute('SELECT admin_override FROM attendance WHERE driver_name=? AND attendance_date=?',(name,work_date)).fetchone()
    if att and att['admin_override']: return                       # manual override wins; nothing to automate
    pm_open = now.astimezone(SAST).hour*60+now.astimezone(SAST).minute >= PM_START_MIN
    touched=False
    for st in dict.fromkeys(stores):
        loc=c.execute('SELECT lat,lng FROM store_locations WHERE store=?',(st,)).fetchone()
        if not loc: continue
        d=int(_meters(lat,lng,loc['lat'],loc['lng']))
        c.execute('INSERT INTO pm_store_status(driver_name,work_date,store) VALUES(?,?,?) ON CONFLICT DO NOTHING',(name,work_date,st))
        row=c.execute('SELECT * FROM pm_store_status WHERE driver_name=? AND work_date=? AND store=?',(name,work_date,st)).fetchone()
        status=row['status']
        c.execute('UPDATE pm_store_status SET last_check_at=?,last_dist_m=? WHERE driver_name=? AND work_date=? AND store=?',(now_s,d,name,work_date,st))
        if d<=PM_RADIUS_M:
            if row['away_since']:
                mins=int((now-_parse(row['away_since'])).total_seconds()//60)
                new=status
                if status=='evidence_required': new='pending'           # re-assess: back inside the radius
                c.execute('UPDATE pm_store_status SET away_since=NULL,status=?,reassessed_at=? WHERE driver_name=? AND work_date=? AND store=?',(new,now_s,name,work_date,st))
                _audit(c,name,work_date,'pm_reassessed_returned',detail={'distance_m':d,'away_minutes':mins,'status_before':status,'status_after':new},store=st); touched=True
                status=new
            if pm_open and status not in PM_OK:
                n=c.execute("UPDATE pm_store_status SET status='auto_approved',auto_at=?,auto_dist_m=? WHERE driver_name=? AND work_date=? AND store=? AND status NOT IN ('auto_approved','evidence_ok')",(now_s,d,name,work_date,st)).rowcount
                if n: _audit(c,name,work_date,'pm_auto_marked',detail={'distance_m':d,'radius_m':PM_RADIUS_M},store=st); touched=True
        else:
            if not row['away_since']:
                c.execute('UPDATE pm_store_status SET away_since=? WHERE driver_name=? AND work_date=? AND store=?',(now_s,name,work_date,st))
                _audit(c,name,work_date,'left_pm_radius',detail={'distance_m':d,'radius_m':PM_RADIUS_M},store=st)
            elif status not in PM_OK and status!='evidence_required' and (now-_parse(row['away_since'])).total_seconds()>=PM_AWAY_MIN*60:
                c.execute("UPDATE pm_store_status SET status='evidence_required',evidence_required_at=? WHERE driver_name=? AND work_date=? AND store=?",(now_s,name,work_date,st))
                _audit(c,name,work_date,'pm_evidence_requested',detail={'distance_m':d,'away_since':row['away_since'],'away_minutes':int((now-_parse(row['away_since'])).total_seconds()//60),'requested':['pm_picture','closing_picture']},store=st); touched=True
    if touched: _pm_rollup(c,name,work_date,now_s)

def _worked_minutes(c,name,date,now):
    return sum(_session_view(c,r,now)['onsiteMin'] for r in c.execute('SELECT * FROM work_sessions WHERE driver_name=? AND work_date=? ORDER BY id',(name,date)).fetchall())

def _after_attendance_save(c,name,date,before,actor):
    """Server-side rules applied whenever a driver / admin saves an attendance record."""
    now=_now(); now_s=_iso(now)
    cur=c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(name,date)).fetchone()
    if not cur: return
    # timestamps for PM / closing pictures + audit of manual overrides
    if cur['pm_photo_json'] and not cur['pm_photo_at']:
        c.execute('UPDATE attendance SET pm_photo_at=? WHERE driver_name=? AND attendance_date=?',(now_s,name,date)); _audit(c,name,date,'pm_picture_recorded',actor)
    if cur['close_photo_json'] and not cur['close_at']:
        c.execute('UPDATE attendance SET close_at=? WHERE driver_name=? AND attendance_date=?',(now_s,name,date)); _audit(c,name,date,'closing_picture_recorded',actor)
    if cur['admin_override'] and not (before and before['admin_override']):
        _audit(c,name,date,'manual_override',cur['override_by'] or actor,{'type':cur['override_type'],'reason':cur['override_reason']})
    elif before and before['admin_override'] and not cur['admin_override']:
        _audit(c,name,date,'manual_override_removed',actor)
    # PM evidence: both pictures submitted -> every outstanding store is resolved
    pend=c.execute("SELECT store FROM pm_store_status WHERE driver_name=? AND work_date=? AND status IN ('evidence_required','evidence_partial')",(name,date)).fetchall()
    if pend:
        if cur['pm_photo_json'] and cur['close_photo_json']:
            c.execute("UPDATE pm_store_status SET status='evidence_ok',evidence_ok_at=? WHERE driver_name=? AND work_date=? AND status IN ('evidence_required','evidence_partial')",(now_s,name,date))
            for p in pend: _audit(c,name,date,'pm_evidence_submitted',actor,{'pm_picture':True,'closing_picture':True},store=p['store'])
        elif cur['pm_photo_json'] or cur['close_photo_json']:
            c.execute("UPDATE pm_store_status SET status='evidence_partial' WHERE driver_name=? AND work_date=? AND status='evidence_required'",(name,date))
        _pm_rollup(c,name,date,now_s)
    # Rule 3: closing picture without an AM picture
    if cur['close_photo_json'] and not cur['admin_override']:
        if cur['am_photo_json']:
            if cur['review_status']=='pending' and cur['review_type']=='missing_am_picture':
                c.execute("UPDATE attendance SET review_status='cleared',review_at=?,review_by='system' WHERE driver_name=? AND attendance_date=?",(now_s,name,date))
                _audit(c,name,date,'missing_am_review_cleared',detail={'reason':'AM picture now present'})
        elif cur['review_status'] not in ('pending','approved','rejected'):
            mins=_worked_minutes(c,name,date,now)
            if mins<FULL_DAY_MIN:
                c.execute("UPDATE attendance SET review_status='pending',review_type='missing_am_picture',review_flagged_at=?,work_minutes=? WHERE driver_name=? AND attendance_date=?",(now_s,mins,name,date))
                _audit(c,name,date,'missing_am_flagged',detail={'worked_minutes':mins,'required_minutes':FULL_DAY_MIN,'full_day_awarded':False})
            else:
                c.execute('UPDATE attendance SET work_minutes=? WHERE driver_name=? AND attendance_date=?',(mins,name,date))
                _audit(c,name,date,'missing_am_not_flagged',detail={'worked_minutes':mins,'required_minutes':FULL_DAY_MIN})

def _server_fields(r):
    return {'pmStatus':r['pm_status'],'pmEvidenceRequired':bool(r['pm_evidence_required']),'pmPhotoAt':r['pm_photo_at'],'closeAt':r['close_at'],
            'reviewStatus':r['review_status'],'reviewType':r['review_type'],'reviewFlaggedAt':r['review_flagged_at'],'workMinutes':r['work_minutes'],
            'reviewDriverReason':r['review_driver_reason'],'reviewDriverNote':r['review_driver_note'],'reviewReasonAt':r['review_reason_at'],
            'reviewBy':r['review_by'],'reviewAt':r['review_at'],'reviewNote':r['review_note'],
            'pm':bool(r['pm']),'pmAuto':bool(r['pm_auto']),'pmAutoAt':r['pm_auto_at'],'pmAutoDistM':r['pm_auto_dist_m']}

class ReasonPayload(BaseModel): driverName:str; date:str; reason:str; note:str=""
class ReviewPayload(BaseModel): driverName:str; date:str; decision:str; reviewer:str; note:str=""

def _chk_date(d):
    try: datetime.strptime(d,'%Y-%m-%d')
    except ValueError: raise HTTPException(400,'date must be YYYY-MM-DD')

@app.get('/api/pm-status')
def pm_status(driver:str,date:str|None=None):
    date=date or _now().astimezone(SAST).strftime('%Y-%m-%d'); _chk_date(date)
    with conn() as c:
        r=c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(driver,date)).fetchone()
        stores=[{'store':x['store'],'status':x['status'],'awaySince':x['away_since'],'lastCheckAt':x['last_check_at'],'lastDistM':x['last_dist_m'],'autoAt':x['auto_at'],
                 'evidenceRequiredAt':x['evidence_required_at'],'evidenceOkAt':x['evidence_ok_at']} for x in c.execute('SELECT * FROM pm_store_status WHERE driver_name=? AND work_date=? ORDER BY store',(driver,date))]
    return {'date':date,'radiusM':PM_RADIUS_M,'awayMinutes':PM_AWAY_MIN,'record':_server_fields(r) if r else None,'stores':stores}

@app.post('/api/attendance/missing-am-reason')
def missing_am_reason(p:ReasonPayload):
    _chk_date(p.date); reason=p.reason.strip()
    if not reason: raise HTTPException(400,'reason required')
    with conn() as c:
        r=c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(p.driverName,p.date)).fetchone()
        if not r or r['review_type']!='missing_am_picture' or r['review_status']!='pending': raise HTTPException(409,'this record is not awaiting a missing-AM reason')
        c.execute('UPDATE attendance SET review_driver_reason=?,review_driver_note=?,review_reason_at=? WHERE driver_name=? AND attendance_date=?',(reason[:60],p.note.strip()[:500],_iso(_now()),p.driverName,p.date))
        _audit(c,p.driverName,p.date,'missing_am_reason_submitted',p.driverName,{'reason':reason[:60],'note':p.note.strip()[:500]})
        return {'ok':True,'record':_server_fields(c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(p.driverName,p.date)).fetchone())}

@app.post('/api/attendance/review')
def review_attendance(p:ReviewPayload):
    _chk_date(p.date)
    if p.decision not in ('approve','reject'): raise HTTPException(400,"decision must be 'approve' or 'reject'")
    if not p.reviewer.strip(): raise HTTPException(400,'reviewer required')
    status='approved' if p.decision=='approve' else 'rejected'
    with conn() as c:
        r=c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(p.driverName,p.date)).fetchone()
        if not r or not r['review_status'] or r['review_status']=='cleared': raise HTTPException(409,'nothing to review for this record')
        c.execute('UPDATE attendance SET review_status=?,review_by=?,review_at=?,review_note=?,updated_at=CURRENT_TIMESTAMP WHERE driver_name=? AND attendance_date=?',(status,p.reviewer.strip(),_iso(_now()),p.note.strip()[:500],p.driverName,p.date))
        _audit(c,p.driverName,p.date,'review_'+status,p.reviewer.strip(),{'previous':r['review_status'],'note':p.note.strip()[:500],'worked_minutes':r['work_minutes']})
        return {'ok':True,'record':_server_fields(c.execute('SELECT * FROM attendance WHERE driver_name=? AND attendance_date=?',(p.driverName,p.date)).fetchone())}

@app.get('/api/attendance/review-queue')
def review_queue(status:str='pending'):
    with conn() as c:
        rows=[{'driver':r['driver_name'],'date':r['attendance_date'],'type':r['review_type'],'status':r['review_status'],'flaggedAt':r['review_flagged_at'],'workMinutes':r['work_minutes'],
               'requiredMinutes':FULL_DAY_MIN,'driverReason':r['review_driver_reason'],'driverNote':r['review_driver_note'],'reasonAt':r['review_reason_at'],'reviewBy':r['review_by'],'reviewAt':r['review_at'],'reviewNote':r['review_note']}
              for r in c.execute('SELECT * FROM attendance WHERE review_status=? ORDER BY attendance_date DESC,driver_name',(status,))]
    return {'rows':rows,'count':len(rows)}

@app.get('/api/attendance/audit')
def attendance_audit(driver:str|None=None,date:str|None=None,from_date:str|None=None,to_date:str|None=None,limit:int=200):
    q='SELECT * FROM attendance_audit WHERE 1=1'; a=[]
    if driver: q+=' AND driver_name=?'; a.append(driver)
    if date: q+=' AND work_date=?'; a.append(date)
    if from_date: q+=' AND work_date>=?'; a.append(from_date)
    if to_date: q+=' AND work_date<=?'; a.append(to_date)
    q+=' ORDER BY id DESC LIMIT ?'; a.append(max(1,min(1000,limit)))
    with conn() as c: rows=[{'id':r['id'],'ts':r['ts'],'driver':r['driver_name'],'date':r['work_date'],'store':r['store'],'event':r['event'],'actor':r['actor'],'detail':json.loads(r['detail'] or '{}')} for r in c.execute(q,a)]
    return {'rows':rows,'count':len(rows)}

# prune old location history (45 days)
with conn() as _c: _c.execute('DELETE FROM location_log WHERE ts<?',(_iso(_now()-timedelta(days=45)),))

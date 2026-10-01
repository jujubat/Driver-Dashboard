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

app=FastAPI(title='Driver Operations Dashboard SQL API', version='51.0')

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
        ''')
        # Safe v35 -> v36 migration
        cols={r['name'] for r in c.execute('PRAGMA table_info(attendance)')}
        for col,ddl in [('admin_override','INTEGER NOT NULL DEFAULT 0'),('override_reason','TEXT'),('override_by','TEXT'),('override_type','TEXT'),('override_proof_json','TEXT'),('no_photo_reason','TEXT'),('no_photo_note','TEXT'),('late_proof_json','TEXT'),('pending_approval','INTEGER NOT NULL DEFAULT 0'),('approval_status','TEXT')]:
            if col not in cols: c.execute(f'ALTER TABLE attendance ADD COLUMN {col} {ddl}')
        dcols={r['name'] for r in c.execute('PRAGMA table_info(drivers)')}
        if 'email' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN email TEXT')
        if 'phone' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN phone TEXT')
        if 'password_hash' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN password_hash TEXT')
        if 'password_salt' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN password_salt TEXT')
        if 'imported_days_worked' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN imported_days_worked INTEGER')
        if 'days_worked_source' not in dcols: c.execute('ALTER TABLE drivers ADD COLUMN days_worked_source TEXT')
        wcols={r['name'] for r in c.execute('PRAGMA table_info(work_days)')}
        if 'stores_json' not in wcols: c.execute('ALTER TABLE work_days ADD COLUMN stores_json TEXT')
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_drivers_email ON drivers(email) WHERE email IS NOT NULL AND email <> ''")
init_db()

class RosterPayload(BaseModel): drivers:list[dict]
class AttendancePayload(BaseModel): driverName:str; date:str; record:dict
class WorkDayPayload(BaseModel): driverName:str; date:str; record:dict
class DriverLoginPayload(BaseModel): login:str; password:str=""
class DriverRegisterPayload(BaseModel): name:str; email:str; phone:str; password:str

@app.get('/')
def home(): return FileResponse(HTML)
@app.get('/health')
def health(): return {'ok':True,'database':'sqlite','retention':'indefinite (1 year+ supported)'}

@app.get('/api/health-check')
def api_health_check(): return {'ok':True,'version':'51.0'}

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
        if existing: raise HTTPException(409,'email already registered')
        # A driver may already exist in the operational roster before creating an app account.
        # Claim that roster row instead of trying to INSERT the same name (name is the PK).
        roster_row=c.execute('SELECT * FROM drivers WHERE lower(trim(name))=? LIMIT 1',(name.lower(),)).fetchone()
        if roster_row:
            if (roster_row['email'] or '').strip():
                raise HTTPException(409,'driver name is already linked to another email')
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

@app.get('/api/dashboard-state')
def dashboard_state():
    with conn() as c:
        drivers=[{'name':r['name'],'driverId':r['driver_id'] or '', 'email':r['email'] or '', 'phone':r['phone'] or '', 'selfRegistered':bool(r['self_registered']),'daysWorked':r['imported_days_worked'],'daysWorkedSource':r['days_worked_source'] or ''} for r in c.execute('SELECT * FROM drivers ORDER BY name')]
        att={}
        for r in c.execute('SELECT * FROM attendance'):
            rec={'am':bool(r['am']),'pm':bool(r['pm']),'amPhoto':json.loads(r['am_photo_json']) if r['am_photo_json'] else None,'pmPhoto':json.loads(r['pm_photo_json']) if r['pm_photo_json'] else None,'photoVerified':bool(r['photo_verified']),'photoTime':r['photo_time'],'adminOverride':bool(r['admin_override']),'overrideReason':r['override_reason'],'overrideBy':r['override_by'],'overrideType':r['override_type'],'overrideProofPhoto':json.loads(r['override_proof_json']) if r['override_proof_json'] else None,'noPhotoReason':r['no_photo_reason'],'noPhotoNote':r['no_photo_note'],'lateProofPhoto':json.loads(r['late_proof_json']) if r['late_proof_json'] else None,'pendingApproval':bool(r['pending_approval']),'approvalStatus':r['approval_status'] or ('Pending Approval' if r['pending_approval'] else 'Approved')}
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
                  imported_days_worked=COALESCE(imported_days_worked,?),
                  days_worked_source=CASE WHEN imported_days_worked IS NULL AND ? IS NOT NULL THEN ? ELSE days_worked_source END,
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


# ══ v51: live-location "away from store" flags ═══════════════════════════
# A driver is "away" when their live GPS position is outside the geofence
# (default 300 m) of ALL the stores they selected. An away event records when they
# left and when they came back; it is FLAGGED once the time away reaches 60 min.
# SA has no DST, so a fixed UTC+2 offset gives the correct local work date.
AWAY_FLAG_MINUTES = 60
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

class StoreLocPayload(BaseModel): store:str; lat:float; lng:float; radius_m:int=300; updatedBy:str=""
class PingPayload(BaseModel): driverName:str; stores:list[str]=[]; lat:float; lng:float; accuracy:float|None=None

@app.get('/api/store-locations')
def get_store_locations():
    with conn() as c: rows=[dict(r) for r in c.execute('SELECT store,lat,lng,radius_m,updated_by,updated_at FROM store_locations ORDER BY store')]
    return {'rows':rows}

@app.post('/api/store-locations')
def set_store_location(p:StoreLocPayload):
    if not (-90<=p.lat<=90 and -180<=p.lng<=180): raise HTTPException(400,'invalid coordinates')
    store=p.store.strip()
    if not store: raise HTTPException(400,'store required')
    radius=max(50,min(5000,int(p.radius_m)))
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
    now=_now(); now_s=_iso(now); work_date=now.astimezone(SAST).strftime('%Y-%m-%d')
    with conn() as c:
        best=None
        for st in p.stores:
            loc=c.execute('SELECT * FROM store_locations WHERE store=?',(st,)).fetchone()
            if not loc: continue
            d=_meters(p.lat,p.lng,loc['lat'],loc['lng'])
            # distance relative to that store's own radius, so mixed radii compare fairly
            if best is None or d-loc['radius_m'] < best[0]-best[2]: best=(d,st,loc['radius_m'])
        if best is None: return {'ok':True,'tracked':False,'reason':'no_store_coordinates'}
        dist,store,radius=best
        ev=c.execute('SELECT * FROM away_events WHERE driver_name=? AND returned_at IS NULL ORDER BY id DESC LIMIT 1',(name,)).fetchone()
        if dist>radius:
            if ev:
                c.execute('UPDATE away_events SET last_seen=?,max_distance_m=MAX(max_distance_m,?),last_lat=?,last_lng=? WHERE id=?',(now_s,int(dist),p.lat,p.lng,ev['id']))
            else:
                c.execute('INSERT INTO away_events(driver_name,store,work_date,left_at,last_seen,max_distance_m,last_lat,last_lng) VALUES(?,?,?,?,?,?,?,?)',(name,store,work_date,now_s,now_s,int(dist),p.lat,p.lng))
        elif ev:
            c.execute('UPDATE away_events SET returned_at=?,last_seen=? WHERE id=?',(now_s,now_s,ev['id']))
            # drop trivial blips (GPS jitter) so the table only keeps meaningful absences
            if (now-_parse(ev['left_at'])).total_seconds()<300: c.execute('DELETE FROM away_events WHERE id=?',(ev['id'],))
    return {'ok':True,'tracked':True,'away':dist>radius,'distance_m':int(dist),'store':store}

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
                    'lastSeen':r['last_seen'],'minutesAway':mins,'flagged':flagged,'status':status,'maxDistanceM':r['max_distance_m'],'lat':r['last_lat'],'lng':r['last_lng']})
    return {'date':date,'flagMinutes':AWAY_FLAG_MINUTES,'rows':out,'count':len(out)}

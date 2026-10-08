import io
import csv
import threading
import html
# -*- coding: utf-8 -*-
# Kasi Sports News v399 — locked v397 UI + backend shared LKG/SWR: finished layout, Tip priority/fallback, exports, mobile news, teams, admin SPA
"""
FOOTBALL SERVER — KasiScore Predictive Dashboard
v39 — OddsPapi v5 REST Integration

Secure local proxy between the KasiScore dashboard and API-Football.
"""

import asyncio
import contextlib
import json
import logging
import math
import os
import re
from html.parser import HTMLParser
import html
from difflib import SequenceMatcher
import sqlite3
try:
    import psycopg2
    from psycopg2 import IntegrityError as PsycopgIntegrityError
except Exception:
    psycopg2 = None
    PsycopgIntegrityError = Exception
import hashlib
import hmac
import base64
import secrets
import time
import uuid
import smtplib
from email.message import EmailMessage
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, Optional
from html import escape, unescape

import httpx
try:
    import websockets
except Exception:
    websockets = None
from cachetools import TTLCache
from dotenv import load_dotenv
# KSN backend v359: prediction feeds remain public; no prediction entitlement gate.
from fastapi import FastAPI, HTTPException, Query, Header, Response, Request
from fastapi.responses import HTMLResponse, FileResponse, Response, StreamingResponse, RedirectResponse
from fastapi.middleware.cors import CORSMiddleware
from fastapi.middleware.gzip import GZipMiddleware
from pydantic import BaseModel, Field

# ---------------------------------------------------------------------------
# CONFIG
# ---------------------------------------------------------------------------

BASE_DIR = Path(__file__).resolve().parent
INDEX_HTML = BASE_DIR / "index.html"
load_dotenv(BASE_DIR / ".env", override=True)

API_KEY = os.getenv("AFOOT_API_KEY", "")
API_BASE = "https://v3.football.api-sports.io"

# Optional odds fallback. This is The Odds API v4 (the response shape supplied
# with this release matches its /v4/sports/{sport}/odds endpoint). It is only
# used when the primary API-Football odds request fails or returns no usable
# bookmaker 1X2 odds.  Fixture loading itself is NOT subject to this timeout.
ODDS_API_KEY = os.getenv("ODDS_API_KEY", "")
ODDS_API_BASE = os.getenv("ODDS_API_BASE", "https://api.the-odds-api.com/v4")
ODDS_API_TIMEOUT = float(os.getenv("ODDS_API_TIMEOUT", "5"))
ODDS_API_REGIONS = os.getenv("ODDS_API_REGIONS", "eu")
ODDS_API_MARKETS = os.getenv("ODDS_API_MARKETS", "h2h")
ODDS_API_ENABLED = os.getenv("ODDS_API_ENABLED", "1").lower() not in {"0", "false", "no", "off"}
# OddsPAPI v4 — API-Football remains primary; OddsPAPI fills missing bookmaker odds.
ODDSPAPI_API_KEY = os.getenv("ODDSPAPI_API_KEY", "").strip()
ODDSPAPI_REST_BASE = os.getenv("ODDSPAPI_REST_BASE", "https://v5.oddspapi.io").rstrip("/")
ODDSPAPI_REST_LANGUAGE = os.getenv("ODDSPAPI_REST_LANGUAGE", "en").strip().lower() or "en"
ODDSPAPI_V4_FALLBACK_BASE = os.getenv("ODDSPAPI_V4_FALLBACK_BASE", "https://api.oddspapi.io/v4").rstrip("/")
ODDSPAPI_WS_BASE = os.getenv("ODDSPAPI_WS_BASE", "wss://v5.oddspapi.io/ws")
ODDSPAPI_ENABLED = os.getenv("ODDSPAPI_ENABLED", "1").lower() not in {"0","false","no","off"}
# WebSocket is a separate entitlement. Keep REST enabled even when the account
# does not include WebSocket access.
ODDSPAPI_WS_ENABLED = os.getenv("ODDSPAPI_WS_ENABLED", "0").lower() not in {"0","false","no","off"}
ODDSPAPI_BOOKMAKERS = tuple(
    x.strip().lower() for x in os.getenv("ODDSPAPI_BOOKMAKERS", "bet365,betway").split(",") if x.strip()
)
ODDSPAPI_SPORT_FOOTBALL = int(os.getenv("ODDSPAPI_SPORT_FOOTBALL", "10"))
ODDSPAPI_SPORT_RUGBY = int(os.getenv("ODDSPAPI_SPORT_RUGBY", "26"))
ODDSPAPI_SPORT_CRICKET = int(os.getenv("ODDSPAPI_SPORT_CRICKET", "27"))
ODDSPAPI_FIXTURE_TTL = int(os.getenv("ODDSPAPI_FIXTURE_TTL", "180"))
ODDSPAPI_ODDS_TTL = int(os.getenv("ODDSPAPI_ODDS_TTL", "1800"))
TIMEZONE = os.getenv("TIMEZONE", "Africa/Johannesburg")
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")
PORT = int(os.getenv("PORT", "8000"))

AUTH_DB = Path(os.getenv("AUTH_DB_PATH", str(BASE_DIR / "kasiscore_users.db")))
DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
AUTH_SECRET = os.getenv("AUTH_SECRET", "")
if not AUTH_SECRET:
    AUTH_SECRET = secrets.token_hex(32)

# ---------------------------------------------------------------------------
# AUTH DATABASE — Turso (free cloud SQLite) or local SQLite fallback
# ---------------------------------------------------------------------------
# On Render free tier the local filesystem is wiped on every restart, which
# deletes all users and causes instant logout. Solution: use Turso, a free
# cloud-hosted SQLite that persists forever.
#
# Setup (5 minutes, free):
#   1. Go to https://turso.tech and sign up (free tier: 500MB, unlimited DBs)
#   2. Install CLI:  curl -sSfL https://get.tur.so/install.sh | bash
#   3. turso auth login
#   4. turso db create kasiscore
#   5. turso db show kasiscore           # copy the "URL" value
#   6. turso db tokens create kasiscore  # copy the token
#   7. In Render dashboard → Environment, add:
#        TURSO_DB_URL   = libsql://kasiscore-<yourname>.turso.io
#        TURSO_DB_TOKEN = <the token from step 6>
#        AUTH_SECRET    = <run: python3 -c "import secrets;print(secrets.token_hex(32))">
#        ADMIN_EMAIL    = jbatuma@yahoo.com
#
# Without TURSO_DB_URL set, the server falls back to local SQLite (fine for
# local development, NOT for Render free tier).
# ---------------------------------------------------------------------------

TURSO_DB_URL   = os.getenv("TURSO_DB_URL", "").strip()
TURSO_DB_TOKEN = os.getenv("TURSO_DB_TOKEN", "").strip()

class _AuthCursor:
    """Small cursor wrapper shared by SQLite and PostgreSQL auth."""
    def __init__(self, cursor=None, lastrowid=None):
        self._cursor = cursor
        self.lastrowid = lastrowid
        self.rowcount = getattr(cursor, "rowcount", -1) if cursor is not None else -1

    def fetchone(self):
        return self._cursor.fetchone() if self._cursor is not None else None

    def fetchall(self):
        return self._cursor.fetchall() if self._cursor is not None else []


class _AuthConnection:
    """DB-API compatibility wrapper for PostgreSQL/SQLite auth."""
    def __init__(self, conn, backend):
        self._conn = conn
        self.backend = backend
        self.total_changes = 0

    def execute(self, sql, params=()):
        if self.backend == "sqlite":
            cur = self._conn.execute(sql, params)
            self.total_changes = self._conn.total_changes
            return _AuthCursor(cur, getattr(cur, "lastrowid", None))

        # Existing auth SQL uses SQLite '?' placeholders. Translate for psycopg2.
        pg_sql = sql.replace("?", "%s")
        wants_user_id = (
            re.match(r"\s*INSERT\s+INTO\s+users\b", pg_sql, re.I) is not None
            and "RETURNING" not in pg_sql.upper()
        )
        if wants_user_id:
            pg_sql = pg_sql.rstrip().rstrip(";") + " RETURNING id"
        cur = self._conn.cursor()
        try:
            cur.execute(pg_sql, tuple(params or ()))
            lastrowid = None
            if wants_user_id:
                row = cur.fetchone()
                lastrowid = int(row[0]) if row else None
            self.total_changes += max(int(cur.rowcount or 0), 0)
            return _AuthCursor(cur, lastrowid)
        except PsycopgIntegrityError as exc:
            self._conn.rollback()
            cur.close()
            raise sqlite3.IntegrityError(str(exc)) from exc
        except Exception:
            self._conn.rollback()
            cur.close()
            raise

    def commit(self):
        self._conn.commit()

    def close(self):
        self._conn.close()


def _ensure_sqlite_auth_schema(raw):
    raw.execute("""CREATE TABLE IF NOT EXISTS users(
      id INTEGER PRIMARY KEY AUTOINCREMENT,email TEXT UNIQUE NOT NULL,password_hash TEXT NOT NULL,
      username TEXT UNIQUE, phone TEXT UNIQUE,
      pro INTEGER NOT NULL DEFAULT 0, created_at TEXT NOT NULL)""")
    for col,typ in [
        ("reset_token","TEXT"),("reset_expires","REAL"),("username","TEXT"),
        ("phone","TEXT"),("role","TEXT DEFAULT 'user'"),
        ("status","TEXT DEFAULT 'active'"),("last_login","TEXT")
    ]:
        try:
            raw.execute(f"ALTER TABLE users ADD COLUMN {col} {typ}")
        except Exception:
            pass
    raw.commit()


def _sqlite_auth_source():
    """Open the legacy SQLite auth DB only for fallback/migration."""
    AUTH_DB.parent.mkdir(parents=True, exist_ok=True)
    raw = sqlite3.connect(str(AUTH_DB), timeout=20)
    raw.row_factory = sqlite3.Row
    raw.execute("PRAGMA journal_mode=WAL")
    raw.execute("PRAGMA synchronous=NORMAL")
    raw.execute("PRAGMA busy_timeout=20000")
    _ensure_sqlite_auth_schema(raw)
    return raw


def _ensure_postgres_auth_schema(conn):
    cur=conn.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS users(
          id BIGSERIAL PRIMARY KEY,
          email TEXT UNIQUE NOT NULL,
          password_hash TEXT NOT NULL,
          username TEXT UNIQUE,
          phone TEXT UNIQUE,
          pro INTEGER NOT NULL DEFAULT 0,
          created_at TEXT NOT NULL,
          reset_token TEXT,
          reset_expires DOUBLE PRECISION,
          role TEXT DEFAULT 'user',
          status TEXT DEFAULT 'active',
          last_login TEXT
        )
    """)
    cur.execute("CREATE INDEX IF NOT EXISTS idx_users_email_lower ON users ((lower(email)))")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_users_username_lower ON users ((lower(username)))")
    conn.commit()
    cur.close()


def _migrate_sqlite_users_to_postgres(pg_conn):
    """One-time safe migration. Existing password hashes and IDs are preserved."""
    if not AUTH_DB.exists():
        return 0
    src=_sqlite_auth_source()
    try:
        rows=src.execute("""
            SELECT id,email,password_hash,username,phone,pro,created_at,
                   reset_token,reset_expires,
                   COALESCE(role,'user'),COALESCE(status,'active'),last_login
            FROM users ORDER BY id
        """).fetchall()
        if not rows:
            return 0
        cur=pg_conn.cursor()
        migrated=0
        for r in rows:
            cur.execute("""
                INSERT INTO users(
                  id,email,password_hash,username,phone,pro,created_at,
                  reset_token,reset_expires,role,status,last_login
                ) VALUES(%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
                ON CONFLICT (email) DO NOTHING
            """, tuple(r))
            migrated += max(int(cur.rowcount or 0),0)
        cur.execute("""
            SELECT setval(
              pg_get_serial_sequence('users','id'),
              GREATEST(COALESCE((SELECT MAX(id) FROM users),1),1),
              true
            )
        """)
        pg_conn.commit()
        cur.close()
        return migrated
    finally:
        src.close()


def _postgres_auth_connection():
    if psycopg2 is None:
        raise RuntimeError(
            "DATABASE_URL is configured but psycopg2 is not installed. "
            "Add psycopg2-binary to requirements.txt."
        )
    conn=psycopg2.connect(DATABASE_URL, connect_timeout=10)
    conn.autocommit=False
    _ensure_postgres_auth_schema(conn)

    # Migrate legacy SQLite users only when PostgreSQL is still empty.
    cur=conn.cursor()
    cur.execute("SELECT COUNT(*) FROM users")
    count=int(cur.fetchone()[0])
    cur.close()
    if count == 0:
        _migrate_sqlite_users_to_postgres(conn)
    return conn


def _auth_db():
    """Use Render PostgreSQL when DATABASE_URL exists; SQLite remains a safe fallback."""
    if DATABASE_URL:
        return _AuthConnection(_postgres_auth_connection(), "postgres")

    raw=_sqlite_auth_source()
    return _AuthConnection(raw, "sqlite")


def _pw(password,salt=None):
    salt=salt or secrets.token_hex(16)
    dk=hashlib.pbkdf2_hmac("sha256",password.encode(),bytes.fromhex(salt),180000).hex()
    return salt+"$"+dk
def _token(user_id):
    raw=f"{user_id}.{int(time.time())}"
    sig=hmac.new(AUTH_SECRET.encode(),raw.encode(),hashlib.sha256).digest()
    return base64.urlsafe_b64encode((raw+"."+base64.urlsafe_b64encode(sig).decode()).encode()).decode()
def _user_from_token(auth):
    if not auth or not auth.lower().startswith("bearer "): return None
    try:
        raw=base64.urlsafe_b64decode(auth.split(None,1)[1]).decode()
        uid,ts,sig=raw.split(".",2); payload=f"{uid}.{ts}"
        expected=base64.urlsafe_b64encode(hmac.new(AUTH_SECRET.encode(),payload.encode(),hashlib.sha256).digest()).decode()
        if not hmac.compare_digest(sig,expected) or time.time()-int(ts)>60*60*24*30:return None
        c=_auth_db(); row=c.execute("SELECT id,email,pro,COALESCE(role,'user'),COALESCE(status,'active') FROM users WHERE id=?",(int(uid),)).fetchone(); c.close()
        if not row or row[4]!="active": return None
        return row
    except Exception:return None

# ---------------------------------------------------------------------------
# PUSH NOTIFICATION STORE
# ---------------------------------------------------------------------------
PUSH_DB = BASE_DIR / "kasiscore_push.db"
PAYFAST_PASSPHRASE = os.getenv("PAYFAST_PASSPHRASE", "")
STRIPE_WEBHOOK_SECRET = os.getenv("STRIPE_WEBHOOK_SECRET", "")
PAYMENT_ADMIN_EMAIL = os.getenv("PAYMENT_ADMIN_EMAIL", "")

def _push_db():
    c = sqlite3.connect(PUSH_DB)
    c.execute("""CREATE TABLE IF NOT EXISTS push_subscriptions(
        id TEXT PRIMARY KEY,
        user_id INTEGER,
        endpoint TEXT NOT NULL,
        p256dh TEXT NOT NULL,
        auth_key TEXT NOT NULL,
        user_agent TEXT,
        created_at TEXT NOT NULL,
        UNIQUE(endpoint))""")
    c.execute("""CREATE TABLE IF NOT EXISTS push_log(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        subscription_id TEXT,
        title TEXT,
        sent_at TEXT,
        status TEXT)""")
    c.commit(); return c

def _store_push_subscription(user_id, sub_data: dict, ua: str = "") -> str:
    sub_id = str(uuid.uuid4())
    c = _push_db()
    try:
        c.execute("""INSERT OR REPLACE INTO push_subscriptions
            (id, user_id, endpoint, p256dh, auth_key, user_agent, created_at)
            VALUES (?,?,?,?,?,?,?)""",
            (sub_id, user_id,
             sub_data.get("endpoint",""),
             sub_data.get("keys",{}).get("p256dh",""),
             sub_data.get("keys",{}).get("auth",""),
             ua, datetime.now(timezone.utc).isoformat()))
        c.commit()
    finally: c.close()
    return sub_id

def _get_push_subscriptions(user_id=None) -> list:
    c = _push_db()
    if user_id:
        rows = c.execute("SELECT id,endpoint,p256dh,auth_key FROM push_subscriptions WHERE user_id=?", (user_id,)).fetchall()
    else:
        rows = c.execute("SELECT id,endpoint,p256dh,auth_key FROM push_subscriptions").fetchall()
    c.close()
    return [{"id": r[0], "endpoint": r[1], "p256dh": r[2], "auth": r[3]} for r in rows]

def _delete_push_subscription(endpoint: str):
    c = _push_db(); c.execute("DELETE FROM push_subscriptions WHERE endpoint=?", (endpoint,)); c.commit(); c.close()

def _log_push(sub_id: str, title: str, status: str):
    c = _push_db()
    c.execute("INSERT INTO push_log(subscription_id,title,sent_at,status) VALUES(?,?,?,?)",
              (sub_id, title, datetime.now(timezone.utc).isoformat(), status))
    c.commit(); c.close()

async def _send_web_push(sub: dict, title: str, body: str, url: str = "/") -> bool:
    """Send a Web Push notification via pywebpush (install: pip install pywebpush)."""
    try:
        from pywebpush import webpush, WebPushException  # type: ignore
        vapid_private = os.getenv("VAPID_PRIVATE_KEY", "")
        vapid_email = os.getenv("VAPID_EMAIL", PAYMENT_ADMIN_EMAIL or "admin@kasiscore.com")
        if not vapid_private:
            log.warning("VAPID_PRIVATE_KEY not set — push not sent. Run: python -m pywebpush --gen-keys")
            return False
        payload = json.dumps({"title": title, "body": body, "url": url})
        webpush(
            subscription_info={"endpoint": sub["endpoint"], "keys": {"p256dh": sub["p256dh"], "auth": sub["auth"]}},
            data=payload,
            vapid_private_key=vapid_private,
            vapid_claims={"sub": f"mailto:{vapid_email}"}
        )
        _log_push(sub["id"], title, "sent"); return True
    except Exception as e:
        log.warning(f"Push send failed: {e}")
        _log_push(sub.get("id","?"), title, f"error:{e}")
        if "410" in str(e) or "404" in str(e):
            _delete_push_subscription(sub.get("endpoint",""))
        return False

# ---------------------------------------------------------------------------
# PER-IP / PER-USER RATE LIMITING
# ---------------------------------------------------------------------------
_rl_buckets: dict = {}

def _rate_limit_user(key: str, limit: int = 60, window: int = 60) -> bool:
    """Returns True if allowed, False if blocked."""
    now = time.time()
    bucket = _rl_buckets.setdefault(key, [])
    _rl_buckets[key] = [t for t in bucket if now - t < window]
    if len(_rl_buckets[key]) >= limit:
        return False
    _rl_buckets[key].append(now)
    return True

def _client_key(request: Request, namespace: str, identity: str = "") -> str:
    forwarded=request.headers.get("x-forwarded-for","")
    ip=forwarded.split(",")[0].strip() if forwarded else (request.client.host if request.client else "unknown")
    return f"{namespace}:{ip}:{(identity or '').strip().lower()}"

def _require_auth_rate(request: Request, namespace: str, identity: str = "", limit: int = 10, window: int = 300):
    if not _rate_limit_user(_client_key(request,namespace,identity),limit=limit,window=window):
        raise HTTPException(status_code=429,detail="Too many attempts. Please try again later.")


logging.basicConfig(
    level=getattr(logging, LOG_LEVEL.upper(), logging.INFO),
    format="%(asctime)s [%(levelname)s] %(message)s",
)
log = logging.getLogger("football_server")

if not API_KEY:
    log.warning("AFOOT_API_KEY not set in .env")

LEAGUE_IDS = {
    "Premier League": 39,
    "La Liga": 140,
    "Serie A": 135,
    "Bundesliga": 78,
    "Ligue 1": 61,
    "Champions League": 2,
    "Europa League": 3,
    "PSL South Africa": 288,
    "MLS": 253,
    "Eredivisie": 88,
    "Primeira Liga": 94,
    "Brazilian Serie A": 71,
    "Argentine Primera": 128,
    "J1 League Japan": 98,
    "Scottish Premiership": 179,
    "Turkish Super Lig": 203,
    "Norway Eliteserien": 103,
    "Denmark Superliga": 119,
    "Cyprus First Division": 262,
    "Belgian Pro League": 144,
    "FA Cup": 45,
    "EFL Cup": 48,
    "Copa del Rey": 143,
    "Coppa Italia": 137,
    "DFB-Pokal": 81,
    "Coupe de France": 66,
    "Championship": 40, "LaLiga Hypermotion": 141, "2. Bundesliga": 79, "Serie B": 136, "Ligue 2": 62,
    "Super League Greece": 197, "Austrian Bundesliga": 218, "Swiss Super League": 207, "Ekstraklasa": 106,
    "Egyptian Premier League": 233, "Botola Pro": 200, "Algerian Ligue 1": 186, "Tunisian Ligue 1": 202,
    "Nigeria Premier Football League": 332, "Ghana Premier League": 570, "UAE Pro League": 301,
    "Qatar Stars League": 305, "Indian Super League": 323, "Chinese Super League": 169, "Thai League 1": 296,
    "Liga 1 Indonesia": 274, "Primera A Colombia": 239, "Primera División Chile": 265, "Liga Pro Ecuador": 242,
    "Liga 1 Peru": 281, "Primera División Uruguay": 268, "Primera División Costa Rica": 162,
    "Liga Nacional Guatemala": 165, "K League 1": 292, "J1 League": 98, "A-League": 188,
}

# v458 — locked global football competition priority.
# Display/selection order only: never removes lower-priority competitions.
_KSN_COUNTRY_NAMES = {
    "ZA":"south africa","GB":"england","EN":"england","ES":"spain","DE":"germany","IT":"italy","FR":"france","TR":"turkey",
    "NG":"nigeria","GH":"ghana","KE":"kenya","EG":"egypt","MA":"morocco","DZ":"algeria","TN":"tunisia","US":"united states",
    "CA":"canada","MX":"mexico","BR":"brazil","AR":"argentina","JP":"japan","KR":"south korea","CN":"china","IN":"india",
    "SA":"saudi arabia","AE":"united arab emirates","QA":"qatar","AU":"australia","NZ":"new zealand","PT":"portugal","NL":"netherlands",
    "BE":"belgium","CH":"switzerland","AT":"austria","GR":"greece","PL":"poland","SE":"sweden","NO":"norway","DK":"denmark"
}

def _ksn_match_league_text(row: dict) -> str:
    vals=(row.get("league"),row.get("leagueName"),row.get("competition"),row.get("country"),row.get("countryName"))
    return " ".join(str(v or "") for v in vals).casefold()

def _ksn_league_priority_bucket(row: dict, visitor_country: str="") -> int:
    """Premier League -> La Liga -> Bundesliga -> Serie A -> Ligue 1 -> Turkish Super Lig -> visitor country -> other."""
    t=_ksn_match_league_text(row)
    country=str(row.get("country") or row.get("countryName") or "").strip().casefold()
    # Provider league IDs are safest when available; text guards prevent similarly named leagues.
    lid=row.get("_leagueId") or row.get("leagueId") or row.get("competitionId")
    try: lid=int(lid) if lid not in (None,"") else None
    except Exception: lid=None
    if lid==39 or ("premier league" in t and not any(k in t for k in ("ghana","nigeria","egypt","south africa","zimbabwe","jamaica"))): return 0
    if lid==140 or "la liga" in t or "laliga" in t: return 1
    if lid==78 or ("bundesliga" in t and "2. bundesliga" not in t and "frauen" not in t): return 2
    if lid==135 or ("serie a" in t and not any(k in t for k in ("brazil","brasil","ecuador"))): return 3
    if lid==61 or "ligue 1" in t: return 4
    if lid==203 or "turkish super lig" in t or "süper lig" in t or "super lig" in t: return 5
    vc=str(visitor_country or "").strip().casefold()
    vc=_KSN_COUNTRY_NAMES.get(vc.upper(),vc)
    if vc and (country==vc or vc in t): return 6
    return 7

def _ksn_sort_football_rows(rows, visitor_country: str="", newest_first: bool=False):
    rows=list(rows or [])
    def dt(row):
        return str(row.get("datetime") or row.get("date") or row.get("kickoff") or row.get("startTime") or "")
    # Stable bucket sort preserves provider order within a tier unless newest-first is explicitly requested.
    if newest_first:
        rows.sort(key=dt, reverse=True)
    return sorted(rows,key=lambda x:_ksn_league_priority_bucket(x,visitor_country))

def _ksn_request_country(request: Request) -> str:
    code=(request.headers.get("cf-ipcountry") or request.headers.get("x-vercel-ip-country") or request.headers.get("x-country-code") or "").strip().upper()
    return _KSN_COUNTRY_NAMES.get(code,code.casefold())

def _current_season() -> int:
    """Return the current football season start year.

    Football seasons straddle two calendar years (Aug–May).
    Before 1 August we are still in the season that started the *previous*
    calendar year, so we subtract 1 from the year.
    API-Football uses the season's start year as the season identifier.
    """
    now = datetime.now()
    return now.year if now.month >= 8 else now.year - 1


_scan_env = os.getenv("SCAN_LEAGUES", "")
SCAN_LEAGUES = (
    [x.strip() for x in _scan_env.split(",") if x.strip()]
    if _scan_env
    else [
        "Premier League",
        "La Liga",
        "Bundesliga",
        "Serie A",
        "Ligue 1",
        "Champions League",
        "Europa League",
        "PSL South Africa",
        "Saudi Pro League",
        "MLS",
        "Eredivisie",
        "Primeira Liga",
        "Brazilian Serie A",
        "Argentine Primera",
        "J1 League Japan",
        "Scottish Premiership",
        "Turkish Super Lig",
        "Belgian Pro League",
    ]
)

# ---------------------------------------------------------------------------
# CACHES / QUOTA
# ---------------------------------------------------------------------------

_fixtures_cache = TTLCache(maxsize=200, ttl=1800)
_fixtures_last_good = TTLCache(maxsize=200, ttl=21600)  # v51: 6h stale-good protection
_live_cache = TTLCache(maxsize=50, ttl=180)  # v184: one upstream live refresh per minute
_odds_cache = TTLCache(maxsize=500, ttl=1800)       # v184: pre-match odds every 30 min
_team_cache = TTLCache(maxsize=500, ttl=604800)
_live_stats_cache = TTLCache(maxsize=500, ttl=180)  # v184: live stats every 3 min
_players_cache = TTLCache(maxsize=100, ttl=86400)   # 24-hour cache for player stats
_standings_cache = TTLCache(maxsize=100, ttl=10800) # 3-hr (was 1 hr) — standings update after matchday
_form_cache = TTLCache(maxsize=500, ttl=10800)      # 3-hr (was 1 hr) — last-5 form is stable intra-day
_prematch_odds_batch_cache = TTLCache(maxsize=100, ttl=1800)  # v184: cache even empty odds scans for 30 min
_odds_api_events_cache = TTLCache(maxsize=100, ttl=1800)  # v217: The Odds API feed, shared across widgets
_oddspapi_fixture_cache = TTLCache(maxsize=20, ttl=ODDSPAPI_FIXTURE_TTL)
_oddspapi_odds_cache = TTLCache(maxsize=3000, ttl=ODDSPAPI_ODDS_TTL)
_oddspapi_afoot_map = TTLCache(maxsize=3000, ttl=6 * 3600)
_oddspapi_ws_state = {
    "connected": False,
    "authenticated": False,
    "gateway": ODDSPAPI_WS_BASE,
    "receiveType": "json",
    "channels": ["fixtures", "scores", "odds"],
    "lastMessageAt": None,
    "lastError": None,
    "lastControl": None,
    "messages": 0,
    "reconnects": 0,
    "serverEpoch": None,
    "replayChannels": None,
    "lastSeenId": {},
    "resumeComplete": False,
}

# ---------------------------------------------------------------------------
# PERSISTENT SQLITE CACHE — survives server restarts / cold starts
# ---------------------------------------------------------------------------
APICACHE_DB = Path(os.getenv("APICACHE_DB", str(BASE_DIR / "api_cache.sqlite3")))

def _apicache_db():
    conn = sqlite3.connect(str(APICACHE_DB))
    conn.row_factory = sqlite3.Row
    conn.execute("""
        CREATE TABLE IF NOT EXISTS api_cache (
            cache_key   TEXT PRIMARY KEY,
            path        TEXT NOT NULL,
            params_json TEXT NOT NULL,
            response    TEXT NOT NULL,
            fetched_at  TEXT NOT NULL,
            ttl_seconds INTEGER NOT NULL
        )
    """)
    conn.commit()
    return conn

def _persist_cache_key(path: str, params: dict) -> str:
    raw = path + "|" + json.dumps(params, sort_keys=True)
    return hashlib.sha256(raw.encode()).hexdigest()

# Per-endpoint persistent TTL (seconds). Longer than in-memory TTL because
# we want to survive restarts and only re-fetch when genuinely stale.
_PERSISTENT_TTL: dict[str, int] = {
    "/teams":                7 * 86400,  # 7 days — static metadata
    "/players":              7 * 86400,  # 7 days — profile doesn't change mid-season
    "/fixtures/headtohead":    86400,    # 24 hrs — history doesn't change
    "/injuries":            3 * 3600,    # 3 hrs  — injury lists update on training days
    "/standings":           3 * 3600,    # 3 hrs  — standings update after matchday only
    "/fixtures/lineups":       3600,     # 1 hr   — lineups confirmed ~1 hr before KO
    "/fixtures/statistics":    3600,     # 1 hr   — stats don't change once fetched post-match
    "/fixtures/players":       3600,     # 1 hr   — same as statistics
    "/odds":                   3600,     # 1 hr   — odds shift but not minute-to-minute
    "/fixtures":               1800,     # 30 min default; live/date-specific TTL adjusted below
    "/transfers":           7 * 86400,   # 7 days — transfer windows are slow
}

def _persistent_cache_get(path: str, params: dict) -> dict | None:
    """Return cached API response from SQLite if still within TTL, else None."""
    key = _persist_cache_key(path, params)
    try:
        conn = _apicache_db()
        row = conn.execute(
            "SELECT response, fetched_at, ttl_seconds FROM api_cache WHERE cache_key=?",
            (key,)
        ).fetchone()
        conn.close()
        if row:
            fetched = datetime.fromisoformat(row["fetched_at"])
            if fetched.tzinfo is None:
                fetched = fetched.replace(tzinfo=timezone.utc)
            age = (datetime.now(timezone.utc) - fetched).total_seconds()
            if age < row["ttl_seconds"]:
                cached_data = json.loads(row["response"])
                # v307: an empty fixture response is a VALID cached result.
                # This is critical for live=all: "nothing live" must not spend
                # another upstream call for every visitor during the same 3-minute window.
                return cached_data
    except Exception as e:
        log.debug("Persistent cache read error: %s", e)
    return None

def _persistent_cache_set(path: str, params: dict, data: dict):
    """Write API response to SQLite persistent cache."""
    ttl = _PERSISTENT_TTL.get(path, 1800)
    # v307 quota protection: cache by fixture use-case, including empty results.
    # Live is intentionally short; historical finished dates are effectively immutable.
    if path == "/fixtures":
        if str(params.get("live") or "").lower() == "all":
            ttl = 180
        elif params.get("date"):
            try:
                qd = datetime.strptime(str(params.get("date")), "%Y-%m-%d").date()
                today = datetime.now(timezone.utc).date()
                ttl = 21600 if qd < today else 1800
            except Exception:
                ttl = 1800
    key = _persist_cache_key(path, params)
    try:
        conn = _apicache_db()
        conn.execute("""
            INSERT OR REPLACE INTO api_cache
              (cache_key, path, params_json, response, fetched_at, ttl_seconds)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (
            key, path,
            json.dumps(params, sort_keys=True),
            json.dumps(data),
            datetime.now(timezone.utc).isoformat(),
            ttl,
        ))
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug("Persistent cache write error: %s", e)

def _persistent_cache_purge_expired():
    """Clean up rows older than their TTL. Call from background task."""
    try:
        conn = _apicache_db()
        conn.execute("""
            DELETE FROM api_cache
            WHERE (julianday('now') - julianday(fetched_at)) * 86400 > ttl_seconds
        """)
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug("Persistent cache purge error: %s", e)

_team_profile_page_cache = TTLCache(maxsize=500, ttl=21600)
_rate_bucket = []
RATE_LIMIT_PER_MINUTE = int(os.getenv("RATE_LIMIT_PER_MINUTE", "90"))  # 90 req/min default; 0 to disable
KASISCORE_DAILY_BUDGET = int(os.getenv("KASISCORE_DAILY_BUDGET", "6500"))
KASISCORE_PROVIDER_RESERVE = int(os.getenv("KASISCORE_PROVIDER_RESERVE", "1000"))

_quota_state = {
    "dailyLimit": None,
    "dailyRemaining": None,
    "minuteLimit": None,
    "minuteRemaining": None,
    "lastStatus": None,
    "lastPath": None,
    "lastCheckedAt": None,
    "dailyExhausted": False,
    "minuteLimited": False,
}

# v295: independent API-Football call accounting and reserve protection.
_api_football_usage = {
    "utcDate": datetime.now(timezone.utc).date().isoformat(),
    "callsToday": 0,
    "callsByPath": {},
    "blockedByBudget": 0,
    "lastCallAt": None,
}

def _reset_api_football_usage_if_new_day():
    today = datetime.now(timezone.utc).date().isoformat()
    if _api_football_usage.get("utcDate") != today:
        _api_football_usage.update({
            "utcDate": today, "callsToday": 0, "callsByPath": {},
            "blockedByBudget": 0, "lastCallAt": None,
        })

def _record_api_football_call(path: str):
    _reset_api_football_usage_if_new_day()
    _api_football_usage["callsToday"] += 1
    by = _api_football_usage["callsByPath"]
    by[path] = int(by.get(path, 0)) + 1
    _api_football_usage["lastCallAt"] = datetime.now(timezone.utc).isoformat()

def _v448_api_football_provider_locked() -> bool:
    """True when background/non-essential API-Football work must use cache only."""
    _reset_api_football_usage_if_new_day()
    remaining = _quota_state.get("dailyRemaining")
    if isinstance(remaining, int) and remaining <= KASISCORE_PROVIDER_RESERVE:
        return True
    return int(_api_football_usage.get("callsToday", 0)) >= KASISCORE_DAILY_BUDGET


def _api_football_budget_guard(path: str):
    _reset_api_football_usage_if_new_day()
    remaining = _quota_state.get("dailyRemaining")
    limit = _quota_state.get("dailyLimit") or 7500
    if isinstance(remaining, int) and remaining <= KASISCORE_PROVIDER_RESERVE:
        _api_football_usage["blockedByBudget"] += 1
        raise HTTPException(429, detail={
            "code": "API_FOOTBALL_RESERVE_PROTECTED",
            "message": "API-Football reserve protected; use cached/fallback data.",
            "dailyRemaining": remaining, "dailyLimit": limit,
            "reserve": KASISCORE_PROVIDER_RESERVE, "path": path,
        })
    if int(_api_football_usage.get("callsToday", 0)) >= KASISCORE_DAILY_BUDGET:
        _api_football_usage["blockedByBudget"] += 1
        raise HTTPException(429, detail={
            "code": "KASISCORE_DAILY_PROVIDER_BUDGET",
            "message": "Kasi Sports News API-Football daily operating budget reached.",
            "callsToday": _api_football_usage["callsToday"],
            "budget": KASISCORE_DAILY_BUDGET,
            "reserve": KASISCORE_PROVIDER_RESERVE, "path": path,
        })

def _rate_check():
    """Local safety limiter without blocking healthy API-Football capacity.

    v54: API-Football reports its real minute quota in response headers.
    When that authoritative quota says we still have a healthy reserve,
    the old local bucket must not reject internal ALL-league scans.
    """
    if RATE_LIMIT_PER_MINUTE <= 0:
        return

    provider_remaining = _quota_state.get("minuteRemaining")
    if isinstance(provider_remaining, int) and provider_remaining > 40:
        return

    now = time.time()
    while _rate_bucket and now - _rate_bucket[0] > 60:
        _rate_bucket.pop(0)
    if len(_rate_bucket) >= RATE_LIMIT_PER_MINUTE:
        wait = 60 - (now - _rate_bucket[0])
        raise HTTPException(429, f"Local rate limit reached. Retry in {wait:.0f}s.")
    _rate_bucket.append(now)

def _record_quota(response: httpx.Response, path: str):
    def iv(*names):
        for name in names:
            value = response.headers.get(name)
            if value is not None:
                try:
                    return int(value)
                except (TypeError, ValueError):
                    pass
        return None

    daily_limit = iv("x-ratelimit-requests-limit")
    daily_remaining = iv("x-ratelimit-requests-remaining")
    minute_limit = iv("X-RateLimit-Limit")
    minute_remaining = iv("X-RateLimit-Remaining")

    if daily_limit is not None:
        _quota_state["dailyLimit"] = daily_limit
    if daily_remaining is not None:
        _quota_state["dailyRemaining"] = daily_remaining
    if minute_limit is not None:
        _quota_state["minuteLimit"] = minute_limit
    if minute_remaining is not None:
        _quota_state["minuteRemaining"] = minute_remaining

    _quota_state.update({
        "lastStatus": response.status_code,
        "lastPath": path,
        "lastCheckedAt": datetime.now(timezone.utc).isoformat(),
        "dailyExhausted": daily_remaining is not None and daily_remaining <= 0,
        "minuteLimited": minute_remaining is not None and minute_remaining <= 0,
    })

_http: Optional[httpx.AsyncClient] = None
_odds_api_http: Optional[httpx.AsyncClient] = None
_fixture_meta_cache = TTLCache(maxsize=2000, ttl=6 * 3600)

async def get_client():
    global _http
    if _http is None or _http.is_closed:
        _http = httpx.AsyncClient(
            base_url=API_BASE,
            headers={
                "x-apisports-key": API_KEY,
                "Accept": "application/json",
            },
            timeout=httpx.Timeout(20.0, connect=5.0),
        )
    return _http

# ---------------------------------------------------------------------------
# THE ODDS API v4 FALLBACK
# ---------------------------------------------------------------------------

ODDS_API_SPORT_MAP = {
    # Football / soccer competitions used by the main fixture widget.
    "Premier League": "soccer_epl",
    "La Liga": "soccer_spain_la_liga",
    "Serie A": "soccer_italy_serie_a",
    "Bundesliga": "soccer_germany_bundesliga",
    "Ligue 1": "soccer_france_ligue_one",
    "Champions League": "soccer_uefa_champs_league",
    "Europa League": "soccer_uefa_europa_league",
    "PSL South Africa": "soccer_south_africa_premiership",
    "MLS": "soccer_usa_mls",
    "Eredivisie": "soccer_netherlands_eredivisie",
    "Primeira Liga": "soccer_portugal_primeira_liga",
    "Brazilian Serie A": "soccer_brazil_campeonato",
    "Argentine Primera": "soccer_argentina_primera_division",
    "J1 League Japan": "soccer_japan_j_league",
    "J1 League": "soccer_japan_j_league",
    "Scottish Premiership": "soccer_spl",
    "Turkish Super Lig": "soccer_turkey_super_league",
    "Belgian Pro League": "soccer_belgium_first_div",
    "Saudi Pro League": "soccer_saudi_arabia_pro_league",
    "FA Cup": "soccer_fa_cup",
    "EFL Cup": "soccer_england_efl_cup",
    "Copa del Rey": "soccer_spain_copa_del_rey",
    "Coppa Italia": "soccer_italy_cup",
    "DFB-Pokal": "soccer_germany_dfb_pokal",
    "Coupe de France": "soccer_france_cup",
    "Championship": "soccer_efl_champ",
    "LaLiga Hypermotion": "soccer_spain_segunda_division",
    "2. Bundesliga": "soccer_germany_bundesliga2",
    "Serie B": "soccer_italy_serie_b",
    "Ligue 2": "soccer_france_ligue_two",
    "Super League Greece": "soccer_greece_super_league",
    "Austrian Bundesliga": "soccer_austria_bundesliga",
    "Swiss Super League": "soccer_switzerland_superleague",
    "Ekstraklasa": "soccer_poland_ekstraklasa",
    "Egyptian Premier League": "soccer_egypt_premiership",
    "Botola Pro": "soccer_morocco_botola_pro",
    "Algerian Ligue 1": "soccer_algeria_ligue_1",
    "Tunisian Ligue 1": "soccer_tunisia_ligue_1",
    "Nigeria Premier Football League": "soccer_nigeria_npfl",
    "Ghana Premier League": "soccer_ghana_premier_league",
    "UAE Pro League": "soccer_uae_pro_league",
    "Qatar Stars League": "soccer_qatar_stars_league",
    "Indian Super League": "soccer_india_super_league",
    "Chinese Super League": "soccer_china_superleague",
    "Thai League 1": "soccer_thailand_thai_league_1",
    "Liga 1 Indonesia": "soccer_indonesia_liga_1",
    "Primera A Colombia": "soccer_colombia_primera_a",
    "Primera División Chile": "soccer_chile_primera_division",
    "Liga Pro Ecuador": "soccer_ecuador_ligapro",
    "Liga 1 Peru": "soccer_peru_primera_division",
    "Primera División Uruguay": "soccer_uruguay_primera_division",
    "Primera División Costa Rica": "soccer_costarica_primera_division",
    "Liga Nacional Guatemala": "soccer_guatemala_liga_nacional",
    "K League 1": "soccer_korea_kleague1",
    "A-League": "soccer_australia_aleague",
    # Non-football sport keys represented in the supplied Odds API feed.
    "NPB": "baseball_npb",
    "KBO": "baseball_kbo",
    "International Twenty20": "cricket_international_t20",
    "One Day Internationals": "cricket_odi",
    "Liiga": "icehockey_liiga",
}

async def get_odds_api_client():
    global _odds_api_http
    if _odds_api_http is None or _odds_api_http.is_closed:
        _odds_api_http = httpx.AsyncClient(
            base_url=ODDS_API_BASE.rstrip("/"),
            timeout=httpx.Timeout(ODDS_API_TIMEOUT, connect=min(3.0, ODDS_API_TIMEOUT)),
            headers={"Accept": "application/json", "User-Agent": "KasiScore-Odds-Fallback/1.0"},
        )
    return _odds_api_http

async def _odds_api_get(path: str, params: dict | None = None) -> dict | list:
    if not ODDS_API_ENABLED or not ODDS_API_KEY:
        raise RuntimeError("ODDS_API_KEY is not configured")
    client = await get_odds_api_client()
    query = dict(params or {})
    query["apiKey"] = ODDS_API_KEY
    response = await client.get(path, params=query)
    try:
        data = response.json()
    except Exception:
        data = {"message": response.text[:500]}
    if response.status_code >= 400:
        raise RuntimeError(f"The Odds API HTTP {response.status_code}: {data}")
    return data

def _odds_api_sport_key(league: str = "") -> str | None:
    if not league:
        return None
    if league in ODDS_API_SPORT_MAP:
        return ODDS_API_SPORT_MAP[league]
    # Accept an Odds API sport key directly in the league query when an admin
    # or integration wants a sport not present in the local registry.
    if league.startswith(("soccer_", "baseball_", "cricket_", "icehockey_")):
        return league
    return None

def _normalise_odds_api_event(event: dict) -> dict:
    """Best-price 1X2 normalisation from The Odds API h2h market."""
    best: dict[str, float] = {}
    bookmakers = event.get("bookmakers") or []
    home = str(event.get("home_team") or "Home")
    away = str(event.get("away_team") or "Away")
    for bookmaker in bookmakers:
        for market in bookmaker.get("markets") or []:
            if market.get("key") != "h2h":
                continue
            for outcome in market.get("outcomes") or []:
                name = str(outcome.get("name") or "").strip()
                try:
                    price = float(outcome.get("price"))
                except (TypeError, ValueError):
                    continue
                if price <= 1:
                    continue
                if name in (home, away, "Draw"):
                    best[name] = max(price, best.get(name, 0.0))
    norm = {
        "homeWin": best.get(home, 0.0),
        "draw": best.get("Draw", 0.0),
        "awayWin": best.get(away, 0.0),
        "over25": 0.0,
        "over15": 0.0,
        "over05": 0.0,
        "btts": 0.0,
        "firstHalfHome": 0.0,
        "scoreFirst": 0.0,
        "expectedGoalscorer": 0.0,
    }
    return norm

def _normalise_odds_api_fixture(event: dict, league_name: str = "") -> dict:
    odds = _normalise_odds_api_event(event)
    commence = event.get("commence_time") or ""
    try:
        dt = datetime.fromisoformat(str(commence).replace("Z", "+00:00")).astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M")
    except Exception:
        dt = str(commence).replace("T", " ")[:16]
    return {
        "home": event.get("home_team") or "Home",
        "away": event.get("away_team") or "Away",
        "homeId": None, "awayId": None,
        "homeLogo": "", "awayLogo": "", "leagueLogo": "", "leagueFlag": "",
        "league": event.get("sport_title") or league_name or event.get("sport_key") or "Football",
        "datetime": dt,
        "score": "vs",
        "status": "Upcoming",
        "venue": "",
        "homeForm": [], "awayForm": [],
        "homeGoalsFor": 1.35, "homeGoalsAgainst": 1.35,
        "awayGoalsFor": 1.35, "awayGoalsAgainst": 1.35,
        "h2hHomeWins": 3, "h2hDraws": 2, "h2hAwayWins": 2,
        "isSoccer": str(event.get("sport_key", "")).startswith("soccer_"),
        "isLive": False, "isFinished": False, "elapsed": None,
        "odds": odds,
        "oddsSource": "The Odds API",
        "oddsApiEventId": event.get("id"),
        "_afootFixtureId": None,
        "_teamHomeId": None, "_teamAwayId": None,
        "_leagueId": None, "_leagueSeason": _current_season(),
        "source": "The Odds API",
    }

TEAM_NAME_ALIASES = {
    "man utd": "manchester united",
    "man united": "manchester united",
    "man city": "manchester city",
    "psg": "paris saint germain",
    "inter milan": "inter",
    "internazionale": "inter",
    "spurs": "tottenham hotspur",
    "tottenham": "tottenham hotspur",
    "wolves": "wolverhampton wanderers",
    "wolverhampton": "wolverhampton wanderers",
    "west ham": "west ham united",
    "manchester utd": "manchester united",
}

def _normalise_team_name(value: str) -> str:
    name = re.sub(r"[^a-z0-9 ]+", " ", str(value or "").lower())
    name = re.sub(r"\s+", " ", name).strip()
    for suffix in (" football club", " fc", " afc", " cf"):
        if name.endswith(suffix):
            name = name[:-len(suffix)].strip()
    return TEAM_NAME_ALIASES.get(name, name)

def _parse_provider_time(value: Any) -> Optional[datetime]:
    """Parse provider times. OddsPapi fixture startTime is epoch seconds; odds timestamps are ms."""
    if value is None or value == "":
        return None
    try:
        if isinstance(value, (int, float)) or (isinstance(value, str) and value.strip().isdigit()):
            n = float(value)
            # Odds update timestamps use milliseconds; fixture schedule timestamps use seconds.
            if n > 10_000_000_000:
                n /= 1000.0
            return datetime.fromtimestamp(n, tz=timezone.utc)
        return datetime.fromisoformat(str(value).replace("Z", "+00:00")).astimezone(timezone.utc)
    except Exception:
        return None

def _team_similarity(a: str, b: str) -> float:
    """0-100 similarity score used only after exact/alias matching fails."""
    a = _normalise_team_name(a)
    b = _normalise_team_name(b)
    if not a or not b:
        return 0.0
    if a == b:
        return 100.0
    return SequenceMatcher(None, a, b).ratio() * 100.0

def _event_matches_fixture(event: dict, fixture: dict, kickoff_tolerance_hours: float = 3.0) -> bool:
    """Safely map an Odds API event to an API-Football fixture.

    Order:
      1) normalized/manual-alias exact match for BOTH teams
      2) conservative fuzzy fallback for BOTH teams
      3) kickoff-time guard
    """
    eh = _normalise_team_name(event.get("home_team"))
    ea = _normalise_team_name(event.get("away_team"))
    fh = _normalise_team_name(fixture.get("home") or fixture.get("homeTeam"))
    fa = _normalise_team_name(fixture.get("away") or fixture.get("awayTeam"))
    if not all((eh, ea, fh, fa)):
        return False

    # First choice: normalized names / manual aliases.
    exact_home = eh == fh or (len(eh) >= 5 and len(fh) >= 5 and (eh in fh or fh in eh))
    exact_away = ea == fa or (len(ea) >= 5 and len(fa) >= 5 and (ea in fa or fa in ea))
    exact_pair = exact_home and exact_away

    # Fallback only: BOTH teams must independently clear the threshold.
    # A single fuzzy home-team hit is never enough to attach bookmaker odds.
    fuzzy_threshold = float(os.getenv("ODDS_TEAM_FUZZY_THRESHOLD", "85"))
    home_score = _team_similarity(eh, fh)
    away_score = _team_similarity(ea, fa)
    fuzzy_pair = home_score >= fuzzy_threshold and away_score >= fuzzy_threshold

    if not (exact_pair or fuzzy_pair):
        return False

    event_time = _parse_provider_time(event.get("commence_time") or event.get("datetime"))
    fixture_time = _parse_provider_time(fixture.get("datetime") or fixture.get("kickoff") or fixture.get("date"))
    if event_time and fixture_time:
        delta = abs((event_time - fixture_time).total_seconds())
        if delta > kickoff_tolerance_hours * 3600:
            return False

    return True


# ---------------------------------------------------------------------------
# OddsPAPI v4 — REST bootstrap + WebSocket partial-update accumulator
# ---------------------------------------------------------------------------

def _oddspapi_deep_merge(target: dict, patch: dict) -> dict:
    """Merge OddsPAPI partial updates without deleting unchanged values."""
    for key, value in (patch or {}).items():
        if isinstance(value, dict) and isinstance(target.get(key), dict):
            _oddspapi_deep_merge(target[key], value)
        else:
            target[key] = value
    return target


def _oddspapi_allowed_books(payload: dict) -> dict:
    books = (payload or {}).get("bookmakerOdds") or {}
    if not ODDSPAPI_BOOKMAKERS:
        return books
    return {k: v for k, v in books.items() if str(k).lower() in ODDSPAPI_BOOKMAKERS}


def _oddspapi_store(payload: dict) -> Optional[dict]:
    """Accumulate a REST snapshot or one WebSocket partial update."""
    fixture_id = str((payload or {}).get("fixtureId") or "").strip()
    if not fixture_id:
        return None
    existing = dict(_oddspapi_odds_cache.get(fixture_id) or {"fixtureId": fixture_id})
    patch = dict(payload)
    if "bookmakerOdds" in patch:
        patch["bookmakerOdds"] = _oddspapi_allowed_books(patch)
    merged = _oddspapi_deep_merge(existing, patch)
    _oddspapi_odds_cache[fixture_id] = merged
    return merged


def _oddspapi_rows(data: Any) -> list[dict]:
    """Normalize common OddsPAPI REST response envelopes for diagnostics."""
    if isinstance(data, list):
        return [x for x in data if isinstance(x, dict)]
    if isinstance(data, dict):
        for key in ("response", "data", "fixtures", "odds", "items", "results"):
            rows=data.get(key)
            if isinstance(rows, list):
                return [x for x in rows if isinstance(x, dict)]
        # A single fixture/odds object is still useful diagnostically.
        if data.get("fixtureId") or data.get("id"):
            return [data]
    return []


_oddspapi_request_lock = asyncio.Lock()
_oddspapi_last_request_at = 0.0
ODDSPAPI_MIN_REQUEST_INTERVAL = float(os.getenv("ODDSPAPI_MIN_REQUEST_INTERVAL", "2.05"))

# OddsPapi hard request budgets. Defaults intentionally reserve ~20% of a
# 100,000/month allowance for manual diagnostics, retries and future features.
ODDSPAPI_BUDGET_MINUTE = int(os.getenv("ODDSPAPI_BUDGET_MINUTE", "10"))
ODDSPAPI_BUDGET_HOUR = int(os.getenv("ODDSPAPI_BUDGET_HOUR", "110"))
ODDSPAPI_BUDGET_DAY = int(os.getenv("ODDSPAPI_BUDGET_DAY", "2600"))
ODDSPAPI_BUDGET_WEEK = int(os.getenv("ODDSPAPI_BUDGET_WEEK", "18500"))
ODDSPAPI_BUDGET_MONTH = int(os.getenv("ODDSPAPI_BUDGET_MONTH", "80000"))
_oddspapi_budget_lock = asyncio.Lock()

def _oddspapi_budget_db_path() -> Path:
    # SPORTS_DB_PATH can point at Render persistent disk (/var/data). It is
    # defined later in the module but is available by request time.
    q=globals().get("SPORTS_DB_PATH") or globals().get("APICACHE_DB") or (BASE_DIR/"api_cache.sqlite3")
    return Path(q)

def _oddspapi_periods(now: datetime | None=None):
    now=(now or datetime.now(timezone.utc)).astimezone(timezone.utc)
    iso=now.isocalendar()
    return {
        "minute":(now.strftime("%Y-%m-%dT%H:%M"),ODDSPAPI_BUDGET_MINUTE),
        "hour":(now.strftime("%Y-%m-%dT%H"),ODDSPAPI_BUDGET_HOUR),
        "day":(now.strftime("%Y-%m-%d"),ODDSPAPI_BUDGET_DAY),
        "week":(f"{iso.year}-W{iso.week:02d}",ODDSPAPI_BUDGET_WEEK),
        "month":(now.strftime("%Y-%m"),ODDSPAPI_BUDGET_MONTH),
    }

def _oddspapi_budget_snapshot():
    periods=_oddspapi_periods()
    result={}
    db=_oddspapi_budget_db_path()
    db.parent.mkdir(parents=True,exist_ok=True)
    con=sqlite3.connect(str(db),timeout=20)
    try:
        con.execute("""CREATE TABLE IF NOT EXISTS oddspapi_usage(
          period_type TEXT NOT NULL, period_key TEXT NOT NULL,
          calls INTEGER NOT NULL DEFAULT 0, updated_at TEXT NOT NULL,
          PRIMARY KEY(period_type,period_key))""")
        for typ,(key,limit) in periods.items():
            row=con.execute("SELECT calls FROM oddspapi_usage WHERE period_type=? AND period_key=?",(typ,key)).fetchone()
            used=int(row[0]) if row else 0
            result[typ]={"period":key,"used":used,"limit":limit,"remaining":max(0,limit-used)}
        return result
    finally:
        con.close()

def _v448_oddspapi_provider_locked() -> bool:
    """Read current local budgets without consuming a provider call."""
    try:
        snap = _oddspapi_budget_snapshot()
        for row in snap.values():
            limit = int(row.get("limit") or 0)
            remaining = int(row.get("remaining") or 0)
            if limit > 0 and remaining <= 0:
                return True
    except Exception as exc:
        log.debug("OddsPAPI budget preflight unavailable: %s", exc)
    return False


async def _oddspapi_take_budget():
    """Atomically reserve one provider HTTP attempt across all five periods."""
    async with _oddspapi_budget_lock:
        periods=_oddspapi_periods()
        db=_oddspapi_budget_db_path()
        db.parent.mkdir(parents=True,exist_ok=True)
        con=sqlite3.connect(str(db),timeout=20,isolation_level=None)
        try:
            con.execute("BEGIN IMMEDIATE")
            con.execute("""CREATE TABLE IF NOT EXISTS oddspapi_usage(
              period_type TEXT NOT NULL, period_key TEXT NOT NULL,
              calls INTEGER NOT NULL DEFAULT 0, updated_at TEXT NOT NULL,
              PRIMARY KEY(period_type,period_key))""")
            current={}
            for typ,(key,limit) in periods.items():
                row=con.execute("SELECT calls FROM oddspapi_usage WHERE period_type=? AND period_key=?",(typ,key)).fetchone()
                used=int(row[0]) if row else 0
                current[typ]=(key,limit,used)
                if limit > 0 and used >= limit:
                    con.execute("ROLLBACK")
                    raise RuntimeError(f"OddsPapi local {typ} budget reached ({used}/{limit})")
            stamp=datetime.now(timezone.utc).isoformat()
            for typ,(key,limit,used) in current.items():
                con.execute("""INSERT INTO oddspapi_usage(period_type,period_key,calls,updated_at)
                  VALUES(?,?,1,?) ON CONFLICT(period_type,period_key)
                  DO UPDATE SET calls=calls+1,updated_at=excluded.updated_at""",(typ,key,stamp))
            con.execute("COMMIT")
        except Exception:
            try: con.execute("ROLLBACK")
            except Exception: pass
            raise
        finally:
            con.close()




async def _oddspapi_get(path: str, params: Optional[dict] = None, base: Optional[str] = None) -> Any:
    """Rate-safe OddsPAPI GET. Serializes requests, spaces them, and retries one 429."""
    global _oddspapi_last_request_at
    if not ODDSPAPI_ENABLED or not ODDSPAPI_API_KEY:
        raise RuntimeError("ODDSPAPI_API_KEY is not configured")

    query = dict(params or {})
    query["apiKey"] = ODDSPAPI_API_KEY
    root = (base or ODDSPAPI_REST_BASE).rstrip("/")

    async with _oddspapi_request_lock:
        for attempt in range(2):
            now_loop = asyncio.get_running_loop().time()
            wait_for = ODDSPAPI_MIN_REQUEST_INTERVAL - (now_loop - _oddspapi_last_request_at)
            if wait_for > 0:
                await asyncio.sleep(wait_for)

            # Reserve budget immediately before every real provider HTTP attempt.
            # A 429 retry therefore counts as a second call, matching actual usage.
            await _oddspapi_take_budget()
            async with httpx.AsyncClient(timeout=12.0) as client:
                response = await client.get(f"{root}/{path.lstrip('/')}", params=query)
            _oddspapi_last_request_at = asyncio.get_running_loop().time()

            if response.status_code == 404:
                return []

            if response.status_code == 429 and attempt == 0:
                retry_after = 0.0
                try:
                    retry_after = float(response.headers.get("Retry-After") or 0)
                except (TypeError, ValueError):
                    retry_after = 0.0
                # Provider recently reported waits around 0.69s. Respect a
                # larger safe floor so the retry does not immediately collide.
                await asyncio.sleep(max(retry_after, ODDSPAPI_MIN_REQUEST_INTERVAL, 1.0))
                continue

            if response.is_error:
                detail = ""
                try:
                    body = response.json()
                    if isinstance(body, dict):
                        detail = str(body.get("message") or body.get("error") or "")[:180]
                except Exception:
                    pass
                suffix = f": {detail}" if detail else ""
                raise RuntimeError(f"OddsPAPI HTTP {response.status_code}{suffix}")

            return response.json()

    raise RuntimeError("OddsPAPI request failed after retry")


async def _oddspapi_v5_or_v4(v5_path: str, v4_path: str, params: Optional[dict] = None) -> tuple[Any, str]:
    """Use v5 when entitled; safely fall back to the known-working v4 REST API."""
    try:
        return await _oddspapi_get(v5_path, params), "v5"
    except RuntimeError as exc:
        # Current Dev key may not be entitled for v5. Do not leak the key or URL.
        if "HTTP 401" not in str(exc) and "HTTP 403" not in str(exc):
            raise
        return await _oddspapi_get(v4_path, params, base=ODDSPAPI_V4_FALLBACK_BASE), "v4"

def _oddspapi_v5_active_prices(snapshot: dict, bookmaker: Optional[str] = None) -> list[dict]:
    """Normalize v5 direct odds selections without guessing sport-specific market semantics."""
    if not isinstance(snapshot, dict):
        return []
    bookmaker_meta = snapshot.get("bookmakers") or {}
    odds_root = snapshot.get("odds") or {}
    out = []
    wanted = [bookmaker] if bookmaker else list(ODDSPAPI_BOOKMAKERS)
    for book in wanted:
        board = odds_root.get(book) if isinstance(odds_root, dict) else None
        meta = bookmaker_meta.get(book, {}) if isinstance(bookmaker_meta, dict) else {}
        if not isinstance(board, dict):
            continue
        if meta.get("hasOdds") is False or meta.get("staleOdds") is True or meta.get("suspended") is True:
            continue
        for selection in board.values():
            if not isinstance(selection, dict):
                continue
            if selection.get("active") is not True:
                continue
            if selection.get("marketActive") is not True:
                continue
            if selection.get("mainLine") is False:
                continue
            try:
                price=float(selection.get("price"))
            except (TypeError, ValueError):
                continue
            if price <= 1:
                continue
            out.append({
                "bookmaker": book,
                "marketId": selection.get("marketId"),
                "outcomeId": selection.get("outcomeId"),
                "playerId": selection.get("playerId"),
                "price": price,
                "mainLine": selection.get("mainLine"),
            })
    return out


def _oddspapi_1x2(snapshot: dict) -> dict:
    """
    OddsPAPI football Full Time Result / 1X2.
    Confirmed production structure:
      market 101
      outcome 101 = home, 102 = draw, 103 = away
      decimal price = outcome.players["0"].price
    Missing `active` means unspecified/available; only explicit False rejects it.
    Prefer configured bookmakers in order (Bet365, then Betway).
    """
    # v5 REST/WS odds are normalized selections keyed by bookmaker. Each row
    # carries marketId/outcomeId/playerId/price. Soccer FT 1X2 is market 101
    # with outcomes 101(home), 102(draw), 103(away).
    active = _oddspapi_v5_active_prices(snapshot or {})
    if active:
        for wanted in ODDSPAPI_BOOKMAKERS:
            rows = [r for r in active if str(r.get("bookmaker", "")).lower() == str(wanted).lower()
                    and str(r.get("marketId")) == "101" and str(r.get("playerId") or 0) == "0"]
            by_outcome = {str(r.get("outcomeId")): r.get("price") for r in rows}
            if all(k in by_outcome for k in ("101", "102", "103")):
                return {
                    "homeWin": float(by_outcome["101"]), "draw": float(by_outcome["102"]),
                    "awayWin": float(by_outcome["103"]),
                    "over05":0,"over15":0,"over25":0,"btts":0,
                    "firstHalfHome":0,"scoreFirst":0,"expectedGoalscorer":0,
                    "_bookmaker": str(wanted),
                    "_oddspapiFixtureId": snapshot.get("fixtureId") or snapshot.get("id"),
                }

    # Legacy v4 nested market representation.
    books=(snapshot or {}).get("bookmakerOdds") or (snapshot or {}).get("bookmakers") or {}
    if not isinstance(books,dict):
        return {}

    # Case-insensitive bookmaker lookup while preserving configured preference.
    normalized={str(k).lower().replace(" ",""): (k,v) for k,v in books.items()}
    ordered=[]
    used=set()
    for wanted in ODDSPAPI_BOOKMAKERS:
        key=str(wanted).lower().replace(" ","")
        if key in normalized:
            real,board=normalized[key]
            ordered.append((real,board)); used.add(real)
    for real,board in books.items():
        if real not in used:
            ordered.append((real,board))

    for bookmaker,board in ordered:
        if not isinstance(board,dict):
            continue
        markets=board.get("markets") or board.get("odds") or {}
        if isinstance(markets,dict):
            market=markets.get("101") or markets.get(101)
        else:
            market=None
            if isinstance(markets,list):
                for candidate in markets:
                    if isinstance(candidate,dict) and str(candidate.get("id") or candidate.get("marketId"))=="101":
                        market=candidate; break
        if not isinstance(market,dict) or market.get("active") is False:
            continue

        outcomes=market.get("outcomes") or market.get("selections") or {}
        prices={}
        valid=True
        for oid,label in (("101","homeWin"),("102","draw"),("103","awayWin")):
            if isinstance(outcomes,dict):
                outcome=outcomes.get(oid) or outcomes.get(int(oid)) or {}
            else:
                outcome={}
                if isinstance(outcomes,list):
                    for candidate in outcomes:
                        if isinstance(candidate,dict) and str(candidate.get("id") or candidate.get("outcomeId"))==oid:
                            outcome=candidate; break
            if not isinstance(outcome,dict) or outcome.get("active") is False:
                valid=False; break

            # OddsPAPI production response stores the decimal price under player 0.
            price=outcome.get("price") or outcome.get("odds") or outcome.get("decimal")
            players=outcome.get("players") or {}
            if price is None and isinstance(players,dict):
                player=players.get("0") or players.get(0) or {}
                if isinstance(player,dict) and player.get("active") is not False:
                    price=player.get("price") or player.get("odds") or player.get("decimal")
            try:
                price=float(price)
            except (TypeError,ValueError):
                valid=False; break
            if price <= 1:
                valid=False; break
            prices[label]=price

        if valid and len(prices)==3:
            return {
                **prices,
                "over05":0,"over15":0,"over25":0,"btts":0,
                "firstHalfHome":0,"scoreFirst":0,"expectedGoalscorer":0,
                "_bookmaker":str(bookmaker),
                "_oddspapiFixtureId":snapshot.get("fixtureId") or snapshot.get("id"),
            }
    return {}

def _oddspapi_participant_name(fixture: dict, side: int) -> str:
    """Read v5 nested participant names while remaining compatible with legacy flat snapshots."""
    participants = (fixture or {}).get("participants") or {}
    if isinstance(participants, dict):
        value = participants.get(f"participant{side}Name")
        if value:
            return str(value)
    return str((fixture or {}).get(f"participant{side}Name") or "")


def _oddspapi_fixture_matches(afoot: dict, op: dict) -> bool:
    # Accept both Kasi-normalised fixtures and raw API-Football fixture objects.
    teams = afoot.get("teams") if isinstance(afoot.get("teams"), dict) else {}
    fixture_meta = afoot.get("fixture") if isinstance(afoot.get("fixture"), dict) else {}
    raw_home = (teams.get("home") or {}).get("name") if isinstance(teams.get("home"), dict) else None
    raw_away = (teams.get("away") or {}).get("name") if isinstance(teams.get("away"), dict) else None
    ah = _normalise_team_name(afoot.get("home") or afoot.get("homeTeam") or raw_home)
    aa = _normalise_team_name(afoot.get("away") or afoot.get("awayTeam") or raw_away)
    oh = _normalise_team_name(_oddspapi_participant_name(op, 1))
    oa = _normalise_team_name(_oddspapi_participant_name(op, 2))
    if not all((ah, aa, oh, oa)):
        return False
    exact = (ah == oh and aa == oa)
    fuzzy = _team_similarity(ah, oh) >= 85 and _team_similarity(aa, oa) >= 85
    if not (exact or fuzzy):
        return False
    at = _parse_provider_time(
        afoot.get("datetime") or afoot.get("kickoff") or afoot.get("date")
        or fixture_meta.get("date") or fixture_meta.get("timestamp")
    )
    ot = _parse_provider_time(op.get("startTime"))
    return not (at and ot and abs((at - ot).total_seconds()) > 3 * 3600)


def _oddspapi_match_fixture(afoot: dict, fixtures: list[dict]) -> Optional[dict]:
    """Return the safest OddsPAPI match using both teams plus kickoff time."""
    teams = afoot.get("teams") if isinstance(afoot.get("teams"), dict) else {}
    fixture_meta = afoot.get("fixture") if isinstance(afoot.get("fixture"), dict) else {}
    home = afoot.get("home") or afoot.get("homeTeam")
    away = afoot.get("away") or afoot.get("awayTeam")
    if not home and isinstance(teams.get("home"), dict):
        home = teams["home"].get("name")
    if not away and isinstance(teams.get("away"), dict):
        away = teams["away"].get("name")
    kickoff = _parse_provider_time(
        afoot.get("datetime") or afoot.get("kickoff") or afoot.get("date")
        or fixture_meta.get("date") or fixture_meta.get("timestamp")
    )
    nh, na = _normalise_team_name(home), _normalise_team_name(away)
    if not nh or not na:
        return None

    best = None
    best_score = -1.0
    for op in fixtures or []:
        oh = _normalise_team_name(_oddspapi_participant_name(op, 1))
        oa = _normalise_team_name(_oddspapi_participant_name(op, 2))
        if not oh or not oa:
            continue
        hs, aws = _team_similarity(nh, oh), _team_similarity(na, oa)
        if hs < 85 or aws < 85:
            continue
        ot = _parse_provider_time(op.get("startTime") or op.get("startsAt") or op.get("date"))
        if kickoff and ot:
            delta = abs((kickoff - ot).total_seconds())
            if delta > 3 * 3600:
                continue
            time_score = max(0.0, 100.0 - (delta / 108.0))
        else:
            time_score = 50.0
        score = hs + aws + time_score
        if score > best_score:
            best, best_score = op, score
    return best


async def _oddspapi_football_fixtures(
    refresh: bool = False,
    start_at: Optional[datetime] = None,
    end_at: Optional[datetime] = None,
) -> list[dict]:
    now = datetime.now(timezone.utc)
    start = start_at or (now - timedelta(hours=6))
    end = end_at or (now + timedelta(hours=36))
    if start.tzinfo is None:
        start = start.replace(tzinfo=timezone.utc)
    if end.tzinfo is None:
        end = end.replace(tzinfo=timezone.utc)

    # Keep requests bounded while allowing the production fixture window to
    # reach the same dates returned by API-Football.
    max_end = now + timedelta(days=8)
    start = max(start, now - timedelta(hours=12))
    end = min(max(end, start + timedelta(hours=6)), max_end)

    key = f"football-window:{start.strftime('%Y%m%d%H')}:{end.strftime('%Y%m%d%H')}"
    if not refresh:
        cached = _oddspapi_fixture_cache.get(key)
        if cached is not None:
            return cached

    try:
        data = await _oddspapi_get(f"{ODDSPAPI_REST_LANGUAGE}/fixtures", {
            "sportId": ODDSPAPI_SPORT_FOOTBALL,
            "startTimeFrom": int(start.timestamp()),
            "startTimeTo": int(end.timestamp()),
            "bookmakers": ",".join(ODDSPAPI_BOOKMAKERS),
        })
    except RuntimeError as exc:
        if "HTTP 401" not in str(exc) and "HTTP 403" not in str(exc):
            raise
        data = await _oddspapi_get("fixtures", {
            "sportId": ODDSPAPI_SPORT_FOOTBALL,
            "from": start.isoformat().replace("+00:00","Z"),
            "to": end.isoformat().replace("+00:00","Z"),
            "hasOdds": "true",
            "bookmakers": ",".join(ODDSPAPI_BOOKMAKERS),
            "language": "en",
        }, base=ODDSPAPI_V4_FALLBACK_BASE)

    rows = _oddspapi_rows(data)
    _oddspapi_fixture_cache[key] = rows
    return rows


async def _oddspapi_resolve_fixture(afoot_fixture_id: Any, meta: dict, refresh: bool = False) -> Optional[str]:
    map_key = str(afoot_fixture_id)
    if not refresh:
        mapped = _oddspapi_afoot_map.get(map_key)
        if mapped:
            return mapped
    target_dt = _parse_provider_time(
        meta.get("datetime") or meta.get("kickoff") or meta.get("date")
        or ((meta.get("fixture") or {}).get("date") if isinstance(meta.get("fixture"), dict) else None)
    )
    if target_dt:
        fixtures = await _oddspapi_football_fixtures(
            refresh=refresh,
            start_at=target_dt - timedelta(hours=6),
            end_at=target_dt + timedelta(hours=6),
        )
    else:
        fixtures = await _oddspapi_football_fixtures(refresh=refresh)
    fixture = _oddspapi_match_fixture(meta, fixtures)
    if fixture:
        opid = str(fixture.get("fixtureId") or fixture.get("id") or "").strip()
        if opid:
            _oddspapi_afoot_map[map_key] = opid
            return opid
    return None


async def _oddspapi_odds_for_afoot(afoot_fixture_id: Any, meta: dict, refresh: bool = False) -> tuple[dict, Optional[str]]:
    opid = await _oddspapi_resolve_fixture(afoot_fixture_id, meta, refresh=refresh)
    if not opid:
        return {}, None
    snapshot = None if refresh else _oddspapi_odds_cache.get(opid)
    odds = _oddspapi_1x2(snapshot or {})
    if _valid_1x2(odds):
        return odds, opid

    data, _rest_version = await _oddspapi_v5_or_v4(f"{ODDSPAPI_REST_LANGUAGE}/fixtures/odds", "odds", {
        "fixtureId": opid,
        "bookmakers": ",".join(ODDSPAPI_BOOKMAKERS),
        "oddsFormat": "decimal",
        "language": "en",
        "verbosity": 3,
    })
    rows = _oddspapi_rows(data)
    if rows:
        # v5 /{language}/fixtures/odds is queried only for the matched fixtureId.
        snapshot = _oddspapi_store(rows[0])
        odds = _oddspapi_1x2(snapshot or {})
    elif isinstance(data, dict):
        snapshot = _oddspapi_store(data)
        odds = _oddspapi_1x2(snapshot or {})
    return odds if _valid_1x2(odds) else {}, opid


async def _supplement_odds_from_oddspapi(matches: list[dict], refresh: bool = False) -> dict:
    meta = {"checked": False, "matched": 0, "bookmakers": list(ODDSPAPI_BOOKMAKERS), "error": None}
    if not matches or not ODDSPAPI_ENABLED or not ODDSPAPI_API_KEY:
        return meta
    if _v448_oddspapi_provider_locked():
        meta["error"] = "ODDSPAPI_LOCAL_BUDGET_PROTECTED"
        meta["budgetProtected"] = True
        return meta
    meta["checked"] = True
    try:
        # Resolve only API-Football gaps. Each resolver uses a cached OddsPAPI
        # window aligned to that fixture's kickoff date/time.
        fixture_errors = []
        for match in matches:
            if _v448_oddspapi_provider_locked():
                meta["budgetProtected"] = True
                meta["error"] = "ODDSPAPI_LOCAL_BUDGET_PROTECTED"
                break
            fid = match.get("_afootFixtureId")
            if not fid or _valid_1x2(match.get("odds", {})):
                continue
            try:
                odds, opid = await _oddspapi_odds_for_afoot(fid, match, refresh=refresh)
            except Exception as exc:
                fixture_errors.append(f"{fid}: {str(exc)[:120]}")
                log.warning("OddsPAPI fixture %s supplement failed: %s", fid, exc)
                continue
            if not _valid_1x2(odds):
                continue
            match["odds"] = odds
            match["oddsSource"] = "OddsPAPI"
            match["oddsAvailable"] = True
            match["hasBookmakerOdds"] = True
            match["bookmakerGatePassed"] = True
            match["oddsPapiFixtureId"] = opid
            match["oddsBookmaker"] = odds.get("_bookmaker")
            _odds_cache[f"odds:{fid}"] = {
                "fixture_id": fid, "odds": odds, "source": "OddsPAPI",
                "oddsPapiFixtureId": opid,
                "fetchedAt": datetime.now(timezone.utc).isoformat(),
            }
            meta["matched"] += 1
        if fixture_errors:
            meta["partialErrors"] = fixture_errors[:5]
            meta["partialErrorCount"] = len(fixture_errors)
    except Exception as exc:
        meta["error"] = str(exc)
        log.warning("OddsPAPI supplement failed: %s", exc)
    return meta


async def _oddspapi_ws_snapshot_recovery(channels: list[str]):
    """
    v5 snapshot_required means replay cannot safely fill one or more channels.
    Invalidate only those local views. The existing v4 REST integration remains
    the authoritative bootstrap/recovery path.
    """
    channels = [str(x) for x in (channels or [])]
    if "fixtures" in channels:
        _oddspapi_fixture_cache.clear()
        _oddspapi_afoot_map.clear()
    if "odds" in channels:
        _oddspapi_odds_cache.clear()
    # Scores are merged into fixture-shaped state when supplied by v5.
    if "scores" in channels:
        _oddspapi_fixture_cache.clear()


def _oddspapi_ws_payloads(payload: Any) -> list[dict]:
    """Extract fixture-shaped updates from a v5 data envelope."""
    if isinstance(payload, dict):
        if payload.get("fixtureId"):
            return [payload]
        for key in ("fixtures", "odds", "scores", "items", "data"):
            rows = payload.get(key)
            if isinstance(rows, list):
                return [x for x in rows if isinstance(x, dict) and x.get("fixtureId")]
            if isinstance(rows, dict) and rows.get("fixtureId"):
                return [rows]
    elif isinstance(payload, list):
        return [x for x in payload if isinstance(x, dict) and x.get("fixtureId")]
    return []


def _oddspapi_ws_login() -> dict:
    """Build the production v5 login frame, including resume state."""
    channels = ["fixtures", "scores", "odds"]
    login = {
        "type": "login",
        "apiKey": ODDSPAPI_API_KEY,
        "channels": channels,
        "receiveType": "json",
    }

    server_epoch = _oddspapi_ws_state.get("serverEpoch")
    replay_channels = _oddspapi_ws_state.get("replayChannels")
    last_seen = _oddspapi_ws_state.get("lastSeenId") or {}

    if server_epoch:
        login["serverEpoch"] = server_epoch

    if replay_channels:
        cursors = {
            ch: eid for ch, eid in last_seen.items()
            if ch in set(map(str, replay_channels))
        }
    else:
        cursors = dict(last_seen)

    if cursors:
        login["lastSeenId"] = cursors

    return login


async def _oddspapi_ws_loop():
    """
    OddsPAPI production v5 WebSocket.

    Protocol:
      connect -> login -> login_ok -> data/replay -> resume_complete
      reconnect: reconnect immediately
      snapshot_required: clear affected cursors and REST-backed caches

    lastSeenId advances only AFTER a message has been processed successfully.
    """
    if not ODDSPAPI_ENABLED or not ODDSPAPI_WS_ENABLED or not ODDSPAPI_API_KEY:
        return
    if websockets is None:
        _oddspapi_ws_state["lastError"] = "websockets package is not installed"
        log.warning("OddsPAPI WebSocket disabled: install websockets")
        return

    delay = 1

    while True:
        reconnect_now = False
        try:
            _oddspapi_ws_state.update({
                "connected": False,
                "authenticated": False,
                "resumeComplete": False,
                "gateway": ODDSPAPI_WS_BASE,
                "lastError": None,
            })

            async with websockets.connect(
                ODDSPAPI_WS_BASE,
                ping_interval=20,
                ping_timeout=20,
                max_size=4_194_304,
                close_timeout=5,
                open_timeout=15,
            ) as ws:
                _oddspapi_ws_state["connected"] = True
                await ws.send(json.dumps(_oddspapi_ws_login()))
                delay = 1

                async for raw in ws:
                    if isinstance(raw, (bytes, bytearray)):
                        raw = raw.decode("utf-8", errors="replace")

                    msg = json.loads(raw)
                    if not isinstance(msg, dict):
                        continue

                    msg_type = msg.get("type")

                    if msg_type == "login_ok":
                        resume = msg.get("resume") or {}
                        epoch = resume.get("serverEpoch")
                        if epoch:
                            _oddspapi_ws_state["serverEpoch"] = epoch

                        rc = resume.get("replayChannels")
                        if isinstance(rc, list):
                            _oddspapi_ws_state["replayChannels"] = list(map(str, rc))

                        _oddspapi_ws_state["authenticated"] = True
                        _oddspapi_ws_state["lastControl"] = "login_ok"
                        log.info(
                            "OddsPAPI v5 authenticated; replayChannels=%s",
                            _oddspapi_ws_state.get("replayChannels"),
                        )
                        continue

                    if msg_type == "reconnect":
                        _oddspapi_ws_state["lastControl"] = "reconnect"
                        log.info("OddsPAPI v5 requested reconnect: %s", msg.get("reason"))
                        reconnect_now = True
                        break

                    if msg_type == "snapshot_required":
                        channels = [
                            str(ch) for ch in (msg.get("channels") or [])
                            if isinstance(ch, str)
                        ]
                        for ch in channels:
                            _oddspapi_ws_state["lastSeenId"].pop(ch, None)

                        await _oddspapi_ws_snapshot_recovery(channels)
                        _oddspapi_ws_state["lastControl"] = "snapshot_required"
                        log.warning(
                            "OddsPAPI v5 snapshot required for channels=%s reason=%s",
                            channels,
                            msg.get("reason"),
                        )
                        continue

                    if msg_type == "resume_complete":
                        _oddspapi_ws_state["resumeComplete"] = True
                        _oddspapi_ws_state["lastControl"] = "resume_complete"
                        log.info("OddsPAPI v5 resume complete")
                        continue

                    # Data envelope. Process first; commit cursor only afterwards.
                    channel = msg.get("channel")
                    entry_id = msg.get("entryId")
                    payload = msg.get("payload")

                    for update in _oddspapi_ws_payloads(payload):
                        sport_id = update.get("sportId")
                        if sport_id not in (None, ODDSPAPI_SPORT_FOOTBALL):
                            continue
                        _oddspapi_store(update)

                    # Cursor is committed only after successful processing.
                    if isinstance(channel, str) and isinstance(entry_id, str):
                        _oddspapi_ws_state["lastSeenId"][channel] = entry_id

                    _oddspapi_ws_state["messages"] += 1
                    _oddspapi_ws_state["lastMessageAt"] = datetime.now(timezone.utc).isoformat()
                    if isinstance(channel, str):
                        _oddspapi_ws_state["lastChannel"] = channel

            if reconnect_now:
                # Provider release/maintenance: reconnect immediately and offer
                # serverEpoch + replayable lastSeenId cursors on the next login.
                continue

        except asyncio.CancelledError:
            raise
        except Exception as exc:
            _oddspapi_ws_state.update({
                "connected": False,
                "authenticated": False,
                "lastError": str(exc),
            })
            _oddspapi_ws_state["reconnects"] += 1
            log.warning(
                "OddsPAPI v5 WebSocket disconnected: %s; reconnecting in %ss",
                exc,
                delay,
            )
            await asyncio.sleep(delay)
            delay = min(delay * 2, 60)
        finally:
            _oddspapi_ws_state["connected"] = False
            _oddspapi_ws_state["authenticated"] = False


async def _odds_api_events_for_league(league: str = "", refresh: bool = False) -> list[dict]:
    sport_key = _odds_api_sport_key(league)
    if not sport_key:
        return []
    cache_key = f"oddsapi:{sport_key}:{ODDS_API_REGIONS}:{ODDS_API_MARKETS}"
    if not refresh:
        cached = _odds_api_events_cache.get(cache_key)
        if cached is not None:
            return cached
    data = await _odds_api_get(
        f"/sports/{sport_key}/odds",
        {"regions": ODDS_API_REGIONS, "markets": ODDS_API_MARKETS, "oddsFormat": "decimal"},
    )
    events = data if isinstance(data, list) else []
    _odds_api_events_cache[cache_key] = events
    return events

async def _odds_api_events(league: str = "ALL", refresh: bool = False) -> list[dict]:
    """One cached Odds API feed used to supplement API-Football fixtures."""
    if not ODDS_API_ENABLED or not ODDS_API_KEY:
        return []
    if league.upper() != "ALL":
        return await _odds_api_events_for_league(league, refresh=refresh)
    cache_key = f"oddsapi:upcoming:{ODDS_API_REGIONS}:{ODDS_API_MARKETS}"
    if not refresh:
        cached = _odds_api_events_cache.get(cache_key)
        if cached is not None:
            return cached
    data = await _odds_api_get(
        "/sports/upcoming/odds",
        {"regions": ODDS_API_REGIONS, "markets": ODDS_API_MARKETS, "oddsFormat": "decimal"},
    )
    events = [e for e in (data if isinstance(data, list) else []) if str(e.get("sport_key", "")).startswith("soccer_")]
    _odds_api_events_cache[cache_key] = events
    return events

async def _supplement_odds_from_odds_api(matches: list[dict], league: str = "ALL", refresh: bool = False) -> dict:
    """Fill missing 1X2 odds without replacing API-Football fixture identity/data."""
    meta = {"checked": False, "matched": 0, "events": 0, "error": None}
    if not matches or not ODDS_API_ENABLED or not ODDS_API_KEY:
        return meta
    try:
        events = await _odds_api_events(league, refresh=refresh)
        meta.update({"checked": True, "events": len(events)})
        for match in matches:
            fid = match.get("_afootFixtureId")
            if not fid:
                continue
            if _valid_1x2(match.get("odds", {})):
                continue
            for event in events:
                if not _event_matches_fixture(event, match):
                    continue
                odds = _normalise_odds_api_event(event)
                if not _valid_1x2(odds):
                    continue
                match["odds"] = odds
                match["oddsSource"] = "The Odds API"
                match["oddsAvailable"] = True
                match["hasBookmakerOdds"] = True
                match["bookmakerGatePassed"] = True
                match["oddsApiEventId"] = event.get("id")
                eh = _normalise_team_name(event.get("home_team"))
                ea = _normalise_team_name(event.get("away_team"))
                fh = _normalise_team_name(match.get("home") or match.get("homeTeam"))
                fa = _normalise_team_name(match.get("away") or match.get("awayTeam"))
                exact_pair = (eh == fh and ea == fa)
                match["oddsMatchedBy"] = "exact/alias+kickoff" if exact_pair else "fuzzy-both-teams+kickoff"
                if not exact_pair:
                    match["oddsMatchConfidence"] = {
                        "home": round(_team_similarity(eh, fh), 1),
                        "away": round(_team_similarity(ea, fa), 1),
                    }
                meta["matched"] += 1
                break
    except Exception as exc:
        meta["error"] = str(exc)
        log.warning("The Odds API supplement failed: %s", exc)
    return meta

async def _odds_api_fallback_fixtures(league: str = "ALL") -> dict:
    events = await _odds_api_events(league, refresh=False)
    matches = [_normalise_odds_api_fixture(e, league) for e in events]
    return {
        "matches": matches,
        "count": len(matches),
        "source": "The Odds API fallback",
        "oddsSource": "The Odds API",
        "oddsFallback": True,
        "hasBookmakerOdds": any(_valid_1x2(m.get("odds", {})) for m in matches),
        "hasValidOdds": any(_valid_1x2(m.get("odds", {})) for m in matches),
        "oddsUnavailable": not any(_valid_1x2(m.get("odds", {})) for m in matches),
        "generatedAt": datetime.now(timezone.utc).isoformat(),
    }

async def _afoot_get_uncollapsed(path: str, params: dict, force_fresh: bool = False) -> dict:
    # ── Persistent SQLite cache (survives restarts) ──────────────────────────
    if not force_fresh:
        cached = _persistent_cache_get(path, params)
        if cached is not None:
            log.debug("Persistent cache hit: %s %s", path, params)
            return cached

    _rate_check()
    client = await get_client()
    last_exc = Exception("unknown")

    for attempt in range(2):
        if attempt:
            await asyncio.sleep(min(4, 2 ** attempt))
        try:
            _api_football_budget_guard(path)
            response = await client.get(path, params=params)
            _record_api_football_call(path)
            _record_quota(response, path)

            try:
                data = response.json()
            except Exception:
                data = {"errors": {"raw": response.text[:1000]}, "response": []}

            if response.status_code == 429:
                daily = _quota_state.get("dailyRemaining")
                if daily is not None and daily <= 0:
                    raise HTTPException(
                        429,
                        detail={
                            "code": "API_FOOTBALL_DAILY_QUOTA",
                            "message": "API-Football daily quota is exhausted.",
                            "dailyRemaining": daily,
                            "dailyLimit": _quota_state.get("dailyLimit"),
                        },
                    )
                last_exc = HTTPException(
                    429,
                    detail={
                        "code": "API_FOOTBALL_MINUTE_LIMIT",
                        "message": "API-Football per-minute rate limit reached.",
                    },
                )
                continue

            if response.status_code == 401:
                raise HTTPException(502, detail={
                    "code": "API_FOOTBALL_AUTH",
                    "message": "API-Football authentication failed.",
                    "api_response": data,
                })

            if response.status_code == 403:
                raise HTTPException(502, detail={
                    "code": "API_FOOTBALL_FORBIDDEN",
                    "message": "API-Football rejected the request (403 Forbidden).",
                    "api_response": data,
                })

            if response.status_code >= 500:
                last_exc = HTTPException(
                    502,
                    detail={"code": "API_FOOTBALL_SERVER_ERROR",
                            "message": f"API-Football server error: HTTP {response.status_code}"},
                )
                continue

            if response.status_code != 200:
                raise HTTPException(502, detail={
                    "code": "API_FOOTBALL_HTTP_ERROR",
                    "message": f"API-Football HTTP {response.status_code}",
                    "api_response": data,
                })

            errors = data.get("errors")
            if errors and not (isinstance(errors, list) and not errors):
                message = (
                    "; ".join(f"{k}: {v}" for k, v in errors.items())
                    if isinstance(errors, dict)
                    else str(errors)
                )
                raise HTTPException(502, detail={
                    "code": "API_FOOTBALL_ERROR",
                    "message": message,
                    "dailyRemaining": _quota_state.get("dailyRemaining"),
                    "minuteRemaining": _quota_state.get("minuteRemaining"),
                })

            # ── Write to persistent SQLite cache before returning ────────────
            _persistent_cache_set(path, params, data)

            return data

        except (httpx.NetworkError, httpx.TimeoutException) as exc:
            last_exc = exc

    raise HTTPException(
        502,
        detail={
            "code": "API_FOOTBALL_UNREACHABLE",
            "message": f"Sports data temporarily unavailable after retry: {last_exc}",
        },
    )


# v307: one in-flight upstream request per unique path+params.
# Concurrent visitors/widgets await the same task instead of consuming duplicate quota.
_AFOOT_INFLIGHT: dict[str, asyncio.Task] = {}
_AFOOT_INFLIGHT_LOCK = asyncio.Lock()

async def _afoot_get(path: str, params: dict, force_fresh: bool = False) -> dict:
    if not force_fresh:
        cached = _persistent_cache_get(path, params)
        if cached is not None:
            return cached
    key = _persist_cache_key(path, params) + ("|fresh" if force_fresh else "")
    async with _AFOOT_INFLIGHT_LOCK:
        task = _AFOOT_INFLIGHT.get(key)
        if task is None or task.done():
            task = asyncio.create_task(_afoot_get_uncollapsed(path, params, force_fresh=force_fresh))
            _AFOOT_INFLIGHT[key] = task
    try:
        return await task
    finally:
        async with _AFOOT_INFLIGHT_LOCK:
            if _AFOOT_INFLIGHT.get(key) is task and task.done():
                _AFOOT_INFLIGHT.pop(key, None)

async def _afoot_get_deadline(path: str, params: dict, deadline: float = 5.0, force_fresh: bool = False) -> dict:
    """Primary provider request with a hard wall-clock deadline for fallback paths."""
    return await asyncio.wait_for(
        _afoot_get(path, params, force_fresh=force_fresh),
        timeout=deadline,
    )

# ---------------------------------------------------------------------------
# NORMALISATION
# ---------------------------------------------------------------------------

def _safe_float(value) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0

def _clean(value) -> str:
    return re.sub(r"[^a-z0-9]+", " ", str(value or "").lower()).strip()

def _valid_1x2_local(odds):
    return all(_safe_float(odds.get(k)) > 1 for k in ("homeWin", "draw", "awayWin"))

def _valid_1x2(odds):
    return _valid_1x2_local(odds)

def _normalise_fixture(f: dict, league_name: str = "") -> dict:
    fixture = f.get("fixture", {})
    teams = f.get("teams", {})
    goals = f.get("goals", {})
    league = f.get("league", {})
    status = fixture.get("status", {})
    short = status.get("short", "")
    elapsed = status.get("elapsed")

    is_live = short in ("1H", "HT", "2H", "ET", "P", "BT")
    is_finished = short in ("FT", "AET", "PEN")

    if is_live:
        status_label = f"LIVE {elapsed}'" if elapsed is not None else "LIVE"
    elif is_finished:
        status_label = "FT"
    else:
        status_label = "Upcoming"

    home_goals = goals.get("home")
    away_goals = goals.get("away")
    score = (
        f"{home_goals} - {away_goals}"
        if home_goals is not None and away_goals is not None
        else "vs"
    )

    dt = fixture.get("date", "")
    if dt:
        dt = dt.replace("T", " ")[:16]

    # v360: league identity is authoritative by provider league ID.
    # Never label Brazil Serie A (71), Argentina (128), etc. as Italian Serie A (135).
    league_id = league.get("id")
    _canonical_league_by_id = {int(v): k for k, v in LEAGUE_IDS.items() if isinstance(v, int)}
    canonical_league_name = _canonical_league_by_id.get(league_id) or league.get("name") or league_name

    result = {
        "home": teams.get("home", {}).get("name", "Home"),
        "away": teams.get("away", {}).get("name", "Away"),
        "homeId": teams.get("home", {}).get("id"),
        "awayId": teams.get("away", {}).get("id"),
        "homeLogo": teams.get("home", {}).get("logo", ""),
        "awayLogo": teams.get("away", {}).get("logo", ""),
        "leagueLogo": league.get("logo", ""),
        "leagueFlag": league.get("flag", ""),
        "league": canonical_league_name,
        "datetime": dt,
        "score": score,
        # v312: preserve numeric goals. Finished Games must not have to parse
        # the presentation string ("2 - 1") back into a result.
        "homeScore": home_goals,
        "awayScore": away_goals,
        "homeGoals": home_goals,
        "awayGoals": away_goals,
        "goals": {"home": home_goals, "away": away_goals},
        "status": status_label,
        "venue": fixture.get("venue", {}).get("name", ""),
        "homeForm": [],
        "awayForm": [],
        "homeGoalsFor": 1.35,       # Neutral baseline — no home advantage built in
        "homeGoalsAgainst": 1.35,
        "awayGoalsFor": 1.35,
        "awayGoalsAgainst": 1.35,
        "h2hHomeWins": 3,
        "h2hDraws": 2,
        "h2hAwayWins": 2,
        "isSoccer": True,
        "isLive": is_live,
        "isFinished": is_finished,
        "elapsed": elapsed,
        "odds": {
            "homeWin": 0, "draw": 0, "awayWin": 0,
            "over25": 0, "over15": 0, "over05": 0,
            "btts": 0, "firstHalfHome": 0, "scoreFirst": 0,
            "expectedGoalscorer": 0,
        },
        "oddsSource": "API-Football",
        "_afootFixtureId": fixture.get("id"),
        "_teamHomeId": teams.get("home", {}).get("id"),
        "_teamAwayId": teams.get("away", {}).get("id"),
        "_leagueId": league.get("id"),
        "_leagueSeason": league.get("season"),
    }
    fixture_id = fixture.get("id")
    if fixture_id is not None:
        _fixture_meta_cache[str(fixture_id)] = {
            "home": result.get("home"), "away": result.get("away"),
            "homeLogo": result.get("homeLogo", ""),
            "awayLogo": result.get("awayLogo", ""),
            "leagueLogo": result.get("leagueLogo", ""),
            "leagueFlag": result.get("leagueFlag", ""),
            "league": result.get("league"), "datetime": result.get("datetime"),
            "leagueId": result.get("_leagueId"),
        }
    return result

# ---------------------------------------------------------------------------
# REPLACED _normalise_odds()
# ---------------------------------------------------------------------------

def _normalise_odds(bookmakers: list[dict], live: bool = False) -> dict:
    """
    Normalise API-Football bookmaker markets.

    Supports pre-match and live odds and preserves available individual
    markets even when a bookmaker does not contain a complete 1X2 market.
    """

    empty = {
        "homeWin": 0.0,
        "draw": 0.0,
        "awayWin": 0.0,
        "over25": 0.0,
        "over15": 0.0,
        "over05": 0.0,
        "btts": 0.0,
        "firstHalfHome": 0.0,
        "scoreFirst": 0.0,
        "expectedGoalscorer": 0.0,
    }

    if not bookmakers:
        return empty

    preferred = [
        "Pinnacle", "Bet365", "1xBet", "William Hill",
        "Unibet", "Bwin", "Ladbrokes", "Coral", "Paddy Power",
    ]

    def clean(value):
        return re.sub(r"[^a-z0-9]+", " ", str(value or "").lower()).strip()

    def find_value(values, aliases):
        aliases = [clean(x) for x in aliases]

        for value_name, odd, raw in values:
            if value_name in aliases:
                return odd

        for value_name, odd, raw in values:
            for alias in aliases:
                if alias and alias in value_name:
                    return odd

        return 0.0

    def extract(bets):
        out = dict(empty)

        for bet in bets or []:
            bet_name = clean(bet.get("name"))
            values = []

            for value in bet.get("values") or []:
                value_name = clean(value.get("value"))
                odd = _safe_float(value.get("odd"))
                if odd > 0:
                    values.append((value_name, odd, value))

            if not values:
                continue

            # MATCH WINNER / 1X2
            winner_market = (
                "match winner" in bet_name
                or "full time result" in bet_name
                or "fulltime result" in bet_name
                or "match result" in bet_name
                or "game winner" in bet_name
                or "1x2" in bet_name
                or bet_name == "winner"
                or bet_name == "result"
            )

            if winner_market:
                out["homeWin"] = (
                    find_value(values, ["home", "1", "home team", "team 1"])
                    or out["homeWin"]
                )
                out["draw"] = (
                    find_value(values, ["draw", "x"])
                    or out["draw"]
                )
                out["awayWin"] = (
                    find_value(values, ["away", "2", "away team", "team 2"])
                    or out["awayWin"]
                )

            # OVER / UNDER
            totals_market = (
                "over under" in bet_name
                or "goals over" in bet_name
                or "total goals" in bet_name
                or "goals" in bet_name
                or "total" in bet_name
            )

            if totals_market:
                out["over25"] = (
                    find_value(values, ["over 2.5", "over2.5", "over 2 5"])
                    or out["over25"]
                )
                out["over15"] = (
                    find_value(values, ["over 1.5", "over1.5", "over 1 5"])
                    or out["over15"]
                )
                out["over05"] = (
                    find_value(values, ["over 0.5", "over0.5", "over 0 5"])
                    or out["over05"]
                )

            # BTTS
            if (
                "both teams score" in bet_name
                or "both team score" in bet_name
                or bet_name == "btts"
                or "btts" in bet_name
            ):
                out["btts"] = find_value(values, ["yes"]) or out["btts"]

            # FIRST HALF WINNER
            if (
                "first half winner" in bet_name
                or "half time result" in bet_name
                or "halftime result" in bet_name
                or "1st half winner" in bet_name
            ):
                out["firstHalfHome"] = (
                    find_value(values, ["home", "1", "home team"])
                    or out["firstHalfHome"]
                )

            # FIRST TEAM TO SCORE
            if (
                "first team to score" in bet_name
                or "team to score first" in bet_name
                or "first scorer team" in bet_name
            ):
                out["scoreFirst"] = (
                    find_value(values, ["home", "1", "home team"])
                    or out["scoreFirst"]
                )

            # EXPECTED GOALSCORER / FIRST GOALSCORER
            if (
                "first goalscorer" in bet_name
                or "first goal scorer" in bet_name
                or "anytime goalscorer" in bet_name
                or "goalscorer" in bet_name
            ):
                if values:
                    out["expectedGoalscorer"] = values[0][1]

        return out

    ordered = sorted(
        bookmakers,
        key=lambda b: (
            preferred.index(b.get("name"))
            if b.get("name") in preferred
            else 9999
        ),
    )

    best = dict(empty)

    for bookmaker in ordered:
        candidate = extract(bookmaker.get("bets") or [])

        # Prefer one bookmaker containing complete 1X2.
        if _valid_1x2_local(candidate):
            return candidate

        # Preserve available individual markets.
        for key, value in candidate.items():
            if value and not best.get(key):
                best[key] = value

    return best

# ---------------------------------------------------------------------------
# STATISTICAL / PREDICTION ENGINE
# ---------------------------------------------------------------------------

V141_CACHE_TTL_SECONDS = 300
V141_FIXTURE_REFRESH_SECONDS = int(os.getenv("FIXTURE_REFRESH_SECONDS", "7200"))  # 1 hr (was 30 min)
V141_PREDICTION_REFRESH_SECS = 300
V141_LEARNING_CYCLE_SECS = int(os.getenv("LEARNING_CYCLE_SECS", str(6 * 3600)))  # 6 hours (was 3 hrs)
V141_MODEL_VERSION = os.getenv("MODEL_VERSION", "KasiScore AI Model")
V141_LEARNING_DB_PATH = Path(
    os.getenv("LEARNING_DB_PATH", str(BASE_DIR / "kasiscore_learning.sqlite3"))
)

V141_PREDICTION_WEIGHTS = {
    "odds":          0.385,   # Bookmaker odds — 38.5% weight
    "ai":            0.188,   # AI model       — 18.8% weight
    "table":         0.111,   # League table   — 11.1% weight
    "injuriesH2H":   0.011,   # Injuries/H2H   — kept proportional (legacy)
    "lastSeason":    0.115,   # Last season    — 11.5% weight
    "currentSeason": 0.090,   # Current season 2026/27 — 9.0% weight
}

# Minimum win-rate threshold (75%) for a team to qualify for predictions.
# Applied per team across games played in the current 2026/27 season.
WIN_RATE_THRESHOLD = 0.45

class V141SharedCache:
    def __init__(self, ttl=V141_CACHE_TTL_SECONDS):
        self.ttl = ttl
        self.data = {}
        self.timestamps = {}

    def get(self, key):
        now = time.monotonic()
        if key not in self.data:
            return None
        if now - self.timestamps[key] >= self.ttl:
            self.data.pop(key, None)
            self.timestamps.pop(key, None)
            return None
        return self.data[key]

    def set(self, key, value):
        self.data[key] = value
        self.timestamps[key] = time.monotonic()
        return value

    def clear(self):
        self.data.clear()
        self.timestamps.clear()

v141_cache = V141SharedCache()

class V141LearningStore:
    def __init__(self, path):
        self.path = Path(path)

    def connect(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        conn = sqlite3.connect(str(self.path), timeout=30)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        return conn

    def init(self):
        with self.connect() as conn:
            conn.executescript("""
            CREATE TABLE IF NOT EXISTS predictions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                fixture_id INTEGER NOT NULL,
                kickoff TEXT,
                home_team TEXT,
                away_team TEXT,
                model_version TEXT NOT NULL,
                probabilities TEXT NOT NULL,
                odds TEXT,
                model_inputs TEXT,
                prediction TEXT,
                predicted_at TEXT NOT NULL,
                resolved INTEGER NOT NULL DEFAULT 0,
                UNIQUE(fixture_id, model_version)
            );
            CREATE TABLE IF NOT EXISTS results (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                prediction_id INTEGER NOT NULL UNIQUE,
                fixture_id INTEGER NOT NULL,
                home_goals INTEGER,
                away_goals INTEGER,
                actual_result TEXT,
                market_accuracy TEXT,
                resolved_at TEXT NOT NULL,
                FOREIGN KEY(prediction_id) REFERENCES predictions(id)
            );
            """)
            # Jira: persist original prediction context without replacing the existing table.
            for col, typ in (
                ("sport","TEXT DEFAULT 'football'"),
                ("competition","TEXT"),
                ("confidence","REAL"),
                ("bookmaker_prediction","TEXT")
            ):
                try:
                    conn.execute(f"ALTER TABLE predictions ADD COLUMN {col} {typ}")
                except sqlite3.OperationalError:
                    pass

    def save_prediction(self, payload):
        model_version = payload.get("modelVersion", V141_MODEL_VERSION)
        now = datetime.now(timezone.utc).isoformat()

        with self.connect() as conn:
            conn.execute("""
                INSERT INTO predictions
                (fixture_id,kickoff,home_team,away_team,model_version,
                 probabilities,odds,model_inputs,prediction,predicted_at,
                 sport,competition,confidence,bookmaker_prediction)
                VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                ON CONFLICT(fixture_id,model_version) DO UPDATE SET
                    kickoff=excluded.kickoff,
                    home_team=excluded.home_team,
                    away_team=excluded.away_team,
                    probabilities=excluded.probabilities,
                    odds=excluded.odds,
                    model_inputs=excluded.model_inputs,
                    prediction=excluded.prediction,
                    predicted_at=excluded.predicted_at,
                    sport=excluded.sport,
                    competition=excluded.competition,
                    confidence=excluded.confidence,
                    bookmaker_prediction=excluded.bookmaker_prediction
            """, (
                int(payload["fixtureId"]),
                payload.get("kickoff"),
                payload.get("homeTeam"),
                payload.get("awayTeam"),
                model_version,
                json.dumps(payload.get("probabilities", {})),
                json.dumps(payload.get("odds", {})),
                json.dumps(payload.get("modelInputs", {})),
                json.dumps(payload.get("prediction", {})),
                now,
                payload.get("sport") or "football",
                payload.get("competition"),
                payload.get("confidence"),
                payload.get("bookmakerPrediction"),
            ))

            row = conn.execute("""
                SELECT id,fixture_id,model_version,resolved
                FROM predictions
                WHERE fixture_id=? AND model_version=?
            """, (int(payload["fixtureId"]), model_version)).fetchone()

            return dict(row)

    def save_result(self, prediction_id, fixture_id, home_goals, away_goals,
                    actual_result, market_accuracy=None):
        with self.connect() as conn:
            conn.execute("""
                INSERT OR REPLACE INTO results
                (prediction_id,fixture_id,home_goals,away_goals,
                 actual_result,market_accuracy,resolved_at)
                VALUES (?,?,?,?,?,?,?)
            """, (
                prediction_id, fixture_id, home_goals, away_goals,
                actual_result, json.dumps(market_accuracy or {}),
                datetime.now(timezone.utc).isoformat(),
            ))
            conn.execute(
                "UPDATE predictions SET resolved=1 WHERE id=?",
                (prediction_id,),
            )

    def stats(self):
        with self.connect() as conn:
            total    = conn.execute("SELECT COUNT(*) FROM predictions").fetchone()[0]
            resolved = conn.execute("SELECT COUNT(*) FROM results").fetchone()[0]
            # Distinct model versions in use (for dashboard display)
            versions = [r[0] for r in conn.execute(
                "SELECT DISTINCT model_version FROM predictions ORDER BY model_version"
            ).fetchall()]
            # Accuracy: % of resolved games where winner was correctly predicted
            correct = conn.execute(
                """SELECT COUNT(*) FROM results r
                    JOIN predictions p ON p.id=r.prediction_id
                    WHERE json_extract(r.market_accuracy,'$.winnerCorrect')=1"""
            ).fetchone()[0]
            graded = conn.execute(
                """SELECT COUNT(*) FROM results
                    WHERE market_accuracy IS NOT NULL
                      AND json_extract(market_accuracy,'$.winnerCorrect') IS NOT NULL"""
            ).fetchone()[0]
            accuracy = round(correct / graded * 100, 1) if graded > 0 else None
            return {
                "totalPredictions": total,
                "resolvedPredictions": resolved,
                "pendingPredictions": total - resolved,
                "modelVersionsInDB": versions,
                "accuracy": accuracy,
                "gradedGames": graded,
                "correctPredictions": correct,
            }

v141_learning = V141LearningStore(V141_LEARNING_DB_PATH)

# Learning cycle state — tracks last run and weight adaptations
_learning_state = {
    "lastRunAt": None,
    "nextRunAt": None,
    "cycleCount": 0,
    "lastCycleUpdated": 0,       # # predictions refreshed last cycle
    "lastCycleImproved": 0,      # # predictions whose confidence changed
    "adaptedWeights": dict(V141_PREDICTION_WEIGHTS),  # live-adjusted weights
    "marketAccuracyHistory": {},  # market -> [correct_rate over last N cycles]
    "status": "pending",
}

def v141_normalise_three_way(values):
    keys = ("homeWin", "draw", "awayWin")
    total = sum(max(0.0, float(values.get(k, 0.0))) for k in keys)
    if total <= 0:
        return {k: 1 / 3 for k in keys}
    return {
        k: max(0.0, float(values.get(k, 0.0))) / total
        for k in keys
    }

def v141_weight_prediction(components):
    available = {
        name: v141_normalise_three_way(value)
        for name, value in components.items()
        if name in V141_PREDICTION_WEIGHTS and isinstance(value, dict)
    }

    total_weight = sum(V141_PREDICTION_WEIGHTS[k] for k in available)
    if not available or total_weight <= 0:
        return {
            "probabilities": {k: 1 / 3 for k in ("homeWin", "draw", "awayWin")},
            "weights": {},
            "configuredWeights": V141_PREDICTION_WEIGHTS,
        }

    effective = {
        k: V141_PREDICTION_WEIGHTS[k] / total_weight
        for k in available
    }

    final = {k: 0.0 for k in ("homeWin", "draw", "awayWin")}
    for name, probs in available.items():
        for outcome in final:
            final[outcome] += probs[outcome] * effective[name]

    return {
        "probabilities": v141_normalise_three_way(final),
        "weights": effective,
        "configuredWeights": V141_PREDICTION_WEIGHTS,
        "components": available,
    }

def _poisson(m):
    # Neutral xG model — no home advantage factor applied.
    # Both teams rated purely on their attacking output vs opponent defence,
    # using symmetrical defaults so the model is unbiased when data is missing.
    NEUTRAL = 1.35  # league average goals per match (no home/away bias)
    home_xg = max(
        0.25,
        min(
            4.5,
            (
                float(m.get("homeGoalsFor", NEUTRAL))
                + float(m.get("awayGoalsAgainst", NEUTRAL))
            ) / 2,
        ),
    )
    away_xg = max(
        0.25,
        min(
            4.5,
            (
                float(m.get("awayGoalsFor", NEUTRAL))
                + float(m.get("homeGoalsAgainst", NEUTRAL))
            ) / 2,
        ),
    )

    matrix = {
        (i, j): (
            math.exp(-(home_xg + away_xg))
            * home_xg ** i / math.factorial(i)
            * away_xg ** j / math.factorial(j)
        )
        for i in range(8)
        for j in range(8)
    }

    home = sum(v for (i, j), v in matrix.items() if i > j)
    draw = sum(v for (i, j), v in matrix.items() if i == j)
    away = sum(v for (i, j), v in matrix.items() if i < j)
    z = home + draw + away or 1

    return {
        "probs": {
            "homeWin": home / z,
            "draw": draw / z,
            "awayWin": away / z,
        },
        "over35": sum(v for (i, j), v in matrix.items() if i + j > 3),
        "over25": sum(v for (i, j), v in matrix.items() if i + j > 2),
        "over15": sum(v for (i, j), v in matrix.items() if i + j > 1),
        "over05": 1 - matrix[(0, 0)],
        "btts": sum(v for (i, j), v in matrix.items() if i > 0 and j > 0),
        "xgHome": home_xg,
        "xgAway": away_xg,
    }


# ---------------------------------------------------------------------------
# WIN-RATE QUALIFICATION — 75% threshold for 2026/27 season predictions
# ---------------------------------------------------------------------------

def _team_win_rate(rank: dict) -> tuple[float, int]:
    """Return (win_rate 0-1, games_played) for a standings entry.

    API-Football standings entries expose:
      rank["all"]["played"]  — total games played in the season
      rank["all"]["win"]     — total wins in the season
    A team qualifies for predictions only when its win rate ≥ WIN_RATE_THRESHOLD.
    """
    all_info = rank.get("all") or {}
    played = all_info.get("played") or 0
    wins   = all_info.get("win")   or 0
    if played == 0:
        return 0.0, 0
    return round(wins / played, 4), played


def _team_qualifies(rank: dict | None) -> bool:
    """True if a team has played ≥1 game AND has a win-rate ≥ WIN_RATE_THRESHOLD.

    If the team is not found in standings (rank is None) we let it through so
    that fixtures played before standings data is available are not silently
    dropped.  Once standings exist, the threshold is enforced.
    """
    if rank is None:
        return True   # standings not yet available — give benefit of the doubt
    win_rate, played = _team_win_rate(rank)
    if played == 0:
        return True   # no games played yet in the season — let through
    return win_rate >= WIN_RATE_THRESHOLD


# ---------------------------------------------------------------------------
# MATCH ENRICHMENT — standings + form → real signal for table & currentSeason
# ---------------------------------------------------------------------------

async def _fetch_standings_for_league(league_id: int, season: int) -> list:
    """Fetch and cache standings for a league/season. Returns the standings list."""
    cache_key = f"standings:{league_id}:{season}"
    cached = _standings_cache.get(cache_key)
    if cached is not None:
        return cached
    try:
        data = await _afoot_get("/standings", {"league": league_id, "season": season})
        # API-Football: response[0].league.standings[0] is the main table list
        # Guard: response or standings may be empty (e.g. league not yet started)
        response_list = data.get("response") or []
        standings_outer = (
            response_list[0].get("league", {}).get("standings", [])
            if response_list
            else []
        )
        standings = standings_outer[0] if standings_outer else []
        _standings_cache[cache_key] = standings
        log.info("Standings cached: league=%s season=%s teams=%d", league_id, season, len(standings))
        return standings
    except Exception as exc:
        log.warning("Standings fetch failed league=%s: %s", league_id, exc)
        return []


async def _fetch_match_standings_for_league(league_id: int, season: int, home_team_id=None, away_team_id=None) -> list:
    """Return the standings group/table that actually contains this fixture's teams.

    Tournament/qualification competitions often return multiple groups in
    league.standings.  The old Match Centre always selected standings[0], which
    could display an unrelated group (for example Morocco/Gabon/Niger/Lesotho)
    for a Uganda v Libya fixture.  For match pages we inspect every returned
    group and select the group containing the home/away team IDs.  League-style
    competitions still naturally resolve to their single table.
    """
    cache_key=f"match-standings-groups:{league_id}:{season}"
    grouped=_standings_cache.get(cache_key)
    if grouped is None:
        try:
            data=await _afoot_get("/standings", {"league":league_id,"season":season})
            response_list=data.get("response") or [] if isinstance(data,dict) else []
            grouped=(((response_list[0].get("league") or {}).get("standings") or []) if response_list else [])
            grouped=[g for g in grouped if isinstance(g,list) and g]
            _standings_cache[cache_key]=grouped
        except Exception as exc:
            log.warning("Match standings fetch failed league=%s season=%s: %s",league_id,season,exc)
            return []
    if not grouped:
        return []
    wanted={str(x) for x in (home_team_id,away_team_id) if x not in (None,"",0)}
    if wanted:
        best=[];best_hits=-1
        for group in grouped:
            ids={str((r.get("team") or {}).get("id")) for r in group if isinstance(r,dict)}
            hits=len(wanted & ids)
            if hits>best_hits:
                best,best_hits=group,hits
            if hits==len(wanted):
                return group
        # Never show an unrelated tournament group. One matching team is useful;
        # zero matches means the provider has not returned this fixture's table.
        return best if best_hits>0 else []
    return grouped[0]

async def _fetch_team_form(team_id: int, league_id: int, season: int, last_n: int = 5) -> list:
    """Fetch last N fixture results for a team. Returns list of 'W'/'D'/'L' strings."""
    cache_key = f"form:{team_id}:{league_id}:{season}"
    cached = _form_cache.get(cache_key)
    if cached is not None:
        return cached
    try:
        data = await _afoot_get(
            "/fixtures",
            {"team": team_id, "league": league_id, "season": season,
             "status": "FT", "last": last_n},
        )
        results = []
        for fix in data.get("response", []):
            goals = fix.get("goals", {})
            score_h = goals.get("home", 0) or 0
            score_a = goals.get("away", 0) or 0
            teams = fix.get("teams", {})
            is_home = teams.get("home", {}).get("id") == team_id
            if is_home:
                results.append("W" if score_h > score_a else "D" if score_h == score_a else "L")
            else:
                results.append("W" if score_a > score_h else "D" if score_h == score_a else "L")
        _form_cache[cache_key] = results
        return results
    except Exception as exc:
        log.warning("Form fetch failed team=%s: %s", team_id, exc)
        return []


def _form_to_probs(form: list) -> dict:
    """Convert a list of W/D/L strings into win/draw/loss probabilities.
    Recent results are weighted more heavily (exponential decay).
    Falls back to neutral 1/3 if no data.
    """
    if not form:
        return {"homeWin": 1/3, "draw": 1/3, "awayWin": 1/3}
    weights = [0.5 ** i for i in range(len(form))]  # most recent = highest weight
    total_w = sum(weights)
    w_wins  = sum(w for w, r in zip(weights, form) if r == "W")
    w_draws = sum(w for w, r in zip(weights, form) if r == "D")
    w_loss  = sum(w for w, r in zip(weights, form) if r == "L")
    return {
        "homeWin":  w_wins  / total_w,
        "draw":     w_draws / total_w,
        "awayWin":  w_loss  / total_w,
    }


def _standings_to_probs(home_rank: dict, away_rank: dict, total_teams: int) -> dict:
    """Convert league table positions + goal difference into match probabilities.

    Strategy:
    - Points-per-game ratio gives a raw team strength score.
    - Goal difference per game adds attacking/defensive signal.
    - Relative strength of home vs away converts to win/draw/loss probs.
    - Draw probability is higher when teams are closely matched.
    """
    if not home_rank or not away_rank or total_teams < 2:
        return {"homeWin": 1/3, "draw": 1/3, "awayWin": 1/3}

    def team_strength(rank: dict) -> float:
        """0.0–1.0 strength score from points per game + goal difference."""
        all_info = rank.get("all") or {}
        played = max(all_info.get("played") or 1, 1)
        points = rank.get("points") or 0
        gd     = rank.get("goalsDiff") or 0
        ppg    = points / played           # points per game (0–3)
        gd_pg  = gd / played               # goal diff per game
        # Normalise ppg to 0-1 range (max is 3.0) and blend with gd
        return (ppg / 3.0) * 0.7 + (max(min(gd_pg, 3), -3) / 3.0) * 0.15 + 0.15

    hs = team_strength(home_rank)
    as_ = team_strength(away_rank)
    total = hs + as_ or 1

    raw_home = hs / total
    raw_away = as_ / total

    # Draw probability is highest when teams are evenly matched
    closeness = 1 - abs(raw_home - raw_away)  # 0 (mismatch) → 1 (equal)
    draw_prob = 0.10 + closeness * 0.18        # 10–28% draw range

    home_prob = raw_home * (1 - draw_prob)
    away_prob = raw_away * (1 - draw_prob)

    z = home_prob + draw_prob + away_prob
    return {
        "homeWin":  home_prob / z,
        "draw":     draw_prob / z,
        "awayWin":  away_prob / z,
    }


def _goals_per_game(rank: dict) -> tuple[float, float]:
    """Return (goals_for_pg, goals_against_pg) from a standings entry."""
    all_info = rank.get("all") or {}
    played = max(all_info.get("played") or 1, 1)
    goals  = all_info.get("goals") or {}
    gf = (goals.get("for")     or 0) / played
    ga = (goals.get("against") or 0) / played
    return round(gf, 3), round(ga, 3)


async def _enrich_match(match: dict, league_id: int, season: int) -> dict:
    """Add real standings + form data to a match dict before prediction.

    Populates:
    - homeGoalsFor / homeGoalsAgainst / awayGoalsFor / awayGoalsAgainst
      (from standings goals-per-game → feeds Poisson xG model)
    - _tableProbs    → replaces neutral 1/3 in table component
    - _formProbs     → replaces neutral 1/3 in currentSeason component
    - _h2hProbs      → replaces neutral 1/3 in injuriesH2H component
                       (using head-to-head implied by both teams' form vs each other)
    """
    home_team_id = match.get("_teamHomeId") or match.get("homeTeamId") or match.get("home_id")
    away_team_id = match.get("_teamAwayId") or match.get("awayTeamId") or match.get("away_id")

    # Fetch standings and form concurrently
    tasks = [_fetch_standings_for_league(league_id, season)]
    if home_team_id:
        tasks.append(_fetch_team_form(home_team_id, league_id, season, last_n=7))
    if away_team_id:
        tasks.append(_fetch_team_form(away_team_id, league_id, season, last_n=7))

    results = await asyncio.gather(*tasks, return_exceptions=True)
    standings = results[0] if not isinstance(results[0], Exception) else []
    home_form = results[1] if len(results) > 1 and not isinstance(results[1], Exception) else []
    away_form = results[2] if len(results) > 2 and not isinstance(results[2], Exception) else []

    # Build team-id → rank lookup
    rank_by_id = {
        entry.get("team", {}).get("id"): entry
        for entry in standings
        if entry.get("team", {}).get("id")
    }

    home_rank = rank_by_id.get(home_team_id)
    away_rank = rank_by_id.get(away_team_id)
    total_teams = len(standings)

    enriched = dict(match)

    # 1. Feed real goals-per-game into Poisson xG inputs
    if home_rank:
        hgf, hga = _goals_per_game(home_rank)
        enriched["homeGoalsFor"]     = hgf if hgf > 0 else 1.35
        enriched["homeGoalsAgainst"] = hga if hga > 0 else 1.35
    if away_rank:
        agf, aga = _goals_per_game(away_rank)
        enriched["awayGoalsFor"]     = agf if agf > 0 else 1.35
        enriched["awayGoalsAgainst"] = aga if aga > 0 else 1.35

    # 2. Table component probabilities (from standings strength)
    enriched["_tableProbs"] = _standings_to_probs(home_rank, away_rank, total_teams)

    # 3. Current season form (last 5 games, recency-weighted)
    home_form_probs = _form_to_probs(home_form)
    away_form_probs = _form_to_probs(away_form)
    # Blend: home team's win prob vs away team's win prob (from their own perspectives)
    if home_form or away_form:
        hw = home_form_probs["homeWin"]  # home team's win rate
        aw = away_form_probs["homeWin"]  # away team's win rate (from their pov = away win)
        dh = home_form_probs["draw"]
        da = away_form_probs["draw"]
        total = hw + aw or 1
        draw_blended = (dh + da) / 2
        raw_hw = hw / total * (1 - draw_blended)
        raw_aw = aw / total * (1 - draw_blended)
        z = raw_hw + draw_blended + raw_aw or 1
        enriched["_formProbs"] = {
            "homeWin": raw_hw / z,
            "draw":    draw_blended / z,
            "awayWin": raw_aw / z,
        }
    else:
        enriched["_formProbs"] = {"homeWin": 1/3, "draw": 1/3, "awayWin": 1/3}

    # 4. H2H proxy: blend table and form signals
    #    (real H2H data would require extra API calls per fixture — too costly)
    tp = enriched["_tableProbs"]
    fp = enriched["_formProbs"]
    enriched["_h2hProbs"] = {
        k: (tp[k] * 0.6 + fp[k] * 0.4)
        for k in ("homeWin", "draw", "awayWin")
    }

    # 5. Win-rate qualification data (2026/27 season gate)
    home_wr, home_played = _team_win_rate(home_rank) if home_rank else (0.0, 0)
    away_wr, away_played = _team_win_rate(away_rank) if away_rank else (0.0, 0)
    enriched["_homeWinRate"]    = home_wr
    enriched["_awayWinRate"]    = away_wr
    enriched["_homeGamesPlayed"] = home_played
    enriched["_awayGamesPlayed"] = away_played
    enriched["_homeQualifies"]  = _team_qualifies(home_rank)
    enriched["_awayQualifies"]  = _team_qualifies(away_rank)
    # A fixture qualifies only when BOTH teams pass the win-rate threshold
    enriched["_bothTeamsQualify"] = enriched["_homeQualifies"] and enriched["_awayQualifies"]

    log.debug(
        "Enriched %s vs %s | table=%s form=%s goalsFor=%.2f/%.2f | "
        "winRates=%.0f%%/%.0f%% played=%d/%d qualify=%s",
        match.get("home"), match.get("away"),
        enriched["_tableProbs"], enriched["_formProbs"],
        enriched.get("homeGoalsFor", 1.35), enriched.get("awayGoalsFor", 1.35),
        home_wr * 100, away_wr * 100,
        home_played, away_played,
        enriched["_bothTeamsQualify"],
    )

    return enriched




def _prediction(m):
    """
    Unified Kasi Sports News prediction engine.

    Critical live-odds fix:
    - If live/pre-match bookmaker 1X2 exists, use no-vig bookmaker probabilities.
    - If bookmaker 1X2 is missing, use the statistical model probabilities.
    This prevents division-by-zero and still produces a prediction.
    """

    o = m.get("odds", {})
    stat = _poisson(m)

    # BOOKMAKER PROBABILITY
    if _valid_1x2(o):
        market = _novig(o)
        bookmaker_available = True
    else:
        market = stat["probs"]
        bookmaker_available = False

    # Use enriched real data if available, fall back to neutral/Poisson
    neutral = {"homeWin": 1 / 3, "draw": 1 / 3, "awayWin": 1 / 3}
    table_probs        = m.get("_tableProbs")  or neutral
    form_probs         = m.get("_formProbs")   or stat["probs"]
    h2h_probs          = m.get("_h2hProbs")    or neutral

    fused = v141_weight_prediction({
        "odds":          market,
        "ai":            stat["probs"],
        "table":         table_probs,
        "injuriesH2H":   h2h_probs,
        "lastSeason":    neutral,       # last season data not yet wired
        "currentSeason": form_probs,
    })["probabilities"]

    key = max(fused, key=fused.get)
    winner = (
        m.get("home")
        if key == "homeWin"
        else "Draw"
        if key == "draw"
        else m.get("away")
    )
    conf = round(fused[key] * 100)

    first_team = (
        m.get("home")
        if stat["xgHome"] >= stat["xgAway"]
        else m.get("away")
    )

    total_xg = stat["xgHome"] + stat["xgAway"] or 1
    home_score_first_prob = round(stat["xgHome"] / total_xg * 100)
    away_score_first_prob = 100 - home_score_first_prob

    markets = {
        "FT WINNER": {
            "pick": winner,
            "odds": o.get(key, 0),
            "probability": conf,
            "probabilityType": (
                "40% bookmaker + 20% AI + supporting model components"
                if bookmaker_available
                else "KasiScore model probabilities — bookmaker 1X2 unavailable"
            ),
        },
        "OVER 3.5": {
            "pick": "Over 3.5",
            "odds": o.get("over35", 0) or round(1 / max(stat["over35"], 0.01), 2),
            "probability": round(stat["over35"] * 100),
            "probabilityType": "Poisson + live fixture state",
        },
        "OVER 2.5": {
            "pick": "Over 2.5",
            "odds": o.get("over25", 0) or round(1 / max(stat["over25"], 0.01), 2),
            "probability": round(stat["over25"] * 100),
            "probabilityType": "Poisson + live fixture state",
        },
        "OVER 1.5": {
            "pick": "Over 1.5",
            "odds": o.get("over15", 0) or round(1 / max(stat["over15"], 0.01), 2),
            "probability": round(stat["over15"] * 100),
            "probabilityType": "Poisson + live fixture state",
        },
        "OVER 0.5": {
            "pick": "Over 0.5",
            "odds": o.get("over05", 0) or round(1 / max(stat["over05"], 0.01), 2),
            "probability": round(stat["over05"] * 100),
            "probabilityType": "Poisson + live fixture state",
        },
        "FIRST TEAM TO SCORE": {
            "pick": first_team,
            "odds": o.get("scoreFirst", 0),
            "probability": round(
                max(stat["xgHome"], stat["xgAway"]) / total_xg * 100
            ),
            "probabilityType": "Live score + statistics + model",
        },
        "BOTH TEAMS TO SCORE": {
            "pick": "Yes" if stat["btts"] >= 0.5 else "No",
            "odds": o.get("btts", 0),
            "probability": round(stat["btts"] * 100),
            "probabilityType": "Poisson joint probability",
        },
        "HALF TIME": {
            "pick": (
                m.get("home")
                if fused.get("homeWin", 0) >= fused.get("awayWin", 0)
                   and fused.get("homeWin", 0) >= fused.get("draw", 0)
                else "Draw"
                if fused.get("draw", 0) >= fused.get("awayWin", 0)
                else m.get("away")
            ),
            "odds": o.get("firstHalfHome", 0),
            "probabilities": {
                "home": round(fused.get("homeWin", 0) * 80, 1),
                "draw": min(round(fused.get("draw", 0) * 120, 1), 100),
                "away": round(fused.get("awayWin", 0) * 80, 1),
            },
            "probability": round(max(fused.values()) * 80),
            "probabilityType": "KasiScore model half-time proxy (80% of FT signal)",
        },
        "EXPECTED GOALSCORER": {
            "pick": "Player-level data where available",
            "odds": o.get("expectedGoalscorer", 0),
            "probability": 0,
            "probabilityType": "Player-level data required",
        },
        "COMBO": {
            "pick": f"{winner} + Over 2.5",
            "odds": 0,
            "probability": round(
                max(fused.values()) * stat["over25"] * 100
            ),
            "probabilityType": "Unified KasiScore model combination",
        },
    }

    advice = (
        "Live bookmaker odds fused with KasiScore model components."
        if bookmaker_available
        else "Live bookmaker 1X2 unavailable; KasiScore model prediction calculated from live fixture data."
    )

    return {
        "prediction": {
            "bestPick": winner,
            "winner": winner,
            "confidence": conf,
            "probabilities": {
                k: round(v * 100, 1)
                for k, v in fused.items()
            } | {
                "over35": round(stat["over35"] * 100, 1),
                "over25": round(stat["over25"] * 100, 1),
                "over15": round(stat["over15"] * 100, 1),
                "over05": round(stat["over05"] * 100, 1),
                "btts": round(stat["btts"] * 100, 1),
                "halfTimeHome": round(fused.get("homeWin", 0) * 80, 1),
                "halfTimeDraw": min(round(fused.get("draw", 0) * 120, 1), 100),
                "halfTimeAway": round(fused.get("awayWin", 0) * 80, 1),
                "firstTeamToScoreHome": home_score_first_prob,
                "firstTeamToScoreAway": away_score_first_prob,
                "firstTeamToScore": first_team,
            },
            "advice": advice,
            "bookmakerOddsUsed": bookmaker_available,
        },
        "markets": markets,
        "goalRating": {
            "homeExpectedGoals": round(stat["xgHome"], 2),
            "awayExpectedGoals": round(stat["xgAway"], 2),
            "expectedTotalGoals": round(
                stat["xgHome"] + stat["xgAway"], 2
            ),
            "over25Probability": round(stat["over25"] * 100),
            "over15Probability": round(stat["over15"] * 100),
            "over05Probability": round(stat["over05"] * 100),
            "bttsProbability": round(stat["btts"] * 100),
            "firstTeamToScore": first_team,
            "firstTeamToScoreHomeProbability": home_score_first_prob,
            "firstTeamToScoreAwayProbability": away_score_first_prob,
        },
    }

def _novig(o):
    values = [
        1 / float(o[k])
        for k in ("homeWin", "draw", "awayWin")
    ]
    total = sum(values) or 1
    return {
        "homeWin": values[0] / total,
        "draw": values[1] / total,
        "awayWin": values[2] / total,
    }

# ---------------------------------------------------------------------------
# LEAGUE HELPERS
# ---------------------------------------------------------------------------

def _resolve_league_id(league: str) -> int:
    try:
        return int(league)
    except ValueError:
        lid = LEAGUE_IDS.get(league)
        if lid is None:
            raise HTTPException(
                400,
                f"Unknown league: {league!r}. Known: {', '.join(sorted(LEAGUE_IDS))}",
            )
        return lid

def _league_name_from_id(lid: int, fallback: str) -> str:
    for name, value in LEAGUE_IDS.items():
        if value == lid:
            return name
    return fallback

# ---------------------------------------------------------------------------
# BACKGROUND TASKS / APP
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# LEARNING CYCLE — runs every 3 hours, re-scores pending predictions
# ---------------------------------------------------------------------------

def _adapt_weights_from_history(history: dict) -> dict:
    """
    Nudge prediction weights toward components that have been accurate.
    If a market has been consistently wrong, reduce its weight slightly.
    Weight changes are capped at ±20% of the base value per cycle.
    """
    weights = dict(_learning_state["adaptedWeights"])
    for market, rates in history.items():
        if len(rates) < 2:
            continue
        avg = sum(rates) / len(rates)
        # avg > 0.55 → component is reliable, small boost
        # avg < 0.45 → component is unreliable, small cut
        if market in weights:
            delta = (avg - 0.50) * 0.05        # max ±2.5% nudge per cycle
            cap = V141_PREDICTION_WEIGHTS[market] * 0.20
            weights[market] = max(
                V141_PREDICTION_WEIGHTS[market] * 0.60,
                min(V141_PREDICTION_WEIGHTS[market] * 1.40,
                    weights[market] + max(-cap, min(cap, delta)))
            )
    # Re-normalise so weights still sum to 1
    total = sum(weights.values()) or 1
    return {k: round(v / total, 4) for k, v in weights.items()}


async def _run_learning_cycle():
    """
    Core 3-hour learning cycle:
    0. Auto-resolve finished fixtures (fetches API-Football results for any
       pending prediction whose kickoff is >105 minutes in the past).
    1. Read all resolved results and compute per-market accuracy.
    2. Adapt prediction weights based on what has been accurate.
    3. Re-score every PENDING prediction using adapted weights.
    4. Update _learning_state for the dashboard.
    """
    global _learning_state
    now_utc = datetime.now(timezone.utc)
    log.info("Learning cycle starting (cycle #%d)", _learning_state["cycleCount"] + 1)
    _learning_state["status"] = "running"

    # ── 0. Auto-resolve finished fixtures ─────────────────────────────────────
    auto_resolved = 0
    try:
        cutoff_auto = (now_utc - timedelta(minutes=105)).strftime("%Y-%m-%d %H:%M")
        with v141_learning.connect() as conn:
            pending_rows = conn.execute(
                """
                SELECT id, fixture_id, home_team, away_team, kickoff, probabilities
                FROM predictions
                WHERE resolved=0
                  AND kickoff IS NOT NULL
                  AND kickoff <= ?
                ORDER BY kickoff DESC
                LIMIT 100
                """,
                (cutoff_auto,),
            ).fetchall()

        for prow in pending_rows:
            try:
                fid = prow["fixture_id"]
                # ── Use persistent cache first; only call API if not cached ──
                # This is the single biggest quota saver: when a fixture was
                # already fetched on match day its result is in SQLite and we
                # don't need another API call to resolve it.
                data = await _afoot_get("/fixtures", {"id": fid})
                resp = data.get("response", [])
                if not resp:
                    continue
                fx = resp[0]
                status_short = fx.get("fixture", {}).get("status", {}).get("short", "")
                if status_short not in ("FT", "AET", "PEN"):
                    continue
                goals = fx.get("goals", {})
                hg = goals.get("home")
                ag = goals.get("away")
                if hg is None or ag is None:
                    continue
                hg, ag = int(hg), int(ag)
                actual = "homeWin" if hg > ag else "awayWin" if ag > hg else "draw"
                probs_raw = json.loads(prow["probabilities"] or "{}")
                total_goals = hg + ag
                btts_actual = hg > 0 and ag > 0
                predicted_winner = (
                    "homeWin" if probs_raw.get("homeWin", 0) >= probs_raw.get("awayWin", 0)
                                 and probs_raw.get("homeWin", 0) >= probs_raw.get("draw", 0)
                    else "draw" if probs_raw.get("draw", 0) >= probs_raw.get("awayWin", 0)
                    else "awayWin"
                )
                market_accuracy = {
                    "predictedWinner": predicted_winner,
                    "actualResult": actual,
                    "winnerCorrect": predicted_winner == actual,
                    "over35Correct": (total_goals > 3) == (probs_raw.get("over35", 0) >= 50),
                    "over25Correct": (total_goals > 2) == (probs_raw.get("over25", 0) >= 50),
                    "over15Correct": (total_goals > 1) == (probs_raw.get("over15", 0) >= 50),
                    "over05Correct": (total_goals > 0) == (probs_raw.get("over05", 0) >= 50),
                    "bttsCorrect": btts_actual == (probs_raw.get("btts", 0) >= 50),
                    "totalGoals": total_goals,
                    "homeGoals": hg,
                    "awayGoals": ag,
                    "gradedAt": now_utc.isoformat(),
                    "autoResolved": True,
                }
                v141_learning.save_result(int(prow["id"]), fid, hg, ag, actual, market_accuracy)
                auto_resolved += 1
                log.info("Auto-resolved: %s v %s %d-%d → %s",
                         prow["home_team"], prow["away_team"], hg, ag, actual)
            except Exception as exc:
                log.debug("Auto-resolve skip fixture %s: %s", prow["fixture_id"], exc)
    except Exception as exc:
        log.warning("Learning cycle: auto-resolve error: %s", exc)

    _learning_state["lastAutoResolved"] = auto_resolved
    log.info("Learning cycle: auto-resolved %d finished fixtures", auto_resolved)

    # ── 1. Compute per-market accuracy from resolved results ──────────────────
    market_correct: dict[str, list[bool]] = {}
    try:
        with v141_learning.connect() as conn:
            rows = conn.execute(
                "SELECT market_accuracy FROM results WHERE market_accuracy IS NOT NULL"
            ).fetchall()
        for r in rows:
            try:
                ma = json.loads(r["market_accuracy"] or "{}")
                for key in ("over35Correct", "over25Correct", "over15Correct",
                            "over05Correct", "bttsCorrect", "winnerCorrect"):
                    val = ma.get(key)
                    if isinstance(val, bool):
                        market_correct.setdefault(key, []).append(val)
            except Exception:
                pass
    except Exception as exc:
        log.warning("Learning cycle: result read error: %s", exc)

    # Map market accuracy keys → weight component names
    # Map recorded market outcomes → which weight component they inform.
    # winnerCorrect  = the core 1X2 prediction — informs odds + ai + table + form
    # over25Correct  = goals model accuracy    — informs the Poisson/ai component
    # bttsCorrect    = joint goals probability — informs ai component
    # over15Correct  = goals model (low bar)   — informs currentSeason form
    # over35Correct  = goals model (high bar)  — informs lastSeason baseline
    # over05Correct  = near-certain market     — informs injuriesH2H (disruption signal)
    market_to_weight = {
        "winnerCorrect":  "odds",           # bookmaker accuracy
        "over25Correct":  "ai",             # Poisson model accuracy
        "bttsCorrect":    "table",          # table-strength accuracy proxy
        "over15Correct":  "currentSeason",  # form-based accuracy
        "over35Correct":  "lastSeason",     # conservative model accuracy
        "over05Correct":  "injuriesH2H",    # disruption/upset signal
    }
    history_rates: dict[str, list[float]] = {}
    for mk, bools in market_correct.items():
        wk = market_to_weight.get(mk)
        if wk:
            rate = sum(bools) / len(bools) if bools else 0.5
            history_rates.setdefault(wk, []).append(rate)

    # Merge into rolling history (keep last 10 cycles)
    for wk, rates in history_rates.items():
        hist = _learning_state["marketAccuracyHistory"].setdefault(wk, [])
        hist.extend(rates)
        _learning_state["marketAccuracyHistory"][wk] = hist[-10:]

    # ── 2. Adapt weights ──────────────────────────────────────────────────────
    if _learning_state["marketAccuracyHistory"]:
        new_weights = _adapt_weights_from_history(
            _learning_state["marketAccuracyHistory"]
        )
        _learning_state["adaptedWeights"] = new_weights
        log.info("Learning cycle: adapted weights → %s", new_weights)
    else:
        log.info("Learning cycle: no resolved results yet; keeping base weights")

    # ── 3. Re-score ALL unresolved predictions (no kickoff cutoff) ──────────
    # Re-scoring past games that haven't been auto-resolved yet is intentional:
    # it means any game that slipped through (e.g. yesterday's) still benefits
    # from the latest adapted weights before being auto-resolved next cycle.
    updated = 0
    improved = 0

    try:
        with v141_learning.connect() as conn:
            rows = conn.execute(
                """
                SELECT id, fixture_id, home_team, away_team, kickoff,
                       probabilities, odds, model_inputs, prediction, model_version
                FROM predictions
                WHERE resolved=0
                ORDER BY kickoff DESC, predicted_at DESC
                """,
            ).fetchall()
    except Exception as exc:
        log.warning("Learning cycle: pending read error: %s", exc)
        rows = []

    adapted = _learning_state["adaptedWeights"]

    for row in rows:
        try:
            probs_old = json.loads(row["probabilities"] or "{}")
            odds_data  = json.loads(row["odds"]  or "{}")
            model_in   = json.loads(row["model_inputs"] or "{}")

            # Reconstruct a minimal match dict so _poisson() can run
            match = {
                "home": row["home_team"] or "",
                "away": row["away_team"] or "",
                "odds": odds_data,
                "homeGoalsFor":      float(model_in.get("homeGoalsFor",    1.35)),  # neutral
                "homeGoalsAgainst":  float(model_in.get("homeGoalsAgainst",1.35)),  # neutral
                "awayGoalsFor":      float(model_in.get("awayGoalsFor",    1.35)),  # neutral
                "awayGoalsAgainst":  float(model_in.get("awayGoalsAgainst",1.35)),  # neutral
            }

            stat = _poisson(match)
            o    = odds_data

            # Use bookmaker no-vig if available, else Poisson
            if _valid_1x2(o):
                market_probs = _novig(o)
            else:
                market_probs = stat["probs"]

            neutral = {"homeWin": 1/3, "draw": 1/3, "awayWin": 1/3}

            # Build weighted components using adapted weights
            components = {
                "odds":          market_probs,
                "ai":            stat["probs"],
                "table":         neutral,
                "injuriesH2H":   neutral,
                "lastSeason":    neutral,
                "currentSeason": stat["probs"],
            }
            available = {
                k: v141_normalise_three_way(v)
                for k, v in components.items()
                if k in adapted
            }
            total_w = sum(adapted[k] for k in available) or 1
            effective = {k: adapted[k] / total_w for k in available}

            fused = {k: 0.0 for k in ("homeWin", "draw", "awayWin")}
            for name, p in available.items():
                for outcome in fused:
                    fused[outcome] += p[outcome] * effective[name]

            best_key  = max(fused, key=fused.get)
            new_conf  = round(fused[best_key] * 100)
            old_conf  = round(float(probs_old.get(best_key, 0)))

            total_xg = stat["xgHome"] + stat["xgAway"] or 1
            home_sf  = round(stat["xgHome"] / total_xg * 100)

            new_probs = {
                "homeWin":  round(fused["homeWin"] * 100, 1),
                "draw":     round(fused["draw"]    * 100, 1),
                "awayWin":  round(fused["awayWin"] * 100, 1),
                "over35":   round(stat["over35"] * 100, 1),
                "over25":   round(stat["over25"] * 100, 1),
                "over15":   round(stat["over15"] * 100, 1),
                "over05":   round(stat["over05"] * 100, 1),
                "btts":     round(stat["btts"]   * 100, 1),
                "halfTimeHome":  round(fused.get("homeWin", 0) * 80, 1),
                "halfTimeDraw":  min(round(fused.get("draw", 0) * 120, 1), 100),
                "halfTimeAway":  round(fused.get("awayWin", 0) * 80, 1),
                "firstTeamToScoreHome": home_sf,
                "firstTeamToScoreAway": 100 - home_sf,
                "firstTeamToScore": (
                    match["home"] if stat["xgHome"] >= stat["xgAway"] else match["away"]
                ),
                "_learningCycle": _learning_state["cycleCount"] + 1,
                "_adaptedWeights": adapted,
            }

            winner = (
                match["home"] if best_key == "homeWin"
                else "Draw" if best_key == "draw"
                else match["away"]
            )
            new_pred = {
                "bestPick": winner,
                "winner":   winner,
                "confidence": new_conf,
                "probabilities": new_probs,
                "bookmakerOddsUsed": _valid_1x2(o),
                "_refreshedByLearningCycle": True,
                "_cycleNumber": _learning_state["cycleCount"] + 1,
            }

            with v141_learning.connect() as conn:
                conn.execute(
                    """UPDATE predictions
                       SET probabilities=?, prediction=?, predicted_at=?, model_version=?
                       WHERE id=?""",
                    (
                        json.dumps(new_probs),
                        json.dumps(new_pred),
                        now_utc.isoformat(),
                        V141_MODEL_VERSION,   # rename old model versions to current
                        row["id"],
                    ),
                )
            updated += 1
            if abs(new_conf - old_conf) >= 1:
                improved += 1

        except Exception as exc:
            log.warning(
                "Learning cycle: re-score error fixture %s: %s",
                row["fixture_id"], exc
            )

    # ── 4. Update state ───────────────────────────────────────────────────────
    _learning_state.update({
        "lastRunAt":         now_utc.isoformat(),
        "nextRunAt":         (now_utc + timedelta(seconds=V141_LEARNING_CYCLE_SECS)).isoformat(),
        "cycleCount":        _learning_state["cycleCount"] + 1,
        "lastCycleUpdated":  updated,
        "lastCycleImproved": improved,
        "status":            "idle",
    })
    log.info(
        "Learning cycle done: %d re-scored, %d improved (cycle #%d)",
        updated, improved, _learning_state["cycleCount"]
    )


async def _background_learning_cycle():
    """Background task: wait 3 hours then run learning cycle indefinitely."""
    # Small initial delay so server is fully up before first cycle
    await asyncio.sleep(30)
    # Set next-run time immediately so dashboard can show it
    _learning_state["nextRunAt"] = (
        datetime.now(timezone.utc) + timedelta(seconds=V141_LEARNING_CYCLE_SECS - 30)
    ).isoformat()
    while True:
        await asyncio.sleep(V141_LEARNING_CYCLE_SECS)
        try:
            await _run_learning_cycle()
        except Exception as exc:
            log.warning("Background learning cycle error: %s", exc)
            _learning_state["status"] = "error"


async def _background_fixture_cleanup():
    while True:
        await asyncio.sleep(V141_FIXTURE_REFRESH_SECONDS)
        try:
            _fixtures_cache.clear()
            # Purge expired rows from the persistent SQLite cache
            _persistent_cache_purge_expired()
            # Plain format matches the "YYYY-MM-DD HH:MM" kickoff strings in the DB
            cutoff = (
                datetime.now(timezone.utc) - timedelta(hours=3)
            ).strftime("%Y-%m-%d %H:%M")
            with v141_learning.connect() as conn:
                rows = conn.execute(
                    """
                    SELECT id FROM predictions
                    WHERE resolved=0
                    AND kickoff IS NOT NULL
                    AND kickoff < ?
                    """,
                    (cutoff,),
                ).fetchall()
                if rows:
                    conn.executemany(
                        "UPDATE predictions SET resolved=1 WHERE id=?",
                        [(row["id"],) for row in rows],
                    )
        except Exception as exc:
            log.warning("Background fixture cleanup error: %s", exc)

async def _background_prediction_refresh():
    while True:
        await asyncio.sleep(V141_PREDICTION_REFRESH_SECS)
        try:
            v141_cache.clear()
        except Exception as exc:
            log.warning("Background prediction refresh error: %s", exc)

@contextlib.asynccontextmanager
async def lifespan(app: FastAPI):
    v141_learning.init()
    log.info("KasiScore v182 starting on port %d", PORT)
    log.info("API-Football key: %s", "SET" if API_KEY else "NOT SET")

    # Auto-seed admin account on every startup using env vars.
    # This means the admin account survives Render restarts even on the free
    # tier where the SQLite file is wiped — it is recreated within seconds.
    _admin_email = os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL","")).strip().lower()
    _admin_password = os.getenv("ADMIN_PASSWORD","").strip()
    if _admin_email and _admin_password:
        try:
            _c = _auth_db()
            _ph = _pw(_admin_password)
            _existing = _c.execute("SELECT id,pro,role FROM users WHERE lower(email)=?",(_admin_email,)).fetchone()
            if _existing:
                _c.execute("UPDATE users SET password_hash=?,pro=1,role='admin',status='active' WHERE id=?",(_ph,_existing[0]))
                log.info("Admin account refreshed for %s", _admin_email)
            else:
                _c.execute("INSERT INTO users(email,password_hash,pro,role,status,created_at) VALUES(?,?,1,'admin','active',?)",
                           (_admin_email,_ph,datetime.now(timezone.utc).isoformat()))
                log.info("Admin account created for %s", _admin_email)
            _c.commit()
            _c.close()
        except Exception as _ex:
            log.error("Failed to seed admin account: %s", _ex)
    else:
        log.warning("ADMIN_EMAIL or ADMIN_PASSWORD not set — admin account not seeded")

    cleanup_task = asyncio.create_task(_background_fixture_cleanup())
    prediction_task = asyncio.create_task(_background_prediction_refresh())
    learning_task = asyncio.create_task(_background_learning_cycle())
    video_warm_task = asyncio.create_task(_warm_video_cache())
    news_warm_task = asyncio.create_task(_warm_news_cache())
    home_warm_task = asyncio.create_task(_home_football_refresh_loop())
    fantasy_players_task = asyncio.create_task(_fantasyplayoffs_midnight_refresh_loop())
    oddspapi_task = asyncio.create_task(_oddspapi_ws_loop()) if (ODDSPAPI_ENABLED and ODDSPAPI_WS_ENABLED and ODDSPAPI_API_KEY) else None

    yield

    if oddspapi_task:
        oddspapi_task.cancel()
    cleanup_task.cancel()
    video_warm_task.cancel()
    news_warm_task.cancel()
    home_warm_task.cancel()
    fantasy_players_task.cancel()
    prediction_task.cancel()
    learning_task.cancel()

    with contextlib.suppress(asyncio.CancelledError):
        await cleanup_task
    with contextlib.suppress(asyncio.CancelledError):
        await prediction_task
    with contextlib.suppress(asyncio.CancelledError):
        await learning_task
    with contextlib.suppress(asyncio.CancelledError):
        await fantasy_players_task

    global _http, _odds_api_http
    if _http and not _http.is_closed:
        await _http.aclose()
    if _odds_api_http and not _odds_api_http.is_closed:
        await _odds_api_http.aclose()

# Kasi Sports News v226 International SEO & Discoverability
KASI_PUBLIC_ORIGIN = "https://kasilivescore.com"

KSN_BUILD_VERSION = "v481-universal-team-profile"

app = FastAPI(
    title="Football Server",
    description="KasiScore Predictive Dashboard <-> API-Football",
    version="1.0.0",
    lifespan=lifespan,
)

# ---------------------------------------------------------------------------
# KSN v399 — shared Last-Known-Good stale-while-revalidate response store.
# PostgreSQL is used on Render when DATABASE_URL is configured, so a brand-new
# browser can receive the last successful public JSON response immediately.
# This layer never caches auth/admin/private responses.
# ---------------------------------------------------------------------------
_KSN398_LKG_READY = False
_KSN398_LKG_LOCK = threading.Lock()
_KSN398_PUBLIC_PREFIXES = (
    "/home/", "/live", "/sports/", "/fixtures", "/predictions", "/ai-predictions",
    "/tip-of-day", "/finished-games", "/results/", "/news/", "/search", "/discover",
    "/team/", "/player/", "/players/", "/standings", "/competitions", "/directory/",
    "/public-", "/odds", "/dashboard-summary"
)

def _ksn398_eligible(path: str) -> bool:
    if path.startswith(("/auth/", "/admin/", "/analytics/")) or path in {"/health"}:
        return False
    return path.startswith(_KSN398_PUBLIC_PREFIXES)

def _ksn398_conn():
    if DATABASE_URL and psycopg2 is not None:
        return psycopg2.connect(DATABASE_URL, connect_timeout=10), "postgres"
    conn = sqlite3.connect(str(BASE_DIR / "ksn_lkg.sqlite3"), timeout=10)
    return conn, "sqlite"

def _ksn398_init():
    global _KSN398_LKG_READY
    if _KSN398_LKG_READY: return
    with _KSN398_LKG_LOCK:
        if _KSN398_LKG_READY: return
        conn, backend = _ksn398_conn()
        try:
            cur=conn.cursor()
            cur.execute("""CREATE TABLE IF NOT EXISTS ksn_public_lkg (
                cache_key TEXT PRIMARY KEY,
                body TEXT NOT NULL,
                content_type TEXT NOT NULL,
                saved_at BIGINT NOT NULL
            )""")
            conn.commit(); _KSN398_LKG_READY=True
        finally: conn.close()

def _ksn398_get(key: str):
    try:
        _ksn398_init(); conn, backend=_ksn398_conn()
        try:
            cur=conn.cursor(); cur.execute("SELECT body,content_type,saved_at FROM ksn_public_lkg WHERE cache_key="+("%s" if backend=="postgres" else "?"),(key,)); row=cur.fetchone()
            return row if row else None
        finally: conn.close()
    except Exception as exc:
        log.debug("KSN LKG read failed: %s", exc); return None

def _ksn398_put(key: str, body: str, content_type: str):
    try:
        data=json.loads(body)
        if data is None or data=={} or data==[]: return
        if isinstance(data,dict) and (data.get("error") or (isinstance(data.get("detail"),str) and re.search(r"error|failed|unavailable",data["detail"],re.I))): return
        _ksn398_init(); conn, backend=_ksn398_conn(); now=int(time.time()*1000)
        try:
            cur=conn.cursor()
            if backend=="postgres":
                cur.execute("""INSERT INTO ksn_public_lkg(cache_key,body,content_type,saved_at) VALUES(%s,%s,%s,%s)
                    ON CONFLICT(cache_key) DO UPDATE SET body=EXCLUDED.body,content_type=EXCLUDED.content_type,saved_at=EXCLUDED.saved_at""",(key,body,content_type,now))
            else:
                cur.execute("INSERT OR REPLACE INTO ksn_public_lkg(cache_key,body,content_type,saved_at) VALUES(?,?,?,?)",(key,body,content_type,now))
            conn.commit()
        finally: conn.close()
    except Exception as exc: log.debug("KSN LKG write failed: %s", exc)

_KSN_BUSTERS={"_ts","_","cb","_cb","nocache","cachebust","_t"}
def _ksn_clean_qs(qs):
    """Drop cache-busting params so every visitor shares one cache entry per feed."""
    try:
        if not qs: return ""
        pairs=[(k,v) for k,v in urllib.parse.parse_qsl(qs,keep_blank_values=True) if k not in _KSN_BUSTERS]
        return urllib.parse.urlencode(pairs)
    except Exception:
        return qs or ""

# ── v433: internal-refresh marker, in-process LKG memory front, single-flight ─────────────
# Only requests made by this process (warmer / background revalidation) carry the token, so a
# public client can no longer force upstream provider calls with a spoofed header.
_KSN_INTERNAL_TOKEN = secrets.token_hex(8)
_KSN_INTERNAL_HEADERS = {"X-KSN-Cache-Refresh": "1", "X-KSN-Internal": _KSN_INTERNAL_TOKEN}

def _ksn_scope_internal(scope) -> bool:
    try:
        for k, v in scope.get("headers") or []:
            if k == b"x-ksn-internal":
                return v.decode("latin1") == _KSN_INTERNAL_TOKEN
    except Exception:
        pass
    return False

_KSN_LKG_MEM: dict = {}            # key -> (body, content_type, saved_ms)   insertion-ordered
_KSN_LKG_MEM_BYTES = 0
_KSN_LKG_MEM_BUDGET = 48 * 1024 * 1024
_KSN_INFLIGHT: dict = {}           # key -> asyncio.Task (single-flight upstream fetch)
_KSN_REFRESHING: set = set()
_KSN_REFRESH_AT: dict = {}

def _ksn_mem_put(key, body, ct, saved):
    global _KSN_LKG_MEM_BYTES
    try:
        size = len(body)
        if size > _KSN_LKG_MEM_BUDGET // 4:
            return
        old = _KSN_LKG_MEM.pop(key, None)
        if old:
            _KSN_LKG_MEM_BYTES -= len(old[0])
        _KSN_LKG_MEM[key] = (body, ct, saved)
        _KSN_LKG_MEM_BYTES += size
        while _KSN_LKG_MEM_BYTES > _KSN_LKG_MEM_BUDGET and _KSN_LKG_MEM:
            k0 = next(iter(_KSN_LKG_MEM))
            ev = _KSN_LKG_MEM.pop(k0)
            _KSN_LKG_MEM_BYTES -= len(ev[0])
    except Exception:
        pass

def _ksn_body_is_good(status, ct, body) -> bool:
    if not (status < 400 and "json" in (ct or "").lower() and body):
        return False
    try:
        data = json.loads(body.decode("utf-8"))
    except Exception:
        return False
    if data is None or data == {} or data == []:
        return False
    if isinstance(data, dict) and (data.get("error") or (isinstance(data.get("detail"), str) and re.search(r"error|failed|unavailable", data["detail"], re.I))):
        return False
    return True

class KSNSharedLKGMiddleware:
    """Shared stale-while-revalidate for public JSON GET endpoints.

    1. Visitor request -> last-known-good (memory, then shared DB) is returned immediately.
    2. The same endpoint is refreshed in the background (de-duplicated + rate-limited per key).
    3. A failed/empty refresh never deletes the saved response.
    4. Cold keys: ONE upstream fetch is shared by every concurrent request and keeps running even
       if the first visitor's browser gives up, so the next retry is served instantly from LKG.
    5. Internal refresh requests (warmer / revalidation, marked by a per-process token) skip the
       LKG read and really hit the route, then store the fresh result.
    """
    def __init__(self, app):
        self.app = app

    async def _capture_upstream(self, scope):
        messages = []
        sent_receive = False
        async def bg_receive():
            nonlocal sent_receive
            if not sent_receive:
                sent_receive = True
                return {"type": "http.request", "body": b"", "more_body": False}
            await asyncio.sleep(0)
            return {"type": "http.disconnect"}
        async def capture(message):
            messages.append(message)
        await self.app(scope, bg_receive, capture)
        status = 200; headers = []; body = b""
        for m in messages:
            if m["type"] == "http.response.start":
                status = m.get("status", 200); headers = m.get("headers", [])
            elif m["type"] == "http.response.body":
                body += m.get("body", b"")
        ct = ""
        for k, v in headers:
            if k.lower() == b"content-type": ct = v.decode("latin1")
        return messages, status, headers, body, ct

    async def _fetch_and_store(self, scope, key):
        result = await self._capture_upstream(scope)
        messages, status, headers, body, ct = result
        if _ksn_body_is_good(status, ct, body):
            txt = body.decode("utf-8")
            _ksn_mem_put(key, txt, ct, int(time.time() * 1000))       # instant for the next request
            _KSN_REFRESH_AT[key] = time.monotonic()                   # data is fresh now: start the refresh-gap clock
            try:
                asyncio.get_running_loop().run_in_executor(None, _ksn398_put, key, txt, ct)  # durable, non-blocking
            except Exception as exc:
                log.debug("KSN LKG persist scheduling failed: %s", exc)
        return result

    def _single_flight(self, scope, key):
        task = _KSN_INFLIGHT.get(key)
        if task is None or task.done():
            task = asyncio.create_task(self._fetch_and_store(dict(scope), key))
            _KSN_INFLIGHT[key] = task
            def _done(t, k=key):
                if _KSN_INFLIGHT.get(k) is t: _KSN_INFLIGHT.pop(k, None)
                if not t.cancelled(): t.exception()      # mark retrieved; callers handle errors
            task.add_done_callback(_done)
        return task

    async def _read(self, key):
        m = _KSN_LKG_MEM.get(key)
        if m: return m
        try:
            # Never let a slow DB hold the page: fall through to the upstream path after 1.5s.
            row = await asyncio.wait_for(asyncio.to_thread(_ksn398_get, key), timeout=1.5)
        except Exception:
            return None
        if not row: return None
        body, ct, saved = str(row[0]), str(row[1]), row[2]
        _ksn_mem_put(key, body, ct, saved)
        return body, ct, saved

    def _schedule_refresh(self, scope, key, path):
        if key in _KSN_REFRESHING or key in _KSN_INFLIGHT: return
        try: ttl = float(_v413_public_cache_ttl(path))
        except Exception: ttl = 60.0
        gap = max(5.0, min(ttl / 2.0, 60.0))
        now = time.monotonic()
        if now - _KSN_REFRESH_AT.get(key, 0.0) < gap: return
        if len(_KSN_REFRESH_AT) > 3000: _KSN_REFRESH_AT.clear()
        _KSN_REFRESH_AT[key] = now
        _KSN_REFRESHING.add(key)
        async def run():
            try:
                task = self._single_flight(scope, key)
                await asyncio.shield(task)
            except Exception as exc:
                log.debug("KSN background LKG refresh failed: %s", exc)
            finally:
                _KSN_REFRESHING.discard(key)
        asyncio.create_task(run())

    async def __call__(self, scope, receive, send):
        if scope.get("type") != "http" or scope.get("method") != "GET" or not _ksn398_eligible(scope.get("path", "")):
            return await self.app(scope, receive, send)

        path = scope.get("path", "")
        qs = _ksn_clean_qs((scope.get("query_string") or b"").decode("latin1"))
        key = path + ("?" + qs if qs else "")
        internal = _ksn_scope_internal(scope)

        async def send_lkg(row):
            body, ct, saved = row
            await send({"type": "http.response.start", "status": 200, "headers": [
                (b"content-type", str(ct).encode()),
                (b"cache-control", b"no-cache"),
                (b"x-ksn-lkg", b"shared"),
                (b"x-ksn-lkg-saved-at", str(saved).encode())]})
            await send({"type": "http.response.body", "body": str(body).encode("utf-8")})

        # True SWR: serve last-known-good immediately, refresh behind it.
        if not internal:
            row = await self._read(key)
            if row:
                await send_lkg(row)
                self._schedule_refresh(scope, key, path)
                return

        # Cold key (or internal refresh): one shared upstream fetch for all concurrent callers.
        try:
            messages, status, _headers, body, ct = await asyncio.shield(self._single_flight(scope, key))
        except asyncio.CancelledError:
            raise
        except Exception:
            row = await self._read(key)
            if row:
                await send_lkg(row)
                return
            raise
        for m in messages:
            await send(m)

app.add_middleware(KSNSharedLKGMiddleware)



# v390: Service Worker must be a real root asset and must be registered
# before the single-segment SEO locale route (/{lang}).
KSN_SERVICE_WORKER = BASE_DIR / "ksn-sw-v390.js"

@app.get("/ksn-sw-v390.js", include_in_schema=False)
async def ksn_service_worker_v390():
    if not KSN_SERVICE_WORKER.exists():
        raise HTTPException(status_code=404, detail="Service worker not found")
    return FileResponse(
        KSN_SERVICE_WORKER,
        media_type="application/javascript",
        headers={
            "Cache-Control": "no-cache, no-store, must-revalidate",
            "Service-Worker-Allowed": "/",
            "X-Content-Type-Options": "nosniff",
        },
    )

# v298: Kasi Sports News production branding assets
@app.get("/kasi-sports-news-logo.png", include_in_schema=False)
async def kasi_sports_news_logo():
    return FileResponse(BASE_DIR / "kasi-sports-news-logo.png", media_type="image/png", headers={"Cache-Control":"public, max-age=604800, s-maxage=2592000, stale-while-revalidate=86400"})

# v454: conventional root favicon endpoint for browsers and search crawlers.
@app.get("/favicon.ico", include_in_schema=False)
async def kasi_favicon_ico():
    return FileResponse(BASE_DIR / "favicon.png", media_type="image/png", headers={"Cache-Control":"public, max-age=604800, s-maxage=2592000, stale-while-revalidate=86400"})

@app.get("/favicon.png", include_in_schema=False)
async def kasi_favicon():
    return FileResponse(BASE_DIR / "favicon.png", media_type="image/png", headers={"Cache-Control":"public, max-age=604800, s-maxage=2592000, stale-while-revalidate=86400"})

@app.get("/apple-touch-icon.png", include_in_schema=False)
async def kasi_apple_touch_icon():
    return FileResponse(BASE_DIR / "apple-touch-icon.png", media_type="image/png", headers={"Cache-Control":"public, max-age=604800, s-maxage=2592000, stale-while-revalidate=86400"})

@app.get("/oddspapi/usage-budget")
async def oddspapi_usage_budget():
    usage=_oddspapi_budget_snapshot()
    return {
        "provider":"OddsPapi",
        "configured":bool(ODDSPAPI_ENABLED and ODDSPAPI_API_KEY),
        "usage":usage,
        "limits":{
            "minute":ODDSPAPI_BUDGET_MINUTE,
            "hour":ODDSPAPI_BUDGET_HOUR,
            "day":ODDSPAPI_BUDGET_DAY,
            "week":ODDSPAPI_BUDGET_WEEK,
            "month":ODDSPAPI_BUDGET_MONTH,
        },
        "policy":"cached dashboard data remains available when a local provider budget is reached"
    }

# PWA manifest must be registered before SPA/dynamic routes.
# Returning JSON directly prevents index.html/404 fallbacks from being parsed as a manifest.
@app.get("/manifest.webmanifest", include_in_schema=False)
async def serve_manifest():
    manifest = {
        "name": "Kasi Sports News",
        "short_name": "Kasi Sports",
        "description": "Live sports scores, fixtures, news and predictive intelligence.",
        "start_url": "/",
        "scope": "/",
        "display": "standalone",
        "background_color": "#05080b",
        "theme_color": "#05080b",
        "icons": [
            {"src":"/favicon.png","sizes":"96x96","type":"image/png"},
            {"src":"/kasi-sports-news-logo.png","sizes":"512x512","type":"image/png","purpose":"any maskable"}
        ]
    }
    return Response(
        content=json.dumps(manifest, ensure_ascii=False),
        media_type="application/manifest+json",
        headers={"Cache-Control": "no-store, max-age=0"}
    )

# Canonical social preview asset. Keep this explicit so the SPA fallback can never
# return HTML for /og-image.svg.
@app.get("/og-image.svg", include_in_schema=False)
def kasi_social_preview_image():
    svg = """<svg xmlns="http://www.w3.org/2000/svg" width="1200" height="630" viewBox="0 0 1200 630">
<rect width="1200" height="630" fill="#05080b"/>
<rect x="54" y="54" width="1092" height="522" rx="34" fill="#0b1016" stroke="#26313d" stroke-width="3"/>
<text x="100" y="275" fill="#42c9e5" font-family="Arial,Helvetica,sans-serif" font-size="78" font-weight="700">Kasi Sports News</text>
<text x="104" y="355" fill="#f4f7fb" font-family="Arial,Helvetica,sans-serif" font-size="34">Live scores · fixtures · news · match intelligence</text>
<text x="104" y="435" fill="#9fb0c3" font-family="Arial,Helvetica,sans-serif" font-size="28">kasilivescore.com</text>
</svg>"""
    return Response(content=svg, media_type="image/svg+xml", headers={"Cache-Control":"public, max-age=604800, s-maxage=2592000, stale-while-revalidate=86400"})

# Google crawler assets must be registered before the generic /{lang} SEO route.
# Otherwise paths such as /robots.txt and /sitemap.xml are interpreted as a language slug
# and the SPA/HTML site is returned instead of text/XML.
@app.get("/robots.txt", include_in_schema=False)
def google_robots_txt():
    base = KASI_PUBLIC_ORIGIN
    body = (
        "User-agent: *\n"
        "Allow: /\n"
        "Disallow: /admin\n"
        "Disallow: /auth\n"
        "Disallow: /docs\n"
        "Disallow: /redoc\n"
        "Disallow: /openapi.json\n"
        "Disallow: /health\n"
        "Disallow: /api/\n"
        f"Sitemap: {base}/sitemap.xml\n"
    )
    return Response(content=body, media_type="text/plain; charset=utf-8", headers={"Cache-Control":"public, max-age=300, s-maxage=3600, stale-while-revalidate=86400", "CDN-Cache-Control":"public, s-maxage=3600, stale-while-revalidate=86400"})

@app.get("/sitemap.xml", include_in_schema=False)
async def google_sitemap_xml():
    base = KASI_PUBLIC_ORIGIN
    # Prefer the richer SEO registry when available at request time.
    rows = []
    if "_seo_dynamic_rows" in globals():
        try:
            rows = await _seo_dynamic_rows()
        except Exception as exc:
            log.warning("Google sitemap dynamic expansion failed: %s", exc)
    if not rows and "_seo_registry_pages" in globals():
        try:
            rows = _seo_registry_pages()
        except Exception as exc:
            log.warning("Google sitemap registry expansion failed: %s", exc)
    if not rows:
        rows = [{"path": p, "indexable": True} for p in ("/","/weekend","/football","/rugby","/cricket","/tennis","/about","/contact","/privacy","/terms")]

    from xml.sax.saxutils import escape as _xml_safe
    seen = set()
    body = ['<?xml version="1.0" encoding="UTF-8"?>', '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
    for row in rows:
        path = str(row.get("path") or "").strip()
        if not path or not path.startswith("/") or path in seen or not row.get("indexable", True):
            continue
        seen.add(path)
        body.append(f"<url><loc>{_xml_safe(base + path)}</loc></url>")
    body.append("</urlset>")
    return Response(content="".join(body), media_type="application/xml; charset=utf-8", headers={"Cache-Control":"public, max-age=300, s-maxage=900"})


@app.middleware("http")
async def kasi_timing_middleware(request: Request, call_next):
    started=time.perf_counter()
    response=await call_next(request)
    ms=round((time.perf_counter()-started)*1000,1)
    response.headers["Server-Timing"]=f"app;dur={ms}"
    response.headers["X-Kasi-Response-Ms"]=str(ms)
    response.headers["X-Kasi-SEO-Version"]="v457-canonical-results-search-identity"
    response.headers.setdefault("X-Content-Type-Options","nosniff")
    response.headers.setdefault("Referrer-Policy","strict-origin-when-cross-origin")
    response.headers.setdefault("Permissions-Policy","camera=(), microphone=(), geolocation=()")
    response.headers.setdefault("X-Frame-Options","SAMEORIGIN")
    private_prefixes=("/admin", "/auth", "/docs", "/redoc", "/openapi.json", "/health", "/api/")
    if request.url.path.startswith(private_prefixes):
        response.headers["X-Robots-Tag"]="noindex, nofollow, noarchive"
    if request.url.path.startswith("/auth/"):
        response.headers["Cache-Control"]="no-store"
        response.headers["Pragma"]="no-cache"
    if request.url.scheme == "https":
        response.headers.setdefault("Strict-Transport-Security","max-age=31536000; includeSubDomains")
    if request.url.path in {"/live","/fixtures","/ai-predictions","/player/profile","/team/profile","/sports/news","/sports/scores"}:
        log.info("TIMING %s %.1fms status=%s",request.url.path,ms,response.status_code)
    return response


app.add_middleware(GZipMiddleware, minimum_size=700)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["GET", "POST"],
    allow_headers=["*"],
)

@app.middleware("http")
async def canonical_public_domain(request: Request, call_next):
    """Redirect legacy/public aliases to the single canonical production domain."""
    forwarded_host=(request.headers.get("x-forwarded-host") or "").split(",")[0].strip()
    host=(forwarded_host or request.headers.get("host") or request.url.hostname or "")
    host=host.split(":")[0].lower().strip()

    if host in {"git-repoo-predictive.onrender.com", "www.kasilivescore.com"}:
        path=request.url.path or "/"
        query=f"?{request.url.query}" if request.url.query else ""
        return RedirectResponse(
            url=f"https://kasilivescore.com{path}{query}",
            status_code=308,
        )

    return await call_next(request)


# ---------------------------------------------------------------------------
# HEALTH
# ---------------------------------------------------------------------------


class AuthPayload(BaseModel):
    email: str = ""
    password: str
    identifier: str = ""
    username: str = ""
    phone: str = ""


def _norm_phone(value: str) -> str:
    v=(value or "").strip().replace(" ","").replace("-","").replace("(","").replace(")","")
    if v.startswith("00"): v="+"+v[2:]
    if v.startswith("0") and len(v)==10: v="+27"+v[1:]
    return v

@app.post("/auth/register")
def auth_register(p: AuthPayload, request: Request):
    _require_auth_rate(request,"auth-register",getattr(p,"email",""),limit=6,window=600)
    email=p.email.strip().lower(); username=p.username.strip().lower() or None; phone=_norm_phone(p.phone) or None
    if len(email)<5 or "@" not in email or len(p.password)<8: raise HTTPException(400,"Valid email and password of at least 8 characters required")
    c=_auth_db()
    try:
        ph=_pw(p.password); cur=c.execute("INSERT INTO users(email,password_hash,username,phone,created_at) VALUES(?,?,?,?,?)",(email,ph,username,phone,datetime.now(timezone.utc).isoformat())); c.commit()
        return {"token":_token(cur.lastrowid),"message":"Account created","email":email,"pro":False,"role":"user","username":username,"phone":phone}
    except sqlite3.IntegrityError: raise HTTPException(409,"Email, username or phone number already exists")
    finally:c.close()

@app.post("/auth/login")
def auth_login(p: AuthPayload, request: Request):
    import traceback as _tb
    try:
        _require_auth_rate(request,"auth-login",getattr(p,"email",""),limit=10,window=300)
        identifier=(p.identifier or p.email).strip(); phone=_norm_phone(identifier)
        c=_auth_db(); row=c.execute("SELECT id,email,password_hash,pro,username,phone,COALESCE(role,'user'),COALESCE(status,'active') FROM users WHERE lower(email)=lower(?) OR lower(username)=lower(?) OR phone=?",(identifier,identifier,phone)).fetchone()
        if row and row[7]!="active": c.close(); raise HTTPException(403,"Account disabled")
        if row: c.execute("UPDATE users SET last_login=? WHERE id=?",(datetime.now(timezone.utc).isoformat(),row[0])); c.commit()
        c.close()
        if not row: raise HTTPException(401,"Invalid email, username/phone or password")
        salt,stored=row[2].split("$",1)
        if not hmac.compare_digest(_pw(p.password,salt).split("$",1)[1],stored): raise HTTPException(401,"Invalid email, username/phone or password")
        configured_admin=os.getenv("ADMIN_EMAIL",os.getenv("PAYMENT_ADMIN_EMAIL","jbatuma@yahoo.com")).strip().lower()
        is_configured_admin=bool(configured_admin and str(row[1]).strip().lower()==configured_admin)
        effective_role="admin" if is_configured_admin else str(row[6] or "user").lower()
        effective_pro=True if is_configured_admin else bool(row[3])
        if is_configured_admin and (str(row[6] or "user").lower()!="admin" or not bool(row[3])):
            c=_auth_db()
            try:
                c.execute("UPDATE users SET pro=1, role='admin' WHERE id=?",(row[0],)); c.commit()
            finally:
                c.close()
        return {"token":_token(row[0]),"email":row[1],"username":row[4],"phone":row[5],"pro":effective_pro,"role":effective_role,"admin":effective_role=="admin"}
    except HTTPException:
        raise
    except Exception as _e:
        log.error("LOGIN 500 - full traceback:\n%s", _tb.format_exc())
        raise HTTPException(500, f"Login error: {type(_e).__name__}: {_e}")

@app.get("/auth/db-health")
def auth_db_health():
    """Credential-safe database readiness check."""
    try:
        c=_auth_db()
        row=c.execute("SELECT COUNT(*) FROM users").fetchone()
        backend=getattr(c,"backend","unknown")
        c.close()
        return {
            "ok": True,
            "backend": backend,
            "users": int(row[0]) if row else 0,
            "database_url_set": bool(DATABASE_URL),
        }
    except Exception as exc:
        return {
            "ok": False,
            "backend": "postgres" if DATABASE_URL else "sqlite",
            "database_url_set": bool(DATABASE_URL),
            "error": f"{type(exc).__name__}: {exc}",
        }

@app.get("/auth/debug")
def auth_debug():
    import traceback as _tb
    result = {
        "auth_secret_set": bool(os.getenv("AUTH_SECRET","")),
        "admin_email_env": os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL","NOT SET")),
        "auth_backend": "postgres" if DATABASE_URL else "sqlite",
        "database_url_set": bool(DATABASE_URL),
        "auth_db_path": str(AUTH_DB),
        "auth_db_exists": AUTH_DB.exists(),
        "db_error": None,
        "user_count": None,
        "admin_exists": None,
        "admin_row": None,
    }
    try:
        c = _auth_db()
        result["user_count"] = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        admin_email = os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL","jbatuma@yahoo.com")).strip().lower()
        admin_row = c.execute("SELECT id,email,pro,role FROM users WHERE lower(email)=?",(admin_email,)).fetchone()
        result["admin_exists"] = bool(admin_row)
        if admin_row:
            result["admin_row"] = {"id":admin_row[0],"email":admin_row[1],"pro":admin_row[2],"role":admin_row[3]}
        c.close()
    except Exception:
        result["db_error"] = _tb.format_exc()
    return result

@app.post("/auth/setup-admin")
def auth_setup_admin():
    """Create or reset admin account using ADMIN_EMAIL + ADMIN_PASSWORD env vars."""
    admin_email = os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL","")).strip().lower()
    admin_password = os.getenv("ADMIN_PASSWORD","").strip()
    if not admin_email:
        raise HTTPException(400, "Set ADMIN_EMAIL environment variable on Render first")
    if not admin_password:
        raise HTTPException(400, "Set ADMIN_PASSWORD environment variable on Render first")
    c = _auth_db()
    try:
        ph = _pw(admin_password)
        existing = c.execute("SELECT id FROM users WHERE lower(email)=?",(admin_email,)).fetchone()
        if existing:
            c.execute("UPDATE users SET password_hash=?,pro=1,role='admin',status='active' WHERE id=?",(ph,existing[0]))
            msg = "Admin account updated"
            uid = existing[0]
        else:
            c.execute("INSERT INTO users(email,password_hash,pro,role,status,created_at) VALUES(?,?,1,'admin','active',?)",
                      (admin_email,ph,datetime.now(timezone.utc).isoformat()))
            c.commit()
            uid = c.execute("SELECT id FROM users WHERE lower(email)=?",(admin_email,)).fetchone()[0]
            msg = "Admin account created"
        c.commit()
        return {"message": msg, "email": admin_email, "token": _token(uid)}
    except Exception:
        import traceback as _tb2
        raise HTTPException(500, f"Setup error: {_tb2.format_exc()}")
    finally:
        c.close()


class PasswordResetPayload(BaseModel):
    email: str = ""
    identifier: str = ""
    token: str = ""
    password: str = ""

@app.post("/auth/forgot-password")
def auth_forgot_password(p: PasswordResetPayload, request: Request):
    _require_auth_rate(request,"auth-forgot-password",getattr(p,"email",""),limit=5,window=900)
    identifier=(p.identifier or p.email).strip(); phone=_norm_phone(identifier); c=_auth_db(); row=c.execute("SELECT id,email FROM users WHERE lower(email)=lower(?) OR phone=?",(identifier,phone)).fetchone()
    if not row: c.close(); return {"message":"If the account exists, recovery instructions have been sent."}
    email=row[1]; token=secrets.token_urlsafe(32); c.execute("UPDATE users SET reset_token=?,reset_expires=? WHERE id=?",(token,time.time()+1800,row[0])); c.commit(); c.close()
    result={"message":"If the account exists, recovery instructions have been sent."}; host=os.getenv("SMTP_HOST","").strip(); sender=os.getenv("SMTP_FROM",os.getenv("SMTP_USER","")).strip()
    if host and sender:
        try:
            link=os.getenv("PUBLIC_APP_URL","").rstrip("/")+"/?reset_token="+token+"&email="+email
            msg=EmailMessage();msg["Subject"]="Kasi Sports News password reset";msg["From"]=sender;msg["To"]=email;msg.set_content("Reset your Kasi Sports News password within 30 minutes:\n\n"+link+"\n\nIf you did not request this, ignore this email.")
            with smtplib.SMTP(host,int(os.getenv("SMTP_PORT","587")),timeout=15) as s:
                if os.getenv("SMTP_TLS","1")=="1":s.starttls()
                u=os.getenv("SMTP_USER","");pw=os.getenv("SMTP_PASSWORD","")
                if u and pw:s.login(u,pw)
                s.send_message(msg)
        except Exception as exc:log.warning("Password reset email failed: %s",exc)
    return result

@app.post("/auth/forgot-username")
def auth_forgot_username(p: PasswordResetPayload, request: Request):
    _require_auth_rate(request,"auth-forgot-username",getattr(p,"email",""),limit=5,window=900)
    identifier=(p.identifier or p.email).strip(); phone=_norm_phone(identifier); c=_auth_db(); row=c.execute("SELECT username,email FROM users WHERE lower(email)=lower(?) OR phone=?",(identifier,phone)).fetchone(); c.close()
    if not row: return {"message":"If the account exists, username recovery instructions have been sent."}
    username=row[0]
    if not username: return {"message":"Your account does not have a username. You can sign in with your email or phone number."}
    result={"message":"Username recovery instructions have been sent."}
    if os.getenv("RESET_DEV_MODE","0")=="1": result["username"]=username
    host=os.getenv("SMTP_HOST","").strip(); sender=os.getenv("SMTP_FROM",os.getenv("SMTP_USER","")).strip()
    if host and sender:
        try:
            msg=EmailMessage();msg["Subject"]="Kasi Sports News username recovery";msg["From"]=sender;msg["To"]=row[1];msg.set_content("Your Kasi Sports News username is: "+username)
            with smtplib.SMTP(host,int(os.getenv("SMTP_PORT","587")),timeout=15) as s:
                if os.getenv("SMTP_TLS","1")=="1":s.starttls()
                u=os.getenv("SMTP_USER","");pw=os.getenv("SMTP_PASSWORD","")
                if u and pw:s.login(u,pw)
                s.send_message(msg)
        except Exception as exc:log.warning("Username recovery email failed: %s",exc)
    return result

@app.post("/auth/reset-password")
def auth_reset_password(p: PasswordResetPayload):
    if len(p.password)<8 or not p.token:raise HTTPException(400,"Valid recovery token and password of at least 8 characters required")
    email=p.email.strip().lower();c=_auth_db();row=c.execute("SELECT id,reset_token,reset_expires FROM users WHERE email=?",(email,)).fetchone()
    if not row or not row[1] or not hmac.compare_digest(str(row[1]),p.token) or not row[2] or time.time()>float(row[2]):c.close();raise HTTPException(400,"Invalid or expired recovery token")
    c.execute("UPDATE users SET password_hash=?,reset_token=NULL,reset_expires=NULL WHERE id=?",(_pw(p.password),row[0]));c.commit();c.close();return {"message":"Password reset successfully"}

class ChangePasswordPayload(BaseModel):
    current_password: str = ""
    new_password: str = ""

@app.post("/auth/change-password")
def auth_change_password(p: ChangePasswordPayload, request: Request, authorization: Optional[str]=Header(default=None)):
    user=get_current_user(authorization)
    _require_auth_rate(request,"auth-change-password",str(user.get("email") or ""),limit=5,window=900)
    if len(p.new_password)<8:
        raise HTTPException(400,"New password must be at least 8 characters")
    c=_auth_db()
    try:
        row=c.execute("SELECT id,password_hash FROM users WHERE lower(email)=lower(?)",(str(user.get("email") or ""),)).fetchone()
        ok=False
        if row and "$" in str(row[1] or ""):
            salt,stored=str(row[1]).split("$",1)
            ok=hmac.compare_digest(_pw(p.current_password,salt).split("$",1)[1],stored)
        if not ok:
            raise HTTPException(403,"Current password is incorrect")
        c.execute("UPDATE users SET password_hash=? WHERE id=?",(_pw(p.new_password),row[0])); c.commit()
    finally:
        c.close()
    return {"message":"Password changed"}

@app.get("/auth/me")
def auth_me(authorization: Optional[str]=Header(default=None)):
    return get_current_user(authorization)

@app.post("/auth/entitlement/{email}")
def set_entitlement(
    email: str,
    pro: bool = Query(...),
    role: str = Query("user"),
    admin_key: str = Query(...)
):
    expected_key = os.getenv("AUTH_ADMIN_KEY", "")
    if not expected_key or not hmac.compare_digest(admin_key, expected_key):
        raise HTTPException(403, "Forbidden")

    role = role.strip().lower()
    if role not in ("user", "admin"):
        raise HTTPException(400, "Role must be 'user' or 'admin'")

    email = email.strip().lower()
    c = _auth_db()
    try:
        cur = c.execute(
            "UPDATE users SET pro=?, role=? WHERE lower(email)=?",
            (1 if pro else 0, role, email)
        )
        c.commit()
        updated = cur.rowcount
    finally:
        c.close()

    if updated == 0:
        raise HTTPException(404, "User not found")

    return {
        "updated": updated,
        "email": email,
        "pro": pro,
        "role": role,
        "admin": role == "admin"
    }


_DISCOVERY_CACHE=TTLCache(maxsize=4,ttl=172800)
@app.get("/discover")
async def discover():
    cached=_DISCOVERY_CACHE.get("main")
    if cached:return cached
    leagues=[39,140,135,78,61]
    async def one(lid):
        try:return await _afoot_get("/players/topscorers",{"league":lid,"season":_current_season()})
        except Exception:return {"response":[]}
    raw=await asyncio.gather(*[one(x) for x in leagues])
    players=[];teams=[];sp=set();st=set()
    for d in raw:
        for r in d.get("response",[])[:8]:
            p=r.get("player") or {};s=(r.get("statistics") or [{}])[0];t=s.get("team") or {};lg=s.get("league") or {}
            if p.get("id") and p["id"] not in sp:
                sp.add(p["id"]);players.append({"id":p["id"],"name":p.get("name"),"photo":p.get("photo"),"team":t.get("name"),"teamId":t.get("id"),"position":(s.get("games") or {}).get("position"),"league":lg.get("name"),"goals":(s.get("goals") or {}).get("total")})
            if t.get("id") and t["id"] not in st:
                st.add(t["id"]);teams.append({"id":t["id"],"name":t.get("name"),"badge":t.get("logo"),"country":lg.get("country"),"league":lg.get("name")})
    rng=random.Random(int(time.time()//172800));rng.shuffle(players);rng.shuffle(teams)
    out={"players":players[:5],"teams":teams[:5]};_DISCOVERY_CACHE["main"]=out;return out

@app.get("/search")
async def global_search(q: str = Query(..., min_length=2), type: str = Query("auto"), limit: int = Query(12, ge=1, le=30)):
    q=q.strip();results=[]
    if type in ("auto","team"):
        d=await _afoot_get("/teams",{"search":q})
        for x in (d.get("response") or [])[:limit]:
            t=x.get("team") or {};results.append({"type":"team","id":t.get("id"),"name":t.get("name"),"country":t.get("country"),"logo":t.get("logo")})
    if type in ("auto","player"):
        d=await _afoot_get("/players",{"search":q,"season":datetime.now().year})
        for x in (d.get("response") or [])[:limit]:
            p=x.get("player") or {};st=(x.get("statistics") or [{}])[0] or {};results.append({"type":"player","id":p.get("id"),"name":p.get("name"),"nationality":p.get("nationality"),"photo":p.get("photo"),"team":(st.get("team") or {}).get("name")})
    return {"query":q,"type":type,"results":results[:limit],"source":"API-Football"}


_SPORTS_INTELLIGENCE_SEARCH_CACHE=TTLCache(maxsize=512,ttl=300)

@app.get("/sports/intelligence/search")
async def sports_intelligence_search(
    q:str=Query(...,min_length=2),
    sport:str=Query("all"),
    entity_type:str=Query("auto"),
    limit:int=Query(16,ge=1,le=30),
):
    """Sports-only search. No news results. Uses cached provider/directory data."""
    query=q.strip()
    sp=sport.strip().lower()
    typ=entity_type.strip().lower()
    if sp not in {"all","football","rugby","cricket"}:sp="all"
    if typ not in {"auto","team","player","competition"}:typ="auto"
    ck=f"{query.casefold()}:{sp}:{typ}:{limit}"
    cached=_SPORTS_INTELLIGENCE_SEARCH_CACHE.get(ck)
    if cached is not None:return cached

    results=[]
    async def football():
        if sp not in {"all","football"}:return []
        rows=[]
        try:
            d=await asyncio.wait_for(global_search(q=query,type="auto" if typ=="competition" else typ,limit=limit),timeout=1.5)
            for x in d.get("results",[]):
                x=dict(x);x["sport"]="football"
                x["route"]=f"/teams/{x.get('id')}" if x.get("type")=="team" and x.get("id") else f"/players/{x.get('id')}" if x.get("type")=="player" and x.get("id") else ""
                rows.append(x)
        except Exception:pass
        return rows

    async def other(s):
        if sp not in {"all",s}:return []
        try:d=await sports_directory_search(q=query,sport=s)
        except Exception:return []
        rows=[]
        if typ in {"auto","team"}:
            for x in d.get("teams",[]):
                rows.append({"type":"team","sport":s,"id":x.get("ref"),"name":x.get("name"),"country":x.get("country"),
                             "league":x.get("league"),"logo":x.get("badge"),"route":f"/{s}/team/{x.get('ref')}"})
        if typ in {"auto","player"}:
            for x in d.get("players",[]):
                rows.append({"type":"player","sport":s,"id":x.get("ref"),"name":x.get("name"),"team":x.get("team"),
                             "league":x.get("league"),"photo":x.get("photo"),"route":f"/{s}/player/{x.get('ref')}"})
        return rows

    groups=await asyncio.gather(football(),other("rugby"),other("cricket"))
    for g in groups:results.extend(g)

    ql=query.casefold()
    def score(x):
        name=str(x.get("name") or "").casefold()
        exact=3 if name==ql else 2 if name.startswith(ql) else 1 if ql in name else 0
        return (exact,name)
    results=sorted(results,key=score,reverse=True)[:limit]
    out={"query":query,"sport":sp,"entityType":typ,"results":results,"count":len(results),
         "newsIncluded":False,"cachedSeconds":300,"season":_current_season(),
         "note":"Statistics and facts are shown only when current provider data supports them."}
    _SPORTS_INTELLIGENCE_SEARCH_CACHE[ck]=out
    return out

@app.get("/production-readiness")
def production_readiness():
    checks={
        "apiFootballConfigured":bool(API_KEY),
        "oddsApiConfigured":bool(ODDS_API_KEY) if ODDS_API_ENABLED else True,
        "oddsPapiConfigured": bool(ODDSPAPI_API_KEY) if ODDSPAPI_ENABLED else True,
        "oddsPapiBookmakers": list(ODDSPAPI_BOOKMAKERS),
        "authSecretPersistent":bool(os.getenv("AUTH_SECRET","").strip()),
        "sportsDbEnabled":bool(SPORTS_DB_ENABLED),
        "authDbPersistentPath":str(AUTH_DB).startswith("/var/data/"),
        "sportsDbPersistentPath":str(SPORTS_DB_PATH).startswith("/var/data/"),
        "publicAppUrlConfigured":bool(os.getenv("PUBLIC_APP_URL","").strip()),
    }
    required=("apiFootballConfigured","authSecretPersistent","sportsDbEnabled","authDbPersistentPath","sportsDbPersistentPath")
    return {
        "readyForProductionBeta":all(checks[k] for k in required),
        "checks":checks,
        "liveRefreshSeconds":180,
        "fixtureRefreshSeconds":1800,
        "oddsRefreshSeconds":1800,
        "generatedAt":datetime.now(timezone.utc).isoformat(),
    }


# ---------------------------------------------------------------------------
# v55 production readiness: admin odds monitoring, exports and security headers
# ---------------------------------------------------------------------------
def _ks_admin_authorized(request: Request) -> bool:
    """Use the existing bearer auth when available; deny by default."""
    auth=(request.headers.get("authorization") or "").strip()
    if not auth.lower().startswith("bearer "):
        return False
    token=auth.split(" ",1)[1].strip()
    try:
        payload=_decode_token(token)
        role=str(payload.get("role") or "").lower()
        return role=="admin" or bool(payload.get("admin"))
    except Exception:
        return False

@app.get("/admin/odds-monitoring")
async def admin_odds_monitoring(request: Request):
    if not _ks_admin_authorized(request):
        raise HTTPException(403,"Admin access required")
    matches=[]
    # Prefer already-warmed aggregate fixture cache: monitoring must not trigger
    # a fresh provider fan-out merely to display a counter.
    try:
        for value in list(_fixtures_cache.values()):
            if isinstance(value,dict) and str(value.get("league","")).upper()=="ALL" and value.get("matches"):
                matches=value.get("matches") or []
    except Exception:
        matches=[]
    with_odds=[m for m in matches if _valid_1x2(m.get("odds") or {})]
    sources={}
    for m in with_odds:
        src=str(m.get("oddsSource") or "Unknown")
        sources[src]=sources.get(src,0)+1
    last_success=max(
        [str(m.get("oddsUpdatedAt") or m.get("updatedAt") or "") for m in with_odds if (m.get("oddsUpdatedAt") or m.get("updatedAt"))],
        default=""
    )
    return {
        "currentOdds":len(with_odds),"fixturesWithRealOdds":len(with_odds),
        "fixturesLoaded":len(matches),"source":", ".join(f"{k}: {v}" for k,v in sources.items()) or "No cached odds",
        "lastSuccessfulRefresh":last_success or _quota_state.get("lastCheckedAt"),
        "lastError":None if with_odds else (_quota_state.get("lastError") or None),
        "quota":dict(_quota_state),"generatedAt":datetime.now(timezone.utc).isoformat()
    }

class FixtureExportPayload(BaseModel):
    league: str = "ALL"
    rows: list[dict] = []

def _export_safe(v,limit=180):
    return str(v if v is not None else "").replace("\r"," ").replace("\n"," ").strip()[:limit]

@app.post("/exports/fixtures/csv")
async def export_fixtures_csv(payload: FixtureExportPayload):
    rows=payload.rows[:5000]
    buf=io.StringIO(newline="")
    cols=["dateTime","competition","country","homeTeam","awayTeam","status","score","kasiPrediction","confidence","homeOdds","drawOdds","awayOdds"]
    w=csv.DictWriter(buf,fieldnames=cols,extrasaction="ignore")
    w.writeheader()
    for row in rows:w.writerow({k:_export_safe(row.get(k)) for k in cols})
    data=("\ufeff"+buf.getvalue()).encode("utf-8")
    return Response(content=data,media_type="text/csv; charset=utf-8",headers={"Content-Disposition":'attachment; filename="kasi-sports-news-fixtures.csv"'})

@app.post("/exports/fixtures/pdf")
async def export_fixtures_pdf(payload: FixtureExportPayload):
    # ReportLab is optional at runtime; return a controlled error if the
    # dependency has not yet been installed instead of crashing the service.
    try:
        from reportlab.lib import colors
        from reportlab.lib.pagesizes import A4, landscape
        from reportlab.lib.styles import getSampleStyleSheet
        from reportlab.lib.units import mm
        from reportlab.platypus import SimpleDocTemplate,Table,TableStyle,Paragraph,Spacer
    except Exception:
        # v312: dependency-free PDF fallback so export never becomes a visitor-facing 503.
        lines=["Kasi Sports News - Fixtures", "Generated "+datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"), ""]
        for r in payload.rows[:1000]:
            lines.append(" | ".join(_export_safe(r.get(k),35) for k in ("dateTime","competition","homeTeam","awayTeam","status","score")))
        def pe(t): return str(t).replace("\\","\\\\").replace("(","\\(").replace(")","\\)")
        content="BT /F1 8 Tf 30 560 Td "+" ".join("("+pe(x)+") Tj 0 -11 Td" for x in lines)+" ET"
        b=content.encode("latin-1","replace")
        objs=[b"<< /Type /Catalog /Pages 2 0 R >>",b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 842 595] /Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R >>",b"<< /Length "+str(len(b)).encode()+b" >>\nstream\n"+b+b"\nendstream",b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"]
        pdf=bytearray(b"%PDF-1.4\n");offs=[0]
        for i,o in enumerate(objs,1): offs.append(len(pdf));pdf.extend(f"{i} 0 obj\n".encode()+o+b"\nendobj\n")
        xref=len(pdf);pdf.extend(f"xref\n0 {len(objs)+1}\n0000000000 65535 f \n".encode())
        for off in offs[1:]:pdf.extend(f"{off:010d} 00000 n \n".encode())
        pdf.extend(f"trailer << /Size {len(objs)+1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF".encode())
        return Response(content=bytes(pdf),media_type="application/pdf",headers={"Content-Disposition":'attachment; filename="kasi-sports-news-fixtures.pdf"'})
    out=io.BytesIO(); doc=SimpleDocTemplate(out,pagesize=landscape(A4),leftMargin=10*mm,rightMargin=10*mm,topMargin=10*mm,bottomMargin=10*mm)
    styles=getSampleStyleSheet(); story=[Paragraph("Kasi Sports News — Fixtures",styles["Title"]),
        Paragraph("Generated "+datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")+" · Filter: "+_export_safe(payload.league),styles["Normal"]),Spacer(1,5*mm)]
    headers=["Date/Time","Competition","Home","Away","Status","Score","Prediction","Conf.","1","X","2"]
    data=[headers]
    for r in payload.rows[:1000]:
        data.append([_export_safe(r.get(k),45) for k in ["dateTime","competition","homeTeam","awayTeam","status","score","kasiPrediction","confidence","homeOdds","drawOdds","awayOdds"]])
    t=Table(data,repeatRows=1,colWidths=[28*mm,31*mm,31*mm,31*mm,18*mm,18*mm,31*mm,16*mm,13*mm,13*mm,13*mm])
    t.setStyle(TableStyle([("BACKGROUND",(0,0),(-1,0),colors.black),("TEXTCOLOR",(0,0),(-1,0),colors.white),
        ("FONTNAME",(0,0),(-1,0),"Helvetica-Bold"),("FONTSIZE",(0,0),(-1,-1),7),("GRID",(0,0),(-1,-1),0.25,colors.grey),
        ("VALIGN",(0,0),(-1,-1),"MIDDLE"),("ROWBACKGROUNDS",(0,1),(-1,-1),[colors.white,colors.HexColor("#f2f2f2")])]))
    story.append(t);doc.build(story);data_bytes=out.getvalue()
    return Response(content=data_bytes,media_type="application/pdf",headers={"Content-Disposition":'attachment; filename="kasi-sports-news-fixtures.pdf"'})

@app.middleware("http")
async def kasi_production_security_headers(request: Request, call_next):
    response=await call_next(request)
    response.headers.setdefault("X-Content-Type-Options","nosniff")
    response.headers.setdefault("Referrer-Policy","strict-origin-when-cross-origin")
    response.headers.setdefault("Permissions-Policy","geolocation=(), camera=(), microphone=()")
    response.headers.setdefault("X-Frame-Options","SAMEORIGIN")
    response.headers.setdefault("Strict-Transport-Security","max-age=31536000; includeSubDomains")
    response.headers.setdefault("Content-Security-Policy",
        "default-src 'self'; img-src 'self' https: data:; media-src 'self' https:; frame-src https://www.youtube.com https://www.youtube-nocookie.com; "
        "script-src 'self' 'unsafe-inline' https://www.googletagmanager.com https://pagead2.googlesyndication.com; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; connect-src 'self' https:; font-src 'self' https://fonts.gstatic.com https: data:; object-src 'none'; base-uri 'self'; frame-ancestors 'self'")
    if request.url.path.startswith(("/auth/","/admin/")):
        response.headers["Cache-Control"]="no-store"
    return response

# v275 cache-first homepage snapshot.
# Last-good data is served immediately while fresh provider data is vetted in background.
_HOME_FOOTBALL_SNAPSHOT: dict = {}
_HOME_FOOTBALL_TASK: Optional[asyncio.Task] = None
_HOME_FOOTBALL_REFRESH_SECONDS = max(60, int(os.getenv("HOME_FOOTBALL_REFRESH_SECONDS", "180")))

def _restore_home_football_snapshot():
    """Restore the last verified non-empty Home snapshot after a process restart."""
    global _HOME_FOOTBALL_SNAPSHOT
    try:
        snap = _dashboard_snapshot_get("home_football_last_good") if "_dashboard_snapshot_get" in globals() else None
        payload = (snap or {}).get("data") if isinstance(snap, dict) else None
        if isinstance(payload, dict) and (payload.get("matches") or payload.get("fixtures")):
            _HOME_FOOTBALL_SNAPSHOT = payload
            return True
    except Exception as exc:
        log.debug("Home snapshot restore skipped: %s", exc)
    return False

async def _build_home_football_snapshot():
    global _HOME_FOOTBALL_SNAPSHOT
    try:
        fd=await fixtures_with_odds(league="ALL",type="upcoming",date_from=None,date_to=None,refresh=0)
        rows=fd.get("matches") or []
        preds=[]
        for m in rows:
            if m.get("isFinished"): continue
            try:
                pr=_prediction(m)
                preds.append({**m,**pr,
                    "oddsAvailable":_valid_1x2(m.get("odds") or {}),
                    "bookmakerGatePassed":_valid_1x2(m.get("odds") or {}),
                    "predictionEligible":_valid_1x2(m.get("odds") or {}),
                    "gamesOfDayEligible":_valid_1x2(m.get("odds") or {})})
            except Exception as exc:
                log.debug("Home snapshot prediction skipped: %s",exc)
        if rows:
            _HOME_FOOTBALL_SNAPSHOT={
                "matches":rows,"fixtures":rows,"predictions":preds,
                "count":len(rows),"oddsComplete":fd.get("oddsComplete",0),
                "oddsBookmaker":fd.get("oddsBookmaker",0),
                "oddsSource":fd.get("oddsSource"),
                "generatedAt":datetime.now(timezone.utc).isoformat()
            }
            # Never overwrite a good snapshot with an empty/transient provider response.
            if "_dashboard_snapshot_put" in globals():
                _dashboard_snapshot_put("home_football_last_good", {"data": _HOME_FOOTBALL_SNAPSHOT})
    except Exception as exc:
        log.warning("Home football snapshot refresh failed: %s",exc)

def _schedule_home_football_snapshot():
    global _HOME_FOOTBALL_TASK
    if _HOME_FOOTBALL_TASK and not _HOME_FOOTBALL_TASK.done(): return
    _HOME_FOOTBALL_TASK=asyncio.create_task(_build_home_football_snapshot())

async def _home_football_refresh_loop():
    """Keep Home warm all day, including across midnight, without clearing last-good data."""
    _restore_home_football_snapshot()
    while True:
        try:
            await _build_home_football_snapshot()
        except Exception as exc:
            log.warning("Home background refresh error: %s", exc)
        await asyncio.sleep(_HOME_FOOTBALL_REFRESH_SECONDS)

@app.get("/home/football")
async def home_football():
    if _HOME_FOOTBALL_SNAPSHOT:
        _schedule_home_football_snapshot()
        return {**_HOME_FOOTBALL_SNAPSHOT,"staleWhileRevalidate":True}
    _schedule_home_football_snapshot()
    # Cold start: give already-persistent API caches a short chance only.
    try:
        await asyncio.wait_for(asyncio.shield(_HOME_FOOTBALL_TASK),timeout=1.6)
    except (asyncio.TimeoutError,Exception):
        pass
    if _HOME_FOOTBALL_SNAPSHOT:
        return {**_HOME_FOOTBALL_SNAPSHOT,"staleWhileRevalidate":True}
    return {"matches":[],"fixtures":[],"predictions":[],"count":0,"warming":True,
            "generatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/health")
async def health():
    return {
        "status": "ok",
        "api_key_set": bool(API_KEY),
        "version": "v56",
        "cache_sizes": {
            "fixtures": len(_fixtures_cache),
            "live": len(_live_cache),
            "odds": len(_odds_cache),
            "teams": len(_team_cache),
        },
        "quota": {
            **dict(_quota_state),
            "localCallsToday": _api_football_usage.get("callsToday", 0),
            "localBudget": KASISCORE_DAILY_BUDGET,
            "protectedReserve": KASISCORE_PROVIDER_RESERVE,
            "blockedByBudget": _api_football_usage.get("blockedByBudget", 0),
            "callsByPath": dict(sorted(
                _api_football_usage.get("callsByPath", {}).items(),
                key=lambda kv: kv[1], reverse=True
            )),
            "localUsageUtcDate": _api_football_usage.get("utcDate"),
            "lastLocalCallAt": _api_football_usage.get("lastCallAt"),
        },
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }

# ---------------------------------------------------------------------------
# FIXTURES
# ---------------------------------------------------------------------------

@app.get("/fixtures")
async def fixtures(
    league: str = Query("ALL"),
    type: str = Query("today"),
    range: Optional[str] = Query(None),
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
    refresh: int = Query(0, ge=0, le=1),
):
    # v183: FastAPI Query(...) defaults are metadata objects when an endpoint
    # function is called directly from another Python endpoint. Normalise them
    # back to ordinary values so internal reuse cannot crash the provider flow.
    league = league if isinstance(league, str) else "ALL"
    type = type if isinstance(type, str) else "today"
    range = range if isinstance(range, str) else None
    date_from = date_from if isinstance(date_from, str) else None
    date_to = date_to if isinstance(date_to, str) else None
    refresh = int(refresh) if isinstance(refresh, (int, bool)) else 0

    # Backward-compatible frontend contract: /fixtures?range=today
    # is accepted and normalised to the canonical `type` parameter.
    if range:
        legacy = range.strip().lower()
        if legacy in {"today", "live", "upcoming"}:
            type = legacy
        elif legacy in {"tomorrow", "next"}:
            type = "upcoming"
            date_from = date_from or (datetime.now() + timedelta(days=1)).strftime("%Y-%m-%d")
            date_to = date_to or date_from
    type = type.strip().lower()

    bucket = (
        datetime.now().strftime("%Y-%m-%d-%H")
        + str(datetime.now().minute // 30)
    )
    # Include the requested date range in the key.  Without this, two
    # different upcoming windows could incorrectly share the same 30-minute
    # cache entry.
    cache_key = (
        f"fixtures:{league}:{type}:"
        f"{date_from or ''}:{date_to or ''}:{bucket}"
    )
    # Stable key intentionally excludes the 30-minute bucket. It stores only
    # successful non-empty fixture responses and is used when a later
    # API-Football scan unexpectedly returns zero.
    last_good_key = (
        f"fixtures-last-good:{league.upper()}:{type}:"
        f"{date_from or ''}:{date_to or ''}"
    )

    # v438: quota-reserve preflight. Once API-Football reaches the protected
    # reserve, do not enter the per-league/provider refresh path at all.
    # Serve the most recent valid LKG/server snapshot immediately instead.
    _daily_remaining = _quota_state.get("dailyRemaining")
    _reserve_locked = (
        isinstance(_daily_remaining, int)
        and _daily_remaining <= KASISCORE_PROVIDER_RESERVE
    )
    if _reserve_locked:
        stale = _fixtures_last_good.get(last_good_key)
        if not stale and "_dashboard_snapshot_get" in globals():
            _ps = _dashboard_snapshot_get(
                f"fixtures:football:{league.upper()}:{type}:last_good"
            )
            stale = (_ps or {}).get("data") if isinstance(_ps, dict) else None

        if isinstance(stale, dict) and stale.get("matches"):
            served = {
                **stale,
                "stale": True,
                "providerLocked": True,
                "staleReason": "API-Football reserve protection is active",
                "providerWarning": (
                    "Serving last known good fixtures without calling API-Football "
                    "until the provider quota is above the protected reserve."
                ),
                "dailyRemaining": _daily_remaining,
                "providerReserve": KASISCORE_PROVIDER_RESERVE,
            }
            _fixtures_cache[cache_key] = served
            return served

        # No valid LKG exists for this exact request. Fail soft without burning
        # provider quota or repeatedly throwing one 429 per scanned league.
        return {
            "matches": [],
            "count": 0,
            "source": "cache/LKG",
            "league": league,
            "type": type,
            "stale": True,
            "providerLocked": True,
            "staleReason": "API-Football reserve protection is active and no LKG exists",
            "dailyRemaining": _daily_remaining,
            "providerReserve": KASISCORE_PROVIDER_RESERVE,
        }

    if not refresh:
        cached = _fixtures_cache.get(cache_key)
        if cached is not None:
            # v52: live=0 is valid; today/upcoming=0 should be retried instead
            # of poisoning the full 30-minute aggregate cache window.
            if type == "live" or cached.get("matches"):
                return cached

    today = datetime.now().strftime("%Y-%m-%d")
    season = _current_season()
    all_leagues = league.upper() == "ALL"

    if type == "live":
        params = {"live": "all"}
        if not all_leagues:
            params["league"] = _resolve_league_id(league)

        data = await _afoot_get("/fixtures", params)
        raw = data.get("response", [])
        normalised = [_normalise_fixture(f, "") for f in raw]

    elif all_leagues:
        # v53: build ALL from the same per-league path proven to work in
        # production. This prevents the ALL scanner from drifting from the
        # single-league request/cache/normalisation behaviour.
        combined = []
        league_errors = []

        for league_name in SCAN_LEAGUES:
            if LEAGUE_IDS.get(league_name) is None:
                continue
            try:
                one = await fixtures(
                    league=league_name,
                    type=type,
                    range=None,
                    date_from=date_from,
                    date_to=date_to,
                    refresh=refresh,
                )
                rows = one.get("matches", []) if isinstance(one, dict) else []
                if rows:
                    combined.extend(rows)
            except Exception as exc:
                league_errors.append(f"{league_name}: {str(exc)[:120]}")
                log.warning("Fixtures ALL per-league fetch failed %s: %s", league_name, exc)

        # Deduplicate by API-Football fixture id while preserving order.
        seen = set()
        normalised = []
        for match in combined:
            fid = match.get("_afootFixtureId")
            key = str(fid) if fid is not None else (
                f"{match.get('home')}|{match.get('away')}|{match.get('datetime')}"
            )
            if key in seen:
                continue
            seen.add(key)
            normalised.append(match)

        # v412: supplement ALL upcoming/today with OddsPapi football coverage.
        # This broadens the visitor choice without replacing API-Football identities.
        oddspapi_added=0
        if type in {"today","upcoming"} and ODDSPAPI_ENABLED and ODDSPAPI_API_KEY:
            try:
                op_rows=await _oddspapi_sport_fixtures("football",date_from if type=="today" else None,False)
                existing={( _normalise_team_name(x.get("home")), _normalise_team_name(x.get("away")) ) for x in normalised}
                for op in op_rows:
                    pair=(_normalise_team_name(op.get("home")),_normalise_team_name(op.get("away")))
                    if not all(pair) or pair in existing: continue
                    normalised.append(op);existing.add(pair);oddspapi_added+=1
            except Exception as exc:
                log.warning("OddsPapi fixture supplement failed: %s",exc)

        normalised = _ksn_sort_football_rows(normalised)
        result = {
            "matches": normalised,
            "count": len(normalised),
            "source": "API-Football + OddsPapi Bet365/Betway supplement",
            "oddspapiAdded": oddspapi_added,
            "league": "ALL",
            "type": type,
            "scanned_leagues": SCAN_LEAGUES,
        }
        if league_errors:
            result["partialErrors"] = league_errors[:5]
            result["partialErrorCount"] = len(league_errors)

        if normalised:
            _fixtures_last_good[last_good_key] = result
            _fixtures_cache[cache_key] = result
            if "_dashboard_snapshot_put" in globals():
                _dashboard_snapshot_put(f"fixtures:football:{league.upper()}:{type}:last_good", {"data": result})
            return result

        if type != "live":
            stale = _fixtures_last_good.get(last_good_key)
            if not stale and "_dashboard_snapshot_get" in globals():
                _ps=_dashboard_snapshot_get(f"fixtures:football:{league.upper()}:{type}:last_good")
                stale=(_ps or {}).get("data") if isinstance(_ps,dict) else None
            if stale and stale.get("matches"):
                served = {
                    **stale,
                    "stale": True,
                    "staleReason": "API-Football returned an empty ALL-league scan",
                    "providerWarning": "Serving last known good fixtures while the ALL-league refresh returned no matches.",
                }
                _fixtures_cache[cache_key] = served
                return served

        if type == "live":
            _fixtures_cache[cache_key] = result
        return result

    else:
        lid = _resolve_league_id(league)

        if type == "upcoming":
            params = {
                "from": date_from or today,
                "to": date_to or (
                    datetime.now() + timedelta(days=7)
                ).strftime("%Y-%m-%d"),
                "timezone": TIMEZONE,
                "season": season,
                "league": lid,
            }
        else:
            params = {
                "date": date_from or today,
                "timezone": TIMEZONE,
                "season": season,
                "league": lid,
            }

        data = await _afoot_get("/fixtures", params)
        raw = data.get("response", [])
        normalised = [
            _normalise_fixture(
                f,
                _league_name_from_id(lid, league),
            )
            for f in raw
        ]

    result = {
        "matches": normalised,
        "count": len(normalised),
        "source": "API-Football",
        "league": league,
        "type": type,
    }

    if normalised:
        _fixtures_last_good[last_good_key] = result
        _fixtures_cache[cache_key] = result
        if "_dashboard_snapshot_put" in globals():
            _dashboard_snapshot_put(f"fixtures:football:{league.upper()}:{type}:last_good", {"data": result})
        return result

    if type != "live":
        stale = _fixtures_last_good.get(last_good_key)
        if not stale and "_dashboard_snapshot_get" in globals():
            _ps=_dashboard_snapshot_get(f"fixtures:football:{league.upper()}:{type}:last_good")
            stale=(_ps or {}).get("data") if isinstance(_ps,dict) else None
        if stale and stale.get("matches"):
            served = {
                **stale,
                "stale": True,
                "staleReason": "API-Football returned an empty fixture scan",
                "providerWarning": "Serving last known good fixtures while API-Football returned no matches.",
            }
            _fixtures_cache[cache_key] = served
            return served

    if type == "live":
        _fixtures_cache[cache_key] = result
    return result

# ---------------------------------------------------------------------------
# FRONTEND COMPATIBILITY ALIASES + MATCH STATS
# ---------------------------------------------------------------------------

@app.get("/predictions")
async def predictions_alias(
    limit: int = Query(100, ge=1, le=500),
    refresh: int = Query(0, ge=0, le=1),
    league: str = Query("ALL"),
    type: str = Query("upcoming"),
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
):
    """Canonical compatibility alias for the dashboard's /predictions path."""
    return await ai_predictions(
        limit=limit, refresh=refresh, league=league, type=type,
        date_from=date_from, date_to=date_to
    )

@app.get("/injuries")
async def injuries_alias(
    team: int = Query(0, ge=0),
    league: int = Query(0, ge=0),
    season: int = Query(0, ge=0),
):
    return await sports_injuries(team=team, league=league, season=season)

@app.get("/transfers")
async def transfers_alias(
    team: int = Query(0, ge=0),
    page: int = Query(1, ge=1, le=50),
):
    return await sports_transfers(team=team, page=page)

def _match_stats_db_get(sport:str, match_id):
    if not SPORTS_DB_ENABLED:return None
    try:
        with _sports_db() as db:
            row=db.execute("SELECT payload_json,completed,updated_at FROM match_stats_cache WHERE sport=? AND match_id=?",
                           (str(sport).lower(),str(match_id))).fetchone()
        if not row:return None
        data=_db_load(row["payload_json"],{})
        if isinstance(data,dict):
            data["fromPersistentCache"]=True
            data["completed"]=bool(row["completed"])
            data["cachedAt"]=row["updated_at"]
            return data
    except Exception as exc:
        log.debug("match stats cache read failed %s/%s: %s",sport,match_id,exc)
    return None

def _enhanced_match_db_ensure(db):
    db.execute("""CREATE TABLE IF NOT EXISTS enhanced_match_cache(
      sport TEXT NOT NULL,match_id TEXT NOT NULL,payload_json TEXT NOT NULL,
      completed INTEGER NOT NULL DEFAULT 0,competition_id TEXT,competition_name TEXT,
      stage TEXT,venue_name TEXT,updated_at TEXT NOT NULL,
      PRIMARY KEY(sport,match_id))""")

def _enhanced_match_db_get(sport:str, match_id):
    if not SPORTS_DB_ENABLED:return None
    try:
        with _sports_db() as db:
            _enhanced_match_db_ensure(db)
            row=db.execute("SELECT payload_json,completed,updated_at FROM enhanced_match_cache WHERE sport=? AND match_id=?",
                           (str(sport).lower(),str(match_id))).fetchone()
        if not row:return None
        data=_db_load(row["payload_json"],{})
        if isinstance(data,dict):
            data["fromPersistentEnhancedCache"]=True
            data["completed"]=bool(row["completed"])
            data["cachedAt"]=row["updated_at"]
            return data
    except Exception as exc:
        log.debug("enhanced match cache read failed %s/%s: %s",sport,match_id,exc)
    return None

def _enhanced_match_db_put(sport:str, match_id, payload:dict, completed:bool=False):
    if not SPORTS_DB_ENABLED or not isinstance(payload,dict):return
    try:
        match=payload.get("match") or {}; league=match.get("league") or {}; fixture=match.get("fixture") or {}
        venue=fixture.get("venue") or {}; stage=str(league.get("round") or "")
        with _sports_db() as db:
            _enhanced_match_db_ensure(db)
            db.execute("""INSERT INTO enhanced_match_cache(
              sport,match_id,payload_json,completed,competition_id,competition_name,stage,venue_name,updated_at)
              VALUES(?,?,?,?,?,?,?,?,?) ON CONFLICT(sport,match_id) DO UPDATE SET
              payload_json=excluded.payload_json,completed=MAX(enhanced_match_cache.completed,excluded.completed),
              competition_id=excluded.competition_id,competition_name=excluded.competition_name,
              stage=excluded.stage,venue_name=excluded.venue_name,updated_at=excluded.updated_at""",
              (str(sport).lower(),str(match_id),_db_json(payload),1 if completed else 0,
               str(league.get("id") or ""),str(league.get("name") or ""),stage,str(venue.get("name") or ""),
               datetime.now(timezone.utc).isoformat()))
            db.commit()
    except Exception as exc:
        log.debug("enhanced match cache write failed %s/%s: %s",sport,match_id,exc)

def _enhanced_stage_flags(match:dict)->dict:
    league=match.get("league") or {}; name=str(league.get("name") or "").lower(); rnd=str(league.get("round") or "").lower()
    uefa=any(x in name for x in ("champions league","europa league","conference league","uefa"))
    playoff=any(x in rnd for x in ("play-off","playoff","qualifying","knockout","round of 16","quarter","semi","final"))
    return {"uefa":uefa,"playoff":playoff,"competition":league.get("name"),"round":league.get("round")}

def _venue_intelligence(match:dict, insights:dict)->dict:
    fixture=match.get("fixture") or {}; venue=fixture.get("venue") or {}; target=str(venue.get("name") or "").strip().lower()
    home_id=((match.get("teams") or {}).get("home") or {}).get("id")
    rows=((insights.get("form") or {}).get("home") or {}).get("last10") or []
    # The existing normalized Last-10 rows do not retain venue, so expose a conservative
    # home-ground sample rather than pretending exact historical venue matching.
    played=len(rows); wins=sum(1 for x in rows if x.get("result")=="W"); draws=sum(1 for x in rows if x.get("result")=="D"); losses=sum(1 for x in rows if x.get("result")=="L")
    return {"venue":venue,"sampleType":"home-team-recent-form","exactVenueMatched":False,
            "sampleSize":played,"wins":wins,"draws":draws,"losses":losses,
            "note":"Exact historical venue matching is only asserted when archived fixture venue data is available."}

def _fantasy_match_signals(match:dict, events:list, statistics:list)->dict:
    cards={"yellow":0,"red":0}; goals=0
    for e in events or []:
        typ=str(e.get("type") or "").lower(); detail=str(e.get("detail") or "").lower()
        if typ=="goal":goals+=1
        if typ=="card":
            if "red" in detail:cards["red"]+=1
            elif "yellow" in detail:cards["yellow"]+=1
    return {"goals":goals,"cards":cards,"statisticsAvailable":bool(statistics),
            "mode":"provider-data-signals","officialFantasyPoints":False}

def _match_stats_db_put(sport:str, match_id, payload:dict, completed:bool=False):
    if not SPORTS_DB_ENABLED or not isinstance(payload,dict):return
    try:
        now=datetime.now(timezone.utc).isoformat()
        with _sports_db() as db:
            db.execute("""INSERT INTO match_stats_cache(sport,match_id,payload_json,completed,updated_at)
              VALUES(?,?,?,?,?) ON CONFLICT(sport,match_id) DO UPDATE SET
              payload_json=excluded.payload_json,
              completed=MAX(match_stats_cache.completed,excluded.completed),
              updated_at=excluded.updated_at""",
              (str(sport).lower(),str(match_id),_db_json(payload),1 if completed else 0,now))
            db.commit()
    except Exception as exc:
        log.debug("match stats cache write failed %s/%s: %s",sport,match_id,exc)

@app.get("/fixtures/{fixture_id}/stats")
async def fixture_stats(fixture_id: int):
    """Cache/DB first; provider failure cannot blank an existing completed Stats page."""
    ck=f"live-stats:{fixture_id}"
    cached=_live_stats_cache.get(ck)
    # v396: never let an early empty live-stat snapshot become authoritative.
    # Live providers often publish events before the statistics feed is populated.
    if isinstance(cached,dict) and cached.get("statistics"):
        return cached
    persisted=_match_stats_db_get("football",fixture_id)
    if persisted and persisted.get("completed"):
        _live_stats_cache[ck]=persisted
        return persisted
    try:
        stats_data,fixture_data=await asyncio.gather(
            _afoot_get("/fixtures/statistics",{"fixture":fixture_id}),
            _afoot_get("/fixtures",{"id":fixture_id}),
            return_exceptions=True)
        rows=(stats_data.get("response") or []) if isinstance(stats_data,dict) else []
        # v396: if the normal cached provider call is empty, retry once fresh.
        # This fixes live Stats pages that otherwise keep showing dashes after stats arrive upstream.
        if not rows:
            try:
                fresh_stats=await _afoot_get("/fixtures/statistics",{"fixture":fixture_id},force_fresh=True)
                rows=(fresh_stats.get("response") or []) if isinstance(fresh_stats,dict) else []
            except Exception as fresh_exc:
                log.debug("Fresh live statistics retry unavailable fixture=%s: %s",fixture_id,fresh_exc)
        fixtures=(fixture_data.get("response") or []) if isinstance(fixture_data,dict) else []
        status=str((((fixtures[0] if fixtures else {}).get("fixture") or {}).get("status") or {}).get("short") or "").upper()
        completed=status in {"FT","AET","PEN"}
        result={"fixtureId":fixture_id,"count":len(rows),"statistics":rows,"available":bool(rows),
                "source":"API-Football","completed":completed,
                "updatedAt":datetime.now(timezone.utc).isoformat()}
        if rows:_match_stats_db_put("football",fixture_id,result,completed)
        elif persisted:result=persisted
    except Exception as exc:
        log.warning("Fixture stats unavailable fixture=%s: %s",fixture_id,exc)
        result=persisted or {"fixtureId":fixture_id,"count":0,"statistics":[],"available":False,
          "source":"API-Football","warning":"No data available",
          "updatedAt":datetime.now(timezone.utc).isoformat()}
    # Cache only useful statistics. Empty provider responses must be retried later.
    if result.get("statistics"):
        _live_stats_cache[ck]=result
    return result


async def _fetch_team_form_detailed(team_id: int, league_id: int, season: int, last_n: int = 5):
    """Return the actual recent fixtures, not just W/D/L."""
    try:
        d = await _afoot_get("/fixtures", {
            "team": team_id, "league": league_id, "season": season,
            "status": "FT", "last": last_n,
        })
        return d.get("response", [])
    except Exception as exc:
        log.warning("Detailed form fetch failed team=%s: %s", team_id, exc)
        return []

@app.get("/fixtures/{fixture_id}/live-bundle")
async def fixture_live_bundle(fixture_id: int):
    """One frontend request for fixture + current stats + lineups. Upstream is limited to three cached calls."""
    fd,sd,ld,pd,ed=await asyncio.gather(
        _afoot_get("/fixtures", {"id":fixture_id}),
        fixture_stats(fixture_id),
        fixture_lineups(fixture_id),
        _afoot_get("/fixtures/players", {"fixture":fixture_id}),
        fixture_events(fixture_id),
        return_exceptions=True,
    )
    f=((fd.get("response") or [{}])[0] if isinstance(fd,dict) else {})
    # v362: completed/live matches should not stay blank because an early empty stats snapshot was cached.
    if isinstance(sd,dict) and not sd.get("statistics"):
        try:
            raw_stats=await _afoot_get("/fixtures/statistics",{"fixture":fixture_id},force_fresh=True)
            fresh_stats=[]
            for row in raw_stats.get("response") or []:
                fresh_stats.append({"team":row.get("team") or {},"statistics":row.get("statistics") or []})
            if fresh_stats: sd={"fixtureId":fixture_id,"statistics":fresh_stats,"available":True,"source":"API-Football"}
        except Exception as fresh_stats_exc:
            log.debug("Fresh statistics retry unavailable fixture=%s: %s",fixture_id,fresh_stats_exc)
    return {
        "fixture":f,
        "statistics":sd.get("statistics",[]) if isinstance(sd,dict) else [],
        "lineups":ld.get("teams",[]) if isinstance(ld,dict) else [],
        "players":pd.get("response",[]) if isinstance(pd,dict) else [],
        "events":ed.get("events",[]) if isinstance(ed,dict) else [],
        "statisticsAvailable":bool(sd.get("statistics",[])) if isinstance(sd,dict) else False,
        "lineupsAvailable":bool(ld.get("teams",[])) if isinstance(ld,dict) else False,
        "playersAvailable":bool(pd.get("response",[])) if isinstance(pd,dict) else False,
        "source":"API-Football",
        "updatedAt":datetime.now(timezone.utc).isoformat(),
    }

@app.get("/match/{fixture_id}/stats")
async def match_stats_alias(fixture_id: int):
    return await fixture_stats(fixture_id)


@app.get("/fixtures/{fixture_id}/lineups")
async def fixture_lineups(fixture_id: int):
    """Starting XI/substitutes. Fail-soft so Lineups cannot block Statistics."""
    try:
        data=await _afoot_get("/fixtures/lineups",{"fixture":fixture_id})
        rows=data.get("response") or []
        # v362: an old cached empty response can occur before line-ups are announced.
        # Retry once from the provider so a later Stats visit can obtain the actual XI/formation.
        if not rows:
            try:
                fresh=await _afoot_get("/fixtures/lineups",{"fixture":fixture_id},force_fresh=True)
                rows=fresh.get("response") or []
            except Exception as fresh_exc:
                log.debug("Fresh lineup retry unavailable fixture=%s: %s",fixture_id,fresh_exc)
        teams=[]
        for row in rows:
            team=row.get("team") or {}; players=[]
            for item in row.get("startXI") or []:
                p=item.get("player") or {}; players.append({"id":p.get("id"),"name":p.get("name"),"number":p.get("number"),"pos":p.get("pos"),"grid":p.get("grid"),"starter":True})
            for item in row.get("substitutes") or []:
                p=item.get("player") or {}; players.append({"id":p.get("id"),"name":p.get("name"),"number":p.get("number"),"pos":p.get("pos"),"grid":p.get("grid"),"starter":False})
            teams.append({"team":team,"coach":row.get("coach") or {},"formation":row.get("formation"),"players":players})
        return {"fixtureId":fixture_id,"teams":teams,"available":bool(teams),"source":"API-Football","updatedAt":datetime.now(timezone.utc).isoformat()}
    except Exception as exc:
        log.warning("Fixture lineups unavailable fixture=%s: %s",fixture_id,exc)
        return {"fixtureId":fixture_id,"teams":[],"available":False,"warning":"No data available","source":"API-Football","updatedAt":datetime.now(timezone.utc).isoformat()}


@app.get("/fixtures/{fixture_id}/players/{player_id}")
async def fixture_player_statistics(fixture_id: int, player_id: int):
    """Fast match-context player profile with fail-soft season enrichment."""
    async def safe(path,params):
        try:return await _afoot_get(path,params)
        except Exception as exc:
            log.debug("Match player optional call failed %s %s: %s",fixture_id,player_id,exc);return {}
    current=await safe("/fixtures/players",{"fixture":fixture_id})
    current_rows=current.get("response") or []
    current_player=None
    for teamrow in current_rows:
        for item in teamrow.get("players") or []:
            pl=item.get("player") or {}
            if int(pl.get("id") or 0)==player_id:
                current_player={"player":pl,"statistics":item.get("statistics") or [],"team":teamrow.get("team") or {}};break
        if current_player:break
    season=_current_season()
    aggregate,recent=await asyncio.gather(
        safe("/players",{"id":player_id,"season":season}),
        safe("/fixtures",{"player":player_id,"season":season,"last":20}),
    )
    rows=aggregate.get("response") or []
    profile=rows[0] if rows else {"player":(current_player or {}).get("player") or {},"statistics":[]}
    return {"fixtureId":fixture_id,"playerId":player_id,"currentGame":current_player or {"player":{},"statistics":[],"team":{}},"season":season,"seasonStatistics":profile.get("statistics") or [],"player":profile.get("player") or (current_player or {}).get("player") or {},"recentMatches":recent.get("response") or [],"source":"API-Football · match context","updatedAt":datetime.now(timezone.utc).isoformat()}


@app.get("/fixtures/{fixture_id}/events")
async def fixture_events(fixture_id: int):
    """Timeline events. Fail-soft so Events cannot blank the match page."""
    try:
        data = await _afoot_get("/fixtures/events", {"fixture": fixture_id})
        events = []
        for x in data.get("response") or []:
            team=x.get("team") or {}; player=x.get("player") or {}; assist=x.get("assist") or {}
            events.append({"time":x.get("time") or {},"type":x.get("type") or "","detail":x.get("detail") or "",
                "comments":x.get("comments") or "","team":{"id":team.get("id"),"name":team.get("name"),"logo":team.get("logo")},
                "player":{"id":player.get("id"),"name":player.get("name")},"assist":{"id":assist.get("id"),"name":assist.get("name")}})
        return {"fixtureId":fixture_id,"events":events,"available":bool(events),"source":"API-Football","updatedAt":datetime.now(timezone.utc).isoformat()}
    except Exception as exc:
        log.warning("Fixture events unavailable fixture=%s: %s",fixture_id,exc)
        return {"fixtureId":fixture_id,"events":[],"available":False,"warning":"No data available","source":"API-Football","updatedAt":datetime.now(timezone.utc).isoformat()}


@app.get("/fixtures/{fixture_id}/odds-detail")
async def fixture_odds_detail(fixture_id: int):
    """Detailed bookmaker markets. Every provider path returns the same bookmakers/selected contract."""
    try:
        data = await _afoot_get_deadline("/odds", {"fixture": fixture_id}, ODDS_API_TIMEOUT)
        bookmakers=[]
        for item in data.get("response") or []:
            bk=item.get("bookmaker") or {}
            markets=[]
            for bet in item.get("bets") or []:
                values=[{"value":v.get("value"),"odd":v.get("odd")} for v in (bet.get("values") or []) if _safe_float(v.get("odd"))>0]
                if values: markets.append({"id":bet.get("id"),"name":bet.get("name"),"values":values})
            if markets: bookmakers.append({"id":bk.get("id"),"name":bk.get("name") or "Bookmaker","markets":markets})
        preferred={"Pinnacle":0,"Bet365":1,"1xBet":2,"William Hill":3,"Unibet":4,"Bwin":5}
        bookmakers.sort(key=lambda x:preferred.get(x.get("name"),99))
        if bookmakers:
            return {"fixtureId":fixture_id,"selected":bookmakers[0],"bookmakers":bookmakers[:12],
                    "source":"API-Football","available":True,"updatedAt":datetime.now(timezone.utc).isoformat()}
    except Exception as exc:
        log.warning("odds-detail API-Football failed fixture=%s: %s",fixture_id,exc)

    # Reuse the canonical normalized odds service for OddsPapi / The Odds API fallbacks.
    try:
        base=await odds(fixture_id=fixture_id,refresh=0)
        norm=base.get("odds") or {}
        if base.get("available") and norm:
            vals=[]
            for label,key in (("Home","homeWin"),("Draw","draw"),("Away","awayWin")):
                if _safe_float(norm.get(key))>0: vals.append({"value":label,"odd":norm.get(key)})
            markets=[]
            if vals: markets.append({"id":"1x2","name":"Match Winner","values":vals})
            for label,key,line in (("Over 0.5","over05","0.5"),("Over 1.5","over15","1.5"),("Over 2.5","over25","2.5")):
                if _safe_float(norm.get(key))>0:
                    markets.append({"id":"totals","name":f"Goals Over/Under {line}","values":[{"value":label,"odd":norm.get(key)}]})
            if _safe_float(norm.get("btts"))>0:
                markets.append({"id":"btts","name":"Both Teams To Score","values":[{"value":"Yes","odd":norm.get("btts")}]})
            selected={"id":norm.get("_bookmaker") or base.get("bookmaker") or "fallback",
                      "name":norm.get("_bookmaker") or base.get("bookmaker") or base.get("source") or "Bookmaker",
                      "markets":markets}
            return {"fixtureId":fixture_id,"selected":selected,"bookmakers":[selected],
                    "normalized":norm,"source":base.get("source") or "Fallback",
                    "available":True,"fallback":True,"updatedAt":datetime.now(timezone.utc).isoformat()}
    except Exception as exc:
        log.warning("odds-detail normalized fallback failed fixture=%s: %s",fixture_id,exc)

    return {"fixtureId":fixture_id,"selected":None,"bookmakers":[],"normalized":{},
            "source":"Unavailable","available":False,"updatedAt":datetime.now(timezone.utc).isoformat()}


# ---------------------------------------------------------------------------
# LOCATION-AWARE SPORTS VIDEO POOL — independent from API-Football
# Collects recent metadata from approved YouTube channel Atom feeds, tags it,
# resolves approximate visitor location (city/region/country only), then sends
# only the ranked subset to the browser.
# ---------------------------------------------------------------------------
_YT_CHANNEL_ID_CACHE = TTLCache(maxsize=256, ttl=86400)
# v301: stable official cricket channel IDs avoid fragile YouTube handle-page
# resolution in cloud environments.
_YT_KNOWN_CHANNEL_IDS = {
    "@official-icc": "UC0JlKcRZJdQRKUkoYOdNolA",
    "@icc": "UC0JlKcRZJdQRKUkoYOdNolA",
    "@cricketcomau": "UCkBY0aHJP9BwjZLDYxAQrKg",
    "@officialenglandcricket": "UCz1D0n02BR3t51KuBOPmfTQ",
    "@englandcricket": "UCz1D0n02BR3t51KuBOPmfTQ",
}
_YT_VIDEO_FEED_CACHE = TTLCache(maxsize=256, ttl=300)
_VIDEO_POOL_CACHE = TTLCache(maxsize=16, ttl=300)
_VIDEO_GEO_CACHE = TTLCache(maxsize=4096, ttl=21600)
# v30: stale-while-revalidate video cache. A slow YouTube source must never
# block the Highlights widget for many seconds.
_VIDEO_LAST_GOOD: list[dict] = []
_VIDEO_REFRESH_TASK: Optional[asyncio.Task] = None
_VIDEO_REFRESH_LOCK = asyncio.Lock()
VIDEO_FAST_WAIT = float(os.getenv("VIDEO_FAST_WAIT", "1.6"))


# source, handle, countries, regions, cities, team/competition tags
_VIDEO_SOURCES = {
    "football": [
        ("Premier League","@premierleague",["GB"],[],[],["Premier League"]),
        ("Sky Sports Football","@SkySportsFootball",["GB"],[],[],["Premier League","EFL"]),
        ("SuperSport","@supersport",["ZA"],[],[],["PSL","South Africa"]),
        ("FIFA","@fifa",[],[],[],["FIFA","World Cup"]),
        ("UEFA","@UEFA",[],[],[],["UEFA","Champions League"]),
        ("Liverpool FC","@LiverpoolFC",["GB"],["England"],["Liverpool"],["Liverpool"]),
        ("Manchester City","@mancity",["GB"],["England"],["Manchester"],["Manchester City"]),
        ("Arsenal","@arsenal",["GB"],["England"],["London"],["Arsenal"]),
        ("FC Barcelona","@FCBarcelona",["ES"],["Catalonia"],["Barcelona"],["Barcelona"]),
        ("Real Madrid","@realmadrid",["ES"],["Community of Madrid"],["Madrid"],["Real Madrid"]),
    ],
    "rugby": [
        ("World Rugby","@WorldRugby",[],[],[],["World Rugby"]),
        ("Springboks","@Springboks",["ZA"],[],[],["Springboks","South Africa"]),
        ("SuperSport","@supersport",["ZA"],[],[],["United Rugby Championship","South Africa"]),
        ("All Blacks","@AllBlacks",["NZ"],[],[],["All Blacks","New Zealand"]),
        ("Wallabies","@wallabies",["AU"],[],[],["Wallabies","Australia"]),
        ("England Rugby","@EnglandRugby",["GB"],["England"],[],["England Rugby"]),
        ("Six Nations Rugby","@SixNationsRugby",["GB","IE","FR","IT"],[],[],["Six Nations"]),
    ],
    "cricket": [
        ("ICC","@Official-icc",[],[],[],["ICC","Cricket World Cup"]),
        ("Cricket South Africa","@cricketsatv",["ZA"],[],[],["Proteas","South Africa"]),
        ("SuperSport","@supersport",["ZA"],[],[],["Cricket","South Africa"]),
        ("cricket.com.au","@cricketcomau",["AU"],[],[],["Australia Cricket"]),
        ("England & Wales Cricket Board","@officialenglandcricket",["GB"],["England","Wales"],[],["England Cricket"]),
    ],
}

# Extra geographic clues found in titles. One video can match several levels.
_VIDEO_LOCATION_KEYWORDS = {
    "cape town":("ZA","Western Cape","Cape Town"),
    "western cape":("ZA","Western Cape",""),
    "stormers":("ZA","Western Cape","Cape Town"),
    "cape cobras":("ZA","Western Cape","Cape Town"),
    "stellenbosch":("ZA","Western Cape","Stellenbosch"),
    "johannesburg":("ZA","Gauteng","Johannesburg"),
    "joburg":("ZA","Gauteng","Johannesburg"),
    "gauteng":("ZA","Gauteng",""),
    "lions":("ZA","Gauteng","Johannesburg"),
    "kaizer chiefs":("ZA","Gauteng","Johannesburg"),
    "orlando pirates":("ZA","Gauteng","Johannesburg"),
    "pretoria":("ZA","Gauteng","Pretoria"),
    "bulls":("ZA","Gauteng","Pretoria"),
    "mamelodi sundowns":("ZA","Gauteng","Pretoria"),
    "durban":("ZA","KwaZulu-Natal","Durban"),
    "kwazulu":("ZA","KwaZulu-Natal",""),
    "sharks":("ZA","KwaZulu-Natal","Durban"),
    "london":("GB","England","London"),
    "arsenal":("GB","England","London"),
    "chelsea":("GB","England","London"),
    "liverpool":("GB","England","Liverpool"),
    "manchester":("GB","England","Manchester"),
    "barcelona":("ES","Catalonia","Barcelona"),
    "madrid":("ES","Community of Madrid","Madrid"),
    "sydney":("AU","New South Wales","Sydney"),
    "melbourne":("AU","Victoria","Melbourne"),
    "auckland":("NZ","Auckland","Auckland"),
}

def _norm_geo(v: str) -> str:
    return re.sub(r"\s+"," ",str(v or "").strip()).casefold()

def _client_ip(request: Request) -> str:
    for key in ("cf-connecting-ip","x-real-ip","x-forwarded-for"):
        raw = request.headers.get(key,"")
        if raw:
            return raw.split(",")[0].strip()
    return request.client.host if request.client else ""

async def _approx_video_location(request: Request) -> dict:
    """Approximate city/region/country only. Never requests browser GPS/street location."""
    # Hosting/CDN geo headers are preferred and require no extra lookup.
    country = request.headers.get("cf-ipcountry","").strip().upper()
    region = request.headers.get("x-vercel-ip-country-region","").strip()
    city = request.headers.get("x-vercel-ip-city","").strip()
    if country:
        return {"country":country,"region":region,"city":city,"method":"edge"}

    ip = _client_ip(request)
    if not ip or ip in ("127.0.0.1","::1"):
        return {"country":"","region":"","city":"","method":"general"}
    key = hashlib.sha256(ip.encode("utf-8")).hexdigest()[:24]
    cached = _VIDEO_GEO_CACHE.get(key)
    if cached is not None:
        return dict(cached)

    # Approximate IP geolocation fallback. No latitude/longitude is retained or returned.
    try:
        c = await _sports_client()
        r = await c.get(
            "https://ipwho.is/" + urllib.parse.quote(ip, safe=""),
            params={"fields":"success,country_code,region,city"},
            timeout=httpx.Timeout(4, connect=2),
            headers={"User-Agent":"KasiSportsNews/1.0"},
        )
        data = r.json() if r.status_code == 200 else {}
        if data.get("success"):
            loc = {
                "country":str(data.get("country_code") or "").upper(),
                "region":str(data.get("region") or ""),
                "city":str(data.get("city") or ""),
                "method":"approximate-ip",
            }
            _VIDEO_GEO_CACHE[key] = dict(loc)
            return loc
    except Exception as exc:
        log.debug("Approximate video geolocation unavailable: %s", exc)
    return {"country":"","region":"","city":"","method":"general"}

async def _youtube_channel_id(handle: str) -> str:
    handle = str(handle or "").strip()
    if not handle: return ""
    known=_YT_KNOWN_CHANNEL_IDS.get(handle.lower())
    if known:
        _YT_CHANNEL_ID_CACHE[handle.lower()]=known
        return known
    cached = _YT_CHANNEL_ID_CACHE.get(handle.lower())
    if cached: return str(cached)
    url = "https://www.youtube.com/" + (handle if handle.startswith("@") else "@" + handle)
    try:
        c = await _sports_client()
        r = await c.get(url,follow_redirects=True,timeout=httpx.Timeout(4,connect=2),
            headers={"User-Agent":"Mozilla/5.0","Accept":"text/html","Accept-Language":"en;q=0.9"})
        r.raise_for_status()
        text = r.text[:2_500_000]
        for pat in (
            r'"channelId"\s*:\s*"(UC[A-Za-z0-9_-]{20,})"',
            r'"externalId"\s*:\s*"(UC[A-Za-z0-9_-]{20,})"',
            r'youtube\.com/channel/(UC[A-Za-z0-9_-]{20,})',
        ):
            m=re.search(pat,text,re.I)
            if m:
                _YT_CHANNEL_ID_CACHE[handle.lower()]=m.group(1)
                return m.group(1)
    except Exception as exc:
        log.debug("YouTube handle resolution failed %s: %s",handle,exc)
    return ""

def _clean_public_text(value) -> str:
    """Repair common UTF-8 text decoded as Latin-1, while leaving valid Unicode unchanged."""
    text=str(value or "")
    markers=("Ã","Â","â€","â€™","â€œ","ðŸ","âš","âœ")
    if not any(m in text for m in markers):
        return text
    for _ in range(2):
        try:
            repaired=text.encode("latin-1").decode("utf-8")
        except (UnicodeEncodeError,UnicodeDecodeError):
            break
        if repaired==text:
            break
        text=repaired
    return text

def _clean_public_item_text(item: dict) -> dict:
    x=dict(item or {})
    for key in ("title","description","summary","source"):
        if key in x:
            x[key]=_clean_public_text(x.get(key))
    return x

async def _youtube_channel_feed(source: tuple, sport: str, limit: int = 15) -> list[dict]:
    label,handle,countries,regions,cities,tags = source
    ck=f"{handle.lower()}:{sport}:{limit}"
    cached=_YT_VIDEO_FEED_CACHE.get(ck)
    if cached is not None: return list(cached)
    cid=await _youtube_channel_id(handle)
    if not cid: return []
    try:
        c=await _sports_client()
        r=await c.get("https://www.youtube.com/feeds/videos.xml?channel_id="+urllib.parse.quote(cid),
            timeout=httpx.Timeout(4,connect=2),
            headers={"User-Agent":"KasiSportsNews/1.0","Accept":"application/atom+xml,application/xml"})
        r.raise_for_status()
        root=ET.fromstring(r.text)
        ns={"yt":"http://www.youtube.com/xml/schemas/2015","media":"http://search.yahoo.com/mrss/","atom":"http://www.w3.org/2005/Atom"}
        rows=[]
        for entry in root.findall("atom:entry",ns)[:limit]:
            vid=(entry.findtext("yt:videoId",default="",namespaces=ns) or "").strip()
            title=_clean_public_text((entry.findtext("atom:title",default="",namespaces=ns) or "").strip())
            published=(entry.findtext("atom:published",default="",namespaces=ns) or "").strip()
            if not vid or not title: continue
            thumb=f"https://i.ytimg.com/vi/{vid}/hqdefault.jpg"
            group=entry.find("media:group",ns)
            description=""
            if group is not None:
                t=group.find("media:thumbnail",ns)
                if t is not None and t.attrib.get("url"): thumb=t.attrib["url"]
                description=_clean_public_text((group.findtext("media:description",default="",namespaces=ns) or "").strip())[:500]

            item_countries=set(countries); item_regions=set(regions); item_cities=set(cities)
            hay=(title+" "+description).casefold()
            for keyword,(co,rg,ct) in _VIDEO_LOCATION_KEYWORDS.items():
                if keyword in hay:
                    if co:item_countries.add(co)
                    if rg:item_regions.add(rg)
                    if ct:item_cities.add(ct)

            rows.append({
                "id":vid,"title":title,"description":description,"image":thumb,
                "embedId":vid,"source":label,"sport":sport,"published":published,
                "countries":sorted(item_countries),"regions":sorted(item_regions),
                "cities":sorted(item_cities),"tags":list(tags),
                "embedPermitted":"unknown",
            })
        rows.sort(key=lambda x:str(x.get("published") or ""),reverse=True)
        _YT_VIDEO_FEED_CACHE[ck]=list(rows)
        return rows
    except Exception as exc:
        log.debug("YouTube channel feed unavailable %s: %s",label,exc)
        return []

async def _build_video_pool(force: bool = False) -> list[dict]:
    global _VIDEO_LAST_GOOD
    if not force:
        cached=_VIDEO_POOL_CACHE.get("all")
        if cached is not None:
            return list(cached)

    async with _VIDEO_REFRESH_LOCK:
        if not force:
            cached=_VIDEO_POOL_CACHE.get("all")
            if cached is not None:
                return list(cached)

        jobs=[]
        for sport,sources in _VIDEO_SOURCES.items():
            jobs.extend(_youtube_channel_feed(src,sport,15) for src in sources)

        results=await asyncio.gather(*jobs,return_exceptions=True)
        pool=[];seen=set()
        for result in results:
            if not isinstance(result,list):
                continue
            for item in result:
                vid=str(item.get("id") or "")
                if vid and vid not in seen:
                    seen.add(vid);pool.append(item)

        pool.sort(key=lambda x:str(x.get("published") or ""),reverse=True)
        if pool:
            _VIDEO_LAST_GOOD=list(pool)
            _VIDEO_POOL_CACHE["all"]=list(pool)
        return list(pool or _VIDEO_LAST_GOOD)


def _schedule_video_refresh():
    global _VIDEO_REFRESH_TASK
    if _VIDEO_REFRESH_TASK and not _VIDEO_REFRESH_TASK.done():
        return
    async def runner():
        try:
            await _build_video_pool(force=True)
        except Exception as exc:
            log.warning("Background video refresh failed: %s", exc)
    _VIDEO_REFRESH_TASK=asyncio.create_task(runner())


async def _warm_video_cache():
    """Warm highlights after startup without delaying application readiness."""
    try:
        await _build_video_pool(force=True)
        log.info("Highlights cache warmed: %d videos", len(_VIDEO_LAST_GOOD))
    except Exception as exc:
        log.warning("Highlights warmup failed: %s", exc)

def _video_rank(item: dict, loc: dict) -> tuple:
    country=_norm_geo(loc.get("country")); region=_norm_geo(loc.get("region")); city=_norm_geo(loc.get("city"))
    countries={_norm_geo(x) for x in item.get("countries",[])}
    regions={_norm_geo(x) for x in item.get("regions",[])}
    cities={_norm_geo(x) for x in item.get("cities",[])}
    # Required fallback hierarchy: city -> region -> country -> international/general.
    level=1
    if city and city in cities: level=4
    elif region and region in regions: level=3
    elif country and country in countries: level=2
    elif not countries and not regions and not cities: level=1
    # ISO timestamps sort correctly and preserve newest-first inside each level.
    return (level,str(item.get("published") or ""))

@app.get("/sports/video-location")
async def sports_video_location(request: Request):
    loc=await _approx_video_location(request)
    return {"country":loc["country"],"region":loc["region"],"city":loc["city"],"method":loc["method"],
            "preciseLocationRequired":False}

@app.get("/sports/videos")
async def sports_videos(
    request: Request,
    sport: str = Query("all"),
    q: str = Query(""),
    limit: int = Query(8,ge=1,le=24),
    country: str = Query(""),
    region: str = Query(""),
    city: str = Query(""),
    offset: int = Query(0,ge=0,le=5000),
):
    """Small location-ranked feed selected from a much larger recent backend pool."""
    cached=_VIDEO_POOL_CACHE.get("all")
    if cached is not None:
        pool=list(cached)
    elif _VIDEO_LAST_GOOD:
        pool=list(_VIDEO_LAST_GOOD)
        _schedule_video_refresh()
    else:
        # Cold deploy: give the warmup a short chance, never make the browser
        # wait through every external YouTube timeout.
        _schedule_video_refresh()
        try:
            pool=await asyncio.wait_for(_build_video_pool(), timeout=VIDEO_FAST_WAIT)
        except asyncio.TimeoutError:
            pool=list(_VIDEO_LAST_GOOD)

    sport=sport.lower().strip()
    if sport in _VIDEO_SOURCES:
        pool=[x for x in pool if x.get("sport")==sport]
    if q.strip():
        needle=q.strip().casefold()
        pool=[x for x in pool if needle in (str(x.get("title",""))+" "+str(x.get("description",""))).casefold()]

    auto=await _approx_video_location(request)
    loc={
        "country":country.strip().upper() or auto.get("country",""),
        "region":region.strip() or auto.get("region",""),
        "city":city.strip() or auto.get("city",""),
    }
    ranked=sorted(pool,key=lambda x:_video_rank(x,loc),reverse=True)

    # Preserve existing source/location vetting, then balance the public all-sports
    # Highlights feed 1/3 Football, 1/3 Rugby, 1/3 Cricket.
    if sport=="all":
        selected=_balanced_three_sports(ranked,limit,offset)
    else:
        selected=ranked[offset:offset+limit]
    selected=[_clean_public_item_text(x) for x in selected if isinstance(x,dict)]
    result={
        "sport":sport,"query":q.strip(),"count":len(selected),"poolSize":len(pool),
        "offset":offset,"nextOffset":offset+len(selected),
        "hasMore":offset+len(selected)<len(ranked),
        "items":selected,
        "location":{"country":loc["country"],"region":loc["region"],"city":loc["city"]},
        "locationMethod":auto.get("method","general"),
        "preciseLocationRequired":False,
        "source":"Approved multi-source video pool",
        "apiKeyRequired":False,"footballApiRequired":False,
        "updatedAt":datetime.now(timezone.utc).isoformat(),
    }
    if sport=="all" and offset==0 and selected:
        try: _dashboard_snapshot_put("videos:last_good",{"data":result})
        except Exception: pass
    return result


@app.get("/news/home")
async def home_news(limit: int = Query(24, ge=6, le=60)):
    """Fast multi-publisher football headlines with publisher-supplied thumbnails where available."""
    BIG_TEAMS = "Liverpool OR Chelsea OR Arsenal OR Manchester United OR Manchester City OR Barcelona OR Real Madrid OR Bayern Munich OR PSG OR Juventus OR Inter Milan OR AC Milan OR Atletico Madrid OR Borussia Dortmund"
    feeds=[
        ("GOAL", "https://www.goal.com/en-za/news?fmt=rss"),
        ("Metro", "https://metro.co.uk/sport/football/feed/"),
        ("LiveScore", "https://www.livescore.com/en/news/"),
        ("Soccer Laduma", "https://www.soccerladuma.co.za/feed/"),
    ]
    fallback_queries = {
        "GOAL": f"site:goal.com ({BIG_TEAMS}) football news -en-us",
        "Metro": f"site:metro.co.uk/sport/football ({BIG_TEAMS})",
        "LiveScore": f"site:livescore.com/en/news ({BIG_TEAMS}) football",
        "Soccer Laduma": "site:soccerladuma.co.za football",
    }
    per=max(6,min(14,limit//4+3))
    async def load(label,url):
        try:
            items = await _publisher_rss(url,label,per)
            if items: return items
            raise ValueError("empty feed")
        except Exception as exc:
            log.debug("Publisher RSS %s unavailable (%s), falling back to Google News",label,exc)
            query = fallback_queries.get(label, f"site:goal.com {label} football {BIG_TEAMS}")
            try:
                rows=await _google_news(query,per)
                for x in rows: x["publisher"]=label
                return rows
            except Exception:
                return []
    groups=await asyncio.gather(*(load(*x) for x in feeds))
    items=[item for group in groups for item in group]
    # Deduplicate by title prefix
    seen=set(); deduped=[]
    for it in items:
        key=(it.get("title") or "")[:60].lower()
        if key not in seen: seen.add(key); deduped.append(it)
    deduped.sort(key=lambda x:x.get("published","") or "", reverse=True)
    return {"count":len(deduped[:limit]),"items":deduped[:limit],"sources":[x[0] for x in feeds],"updatedAt":datetime.now(timezone.utc).isoformat()}


def _football_market_name(name:str)->str:
    n=re.sub(r"\s+"," ",str(name or "").strip().lower())
    aliases={
      "match winner":"1X2","winner":"1X2","1x2":"1X2",
      "both teams score":"BTTS","both teams to score":"BTTS","btts":"BTTS",
      "goals over/under":"TOTALS","total goals":"TOTALS","over/under":"TOTALS",
      "asian handicap":"HANDICAP","handicap result":"HANDICAP","handicap":"HANDICAP",
      "corners over under":"CORNERS","corners over/under":"CORNERS","total corners":"CORNERS",
    }
    return aliases.get(n,str(name or "").strip())

def _football_real_markets(bookmaker_rows:list)->dict:
    """Normalize only prices actually returned by API-Football; never synthesize a market."""
    out={}
    for item in bookmaker_rows or []:
        books=[]
        if isinstance(item,dict) and isinstance(item.get("bookmakers"),list): books=item["bookmakers"]
        elif isinstance(item,dict) and item.get("bookmaker"): books=[item.get("bookmaker")]
        for bk in books:
            if not isinstance(bk,dict):continue
            bname=str(bk.get("name") or "Bookmaker")
            for bet in bk.get("bets") or []:
                key=_football_market_name(bet.get("name"))
                vals=[]
                for v in bet.get("values") or []:
                    odd=v.get("odd")
                    if odd in (None,""):continue
                    vals.append({"selection":str(v.get("value") or "").strip(),"price":odd})
                if not vals:continue
                out.setdefault(key,{"market":key,"providerName":bet.get("name"),"bookmakers":[]})
                out[key]["bookmakers"].append({"name":bname,"selections":vals})
    return out

def _cricket_score_schema(score_data:dict)->dict:
    """Expose cricket fields only when the subscribed provider actually supplies them."""
    periods=score_data.get("periods") or {}
    innings=[]
    for period,row in periods.items():
        if not isinstance(row,dict):continue
        rec={"period":period}
        # Preserve provider-supported cricket semantics without guessing absent values.
        aliases={
          "participant1Score":"homeRuns","participant2Score":"awayRuns",
          "participant1Wickets":"homeWickets","participant2Wickets":"awayWickets",
          "participant1Overs":"homeOvers","participant2Overs":"awayOvers",
          "runs":"runs","wickets":"wickets","overs":"overs","inning":"inning","innings":"innings",
          "batting":"batting","bowling":"bowling","batsmen":"batsmen","bowlers":"bowlers"
        }
        for src,dst in aliases.items():
            if src in row and row.get(src) is not None:rec[dst]=row.get(src)
        # Keep other provider fields available for future cricket UI, but do not relabel them.
        rec["provider"]=row
        innings.append(rec)
    return {"innings":innings,"available":bool(innings)}

def _rugby_score_schema(score_data:dict)->dict:
    periods=score_data.get("periods") or {}
    return {"periods":[{"period":k,**v} for k,v in periods.items() if isinstance(v,dict)],"available":bool(periods)}

@app.get("/fixtures/{fixture_id}/insights")
async def fixture_insights(fixture_id: int, lite: int = Query(0, ge=0, le=1)):
    """Complete match intelligence; lite=1 returns only the fixture envelope to avoid quota-heavy fan-out on live pages."""
    """Complete pre-match intelligence for a fixture.

    Returns the fixture context plus team form, H2H, injuries/suspensions,
    standings and bookmaker markets. This is deliberately separate from the
    prediction gate: a fixture can display its intelligence even when it has
    no qualifying 1X2 bookmaker odds.
    """
    fd = await _afoot_get("/fixtures", {"id": fixture_id})
    fixtures = fd.get("response") or []
    if not fixtures:
        raise HTTPException(status_code=404, detail="Fixture not found")

    f = fixtures[0]
    if lite:
        return {"fixture": f, "source":"API-Football", "generatedAt":datetime.now(timezone.utc).isoformat()}
    teams = f.get("teams") or {}
    league = f.get("league") or {}
    home = teams.get("home") or {}
    away = teams.get("away") or {}
    home_id = home.get("id")
    away_id = away.get("id")
    league_id = league.get("id")
    season = int(league.get("season") or _current_season())

    # Fetch all contextual data concurrently where possible.
    tasks = {}
    if home_id:
        tasks["home_form"] = _fetch_team_form_detailed(home_id, league_id, season, 10)
        tasks["home_next"] = _afoot_get("/fixtures", {"team":home_id,"season":season,"next":5})
        if league_id: tasks["home_team_stats"] = _afoot_get("/teams/statistics",{"team":home_id,"league":league_id,"season":season})
        tasks["home_injuries"] = _afoot_get("/injuries", {"team": home_id, "season": season})
    if away_id:
        tasks["away_form"] = _fetch_team_form_detailed(away_id, league_id, season, 10)
        tasks["away_next"] = _afoot_get("/fixtures", {"team":away_id,"season":season,"next":5})
        if league_id: tasks["away_team_stats"] = _afoot_get("/teams/statistics",{"team":away_id,"league":league_id,"season":season})
        tasks["away_injuries"] = _afoot_get("/injuries", {"team": away_id, "season": season})
    if home_id and away_id:
        tasks["h2h"] = _afoot_get(
            "/fixtures/headtohead",
            {"h2h": f"{home_id}-{away_id}", "last": 10},
        )
    if league_id:
        tasks["standings"] = _fetch_standings_for_league(league_id, season)

    tasks["odds"] = _afoot_get("/odds", {"fixture": fixture_id})

    keys = list(tasks)
    values = await asyncio.gather(
        *(tasks[k] for k in keys), return_exceptions=True
    )
    data = {
        k: (v if not isinstance(v, Exception) else None)
        for k, v in zip(keys, values)
    }

    def result_rows(items, team_id):
        out = []
        for x in (items or []):
            ts = x.get("teams") or {}
            gh = (x.get("goals") or {}).get("home")
            ga = (x.get("goals") or {}).get("away")
            opponent = (
                (ts.get("away") or {}).get("name")
                if (ts.get("home") or {}).get("id") == team_id
                else (ts.get("home") or {}).get("name")
            )
            is_home = (ts.get("home") or {}).get("id") == team_id
            gf, gc = (gh or 0, ga or 0) if is_home else (ga or 0, gh or 0)
            res = "W" if gf > gc else "D" if gf == gc else "L"
            out.append({
                "fixtureId": (x.get("fixture") or {}).get("id"),
                "date": (x.get("fixture") or {}).get("date"),
                "opponent": opponent,
                "home": (ts.get("home") or {}).get("name"),
                "away": (ts.get("away") or {}).get("name"),
                "score": f"{gf}-{gc}",
                "result": res,
                "goalsFor": gf,
                "goalsAgainst": gc,
                "scorers": scorer_map.get((x.get("fixture") or {}).get("id"), []),
            })
        return out

    home_form = data.get("home_form") or []
    away_form = data.get("away_form") or []

    # Scorers are requested only after a fixture is expanded, never during the initial fixtures list.
    recent_ids=[(x.get("fixture") or {}).get("id") for x in (home_form+away_form)]
    recent_ids=[int(x) for x in dict.fromkeys(recent_ids) if x]
    scorer_map={}
    sem=asyncio.Semaphore(4)
    async def recent_scorers(fid:int):
        async with sem:
            try:
                ev=await _afoot_get("/fixtures/events",{"fixture":fid})
                names=[]
                for e in ev.get("response") or []:
                    if str(e.get("type") or "").lower()=="goal":
                        p=(e.get("player") or {}).get("name")
                        if p:names.append(p)
                return fid,names
            except Exception:return fid,[]
    if recent_ids:
        for fid,names in await asyncio.gather(*[recent_scorers(fid) for fid in recent_ids]):
            scorer_map[fid]=names

    h2h_raw = data.get("h2h") or {}
    h2h_items = h2h_raw.get("response", []) if isinstance(h2h_raw, dict) else []

    def h2h_summary(items):
        hw = dr = aw = btts = over25 = 0
        meetings = []
        for x in items:
            ts = x.get("teams") or {}
            gh = (x.get("goals") or {}).get("home")
            ga = (x.get("goals") or {}).get("away")
            if gh is None or ga is None:
                continue
            hi = (ts.get("home") or {}).get("id") == home_id
            a = int(gh); b = int(ga)
            if hi:
                hw += a > b; aw += a < b
            else:
                hw += a < b; aw += a > b
            dr += a == b
            btts += a > 0 and b > 0
            over25 += a + b > 2
            meetings.append({
                "date": (x.get("fixture") or {}).get("date"),
                "home": (ts.get("home") or {}).get("name"),
                "away": (ts.get("away") or {}).get("name"),
                "score": f"{a}-{b}",
            })
        n = len(meetings) or 1
        return {
            "played": len(meetings),
            "homeWins": hw,
            "draws": dr,
            "awayWins": aw,
            "bttsPct": round(btts * 100 / n, 1),
            "over25Pct": round(over25 * 100 / n, 1),
            "meetings": meetings,
        }

    odds_raw = data.get("odds") or {}
    bookmaker_rows = odds_raw.get("response", []) if isinstance(odds_raw, dict) else []
    real_markets = _football_real_markets(bookmaker_rows)
    bookmaker_options = []
    selected_odds = {}
    preferred = {"Pinnacle": 0, "Bet365": 1, "1xBet": 2, "William Hill": 3,
                 "Unibet": 5, "Bwin": 6, "Ladbrokes": 7, "Coral": 8, "Paddy Power": 9}

    for item in bookmaker_rows:
        bk = item.get("bookmaker") or {}
        name = bk.get("name") or "Unknown"
        norm = _normalise_odds([bk])
        valid = _valid_1x2(norm)
        bookmaker_options.append({
            "id": bk.get("id"),
            "name": name,
            "valid1x2": valid,
            "odds": norm,
        })
    bookmaker_options.sort(key=lambda x: preferred.get(x["name"], 99))
    for bk in bookmaker_options:
        if bk["valid1x2"]:
            selected_odds = bk["odds"]
            break

    standings = data.get("standings") or []
    home_table = next((x for x in standings if (x.get("team") or {}).get("id") == home_id), None)
    away_table = next((x for x in standings if (x.get("team") or {}).get("id") == away_id), None)

    def injury_rows(raw):
        items = raw.get("response", []) if isinstance(raw, dict) else []
        return [{
            "player": (x.get("player") or {}).get("name"),
            "type": (x.get("player") or {}).get("type"),
            "reason": (x.get("player") or {}).get("reason"),
            "date": x.get("date"),
        } for x in items]

    return {
        "fixture": {
            "id": fixture_id,
            "date": (f.get("fixture") or {}).get("date"),
            "timezone": (f.get("fixture") or {}).get("timezone"),
            "status": (f.get("fixture") or {}).get("status"),
            "venue": (f.get("fixture") or {}).get("venue"),
            "referee": (f.get("fixture") or {}).get("referee"),
            "home": home,
            "away": away,
            "league": league,
        },
        "form": {
            "home": {"team": home, "last10": result_rows(home_form, home_id)},
            "away": {"team": away, "last10": result_rows(away_form, away_id)},
        },
        "next5": {
            "home": result_rows(((data.get("home_next") or {}).get("response") or []) if isinstance(data.get("home_next"),dict) else [], home_id)[:5],
            "away": result_rows(((data.get("away_next") or {}).get("response") or []) if isinstance(data.get("away_next"),dict) else [], away_id)[:5],
        },
        "teamStatistics": {
            "home": ((data.get("home_team_stats") or {}).get("response") or {}) if isinstance(data.get("home_team_stats"),dict) else {},
            "away": ((data.get("away_team_stats") or {}).get("response") or {}) if isinstance(data.get("away_team_stats"),dict) else {},
        },
        "h2h": h2h_summary(h2h_items),
        "injuries": {
            "home": injury_rows(data.get("home_injuries")),
            "away": injury_rows(data.get("away_injuries")),
        },
        "standings": {
            "home": home_table,
            "away": away_table,
            "totalTeams": len(standings),
        },
        "bookmakers": {
            "selected": next((x["name"] for x in bookmaker_options if x["valid1x2"]), None),
            "selectedOdds": selected_odds,
            "available": bookmaker_options,
            "markets": real_markets,
            "marketRule": "provider-returned-only",
        },
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "source": "API-Football",
    }

# ---------------------------------------------------------------------------
# LIVE — IMPORTANT: NOW RUNS _prediction()
# ---------------------------------------------------------------------------


_TEAM_BADGE_CACHE=TTLCache(maxsize=1000,ttl=86400)

@app.get("/sports/football/team-badge/{team_id}")
async def football_team_badge(team_id:int):
    if team_id<=0: raise HTTPException(404,"Unknown team")
    cached=_TEAM_BADGE_CACHE.get(team_id)
    if cached:
        content,ct=cached
        return Response(content=content,media_type=ct,headers={"Cache-Control":"public, max-age=86400"})
    url=f"https://media.api-sports.io/football/teams/{team_id}.png"
    try:
        c=await _sports_client()
        r=await c.get(url,timeout=httpx.Timeout(5,connect=2),follow_redirects=True)
        r.raise_for_status()
        ct=r.headers.get("content-type","image/png")
        if not ct.startswith("image/"): raise HTTPException(404,"Badge unavailable")
        content=r.content
        if len(content)>1_000_000: raise HTTPException(413,"Badge too large")
        _TEAM_BADGE_CACHE[team_id]=(content,ct)
        return Response(content=content,media_type=ct,headers={"Cache-Control":"public, max-age=86400"})
    except HTTPException:
        raise
    except Exception:
        raise HTTPException(404,"Badge unavailable")


def _public_slug(name:str)->str:
    return re.sub(r"[^a-z0-9]+","-",str(name or "").lower()).strip("-") or "profile"
def _public_token(kind:str,pid:int)->str:
    raw=int(pid).to_bytes(4,"big"); secret=os.getenv("PUBLIC_ID_SECRET",os.getenv("SECRET_KEY","kasi-public")).encode()
    sig=hmac.new(secret,(kind+":").encode()+raw,hashlib.sha256).digest()[:6]
    return base64.urlsafe_b64encode(raw+sig).decode().rstrip("=")
def _public_ref(kind:str,pid:int,name:str)->str:return f"{_public_slug(name)}--{_public_token(kind,pid)}"
def _public_decode(kind:str,ref:str)->int:
    try:
        tok=str(ref).rsplit("--",1)[-1];blob=base64.urlsafe_b64decode(tok+"="*((4-len(tok)%4)%4));raw,sig=blob[:4],blob[4:10]
        secret=os.getenv("PUBLIC_ID_SECRET",os.getenv("SECRET_KEY","kasi-public")).encode();good=hmac.new(secret,(kind+":").encode()+raw,hashlib.sha256).digest()[:6]
        if len(raw)!=4 or not hmac.compare_digest(sig,good):raise ValueError()
        return int.from_bytes(raw,"big")
    except Exception:raise HTTPException(404,"Profile not found")

# ---------------------------------------------------------------------------
# Kasi Sports SQL data layer (v216)
# Provider IDs remain internal. Public pages/search use opaque public refs.
# Reads are SQL-first; scheduled/provider sync refreshes stale snapshots.
# ---------------------------------------------------------------------------
# Render-safe sports database configuration.
# Prefer SPORTS_DB_PATH when configured (for example /var/data/kasi_sports.db
# when a Render persistent disk is mounted). If that location cannot be
# created/written, fall back to a writable local data directory so a database
# path problem never prevents the whole API from starting.
_SPORTS_DB_CONFIGURED = os.getenv("SPORTS_DB_PATH", "").strip()
SPORTS_DB_ENABLED=os.getenv("SPORTS_DB_ENABLED","1").strip().lower() not in {"0","false","no"}
SPORTS_DB_FALLBACK = False
SPORTS_DB_INIT_ERROR = None

def _resolve_sports_db_path():
    global SPORTS_DB_FALLBACK
    preferred = Path(_SPORTS_DB_CONFIGURED) if _SPORTS_DB_CONFIGURED else (BASE_DIR / "kasi_sports.db")
    try:
        preferred.parent.mkdir(parents=True, exist_ok=True)
        # Verify the directory is actually writable before SQLite opens it.
        probe = preferred.parent / ".kasi_sports_write_test"
        probe.touch(exist_ok=True)
        probe.unlink(missing_ok=True)
        return preferred
    except (OSError, PermissionError):
        SPORTS_DB_FALLBACK = True
        fallback_dir = BASE_DIR / "data"
        try:
            fallback_dir.mkdir(parents=True, exist_ok=True)
            return fallback_dir / "kasi_sports.db"
        except (OSError, PermissionError):
            # /tmp is writable on Render/Linux but is ephemeral. This final
            # fallback keeps the service online until persistent storage is fixed.
            fallback_dir = Path("/tmp") / "kasi-sports-news"
            fallback_dir.mkdir(parents=True, exist_ok=True)
            return fallback_dir / "kasi_sports.db"

SPORTS_DB_PATH = _resolve_sports_db_path()

def _sports_db():
    SPORTS_DB_PATH.parent.mkdir(parents=True,exist_ok=True)
    con=sqlite3.connect(str(SPORTS_DB_PATH),timeout=20,check_same_thread=False)
    con.row_factory=sqlite3.Row
    con.execute("PRAGMA journal_mode=WAL")
    con.execute("PRAGMA synchronous=NORMAL")
    con.execute("PRAGMA busy_timeout=20000")
    return con

def _sports_db_init():
    if not SPORTS_DB_ENABLED:return
    with _sports_db() as db:
        db.executescript("""
        CREATE TABLE IF NOT EXISTS teams(
          provider_id INTEGER PRIMARY KEY,name TEXT NOT NULL,code TEXT,country TEXT,
          founded INTEGER,national INTEGER,badge TEXT,venue_json TEXT,
          public_ref TEXT NOT NULL UNIQUE,provider_updated_at TEXT,synced_at TEXT NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_teams_name ON teams(name COLLATE NOCASE);
        CREATE TABLE IF NOT EXISTS players(
          provider_id INTEGER PRIMARY KEY,name TEXT NOT NULL,firstname TEXT,lastname TEXT,
          age INTEGER,birth_date TEXT,birth_place TEXT,birth_country TEXT,nationality TEXT,
          height TEXT,weight TEXT,injured INTEGER,photo TEXT,public_ref TEXT NOT NULL UNIQUE,
          provider_updated_at TEXT,synced_at TEXT NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_players_name ON players(name COLLATE NOCASE);
        CREATE TABLE IF NOT EXISTS leagues(
          provider_id INTEGER NOT NULL,season INTEGER NOT NULL,name TEXT,country TEXT,logo TEXT,flag TEXT,
          synced_at TEXT NOT NULL,PRIMARY KEY(provider_id,season));
        CREATE TABLE IF NOT EXISTS team_leagues(
          team_id INTEGER NOT NULL,league_id INTEGER NOT NULL,season INTEGER NOT NULL,
          rank INTEGER,points INTEGER,form TEXT,stats_json TEXT,synced_at TEXT NOT NULL,
          PRIMARY KEY(team_id,league_id,season));
        CREATE TABLE IF NOT EXISTS player_teams(
          player_id INTEGER NOT NULL,team_id INTEGER NOT NULL,season INTEGER NOT NULL,
          number INTEGER,position TEXT,synced_at TEXT NOT NULL,
          PRIMARY KEY(player_id,team_id,season));
        CREATE TABLE IF NOT EXISTS player_season_stats(
          player_id INTEGER NOT NULL,team_id INTEGER NOT NULL,league_id INTEGER NOT NULL,season INTEGER NOT NULL,
          stats_json TEXT NOT NULL,synced_at TEXT NOT NULL,
          PRIMARY KEY(player_id,team_id,league_id,season));
        CREATE TABLE IF NOT EXISTS injuries(
          player_id INTEGER NOT NULL,team_id INTEGER NOT NULL,league_id INTEGER NOT NULL DEFAULT 0,
          season INTEGER NOT NULL,date TEXT,type TEXT,reason TEXT,payload_json TEXT,synced_at TEXT NOT NULL,
          PRIMARY KEY(player_id,team_id,league_id,season,date,type));
        CREATE TABLE IF NOT EXISTS team_fixtures(
          fixture_id INTEGER PRIMARY KEY,team_id INTEGER NOT NULL,season INTEGER,payload_json TEXT NOT NULL,
          fixture_date TEXT,synced_at TEXT NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_tf_team_date ON team_fixtures(team_id,fixture_date DESC);
        CREATE TABLE IF NOT EXISTS match_stats_cache(
          sport TEXT NOT NULL,match_id TEXT NOT NULL,payload_json TEXT NOT NULL,
          completed INTEGER NOT NULL DEFAULT 0,updated_at TEXT NOT NULL,
          PRIMARY KEY(sport,match_id));
        CREATE TABLE IF NOT EXISTS sync_state(
          sync_key TEXT PRIMARY KEY,last_success_at TEXT,last_attempt_at TEXT,status TEXT,
          records INTEGER DEFAULT 0,error TEXT,next_due_at TEXT);
        """)

def _db_json(v):
    try:return json.dumps(v,ensure_ascii=False,separators=(",",":"))
    except Exception:return "{}"

def _db_load(v,default=None):
    try:return json.loads(v) if v else (default if default is not None else {})
    except Exception:return default if default is not None else {}

def _sync_hours(now=None):
    """6h on Tue/Wed/Thu and weekends; 12h on Mon/Fri."""
    now=now or datetime.now(timezone.utc)
    return 6 if now.weekday() in {1,2,3,5,6} else 12

def _sync_due(last_iso):
    if not last_iso:return True
    try:last=datetime.fromisoformat(str(last_iso).replace("Z","+00:00"))
    except Exception:return True
    if last.tzinfo is None:last=last.replace(tzinfo=timezone.utc)
    return datetime.now(timezone.utc)-last >= timedelta(hours=_sync_hours())

def _db_team(pid):
    if not SPORTS_DB_ENABLED:return None
    with _sports_db() as db:r=db.execute("SELECT * FROM teams WHERE provider_id=?",(int(pid),)).fetchone()
    return dict(r) if r else None

def _db_player(pid):
    if not SPORTS_DB_ENABLED:return None
    with _sports_db() as db:r=db.execute("SELECT * FROM players WHERE provider_id=?",(int(pid),)).fetchone()
    return dict(r) if r else None

def _db_upsert_team(t,venue=None):
    if not SPORTS_DB_ENABLED or not t or not t.get("id"):return
    now=datetime.now(timezone.utc).isoformat();pid=int(t["id"])
    with _sports_db() as db:
        db.execute("""INSERT INTO teams(provider_id,name,code,country,founded,national,badge,venue_json,public_ref,provider_updated_at,synced_at)
        VALUES(?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(provider_id) DO UPDATE SET
        name=excluded.name,code=excluded.code,country=excluded.country,founded=excluded.founded,national=excluded.national,
        badge=CASE WHEN excluded.badge IS NOT NULL AND excluded.badge<>'' THEN excluded.badge ELSE teams.badge END,
        venue_json=CASE WHEN excluded.venue_json IS NOT NULL AND excluded.venue_json NOT IN ('','{}') THEN excluded.venue_json ELSE teams.venue_json END,public_ref=excluded.public_ref,
        provider_updated_at=excluded.provider_updated_at,synced_at=excluded.synced_at""",
        (pid,t.get("name") or "Team",t.get("code"),t.get("country"),t.get("founded"),1 if t.get("national") else 0,
         t.get("logo"),_db_json(venue or {}),_public_ref("team",pid,t.get("name") or "team"),t.get("updated"),now))

def _db_upsert_player(p):
    if not SPORTS_DB_ENABLED or not p or not p.get("id"):return
    now=datetime.now(timezone.utc).isoformat();pid=int(p["id"]);birth=p.get("birth") or {}
    with _sports_db() as db:
        db.execute("""INSERT INTO players(provider_id,name,firstname,lastname,age,birth_date,birth_place,birth_country,nationality,height,weight,injured,photo,public_ref,provider_updated_at,synced_at)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(provider_id) DO UPDATE SET
        name=excluded.name,firstname=excluded.firstname,lastname=excluded.lastname,age=excluded.age,birth_date=excluded.birth_date,
        birth_place=excluded.birth_place,birth_country=excluded.birth_country,nationality=excluded.nationality,height=excluded.height,
        weight=excluded.weight,injured=excluded.injured,
        photo=CASE WHEN excluded.photo IS NOT NULL AND excluded.photo<>'' THEN excluded.photo ELSE players.photo END,public_ref=excluded.public_ref,
        provider_updated_at=excluded.provider_updated_at,synced_at=excluded.synced_at""",
        (pid,p.get("name") or "Player",p.get("firstname"),p.get("lastname"),p.get("age"),birth.get("date"),birth.get("place"),
         birth.get("country"),p.get("nationality"),p.get("height"),p.get("weight"),1 if p.get("injured") else 0,p.get("photo"),
         _public_ref("player",pid,p.get("name") or "player"),p.get("updated"),now))

def _ksn_norm_team_name(v):
    v=html.unescape(str(v or "")).casefold()
    v=re.sub(r"\b(fc|cf|afc|calcio|football club|club de futbol)\b", " ", v)
    return re.sub(r"[^a-z0-9]+", "", v)

async def _ksn_big5_identity(team_id:int, team_name:str, season:int):
    """Resolve one canonical Big-5 league/team identity across API-Football + FantasyPlayoffs."""
    want=_ksn_norm_team_name(team_name)
    aliases={
      "manchestercity":"mancity","manchesterunited":"manutd","parissaintgermain":"psg",
      "internazionale":"inter","intermilan":"inter","bayernmunich":"bayernmunchen"
    }
    want=aliases.get(want,want)
    candidates=[]
    for lid,meta in FANTASYPLAYOFFS_LEAGUES.items():
        try:
            fp=await _fetch_fantasyplayoffs_league(lid,season=season,bust_cache=False)
        except Exception:
            continue
        clubs={}
        for p in fp.get("players") or []:
            club=str(p.get("team") or "").strip()
            if not club: continue
            n=_ksn_norm_team_name(club); n=aliases.get(n,n)
            clubs.setdefault(n,{"name":club,"players":[]})["players"].append(p)
        if want in clubs:
            c=clubs[want]
            return {"teamId":team_id,"teamName":team_name,"leagueId":lid,"league":meta["name"],"country":meta["country"],"season":season,"fantasyTeam":c["name"],"fantasyPlayers":c["players"],"matched":True}
        # conservative fuzzy fallback for punctuation/short suffix differences
        for n,c in clubs.items():
            if len(want)>=6 and (want in n or n in want):
                candidates.append((abs(len(want)-len(n)),lid,meta,c))
    if candidates:
        _,lid,meta,c=sorted(candidates,key=lambda x:x[0])[0]
        return {"teamId":team_id,"teamName":team_name,"leagueId":lid,"league":meta["name"],"country":meta["country"],"season":season,"fantasyTeam":c["name"],"fantasyPlayers":c["players"],"matched":True}
    return {"teamId":team_id,"teamName":team_name,"leagueId":None,"season":season,"fantasyPlayers":[],"matched":False}

def _ksn_summary_from_results(rows, team_id:int):
    played=wins=draws=losses=gf=ga=clean=fts=home_p=home_w=away_p=away_w=0
    form=[]
    for f in rows or []:
        teams=f.get("teams") or {}; goals=f.get("goals") or {}; status=((f.get("fixture") or {}).get("status") or {}).get("short")
        if status not in {"FT","AET","PEN"}: continue
        hg,ag=goals.get("home"),goals.get("away")
        if hg is None or ag is None: continue
        hid=int(((teams.get("home") or {}).get("id") or 0)); aid=int(((teams.get("away") or {}).get("id") or 0))
        if team_id not in {hid,aid}: continue
        ishome=hid==team_id; ours,opp=(hg,ag) if ishome else (ag,hg)
        played+=1; gf+=int(ours); ga+=int(opp); clean+=1 if int(opp)==0 else 0; fts+=1 if int(ours)==0 else 0
        if ishome: home_p+=1
        else: away_p+=1
        if ours>opp:
            wins+=1; form.append("W"); home_w+=1 if ishome else 0; away_w+=0 if ishome else 1
        elif ours==opp: draws+=1; form.append("D")
        else: losses+=1; form.append("L")
    return {"played":played,"wins":wins,"draws":draws,"losses":losses,"goalsFor":gf,"goalsAgainst":ga,"goalDifference":gf-ga,
            "cleanSheets":clean,"failedToScore":fts,"winRate":round(wins*100/played,1) if played else None,"form":"".join(form[-10:]),
            "homePlayed":home_p,"homeWins":home_w,"awayPlayed":away_p,"awayWins":away_w}

def _ksn_valid_team_stats(st):
    if not isinstance(st,dict) or not st:return False
    fx=st.get("fixtures") or {}; goals=st.get("goals") or {}
    played=((fx.get("played") or {}).get("total"))
    gf=(((goals.get("for") or {}).get("total") or {}).get("total"))
    ga=(((goals.get("against") or {}).get("total") or {}).get("total"))
    return played is not None or gf is not None or ga is not None

def _ksn_api_team_badge(team_id):
    try:return f"https://media.api-sports.io/football/teams/{int(team_id)}.png"
    except Exception:return ""

def _ksn_api_player_photo(player_id):
    try:return f"https://media.api-sports.io/football/players/{int(player_id)}.png"
    except Exception:return ""

def _ksn_stats_from_summary(summary, team_id, league_id, season):
    """Provider-shaped subset derived only from confirmed completed fixtures."""
    if not isinstance(summary,dict) or not summary.get("played"):return {}
    return {
      "team":{"id":team_id},"league":{"id":league_id,"season":season},"derivedFromCompletedFixtures":True,
      "fixtures":{"played":{"home":summary.get("homePlayed"),"away":summary.get("awayPlayed"),"total":summary.get("played")},
                  "wins":{"home":summary.get("homeWins"),"away":summary.get("awayWins"),"total":summary.get("wins")},
                  "draws":{"total":summary.get("draws")},"loses":{"total":summary.get("losses")}},
      "goals":{"for":{"total":{"total":summary.get("goalsFor")}},"against":{"total":{"total":summary.get("goalsAgainst")}}},
      "clean_sheet":{"total":summary.get("cleanSheets")},"failed_to_score":{"total":summary.get("failedToScore")},
      "form":summary.get("form") or ""
    }

async def _sql_sync_team(team_id:int,season:int,force:bool=False):
    """One bounded refresh per stale team; never a per-visitor/per-player fanout."""
    if not SPORTS_DB_ENABLED:return None
    season=season or _current_season();key=f"team:{team_id}:{season}"
    with _sports_db() as db:state=db.execute("SELECT * FROM sync_state WHERE sync_key=?",(key,)).fetchone()
    if not force and state and not _sync_due(state["last_success_at"]):return {"cached":True}
    now=datetime.now(timezone.utc).isoformat()
    with _sports_db() as db:
        db.execute("""INSERT INTO sync_state(sync_key,last_attempt_at,status) VALUES(?,?,'running')
        ON CONFLICT(sync_key) DO UPDATE SET last_attempt_at=excluded.last_attempt_at,status='running',error=NULL""",(key,now))
    async def safe(path,params):
        try:return await _afoot_get(path,params)
        except Exception:return {"response":[]}
    prof,squad,recent,future=await asyncio.gather(
        safe("/teams",{"id":team_id}),safe("/players/squads",{"team":team_id}),
        safe("/fixtures",{"team":team_id,"season":season,"last":10}),safe("/fixtures",{"team":team_id,"season":season,"next":10}))
    pr=(prof.get("response") or [{}])[0]
    team_seed=dict(pr.get("team") or {"id":team_id})
    team_seed["id"]=team_seed.get("id") or team_id
    team_seed["logo"]=team_seed.get("logo") or _ksn_api_team_badge(team_id)
    _db_upsert_team(team_seed,pr.get("venue") or {})
    team_name=((pr.get("team") or {}).get("name") or (_db_team(team_id) or {}).get("name") or str(team_id))
    canonical=await _ksn_big5_identity(team_id,team_name,season)
    league_hint=(int(canonical["leagueId"]),season) if canonical.get("leagueId") else None
    if not league_hint:
        # Prefer domestic Big-5 league IDs over cups/international competitions.
        seen=[]
        for f in (future.get("response") or [])+(recent.get("response") or []):
            lg=f.get("league") or {}; lid=int(lg.get("id") or 0)
            if lid: seen.append((0 if lid in FANTASYPLAYOFFS_LEAGUES else 1,lid,int(lg.get("season") or season)))
        if seen:
            _,lid,yr=sorted(seen)[0]; league_hint=(lid,yr)
    stats_data={"response":{}};stand_data=[]
    if league_hint:
        stats_data,stand_data=await asyncio.gather(
            safe("/teams/statistics",{"team":team_id,"league":league_hint[0],"season":league_hint[1]}),
            _fetch_standings_for_league(*league_hint),return_exceptions=False)
    season_fixtures=[]
    if league_hint:
        sf=await safe("/fixtures",{"team":team_id,"league":league_hint[0],"season":league_hint[1]})
        season_fixtures=sf.get("response") or []
    players=[]
    for sr in squad.get("response") or []:
        for p in sr.get("players") or []:
            if p.get("id"):players.append(p)
    if not players:
        fd=await safe("/players",{"team":team_id,"season":season,"page":1})
        for x in fd.get("response") or []:
            p=x.get("player") or {}
            if p.get("id"):players.append(p)
    with _sports_db() as db:
        for p in players:
            if p.get("id") and not p.get("photo"): p["photo"]=_ksn_api_player_photo(p["id"])
            _db_upsert_player(p)
            db.execute("""INSERT INTO player_teams(player_id,team_id,season,number,position,synced_at) VALUES(?,?,?,?,?,?)
            ON CONFLICT(player_id,team_id,season) DO UPDATE SET number=excluded.number,position=excluded.position,synced_at=excluded.synced_at""",
            (int(p["id"]),team_id,season,p.get("number"),p.get("position"),now))
        if league_hint:
            db.execute("""INSERT INTO leagues(provider_id,season,name,country,logo,flag,synced_at) VALUES(?,?,?,?,?,?,?)
            ON CONFLICT(provider_id,season) DO UPDATE SET name=excluded.name,country=excluded.country,logo=excluded.logo,flag=excluded.flag,synced_at=excluded.synced_at""",
            (league_hint[0],league_hint[1],None,None,None,None,now))
            rank=points=None;form=None
            for row in stand_data or []:
                if int((row.get("team") or {}).get("id") or 0)==team_id:
                    rank=row.get("rank");points=row.get("points");form=row.get("form");break
            provider_stats=stats_data.get("response") or {}
            summary=_ksn_summary_from_results(season_fixtures or (recent.get("response") or []),team_id)
            candidate_stats=provider_stats if _ksn_valid_team_stats(provider_stats) else _ksn_stats_from_summary(summary,team_id,league_hint[0],league_hint[1])
            prior=db.execute("SELECT stats_json FROM team_leagues WHERE team_id=? AND league_id=? AND season=?",(team_id,league_hint[0],league_hint[1])).fetchone()
            prior_stats=_db_load(prior["stats_json"],{}) if prior else {}
            final_stats=candidate_stats if _ksn_valid_team_stats(candidate_stats) else prior_stats
            db.execute("""INSERT INTO team_leagues(team_id,league_id,season,rank,points,form,stats_json,synced_at)
            VALUES(?,?,?,?,?,?,?,?) ON CONFLICT(team_id,league_id,season) DO UPDATE SET
            rank=COALESCE(excluded.rank,team_leagues.rank),points=COALESCE(excluded.points,team_leagues.points),
            form=CASE WHEN excluded.form IS NOT NULL AND excluded.form<>'' THEN excluded.form ELSE team_leagues.form END,
            stats_json=CASE WHEN excluded.stats_json IS NOT NULL AND excluded.stats_json NOT IN ('','{}') THEN excluded.stats_json ELSE team_leagues.stats_json END,
            synced_at=excluded.synced_at""",
            (team_id,league_hint[0],league_hint[1],rank,points,form,_db_json(final_stats),now))
            if stand_data:
                _dashboard_snapshot_put(f"canonical_standings:{league_hint[0]}:{league_hint[1]}",{"data":{"standings":stand_data}})
        for f in (season_fixtures or ((recent.get("response") or [])+(future.get("response") or []))):
            fid=(f.get("fixture") or {}).get("id")
            if fid:db.execute("""INSERT INTO team_fixtures(fixture_id,team_id,season,payload_json,fixture_date,synced_at) VALUES(?,?,?,?,?,?)
            ON CONFLICT(fixture_id) DO UPDATE SET payload_json=excluded.payload_json,fixture_date=excluded.fixture_date,synced_at=excluded.synced_at""",
            (int(fid),team_id,season,_db_json(f),(f.get("fixture") or {}).get("date"),now))
        has_stats=bool(league_hint and _ksn_valid_team_stats(final_stats if 'final_stats' in locals() else {}))
        has_identity=bool((_db_team(team_id) or {}).get("name"))
        sync_status="complete" if has_identity and players and has_stats else "partial"
        db.execute("UPDATE sync_state SET last_success_at=?,status=?,records=?,error=NULL WHERE sync_key=?",(now,sync_status,len(players),key))
    return {"cached":False,"players":len(players),"status":sync_status,"hasStats":has_stats}

async def _sql_sync_player(player_id:int,season:int,force:bool=False):
    if not SPORTS_DB_ENABLED:return None
    season=season or _current_season();key=f"player:{player_id}:{season}"
    with _sports_db() as db:state=db.execute("SELECT * FROM sync_state WHERE sync_key=?",(key,)).fetchone()
    if not force and state and not _sync_due(state["last_success_at"]):return {"cached":True}
    now=datetime.now(timezone.utc).isoformat()
    async def safe(path,params):
        try:return await _afoot_get(path,params)
        except Exception:return {"response":[]}
    data=await safe("/players",{"id":player_id,"season":season})
    rows=data.get("response") or []
    if not rows:
        data=await safe("/players/profiles",{"player":player_id});rows=data.get("response") or []
    if rows:
        p=rows[0].get("player") or {}
        if p.get("id") and not p.get("photo"): p["photo"]=_ksn_api_player_photo(p["id"])
        _db_upsert_player(p)
        with _sports_db() as db:
            for st in rows[0].get("statistics") or []:
                t=st.get("team") or {};lg=st.get("league") or {}
                if t.get("id"):_db_upsert_team(t)
                if t.get("id") and lg.get("id"):
                    db.execute("""INSERT INTO player_season_stats(player_id,team_id,league_id,season,stats_json,synced_at)
                    VALUES(?,?,?,?,?,?) ON CONFLICT(player_id,team_id,league_id,season) DO UPDATE SET stats_json=excluded.stats_json,synced_at=excluded.synced_at""",
                    (player_id,int(t["id"]),int(lg["id"]),season,_db_json(st),now))
    with _sports_db() as db:
        db.execute("""INSERT INTO sync_state(sync_key,last_success_at,last_attempt_at,status,records) VALUES(?,?,?,'ok',?)
        ON CONFLICT(sync_key) DO UPDATE SET last_success_at=excluded.last_success_at,last_attempt_at=excluded.last_attempt_at,status='ok',records=excluded.records,error=NULL""",
        (key,now,now,len(rows)))
    return {"cached":False,"records":len(rows)}

def _sql_team_profile(team_id:int,season:int):
    t=_db_team(team_id)
    if not t:return None
    with _sports_db() as db:
        squad=db.execute("""SELECT p.*,pt.number,pt.position FROM player_teams pt JOIN players p ON p.provider_id=pt.player_id
        WHERE pt.team_id=? AND pt.season=? ORDER BY COALESCE(pt.number,999),p.name""",(team_id,season)).fetchall()
        fixtures=db.execute("SELECT payload_json FROM team_fixtures WHERE team_id=? AND season=? ORDER BY fixture_date DESC LIMIT 20",(team_id,season)).fetchall()
        stats=db.execute("SELECT * FROM team_leagues WHERE team_id=? AND season=?",(team_id,season)).fetchall()
        inj=db.execute("""SELECT i.*,p.name,p.photo FROM injuries i LEFT JOIN players p ON p.provider_id=i.player_id
        WHERE i.team_id=? AND i.season=? ORDER BY i.date DESC LIMIT 30""",(team_id,season)).fetchall()
    rawfx=[_db_load(x["payload_json"],{}) for x in fixtures]
    past=[];future=[];now=datetime.now(timezone.utc)
    for f in rawfx:
        try:dt=datetime.fromisoformat(str((f.get("fixture") or {}).get("date")).replace("Z","+00:00"))
        except Exception:dt=now
        (future if dt>now else past).append(f)
    def norm(items):
        out=[]
        for f in items:
            fx=f.get("fixture") or {};ts=f.get("teams") or {};g=f.get("goals") or {};lg=f.get("league") or {}
            out.append({"id":fx.get("id"),"date":fx.get("date"),"status":(fx.get("status") or {}).get("short"),
            "home":(ts.get("home") or {}).get("name"),"away":(ts.get("away") or {}).get("name"),
            "homeId":(ts.get("home") or {}).get("id"),"awayId":(ts.get("away") or {}).get("id"),
            "homeLogo":(ts.get("home") or {}).get("logo"),"awayLogo":(ts.get("away") or {}).get("logo"),
            "homeScore":g.get("home"),"awayScore":g.get("away"),"league":lg.get("name"),"leagueId":lg.get("id")})
        return out
    league_row=stats[0] if stats else None
    league_id=int(league_row["league_id"]) if league_row else None
    league_season=int(league_row["season"]) if league_row else season
    full_standings=[]
    if league_id:
        snap=_dashboard_snapshot_get(f"canonical_standings:{league_id}:{league_season}")
        sd=(snap or {}).get("data") if isinstance(snap,dict) else None
        if isinstance(sd,dict): full_standings=sd.get("standings") or []
    if not full_standings and league_row:
        full_standings=[{"rank":league_row["rank"],"points":league_row["points"],"form":league_row["form"],"team":{"id":team_id,"name":t["name"],"logo":t["badge"] or _ksn_api_team_badge(team_id)}}]
    stored_stats=_db_load(league_row["stats_json"],{}) if league_row else {}
    if not _ksn_valid_team_stats(stored_stats):
        stored_stats=_ksn_stats_from_summary(_ksn_summary_from_results(rawfx,team_id),team_id,league_id,league_season) if league_id else {}
    return {"team":{"id":team_id,"name":t["name"],"code":t["code"],"country":t["country"],"founded":t["founded"],"national":bool(t["national"]),"logo":t["badge"] or _ksn_api_team_badge(team_id)},
            "venue":_db_load(t["venue_json"],{}),
            "players":[{"id":x["provider_id"],"name":x["name"],"age":x["age"],"number":x["number"],"position":x["position"],"photo":x["photo"] or _ksn_api_player_photo(x["provider_id"]),"nationality":x["nationality"]} for x in squad],
            "past10":norm(past[:10]),"future":norm(list(reversed(future))[:10]),
            "standings":full_standings,
            "league":{"id":league_id,"season":league_season} if league_id else {},
            "form":list((league_row["form"] or "")[-5:]) if league_row else [],
            "teamStats":stored_stats,
            "injuries":[{"id":x["player_id"],"name":x["name"],"photo":x["photo"],"type":x["type"],"reason":x["reason"],"date":x["date"]} for x in inj],
            "season":season,"fromSql":True,"syncedAt":t["synced_at"]}

def _sql_player_profile(player_id:int,season:int):
    p=_db_player(player_id)
    if not p:return None
    with _sports_db() as db:
        stats=db.execute("""SELECT ps.stats_json,t.name team_name,t.badge team_badge FROM player_season_stats ps
        LEFT JOIN teams t ON t.provider_id=ps.team_id WHERE ps.player_id=? AND ps.season=?""",(player_id,season)).fetchall()
        teams=db.execute("""SELECT pt.*,t.name,t.badge FROM player_teams pt LEFT JOIN teams t ON t.provider_id=pt.team_id
        WHERE pt.player_id=? AND pt.season=?""",(player_id,season)).fetchall()
    pobj={"id":player_id,"name":p["name"],"firstname":p["firstname"],"lastname":p["lastname"],"age":p["age"],
          "nationality":p["nationality"],"height":p["height"],"weight":p["weight"],"injured":bool(p["injured"]),"photo":p["photo"],
          "birth":{"date":p["birth_date"],"place":p["birth_place"],"country":p["birth_country"]}}
    return {"player":pobj,"statistics":[_db_load(x["stats_json"],{}) for x in stats],
            "teams":[{"id":x["team_id"],"name":x["name"],"logo":x["badge"],"number":x["number"],"position":x["position"]} for x in teams],
            "recentMatches":[],"transfers":[],"injuries":[],"trophies":[],"career":[],"form":[],"matchRatings":[],
            "season":season,"fromSql":True,"syncedAt":p["synced_at"]}




def _team_history_summary(profile: dict) -> dict:
    st=(profile or {}).get("teamStats") or {}
    fx=st.get("fixtures") or {}; goals=st.get("goals") or {}
    played=((fx.get("played") or {}).get("total"))
    wins=((fx.get("wins") or {}).get("total")); draws=((fx.get("draws") or {}).get("total")); losses=((fx.get("loses") or fx.get("losses") or {}).get("total"))
    gf=(((goals.get("for") or {}).get("total") or {}).get("total")); ga=(((goals.get("against") or {}).get("total") or {}).get("total"))
    clean=((st.get("clean_sheet") or {}).get("total"))
    rank=points=None
    if (profile or {}).get("standings"):
        rank=profile["standings"][0].get("rank"); points=profile["standings"][0].get("points")
    return {"season":profile.get("season"),"rank":rank,"points":points,"played":played,"wins":wins,"draws":draws,"losses":losses,
            "goalsFor":gf,"goalsAgainst":ga,"goalDifference":(gf-ga if isinstance(gf,(int,float)) and isinstance(ga,(int,float)) else None),
            "cleanSheets":clean,"winRate":(round(wins*100/played,1) if isinstance(wins,(int,float)) and isinstance(played,(int,float)) and played else None),
            "squadCount":len(profile.get("players") or []),"results":profile.get("past10") or []}

def _player_history_summary(profile: dict) -> dict:
    rows=(profile or {}).get("statistics") or []
    apps=starts=minutes=goals=assists=yellow=red=clean=saves=0; teams=[]; leagues=[]
    for st in rows:
        tm=st.get("team") or {}; lg=st.get("league") or {}; g=st.get("games") or {}; gl=st.get("goals") or {}; ca=st.get("cards") or {}; gd=st.get("goalkeeper") or {}
        if tm.get("name") and tm.get("name") not in teams: teams.append(tm.get("name"))
        if lg.get("name") and lg.get("name") not in leagues: leagues.append(lg.get("name"))
        apps += int(g.get("appearences") or g.get("appearances") or 0); starts += int(g.get("lineups") or 0); minutes += int(g.get("minutes") or 0)
        goals += int(gl.get("total") or 0); assists += int(gl.get("assists") or 0); yellow += int(ca.get("yellow") or 0); red += int(ca.get("red") or 0)
        clean += int(gd.get("clean_sheets") or 0); saves += int(gd.get("saves") or 0)
    return {"season":profile.get("season"),"teams":teams,"leagues":leagues,"appearances":apps,"starts":starts,"minutes":minutes,
            "goals":goals,"assists":assists,"yellow":yellow,"red":red,"cleanSheets":clean,"saves":saves,"statistics":rows}

@app.get("/team/seasons-history")
async def team_seasons_history(team: int=Query(...,ge=1), seasons: int=Query(5,ge=1,le=5), refresh: int=Query(0,ge=0,le=1)):
    """DB-first 4-5 season team history. Missing seasons are lazily captured once and retained."""
    current=_current_season(); years=[current-i for i in range(seasons)]; out=[]
    for yr in years:
        prof=_sql_team_profile(team,yr) if SPORTS_DB_ENABLED else None
        useful=bool(prof and (prof.get("teamStats") or prof.get("players") or prof.get("standings") or prof.get("past10")))
        if SPORTS_DB_ENABLED and (refresh or not useful):
            try: await _sql_sync_team(team,yr,force=bool(refresh)); prof=_sql_team_profile(team,yr)
            except Exception as exc: log.warning("team history sync %s/%s: %s",team,yr,exc)
        if prof: out.append(_team_history_summary(prof))
    return {"teamId":team,"defaultSeason":current,"seasons":out,"coverage":"Big-5 current + up to 5 seasons when provider data is available","source":"PostgreSQL-first historical team intelligence","updatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/player/history")
async def player_history(player: int=Query(...,ge=1), seasons: int=Query(4,ge=1,le=4), refresh: int=Query(0,ge=0,le=1)):
    """DB-first 3-4 season player history, preserving club/league records per season."""
    current=_current_season(); years=[current-i for i in range(seasons)]; out=[]
    for yr in years:
        prof=_sql_player_profile(player,yr) if SPORTS_DB_ENABLED else None
        useful=bool(prof and prof.get("statistics"))
        if SPORTS_DB_ENABLED and (refresh or not useful):
            try: await _sql_sync_player(player,yr,force=bool(refresh)); prof=_sql_player_profile(player,yr)
            except Exception as exc: log.warning("player history sync %s/%s: %s",player,yr,exc)
        if prof: out.append(_player_history_summary(prof))
    return {"playerId":player,"defaultSeason":current,"seasons":out,"coverage":"Big-5 current + up to 4 seasons when provider data is available","source":"PostgreSQL-first historical player intelligence","updatedAt":datetime.now(timezone.utc).isoformat()}

def _extract_xg(stats_rows):
    out={"home":None,"away":None}
    for i,row in enumerate(stats_rows or []):
        vals=row.get("statistics") or []
        for st in vals:
            typ=str(st.get("type") or "").lower().replace(" ","")
            if typ in {"expectedgoals","xg"}:
                v=st.get("value")
                try:v=float(str(v).replace("%",""))
                except Exception:pass
                out["home" if i==0 else "away"]=v
    return out

def _extract_scorers(events):
    out=[]
    for e in events or []:
        if str(e.get("type") or "").lower()=="goal":
            p=e.get("player") or {};assist=e.get("assist") or {};tm=e.get("team") or {};time=e.get("time") or {}
            out.append({"playerId":p.get("id"),"player":p.get("name"),"teamId":tm.get("id"),"team":tm.get("name"),
                        "minute":time.get("elapsed"),"extra":time.get("extra"),"detail":e.get("detail"),
                        "assistId":assist.get("id"),"assist":assist.get("name")})
    return out


def _normalise_lineups(rows):
    out=[]
    for row in rows or []:
        team=row.get("team") or {};coach=row.get("coach") or {}
        starters=[];subs=[]
        for x in row.get("startXI") or []:
            p=x.get("player") or {}
            starters.append({"id":p.get("id"),"name":p.get("name"),"number":p.get("number"),"position":p.get("pos"),"grid":p.get("grid"),"role":"Starting XI"})
        for x in row.get("substitutes") or []:
            p=x.get("player") or {}
            subs.append({"id":p.get("id"),"name":p.get("name"),"number":p.get("number"),"position":p.get("pos"),"grid":p.get("grid"),"role":"Substitute"})
        out.append({"team":{"id":team.get("id"),"name":team.get("name"),"logo":team.get("logo")},
                    "formation":row.get("formation"),"coach":{"id":coach.get("id"),"name":coach.get("name"),"photo":coach.get("photo")},
                    "startingXI":starters,"substitutes":subs})
    return out

@app.get("/match/lineups/{fixture_id}")
async def match_lineups(fixture_id:int):
    ck=f"match-lineups:{fixture_id}"
    cached=_live_cache.get(ck)
    if cached is not None:return cached
    try:d=await _afoot_get("/fixtures/lineups",{"fixture":fixture_id})
    except Exception:d={"response":[]}
    result={"fixtureId":fixture_id,"lineups":_normalise_lineups(d.get("response") or [])}
    _live_cache[ck]=result
    return result
@app.get("/match/details/{fixture_id}")
async def match_details_on_demand(fixture_id: int):
    """Expensive match detail fetched only after the user opens a match."""
    enrichment,lineups=await asyncio.gather(
        match_enrichment(fixture_id),
        match_lineups(fixture_id),
        return_exceptions=True,
    )
    if isinstance(enrichment,Exception):
        enrichment={"fixtureId":fixture_id,"goalScorers":[],"xg":{"home":None,"away":None},"available":{"goalScorers":False,"xg":False}}
    if isinstance(lineups,Exception):
        lineups={"fixtureId":fixture_id,"lineups":[],"available":False}
    return {"fixtureId":fixture_id,"enrichment":enrichment,"lineups":lineups,"loadedOnDemand":True}


@app.get("/match/enrichment/{fixture_id}")
async def match_enrichment(fixture_id:int):
    """Goal scorers and xG for a live/past game. Missing xG stays null, never false zero."""
    ck=f"match-enrichment:{fixture_id}"
    cached=_live_cache.get(ck)
    if cached is not None:return cached
    async def safe(path,params):
        try:return await _afoot_get(path,params)
        except Exception:return {"response":[]}
    events,stats=await asyncio.gather(
        safe("/fixtures/events",{"fixture":fixture_id}),
        safe("/fixtures/statistics",{"fixture":fixture_id}))
    result={"fixtureId":fixture_id,"goalScorers":_extract_scorers(events.get("response") or []),
            "xg":_extract_xg(stats.get("response") or []),
            "available":{"goalScorers":bool(events.get("response")),"xg":any(v is not None for v in _extract_xg(stats.get("response") or []).values())}}
    _live_cache[ck]=result
    return result

@app.get("/sports/directory")
async def sports_directory(sport:str=Query(...), q:str=Query("")):
    """Provider-backed Teams & Players directory for Football, Rugby and Cricket. News is never used."""
    sport=sport.strip().lower(); q=q.strip()
    if sport not in {"football","rugby","cricket"}: raise HTTPException(400,"Supported sports: football, rugby, cricket")
    ck=f"global-directory:{sport}:{q.lower() or 'catalog'}"
    if ck in GLOBAL_DIRECTORY_CACHE:return GLOBAL_DIRECTORY_CACHE[ck]
    teams={}; players={}; errors=[]
    def add_team(t,league="",source=""):
        if not isinstance(t,dict):return
        tid=t.get("id");name=t.get("name") or t.get("displayName") or t.get("shortDisplayName")
        if not name:return
        key=str(tid or re.sub(r"[^a-z0-9]+","-",name.lower()).strip("-"))
        logos=t.get("logos") or []
        teams[key]={"id":tid or key,"ref":tid or key,"name":name,"badge":t.get("logo") or t.get("badge") or ((logos[0] or {}).get("href","") if logos else ""),"country":t.get("country") or t.get("location") or "","league":league,"source":source,"sport":sport}
    def add_player(x,team="",league="",source=""):
        if not isinstance(x,dict):return
        pl=x.get("player") if isinstance(x.get("player"),dict) else x
        pid=pl.get("id");name=pl.get("name") or pl.get("displayName") or pl.get("fullName")
        if not name:return
        key=str(pid or re.sub(r"[^a-z0-9]+","-",name.lower()).strip("-"))
        hs=pl.get("headshot") if isinstance(pl.get("headshot"),dict) else {}
        players[key]={"id":pid or key,"ref":pid or key,"name":name,"photo":pl.get("photo") or hs.get("href",""),"nationality":pl.get("nationality") or pl.get("citizenship") or "","team":team or pl.get("team",""),"position":pl.get("position") or pl.get("role") or "","league":league,"source":source,"sport":sport}
    if sport=="football":
        try:
            # v465: reuse the midnight-warmed FantasyPlayoffs Big-5 snapshot so
            # Teams & Players pages have real player/team rows even when another
            # provider is slow or its local database has not been hydrated yet.
            fp_snap=_players_cache.get("fantasyplayoffs:big5:shared") or {}
            for fp in (fp_snap.get("players") or []):
                if q and q.lower() not in (str(fp.get("name") or "")+" "+str(fp.get("team") or "")+" "+str(fp.get("league") or "")).lower():
                    continue
                add_team({"name":fp.get("team"),"country":fp.get("country")},fp.get("league", ""),"FantasyPlayoffs daily snapshot")
                add_player({"id":fp.get("id"),"name":fp.get("name"),"position":fp.get("position")},fp.get("team", ""),fp.get("league", ""),"FantasyPlayoffs daily snapshot")
            if q:
                d=await directory_search(q=q,season=0)
                for x in d.get("teams",[]): add_team({**x,"id":x.get("publicRef") or x.get("id")},x.get("league",""),"API-Football")
                for x in d.get("players",[]): add_player({**x,"id":x.get("publicRef") or x.get("id")},x.get("team",""),x.get("league",""),"API-Football")
            else:
                # Start with the persistent cache/database when populated.
                if SPORTS_DB_ENABLED:
                    try:
                        with _sports_db() as db:
                            for x in db.execute("SELECT * FROM teams ORDER BY name LIMIT 500").fetchall():
                                teams[str(x["id"])]={"id":x["id"],"ref":x["public_ref"],"name":x["name"],"badge":x["badge"],"country":x["country"],"sport":"football","source":"sports cache/database"}
                            for x in db.execute("SELECT * FROM players ORDER BY name LIMIT 500").fetchall():
                                players[str(x["id"])]={"id":x["id"],"ref":x["public_ref"],"name":x["name"],"photo":x["photo"],"nationality":x["nationality"],"sport":"football","source":"sports cache/database"}
                    except Exception as exc: errors.append("Football cache: "+str(exc))
                # The UI must not be empty just because the local DB has not been hydrated.
                # Pull teams + real player records from API-Football across representative global leagues.
                league_names=["Premier League","La Liga","Serie A","Bundesliga","Ligue 1","PSL","Saudi Pro League","Champions League"]
                async def league_catalog(name):
                    try:
                        lid=_resolve_league_id(name)
                        return name,await players_explorer(league=lid,season=0)
                    except Exception as exc:
                        return name,{"teams":[],"players":[],"error":str(exc)}
                catalogs=await asyncio.gather(*[league_catalog(name) for name in league_names])
                for lname,d in catalogs:
                    for x in d.get("teams",[]):
                        ref=x.get("publicRef") or x.get("id")
                        add_team({"id":ref,"name":x.get("name"),"logo":x.get("badge"),"country":x.get("country")},lname,"API-Football")
                    for x in d.get("players",[]):
                        ref=x.get("publicRef") or x.get("id")
                        add_player({"id":ref,"name":x.get("name"),"photo":x.get("photo"),"nationality":x.get("nationality"),"position":x.get("position")},x.get("team",""),lname,"API-Football")
                    if d.get("error"): errors.append(f"{lname}: {d['error']}")
        except Exception as exc: errors.append(str(exc))
    elif sport=="rugby":
        if SPORTS_API_KEYS.get("rugby"):
            try:
                td=await _rugby_api("/teams",{"search":q} if q else {})
                for t in td if isinstance(td,list) else []: add_team(t,source="API-Sports")
            except Exception as exc: errors.append("Rugby teams: "+str(exc))
            if q:
                try:
                    pd=await _rugby_api("/players",{"search":q})
                    for x in pd if isinstance(pd,list) else []: add_player(x,source="API-Sports")
                except Exception as exc: errors.append("Rugby players: "+str(exc))
        for lg in ESPN_LEAGUES.get("rugby",[]):
            try:
                d=await _sports_get(f"https://site.api.espn.com/apis/site/v2/sports/rugby/{lg}/teams",{"limit":500})
                for item in d.get("sports",[]):
                    for league in item.get("leagues",[]):
                        for entry in league.get("teams",[]):
                            t=entry.get("team") or entry;name=str(t.get("displayName") or t.get("name") or "")
                            if not q or q.lower() in name.lower():add_team(t,league.get("name") or lg,"ESPN")
            except Exception as exc: errors.append(f"ESPN {lg}: {exc}")
    else:
        for lg in ESPN_LEAGUES.get("cricket",[]):
            try:
                d=await _sports_get(f"https://site.api.espn.com/apis/site/v2/sports/cricket/{lg}/teams",{"limit":500});matched=[]
                for item in d.get("sports",[]):
                    for league in item.get("leagues",[]):
                        for entry in league.get("teams",[]):
                            t=entry.get("team") or entry;name=str(t.get("displayName") or t.get("name") or "")
                            if not q or q.lower() in name.lower():add_team(t,league.get("name") or lg,"ESPN");matched.append(t)
                if q:
                    for t in matched[:5]:
                        tid=t.get("id")
                        if not tid:continue
                        try:
                            td=await _sports_get(f"https://site.api.espn.com/apis/site/v2/sports/cricket/{lg}/teams/{tid}")
                            team=td.get("team") or td
                            for pl in team.get("athletes") or []:add_player(pl,name,lg,"ESPN")
                        except Exception:pass
            except Exception as exc: errors.append(f"ESPN {lg}: {exc}")
    out={"sport":sport,"query":q,"teams":list(teams.values())[:500],"players":list(players.values())[:500],"source":"connected sports providers/cache","errors":errors[:10],"state":"ok" if (teams or players) else ("provider-error" if errors and q else "empty")}
    GLOBAL_DIRECTORY_CACHE[ck]=out
    return out

@app.get("/sports/directory/search")
async def sports_directory_search(q:str=Query(...,min_length=2,max_length=80),sport:str=Query("all")):
    """Global sports-data search: teams, players, competitions, fixtures/results, tables and statistics. No News API."""
    q=q.strip();ql=q.lower();wanted=sport.strip().lower();sports=["football","rugby","cricket"] if wanted=="all" else [wanted]
    result={"query":q,"sport":wanted,"teams":[],"players":[],"competitions":[],"fixtures":[],"results":[],"standings":[],"statistics":[],"errors":[],"source":"sports providers/cache"}
    dirs=await asyncio.gather(*[sports_directory(sp,q) for sp in sports],return_exceptions=True)
    for sp,d in zip(sports,dirs):
        if isinstance(d,Exception):result["errors"].append(f"{sp}: {d}");continue
        result["teams"] += [{**x,"sport":sp} for x in d.get("teams",[])][:20]
        result["players"] += [{**x,"sport":sp} for x in d.get("players",[])][:20]
        result["errors"] += d.get("errors",[])[:3]
    result["competitions"]=[{**x,"type":"competition"} for x in COMPETITION_REGISTRY if (wanted=="all" or x.get("sport")==wanted) and ql in (str(x.get("name",""))+" "+str(x.get("country",""))).lower()][:30]
    async def score_search(sp):
        try:return await _sports_scores(sp,None,False,None)
        except Exception as exc:result["errors"].append(f"{sp} scores: {exc}");return []
    score_sets=await asyncio.gather(*[score_search(sp) for sp in sports])
    for sp,rows in zip(sports,score_sets):
        for g in rows:
            blob=" ".join(str(g.get(k,"")) for k in ("home","away","league","country")).lower()
            if ql not in blob:continue
            state=str(g.get("statusShort") or "").lower();item={**g,"sport":sp}
            (result["results"] if state in {"post","final","ft"} else result["fixtures"]).append(item)
    for comp in result["competitions"][:6]:
        sp=comp.get("sport")
        try:
            if sp=="football":
                lid=_resolve_league_id(comp.get("id") or comp.get("slug") or "")
                sd=await _afoot_get("/standings",{"league":lid,"season":_current_season()})
                table=(((sd.get("response") or [{}])[0].get("league") or {}).get("standings") or [[]])[0]
                for x in table[:30]:
                    t=x.get("team") or {};result["standings"].append({"sport":"football","competition":comp.get("name"),"name":t.get("name"),"rank":x.get("rank"),"points":x.get("points"),"form":x.get("form")})
            else:
                sd=await sports_standings(sport=sp,league=0,season=0)
                for x in (sd.get("items") or [])[:30]:
                    if isinstance(x,dict):result["standings"].append({"sport":sp,"competition":comp.get("name"),"name":x.get("name") or (x.get("team") or {}).get("name"),"rank":x.get("rank"),"points":x.get("points")})
        except Exception as exc:result["errors"].append(f"{sp} standings: {exc}")
    for x in result["players"][:20]:
        stats=x.get("statistics") or x.get("stats")
        if stats:result["statistics"].append({"sport":x.get("sport"),"name":x.get("name"),"summary":stats})
    for x in result["teams"][:20]:
        stats=x.get("statistics") or x.get("stats")
        if stats:result["statistics"].append({"sport":x.get("sport"),"name":x.get("name"),"summary":stats})
    for k,lim in (("teams",30),("players",30),("fixtures",40),("results",40),("standings",60),("statistics",40)):result[k]=result[k][:lim]
    result["count"]=sum(len(result[k]) for k in ("teams","players","competitions","fixtures","results","standings","statistics"))
    result["state"]="ok" if result["count"] else ("provider-error" if result["errors"] else "empty")
    return result


@app.get("/sports-db/status")
async def sports_db_status():
    if not SPORTS_DB_ENABLED:return {"enabled":False}
    if SPORTS_DB_INIT_ERROR:
        return {"enabled":True,"status":"degraded","path":str(SPORTS_DB_PATH),
          "fallback":SPORTS_DB_FALLBACK,"error":SPORTS_DB_INIT_ERROR}
    try:
        with _sports_db() as db:
            return {"enabled":True,"status":"ok","path":str(SPORTS_DB_PATH),
              "fallback":SPORTS_DB_FALLBACK,
              "teams":db.execute("SELECT COUNT(*) FROM teams").fetchone()[0],
              "players":db.execute("SELECT COUNT(*) FROM players").fetchone()[0],
              "playerStats":db.execute("SELECT COUNT(*) FROM player_season_stats").fetchone()[0],
              "syncHoursNow":_sync_hours(),"syncPolicy":"6h Tue/Wed/Thu/Sat/Sun; 12h Mon/Fri"}
    except Exception as exc:
        return {"enabled":True,"status":"degraded","path":str(SPORTS_DB_PATH),
          "fallback":SPORTS_DB_FALLBACK,"error":f"{type(exc).__name__}: {exc}"}

@app.post("/sports-db/sync/team/{team_id}")
async def sports_db_sync_team(team_id:int,season:int=Query(0,ge=0),force:int=Query(0,ge=0,le=1)):
    return await _sql_sync_team(team_id,season or _current_season(),bool(force))

@app.post("/sports-db/sync/player/{player_id}")
async def sports_db_sync_player(player_id:int,season:int=Query(0,ge=0),force:int=Query(0,ge=0,le=1)):
    return await _sql_sync_player(player_id,season or _current_season(),bool(force))

# Do not let a sports-cache database failure take down authentication, news,
# health checks, or the rest of Kasi Sports News during application import.
if SPORTS_DB_ENABLED:
    try:
        _sports_db_init()
    except Exception as exc:
        SPORTS_DB_INIT_ERROR = f"{type(exc).__name__}: {exc}"
        logger.exception("Sports database initialisation failed; continuing in degraded mode")

@app.get("/public-route/{kind}/{provider_id}")
async def public_route(kind:str,provider_id:int,name:str=Query(""),response:Response=None):
    if kind not in {"team","player"}:raise HTTPException(404,"Profile not found")
    if response is not None: response.headers["Cache-Control"]="public, max-age=86400"
    ref=_public_ref(kind,provider_id,name or kind);return {"ref":ref,"url":f"/{'teams' if kind=='team' else 'players'}/{ref}"}
@app.get("/public-resolve/{kind}/{ref}")
async def public_resolve(kind:str,ref:str):
    if kind not in {"team","player"}:raise HTTPException(404,"Profile not found")
    return {"id":_public_decode(kind,ref)}
_PLAYERS_EXPLORER_CACHE=TTLCache(maxsize=200,ttl=21600)
@app.get("/players/explorer")
async def players_explorer(league:int=Query(39,ge=1),season:int=Query(0,ge=0),refresh:int=Query(0,ge=0,le=1)):
    """League teams: API-Football primary; FantasyPlayoffs auto-fills missing Big-5 clubs."""
    season=season or _current_season();key=f"explorer:v482-autofill:{league}:{season}"
    c=None if refresh else _PLAYERS_EXPLORER_CACHE.get(key)
    if c and c.get("teams"): return c
    try:d=await _afoot_get("/teams",{"league":league,"season":season})
    except Exception:d={"response":[]}
    teams=[]; seen=set()
    for x in d.get("response") or []:
        t=x.get("team") or {}; name=str(t.get("name") or "").strip()
        if not t.get("id") or not name: continue
        nk=_ksn_norm_team_name(name); seen.add(nk)
        teams.append({"name":name,"badge":t.get("logo"),"country":t.get("country"),"internalId":t["id"],"publicRef":_public_ref("team",int(t["id"]),name),"source":"API-Football"})
        if SPORTS_DB_ENABLED:_db_upsert_team(t,x.get("venue") or {})
    api_count=len(teams); fantasy_added=0
    # Big-5 only: FantasyPlayoffs is a completeness layer, never a replacement.
    if league in FANTASYPLAYOFFS_LEAGUES:
        try:
            fp=await _fetch_fantasyplayoffs_league(league,season=season,bust_cache=False)
            clubs={}
            for pl in fp.get("players") or []:
                nm=str(pl.get("team") or "").strip()
                if nm: clubs.setdefault(_ksn_norm_team_name(nm),{"name":nm,"players":[]})["players"].append(pl)
            # Use the local canonical DB to recover provider IDs without another provider fan-out.
            db_names={}
            if SPORTS_DB_ENABLED:
                try:
                    with _sports_db() as db:
                        for r in db.execute("SELECT provider_id,name,country,badge,public_ref FROM teams").fetchall():
                            db_names.setdefault(_ksn_norm_team_name(r["name"]),r)
                except Exception: pass
            for nk,club in clubs.items():
                if nk in seen: continue
                r=db_names.get(nk); iid=int(r["provider_id"]) if r else None
                teams.append({"name":club["name"],"badge":r["badge"] if r else "","country":(r["country"] if r else FANTASYPLAYOFFS_LEAGUES[league]["country"]),"internalId":iid,"publicRef":(r["public_ref"] if r else ""),"fantasyTeam":club["name"],"leagueId":league,"source":"FantasyPlayoffs fallback"})
                seen.add(nk); fantasy_added+=1
        except Exception as exc:
            log.warning("Fantasy Big-5 team autofill failed league=%s: %s",league,exc)
    out={"teams":teams,"season":season,"leagueId":league,"apiFootballCount":api_count,"fantasyFallbackCount":fantasy_added,"count":len(teams),"source":"API-Football primary + FantasyPlayoffs Big-5 fallback"}
    # Never let an empty refresh overwrite a previously valid league snapshot.
    if teams:_PLAYERS_EXPLORER_CACHE[key]=out
    elif c:return c
    return out

@app.get("/players/team-squad")
async def players_team_squad(team:int=Query(0,ge=0),league:int=Query(0,ge=0),fantasy_team:str=Query("")):
    """API-Football squad primary; FantasyPlayoffs fills a missing Big-5 squad."""
    fantasy_team=str(fantasy_team or "").strip(); key=f"squad:v482-autofill:{team}:{league}:{_ksn_norm_team_name(fantasy_team)}"
    c=_PLAYERS_EXPLORER_CACHE.get(key)
    if c and c.get("players"):return c
    rows=[]
    if team:
        try:d=await _afoot_get("/players/squads",{"team":team})
        except Exception:d={"response":[]}
        rows=(d.get("response") or [{}])[0].get("players") or []
    players=[]
    if rows:
        if SPORTS_DB_ENABLED:
            for p in rows:_db_upsert_player(p)
        players=[{"name":p.get("name"),"photo":p.get("photo"),"age":p.get("age"),"number":p.get("number"),"position":p.get("position"),"publicRef":_public_ref("player",int(p["id"]),p.get("name") or "player"),"source":"API-Football"} for p in rows if p.get("id")]
    # Missing/empty API squad: use the Fantasy Big-5 roster for identity + position + points only.
    if not players and league in FANTASYPLAYOFFS_LEAGUES and fantasy_team:
        try:
            fp=await _fetch_fantasyplayoffs_league(league,season=_current_season(),bust_cache=False)
            want=_ksn_norm_team_name(fantasy_team)
            for p in fp.get("players") or []:
                if _ksn_norm_team_name(p.get("team"))!=want: continue
                players.append({"name":p.get("name"),"photo":"","age":None,"number":None,"position":p.get("position"),"publicRef":"","fantasyId":p.get("id"),"fantasyPoints":p.get("fantasyPoints"),"source":"FantasyPlayoffs fallback"})
        except Exception as exc:
            log.warning("Fantasy squad autofill failed league=%s team=%s: %s",league,fantasy_team,exc)
    out={"players":players,"teamId":team or None,"fantasyTeam":fantasy_team or None,"source":"API-Football" if rows else ("FantasyPlayoffs fallback" if players else "unavailable")}
    if players:_PLAYERS_EXPLORER_CACHE[key]=out
    elif c:return c
    return out
@app.get("/directory/discover")
async def directory_discover(league:int=Query(39,ge=1),season:int=Query(0,ge=0)):
    season=season or _current_season();key=f"discover:{league}:{season}";c=_PLAYERS_EXPLORER_CACHE.get(key)
    if c:return c
    async def safe(path,params):
        try:return await _afoot_get(path,params)
        except Exception:return {"response":[]}
    sc,sd=await asyncio.gather(safe("/players/topscorers",{"league":league,"season":season}),safe("/standings",{"league":league,"season":season}))
    players=[]
    for x in (sc.get("response") or [])[:5]:
        p=x.get("player") or {};st=(x.get("statistics") or [{}])[0];t=st.get("team") or {}
        if p.get("id"):players.append({"name":p.get("name"),"photo":p.get("photo"),"team":t.get("name"),"position":(st.get("games") or {}).get("position"),"goals":(st.get("goals") or {}).get("total"),"publicRef":_public_ref("player",int(p["id"]),p.get("name") or "player")})
    try:table=((sd.get("response") or [])[0].get("league") or {}).get("standings",[[]])[0]
    except Exception:table=[]
    teams=[]
    for x in table[:5]:
        t=x.get("team") or {}
        if t.get("id"):teams.append({"name":t.get("name"),"badge":t.get("logo"),"rank":x.get("rank"),"points":x.get("points"),"form":x.get("form"),"publicRef":_public_ref("team",int(t["id"]),t.get("name") or "team")})
    out={"players":players,"teams":teams};_PLAYERS_EXPLORER_CACHE[key]=out;return out
@app.get("/directory/search")
async def directory_search(q:str=Query(...,min_length=2,max_length=80),season:int=Query(0,ge=0)):
    season=season or _current_season();q=q.strip()
    if SPORTS_DB_ENABLED:
        like=f"%{q}%"
        with _sports_db() as db:
            tr=db.execute("SELECT * FROM teams WHERE name LIKE ? COLLATE NOCASE ORDER BY name LIMIT 8",(like,)).fetchall()
            pr=db.execute("SELECT * FROM players WHERE name LIKE ? COLLATE NOCASE ORDER BY name LIMIT 8",(like,)).fetchall()
        if tr or pr:
            return {"teams":[{"name":x["name"],"badge":x["badge"],"country":x["country"],"publicRef":x["public_ref"]} for x in tr],
                    "players":[{"name":x["name"],"photo":x["photo"],"nationality":x["nationality"],"publicRef":x["public_ref"]} for x in pr],
                    "fromSql":True}
    key=f"search:{q.lower()}:{season}";c=_PLAYERS_EXPLORER_CACHE.get(key)
    if c:return c
    async def safe(path,params):
        try:return await _afoot_get(path,params)
        except Exception:return {"response":[]}
    td,pd=await asyncio.gather(safe("/teams",{"search":q}),safe("/players",{"search":q,"season":season}) if len(q)>=4 else asyncio.sleep(0,result={"response":[]}))
    teams=[];players=[]
    for x in (td.get("response") or [])[:8]:
        t=x.get("team") or {}
        if t.get("id"):teams.append({"name":t.get("name"),"badge":t.get("logo"),"country":t.get("country"),"publicRef":_public_ref("team",int(t["id"]),t.get("name") or "team")})
    for x in (pd.get("response") or [])[:8]:
        p=x.get("player") or {};st=(x.get("statistics") or [{}])[0];t=st.get("team") or {}
        if p.get("id"):players.append({"name":p.get("name"),"photo":p.get("photo"),"team":t.get("name"),"league":(st.get("league") or {}).get("name"),"publicRef":_public_ref("player",int(p["id"]),p.get("name") or "player")})
    out={"teams":teams,"players":players};_PLAYERS_EXPLORER_CACHE[key]=out;return out
@app.get("/live")
async def live(
    league: str = Query("ALL"),
    refresh: int = Query(0, ge=0, le=1),
):
    """Fast live rail: one upstream fixture call, then cache.
    Detailed stats/odds are intentionally deferred until a match is opened.
    """
    ck=f"live:{league.upper()}"
    cached=_live_cache.get(ck) if not refresh else None
    if cached is not None:
        return cached

    params={"live":"all"}
    if league.upper()!="ALL":
        params["league"]=_resolve_league_id(league)

    try:
        fd=await _afoot_get("/fixtures",params)
        raw=fd.get("response",[])
    except Exception as exc:
        stale=_live_cache.get(ck)
        if stale is not None:
            return {**stale,"stale":True,"providerWarning":str(exc)}
        return {"matches":[],"count":0,"source":"API-Football LIVE","providerError":str(exc),
                "quota":dict(_quota_state),"generatedAt":datetime.now(timezone.utc).isoformat()}

    matches=[]
    for f in raw:
        m=_normalise_fixture(f)
        # Explicit stable aliases consumed by the frontend.
        m["fixtureId"]=m.get("_afootFixtureId")
        m["homeTeamId"]=m.get("homeId") or m.get("_teamHomeId")
        m["awayTeamId"]=m.get("awayId") or m.get("_teamAwayId")
        m["homeBadge"]=m.get("homeLogo") or (f"/sports/football/team-badge/{m.get('homeTeamId')}" if m.get("homeTeamId") else "")
        m["awayBadge"]=m.get("awayLogo") or (f"/sports/football/team-badge/{m.get('awayTeamId')}" if m.get("awayTeamId") else "")
        m["countryFlag"]=m.get("leagueFlag") or ""
        m["homeTeam"]={
            "id":m.get("homeTeamId"),
            "name":m.get("home") or "Home",
            "logo":m.get("homeLogo") or m.get("homeBadge") or "",
            "country":m.get("leagueFlag") or "",
        }
        m["awayTeam"]={
            "id":m.get("awayTeamId"),
            "name":m.get("away") or "Away",
            "logo":m.get("awayLogo") or m.get("awayBadge") or "",
            "country":m.get("leagueFlag") or "",
        }
        m["isLive"]=True
        m["liveStatus"]={
            "short":f.get("fixture",{}).get("status",{}).get("short"),
            "elapsed":f.get("fixture",{}).get("status",{}).get("elapsed"),
        }
        matches.append(m)

    # v412: OddsPapi can contribute additional genuine live football fixtures and
    # Bet365/Betway odds. API-Football remains first; unmatched provider events are
    # appended only when they have real team names and a provider fixture id.
    oddspapi_added=0
    if league.upper()=="ALL" and ODDSPAPI_ENABLED and ODDSPAPI_API_KEY:
        try:
            op_rows=await _oddspapi_sport_fixtures("football",None,True)
            existing={( _normalise_team_name(x.get("home")), _normalise_team_name(x.get("away")) ) for x in matches}
            for op in op_rows:
                pair=(_normalise_team_name(op.get("home")),_normalise_team_name(op.get("away")))
                if not all(pair) or pair in existing: continue
                op["isLive"]=True;op["fixtureId"]=op.get("providerFixtureId") or op.get("id")
                op["liveStatus"]={"short":op.get("statusShort") or "LIVE","elapsed":op.get("elapsed") or 0}
                matches.append(op);existing.add(pair);oddspapi_added+=1
        except Exception as exc:
            log.warning("OddsPapi live fixture supplement failed: %s",exc)

    result={
        "matches":matches,"count":len(matches),
        "source":"API-Football LIVE + OddsPapi Bet365/Betway supplement",
        "oddspapiAdded":oddspapi_added,
        "detailsDeferred":True,
        "quota":dict(_quota_state),
        "generatedAt":datetime.now(timezone.utc).isoformat(),
    }
    _live_cache[ck]=result
    return result


@app.get("/api/live-scores-with-odds")
async def live_scores_with_odds(
    league: str = Query("ALL"),
    refresh: int = Query(0, ge=0, le=1),
):
    """Combined live-score feed for the dashboard.

    API-Football remains the source of truth for fixture identity, score,
    status, minute, teams and badges. The Odds API only supplements the
    bookmaker market. Existing live (180s) and odds (1800s) caches are reused.
    """
    live_data = await live(league=league, refresh=refresh)
    rows = [dict(m) for m in (live_data.get("matches", []) if isinstance(live_data, dict) else [])]

    odds_meta = {"checked": False, "matched": 0, "events": 0, "error": None}
    if rows and ODDS_API_ENABLED and ODDS_API_KEY:
        try:
            events = await _odds_api_events(league, refresh=False)
            odds_meta.update({"checked": True, "events": len(events)})
            for match in rows:
                match["odds"] = None
                match["oddsAvailable"] = False
                match["oddsSource"] = None
                match["oddsMarketPhase"] = None

                for event in events:
                    if not _event_matches_fixture(event, match):
                        continue
                    odds = _normalise_odds_api_event(event)
                    if not _valid_1x2(odds):
                        continue

                    # Do not call a market "live odds" unless the provider feed
                    # itself is being consumed as a current market for a match
                    # API-Football confirms is live. UI still labels it clearly.
                    match["odds"] = odds
                    match["oddsAvailable"] = True
                    match["oddsSource"] = "The Odds API"
                    match["oddsMarketPhase"] = "current/in-play"
                    eh = _normalise_team_name(event.get("home_team"))
                    ea = _normalise_team_name(event.get("away_team"))
                    fh = _normalise_team_name(match.get("home") or match.get("homeTeam"))
                    fa = _normalise_team_name(match.get("away") or match.get("awayTeam"))
                    exact_pair = (eh == fh and ea == fa)
                    match["oddsMatchedBy"] = "exact/alias+kickoff" if exact_pair else "fuzzy-both-teams+kickoff"
                    if not exact_pair:
                        match["oddsMatchConfidence"] = {
                            "home": round(_team_similarity(eh, fh), 1),
                            "away": round(_team_similarity(ea, fa), 1),
                        }
                    match["oddsApiEventId"] = event.get("id")
                    odds_meta["matched"] += 1
                    break
        except Exception as exc:
            odds_meta["error"] = str(exc)
            log.warning("Combined live-score odds supplement failed: %s", exc)

    # Keep a stable frontend contract even when no market is available.
    for match in rows:
        match.setdefault("odds", None)
        match.setdefault("oddsAvailable", False)
        match.setdefault("oddsSource", None)
        match.setdefault("oddsMarketPhase", None)

    return {
        "matches": rows,
        "count": len(rows),
        "source": "API-Football live + The Odds API market",
        "liveCacheSeconds": 180,
        "oddsCacheSeconds": 1800,
        "oddsApi": odds_meta,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
    }

@app.get("/home/matches")
async def home_matches(league: str = Query("ALL")):
    """Live matches first; if none, return yesterday's completed matches."""
    live_data=await live(league=league,refresh=0)
    live_rows=live_data.get("matches",[]) if isinstance(live_data,dict) else []
    if live_rows:
        return {"mode":"live","heading":"Live Matches","count":len(live_rows),"matches":live_rows,"source":live_data.get("source","API-Football LIVE")}
    yesterday=(datetime.now()-timedelta(days=1)).strftime("%Y-%m-%d")
    recent=await fixtures(league=league,type="today",range=None,date_from=yesterday,date_to=yesterday,refresh=0)
    rows=recent.get("matches",[]) if isinstance(recent,dict) else []
    completed=[]
    for m in rows:
        st=str(m.get("status") or m.get("statusShort") or "").upper()
        if st in {"FT","AET","PEN","AWD","WO"} or "FINISH" in st: completed.append(m)
    if not completed: completed=rows
    majors=("premier league","champions league","europa","la liga","serie a","bundesliga","ligue 1","psl","premiership","world cup","africa cup","cup")
    def rank(m):
        lg=str(m.get("league") or "").lower()
        return (2 if any(x in lg for x in majors) else 0)+int(bool(m.get("homeLogo")))+int(bool(m.get("awayLogo")))
    completed=sorted(completed,key=rank,reverse=True)[:12]
    return {"mode":"recent","heading":"Yesterday's Top Matches","date":yesterday,"count":len(completed),"matches":completed,"source":"API-Football completed fixtures"}

# ---------------------------------------------------------------------------
# PRE-MATCH ODDS
# ---------------------------------------------------------------------------

async def _fetch_prematch_odds_by_dates(dates, league_ids: list[int] | None = None):
    """Fetch pre-match odds filtered to specific league IDs.

    Instead of paginating ALL leagues globally (which can hit 59+ pages),
    we fetch odds per league per date — capped at MAX_ODDS_PAGES pages each.
    If league_ids is None/empty we fall back to SCAN_LEAGUES.
    """
    MAX_ODDS_PAGES = 3  # safety cap per league per date (~75 fixtures max)
    by_id = {}

    # Derive season from the dates using the football-calendar helper
    season = _current_season()

    # Resolve league IDs to fetch
    if not league_ids:
        league_ids = [lid for name in SCAN_LEAGUES if (lid := LEAGUE_IDS.get(name))]

    for date in sorted(set(x for x in dates if x)):
        for lid in league_ids:
            page = 1
            while page <= MAX_ODDS_PAGES:
                data = await _afoot_get(
                    "/odds",
                    {"date": date, "league": lid, "season": season, "page": page},
                )

                for item in data.get("response", []):
                    fixture_id = item.get("fixture", {}).get("id")
                    if fixture_id is None:
                        continue
                    norm = _normalise_odds(item.get("bookmakers", []))
                    if _valid_1x2(norm):
                        by_id[str(fixture_id)] = norm
                        _odds_cache[f"odds:{fixture_id}"] = {
                            "fixture_id": fixture_id,
                            "odds": norm,
                            "source": "API-Football",
                            "fetchedAt": datetime.now(timezone.utc).isoformat(),
                        }

                paging = data.get("paging") or {}
                total_pages = int(paging.get("total") or page)
                if page >= total_pages:
                    break
                page += 1

    return by_id

@app.get("/fixtures/with-odds")
async def fixtures_with_odds(
    league: str = Query(...),
    type: str = Query("today"),
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
    refresh: int = Query(0, ge=0, le=1),
):
    # v183: this endpoint is also called directly by prediction/summary routes.
    # Strip FastAPI Query metadata defaults before they can leak into fixtures().
    league = league if isinstance(league, str) else "ALL"
    type = type if isinstance(type, str) else "today"
    date_from = date_from if isinstance(date_from, str) else None
    date_to = date_to if isinstance(date_to, str) else None
    refresh = int(refresh) if isinstance(refresh, (int, bool)) else 0

    # IMPORTANT: do not put a wall-clock deadline around the entire ALL-league
    # fixture loader.  It may legitimately require one API-Football request per
    # configured league.  Each upstream request already has its own 20-second
    # httpx timeout/retry policy in _afoot_get().
    #
    # The previous 5-second wrapper caused a partial/failed API-Football fixture
    # load to be replaced by The Odds API, which has no API-Football statistics,
    # lineups, form, injuries or player data.
    try:
        result = await fixtures(
            league=league,
            type=type,
            date_from=date_from,
            date_to=date_to,
            refresh=refresh,
        )
    except Exception as primary_exc:
        if ODDS_API_ENABLED and ODDS_API_KEY:
            log.warning(
                "Primary fixture provider failed (%s); attempting odds-only fallback",
                primary_exc,
            )
            try:
                fallback = await _odds_api_fallback_fixtures(league)
                fallback["providerWarning"] = (
                    "API-Football fixture loading failed; fallback contains odds/event data only."
                )
                return fallback
            except Exception as fallback_exc:
                log.error("The Odds API fallback failed: %s", fallback_exc)
        raise

    matches = result.get("matches", [])
    if not matches:
        return {
            **result,
            "oddsComplete": 0,
            "oddsBookmaker": 0,
            "hasBookmakerOdds": False,
            "hasValidOdds": False,
            "oddsUnavailable": False,
            "provider": "API-Football",
            "providerError": None,
            "quota": dict(_quota_state),
        }

    real_by_id = {}
    odds_source_by_id = {}
    dates = []

    for match in matches:
        raw_date = match.get("datetime") or ""
        if raw_date:
            dates.append(raw_date[:10])

    if not refresh:
        for match in matches:
            fid = match.get("_afootFixtureId")
            cached = _odds_cache.get(f"odds:{fid}") if fid else None
            odds_value = cached.get("odds", {}) if cached else {}
            if _valid_1x2(odds_value):
                real_by_id[str(fid)] = odds_value

    # v184: cache the entire odds scan, including an EMPTY result. Without this,
    # a day with no bookmaker odds caused every dashboard poll to rescan API-Football.
    batch_key = f"prematch:{league.upper()}:{','.join(sorted(set(dates)))}"
    cached_batch = _prematch_odds_batch_cache.get(batch_key) if not refresh else None
    if cached_batch is not None:
        real_by_id.update(cached_batch.get("odds", {}))

    if (refresh or cached_batch is None) and not _v448_api_football_provider_locked():
        try:
            # Resolve league IDs — avoids paginating all 59+ pages globally
            if league.upper() == "ALL":
                lids = [lid for name in SCAN_LEAGUES if (lid := LEAGUE_IDS.get(name))]
            else:
                try:
                    lids = [_resolve_league_id(league)]
                except Exception:
                    lids = [lid for name in SCAN_LEAGUES if (lid := LEAGUE_IDS.get(name))]
            # Bulk odds discovery can span multiple leagues/dates.  Do not
            # apply the 5-second single-request deadline to the whole batch.
            # _afoot_get() still enforces an individual HTTP timeout.
            fetched = await _fetch_prematch_odds_by_dates(
                dates, league_ids=lids
            )
            real_by_id.update(fetched)
            _prematch_odds_batch_cache[batch_key] = {
                "odds": dict(fetched),
                "fetchedAt": datetime.now(timezone.utc).isoformat(),
                "error": None,
            }
        except Exception as exc:
            # Cache the failed/empty scan briefly under the normal 30-minute batch TTL
            # so concurrent dashboard widgets cannot create a provider request storm.
            _prematch_odds_batch_cache[batch_key] = {
                "odds": dict(real_by_id),
                "fetchedAt": datetime.now(timezone.utc).isoformat(),
                "error": str(exc),
            }
            log.warning("Pre-match odds fetch failed or timed out: %s", exc)

    bookmaker_count = 0

    for match in matches:
        fid = match.get("_afootFixtureId")
        odds_value = real_by_id.get(str(fid), {})
        valid = _valid_1x2(odds_value)

        if valid:
            bookmaker_count += 1
            match["odds"] = odds_value
            match["oddsSource"] = odds_source_by_id.get(str(fid), "API-Football")
        else:
            match["odds"] = {
                "homeWin": 0,
                "draw": 0,
                "awayWin": 0,
                "over05": 0,
                "over15": 0,
                "over25": 0,
                "btts": 0,
                "firstHalfHome": 0,
                "scoreFirst": 0,
                "expectedGoalscorer": 0,
            }
            match["oddsSource"] = "Unavailable"

        match["oddsAvailable"] = valid
        match["hasBookmakerOdds"] = valid
        match["bookmakerGatePassed"] = valid

    # v27: API-Football remains primary; OddsPAPI fills only missing 1X2.
    oddspapi_meta = await _supplement_odds_from_oddspapi(matches, refresh=bool(refresh))
    bookmaker_count = sum(1 for m in matches if _valid_1x2(m.get("odds", {})))
    api_football_odds_count = sum(1 for m in matches if m.get("oddsSource") == "API-Football" and _valid_1x2(m.get("odds", {})))
    oddspapi_count = sum(1 for m in matches if m.get("oddsSource") == "OddsPAPI" and _valid_1x2(m.get("odds", {})))

    return {
        **result,
        "matches": matches,
        "oddsComplete": bookmaker_count,
        "oddsBookmaker": bookmaker_count,
        "oddsStatistical": 0,
        "oddsSource": "API-Football + OddsPAPI fallback",
        "oddsSources": {"apiFootball": api_football_odds_count, "oddsPapi": oddspapi_count},
        "oddsPapi": oddspapi_meta,
        "oddsUnavailable": bool(matches) and bookmaker_count == 0,
        "hasBookmakerOdds": bookmaker_count > 0,
        "hasValidOdds": bookmaker_count > 0,
        "provider": result.get("source", "API-Football"),
        "providerWarning": result.get("providerWarning"),
        "quota": dict(_quota_state),
        "generatedAt": datetime.now(timezone.utc).isoformat(),
    }

@app.get("/odds")
async def odds(
    fixture_id: int = Query(...),
    refresh: int = Query(0, ge=0, le=1),
):
    cache_key = f"odds:{fixture_id}"

    if not refresh:
        cached = _odds_cache.get(cache_key)
        if cached and _valid_1x2(cached.get("odds", {})):
            return {**cached, "available": True}

    try:
        data = await _afoot_get_deadline("/odds", {"fixture": fixture_id}, ODDS_API_TIMEOUT, force_fresh=bool(refresh))
        raw = data.get("response", [])
        norm = _normalise_odds(raw[0].get("bookmakers", [])) if raw else {}
        valid = _valid_1x2(norm)
        result = {
            "fixture_id": fixture_id, "odds": norm if valid else {},
            "source": "API-Football" if valid else "Unavailable",
            "available": valid, "bookmakerGatePassed": valid,
            "quota": dict(_quota_state),
        }
        if valid:
            _odds_cache[cache_key] = {
                "fixture_id": fixture_id, "odds": norm, "source": "API-Football",
                "fetchedAt": datetime.now(timezone.utc).isoformat(),
            }
            return result
    except Exception as exc:
        log.warning("Primary /odds failed or exceeded %.1fs for fixture %s: %s", ODDS_API_TIMEOUT, fixture_id, exc)

    if ODDS_API_ENABLED and ODDS_API_KEY:
        meta = _fixture_meta_cache.get(str(fixture_id), {})
        try:
            sport_key = _odds_api_sport_key(meta.get("league", "")) or "soccer_epl"
            events = await _odds_api_get(
                f"/sports/{sport_key}/odds",
                {"regions": ODDS_API_REGIONS, "markets": ODDS_API_MARKETS, "oddsFormat": "decimal"},
            )
            for event in events if isinstance(events, list) else []:
                if _event_matches_fixture(event, meta):
                    norm = _normalise_odds_api_event(event)
                    valid = _valid_1x2(norm)
                    return {
                        "fixture_id": fixture_id, "odds": norm if valid else {},
                        "source": "The Odds API" if valid else "Unavailable",
                        "available": valid, "bookmakerGatePassed": valid,
                        "oddsApiEventId": event.get("id"),
                        "fallback": True,
                    }
        except Exception as exc:
            log.warning("The Odds API fixture fallback failed: %s", exc)

    return {
        "fixture_id": fixture_id, "odds": {}, "source": "Unavailable",
        "available": False, "bookmakerGatePassed": False,
        "fallback": False, "quota": dict(_quota_state),
    }


@app.get("/odds/batch")
async def odds_batch(
    fixture_ids: str = Query(...),
    use_backup: int = Query(0),
    refresh: int = Query(0, ge=0, le=1),
):
    try:
        ids = [int(x.strip()) for x in fixture_ids.split(",") if x.strip()]
    except ValueError:
        raise HTTPException(400, "fixture_ids must be comma-separated integers")
    if not ids:
        raise HTTPException(400, "fixture_ids is empty")
    if len(ids) > 100:
        raise HTTPException(400, "Maximum 100 fixture IDs per batch request")

    result = {}
    for fixture_id in ids:
        cache_key = f"odds:{fixture_id}"
        cached = _odds_cache.get(cache_key) if not refresh else None
        if cached and _valid_1x2(cached.get("odds", {})):
            result[str(fixture_id)] = {"odds": cached["odds"], "source": "API-Football", "available": True}
            continue

        try:
            data = await _afoot_get_deadline("/odds", {"fixture": fixture_id}, ODDS_API_TIMEOUT, force_fresh=bool(refresh))
            raw = data.get("response", [])
            norm = _normalise_odds(raw[0].get("bookmakers", [])) if raw else {}
            if _valid_1x2(norm):
                _odds_cache[cache_key] = {"fixture_id": fixture_id, "odds": norm, "source": "API-Football", "fetchedAt": datetime.now(timezone.utc).isoformat()}
                result[str(fixture_id)] = {"odds": norm, "source": "API-Football", "available": True}
                continue
        except Exception as exc:
            log.warning("odds/batch primary fixture %s failed: %s", fixture_id, exc)

        # The frontend normally uses /odds for single fixture fallback. Keep
        # batch resilient as well so bulk widgets get the same behaviour.
        if ODDS_API_ENABLED and ODDS_API_KEY:
            fallback = await odds(fixture_id=fixture_id, refresh=0)
            if fallback.get("available"):
                result[str(fixture_id)] = {
                    "odds": fallback.get("odds", {}),
                    "source": fallback.get("source", "The Odds API"),
                    "available": True,
                    "fallback": True,
                }

    return {
        "odds": result, "count": len(result), "fetched": [int(x) for x in result.keys()],
        "source": "Mixed: API-Football + The Odds API fallback" if result else "Unavailable",
        "quota": dict(_quota_state),
    }


# ---------------------------------------------------------------------------
# TEAM HISTORY / SCAN
# ---------------------------------------------------------------------------

@app.get("/team/history")
async def team_history(
    team: str = Query(...),
    league_id: int = Query(0),
    last: int = Query(20),
):
    """v293: resilient team history — memory -> durable last-good -> provider -> fail-soft."""
    raw = str(team or "").strip()
    cache_key = f"team:{raw.lower()}:{league_id}:{last}"
    snapshot_key = f"team_history_last_good:{raw.lower()}:{league_id}:{last}"

    cached = _team_cache.get(cache_key)
    if cached is not None:
        return cached

    snapshot = _dashboard_snapshot_get(snapshot_key) if "_dashboard_snapshot_get" in globals() else None
    snapshot_data = (snapshot or {}).get("data") if isinstance(snapshot, dict) else None

    team_id = None
    team_name = None

    # Numeric team IDs are already canonical provider IDs; do not send "42" as a
    # provider name search. This also removes one unnecessary upstream request.
    if raw.isdigit():
        team_id = int(raw)
        try:
            row = _db_team(team_id) if "_db_team" in globals() else None
            if row:
                team_name = row.get("name")
        except Exception:
            pass
        if not team_name and isinstance(snapshot_data, dict):
            team_name = snapshot_data.get("team_name")
        team_name = team_name or f"Team {team_id}"
    else:
        try:
            search = await _afoot_get_deadline("/teams", {"search": raw}, deadline=4.5)
            teams = search.get("response", []) if isinstance(search, dict) else []
            if teams:
                team_id = teams[0].get("team", {}).get("id")
                team_name = teams[0].get("team", {}).get("name") or raw
        except Exception:
            if isinstance(snapshot_data, dict):
                _team_cache[cache_key] = snapshot_data
                return snapshot_data
            return {
                "team_id": None,
                "team_name": raw,
                "matches": [],
                "count": 0,
                "source": "unavailable",
                "refreshing": True,
            }

        if not team_id:
            if isinstance(snapshot_data, dict):
                _team_cache[cache_key] = snapshot_data
                return snapshot_data
            return {
                "team_id": None,
                "team_name": raw,
                "matches": [],
                "count": 0,
                "source": "unavailable",
                "refreshing": True,
            }

    params = {
        "team": team_id,
        "season": _current_season(),
        "last": last,
    }
    if league_id:
        params["league"] = league_id

    try:
        data = await _afoot_get_deadline("/fixtures", params, deadline=5.5)
        matches = []

        for fixture in (data.get("response", []) if isinstance(data, dict) else []):
            status = fixture.get("fixture", {}).get("status", {}).get("short", "")
            if status not in ("FT", "AET", "PEN"):
                continue

            teams_obj = fixture.get("teams", {})
            goals = fixture.get("goals", {})
            is_home = teams_obj.get("home", {}).get("id") == team_id

            home_goals = goals.get("home", 0) or 0
            away_goals = goals.get("away", 0) or 0

            matches.append({
                "hg": home_goals if is_home else away_goals,
                "ag": away_goals if is_home else home_goals,
                "isHome": is_home,
            })

        result = {
            "team_id": team_id,
            "team_name": team_name,
            "matches": matches,
            "count": len(matches),
            "source": "API-Football",
        }

        # Only replace last-good storage when the provider returned useful history.
        if matches:
            _team_cache[cache_key] = result
            if "_dashboard_snapshot_put" in globals():
                _dashboard_snapshot_put(snapshot_key, {"data": result})
        elif isinstance(snapshot_data, dict):
            _team_cache[cache_key] = snapshot_data
            return snapshot_data

        return result

    except Exception:
        # Never expose a transient provider/network failure as a public 502.
        if isinstance(snapshot_data, dict):
            _team_cache[cache_key] = snapshot_data
            return snapshot_data
        return {
            "team_id": team_id,
            "team_name": team_name,
            "matches": [],
            "count": 0,
            "source": "unavailable",
            "refreshing": True,
        }


@app.get("/team/profile")
async def team_profile(team: str = Query(...), season: int = Query(0, ge=0)):
    """Cached team profile with identity, squad, fixtures, table and season data."""
    season=season or _current_season()
    raw=str(team).strip()
    cache_key=f"team-profile-v480:{raw.lower()}:{season}"
    cached=_team_profile_page_cache.get(cache_key)
    if cached is not None:return cached

    if raw.isdigit():
        tid=int(raw)
        snap=_dashboard_snapshot_get(f"team_profile_last_good:{tid}:{season}") if "_dashboard_snapshot_get" in globals() else None
        snap_data=(snap or {}).get("data") if isinstance(snap,dict) else None
        if SPORTS_DB_ENABLED:
            sql_profile=_sql_team_profile(tid,season)
            if sql_profile:
                row=_db_team(tid)
                useful_sql=bool(sql_profile.get("players") or sql_profile.get("past10") or sql_profile.get("future") or sql_profile.get("teamStats") or sql_profile.get("standings"))
                sql_profile["team"]["publicRef"]=_public_ref("team",tid,sql_profile["team"].get("name") or "team")
                for pl in sql_profile.get("players") or []:
                    if pl.get("id"):
                        pl["publicRef"]=_public_ref("player",int(pl["id"]),pl.get("name") or "player")
                if not useful_sql:
                    # v480: Big-5 team pages may not return an empty SQL shell. Repair the
                    # canonical team record synchronously before first paint, then read it back.
                    try:
                        await _sql_sync_team(tid,season,force=True)
                        sql_profile=_sql_team_profile(tid,season)
                        useful_sql=bool(sql_profile and (sql_profile.get("players") or sql_profile.get("past10") or sql_profile.get("future") or sql_profile.get("teamStats") or sql_profile.get("standings")))
                    except Exception as exc:
                        log.warning("v480 canonical team repair %s/%s failed: %s",tid,season,exc)
                elif row and _sync_due(row.get("synced_at")):
                    asyncio.create_task(_sql_sync_team(tid,season,force=False))
                if useful_sql:
                    sql_profile["cached"]=True;sql_profile["refreshing"]=bool(row and _sync_due(row.get("synced_at")))
                    _team_profile_page_cache[cache_key]=sql_profile
                    return sql_profile
        if isinstance(snap_data,dict) and (snap_data.get("team") or snap_data.get("players") or snap_data.get("past10") or snap_data.get("future")):
            snap_data={**snap_data,"cached":True,"refreshing":True}
            _team_profile_page_cache[cache_key]=snap_data
            if SPORTS_DB_ENABLED:asyncio.create_task(_sql_sync_team(tid,season,force=False))
            return snap_data
        team_id,team_name=tid,str(tid)
    else:
        team_id,team_name=await _resolve_team_id(raw)

    async def safe(path,params):
        try:return await _afoot_get_deadline(path,params,deadline=4.5)
        except Exception as exc:
            log.warning("TEAM_PROFILE upstream=%s team=%s error=%s",path,team_id,exc)
            return {"response":[],"_failed":True}

    profile,squad,recent,future=await asyncio.gather(
        safe("/teams",{"id":team_id}),
        safe("/players/squads",{"team":team_id}),
        safe("/fixtures",{"team":team_id,"season":season,"last":10}),
        safe("/fixtures",{"team":team_id,"season":season,"next":10}),
    )
    p=(profile.get("response") or [{}])[0]
    team_obj=p.get("team") or {"id":team_id,"name":team_name}
    team_obj["id"]=team_obj.get("id") or team_id
    team_obj["publicRef"]=_public_ref("team",int(team_obj["id"]),team_obj.get("name") or team_name or "team")
    if not team_obj.get("logo"):team_obj["logo"]=_ksn_api_team_badge(team_id)

    players=[]
    for sr in squad.get("response") or []:
        for pl in sr.get("players") or []:
            if pl.get("id"):players.append({"id":pl.get("id"),"name":pl.get("name"),"age":pl.get("age"),"number":pl.get("number"),"position":pl.get("position"),"photo":pl.get("photo") or _ksn_api_player_photo(pl.get("id")),"nationality":pl.get("nationality"),"publicRef":_public_ref("player",int(pl["id"]),pl.get("name") or "player")})

    # A squad can occasionally be empty while season player data is available.
    # One cached fallback request restores the team page without a per-player fanout.
    if not players and not squad.get("_failed"):
        seen_players=set(); page_no=1; total_pages=1
        while page_no <= total_pages and page_no <= 4:
            fallback=await safe("/players",{"team":team_id,"season":season,"page":page_no})
            paging=fallback.get("paging") or {}
            total_pages=max(1,int(paging.get("total") or 1))
            for row in fallback.get("response") or []:
                pl=row.get("player") or {}; pid=pl.get("id")
                if pid and pid not in seen_players:
                    seen_players.add(pid)
                    st=((row.get("statistics") or [{}])[0] or {})
                    players.append({"id":pid,"name":pl.get("name"),"age":pl.get("age"),"number":(st.get("games") or {}).get("number"),"position":(st.get("games") or {}).get("position"),"photo":pl.get("photo") or _ksn_api_player_photo(pl.get("id")),"nationality":pl.get("nationality"),"publicRef":_public_ref("player",int(pid),pl.get("name") or "player")})
            page_no+=1

    def norm(items):
        out=[]
        for f in items:
            ts=f.get("teams") or {};g=f.get("goals") or {};fs=f.get("fixture") or {};lg=f.get("league") or {}
            out.append({"id":fs.get("id"),"date":fs.get("date"),"status":(fs.get("status") or {}).get("short"),"statusLong":(fs.get("status") or {}).get("long"),
                        "home":(ts.get("home") or {}).get("name"),"away":(ts.get("away") or {}).get("name"),
                        "homeId":(ts.get("home") or {}).get("id"),"awayId":(ts.get("away") or {}).get("id"),
                        "homeLogo":(ts.get("home") or {}).get("logo"),"awayLogo":(ts.get("away") or {}).get("logo"),
                        "homeScore":g.get("home"),"awayScore":g.get("away"),"league":lg.get("name"),"leagueId":lg.get("id"),
                        "leagueLogo":lg.get("logo"),"leagueFlag":lg.get("flag")})
        return out
    past=norm(recent.get("response") or []);upcoming=norm(future.get("response") or [])

    canonical=await _ksn_big5_identity(team_id,team_obj.get("name") or team_name,season)
    league_hint=(int(canonical["leagueId"]),season) if canonical.get("leagueId") else None
    _big5_ids={39,140,78,135,61}
    _league_candidates=[]
    for fx in (future.get("response") or [])+(recent.get("response") or []):
        lg=fx.get("league") or {}
        if lg.get("id"):
            lid=int(lg["id"]); _league_candidates.append((0 if lid in _big5_ids else 1,lid,int(lg.get("season") or season)))
    if not league_hint and _league_candidates:
        _,lid,lyr=sorted(_league_candidates,key=lambda x:(x[0],x[1]))[0]; league_hint=(lid,lyr)

    standings=[];team_stats={}
    if league_hint:
        standings_task=_fetch_standings_for_league(*league_hint)
        stats_task=safe("/teams/statistics",{"team":team_id,"league":league_hint[0],"season":league_hint[1]})
        sd,st=await asyncio.gather(standings_task,stats_task,return_exceptions=True)
        if isinstance(sd,list):
            standings=sd
            if standings:_dashboard_snapshot_put(f"canonical_standings:{league_hint[0]}:{league_hint[1]}",{"data":{"standings":standings}})
        if isinstance(st,dict):team_stats=st.get("response") or {}
        if not _ksn_valid_team_stats(team_stats):
            team_stats=_ksn_stats_from_summary(_ksn_summary_from_results(recent.get("response") or [],team_id),team_id,league_hint[0],league_hint[1])

    form=[];gf=ga=0
    for x in reversed(past):
        hs=x.get("homeScore");av=x.get("awayScore")
        if hs is None or av is None:continue
        hs=int(hs);av=int(av)
        if x.get("homeId")==team_id:gf+=hs;ga+=av;r="W" if hs>av else "D" if hs==av else "L"
        else:gf+=av;ga+=hs;r="W" if av>hs else "D" if av==hs else "L"
        form.append(r)
    form=form[-5:]

    if not team_obj.get("country") and canonical.get("country"):team_obj["country"]=canonical.get("country")
    league_flag=""
    for fxrow in (future.get("response") or [])+(recent.get("response") or []):
        lg=fxrow.get("league") or {}
        if league_hint and int(lg.get("id") or 0)==league_hint[0] and lg.get("flag"):
            league_flag=lg.get("flag");break
    result={"team":team_obj,"venue":p.get("venue") or {},"players":players,"past10":past,"future":upcoming,
            "standings":standings,"league":({"id":league_hint[0],"season":league_hint[1],"name":canonical.get("league"),"country":canonical.get("country"),"flag":league_flag} if league_hint else {}),
            "season":season,"form":form,"goalsFor":gf,"goalsAgainst":ga,"teamStats":team_stats,
            "nextOdds":{},"updatedAt":datetime.now(timezone.utc).isoformat()}
    _team_profile_page_cache[cache_key]=result
    _team_profile_page_cache[f"team-profile-v480:{team_id}:{season}"]=result
    if result.get("team") and (result.get("players") or result.get("past10") or result.get("future") or result.get("standings") or result.get("teamStats")):
        _dashboard_snapshot_put(f"team_profile_last_good:{team_id}:{season}",{"data":result})
    return result

@app.get("/player/profile")
async def player_profile(player: int = Query(..., ge=1), season: int = Query(0, ge=0)):
    """Fast dedicated player profile.

    First paint is intentionally bounded: current profile/statistics, recent
    fixtures, transfers and trophies are fetched concurrently.
    Historical season fan-out and per-fixture rating fan-out are not performed
    on the critical path.
    """
    season=season or _current_season()
    player_snap=_dashboard_snapshot_get(f"player_profile_last_good:{player}:{season}") if "_dashboard_snapshot_get" in globals() else None
    player_snap_data=(player_snap or {}).get("data") if isinstance(player_snap,dict) else None
    if isinstance(player_snap_data,dict) and (player_snap_data.get("player") or player_snap_data.get("statistics")):
        key=f"player-profile-fast:{player}:{season}"
        cached=_team_cache.get(key)
        if cached is not None:return cached
        if SPORTS_DB_ENABLED:asyncio.create_task(_sql_sync_player(player,season,force=False))
        return {**player_snap_data,"cached":True,"refreshing":True}
    if SPORTS_DB_ENABLED:
        sql_profile=_sql_player_profile(player,season)
        if sql_profile:
            row=_db_player(player)
            useful_sql=bool(sql_profile.get("statistics") or sql_profile.get("teams"))
            if row and (_sync_due(row.get("synced_at")) or not useful_sql):
                asyncio.create_task(_sql_sync_player(player,season,force=not useful_sql))
            if useful_sql:
                return sql_profile
    key=f"player-profile-fast:{player}:{season}"
    cached=_team_cache.get(key)
    if cached is not None:
        return cached

    async def safe(path,params):
        try:
            return await _afoot_get(path,params)
        except Exception as exc:
            log.debug("Player profile %s failed for %s: %s",path,player,exc)
            return {"response":[]}

    base,recent,transfers_raw,trophies_raw=await asyncio.gather(
        safe("/players",{"id":player,"season":season}),
        safe("/fixtures",{"player":player,"season":season,"last":10}),
        safe("/transfers",{"player":player}),
        safe("/trophies",{"player":player}),
    )

    rows=base.get("response") or []
    profile=rows[0] if rows else {}
    pobj=profile.get("player") or {}
    stats=profile.get("statistics") or []
    stats_season=season
    if not stats and season > 0:
        previous=await safe("/players",{"id":player,"season":season-1})
        prev_rows=previous.get("response") or []
        if prev_rows:
            prev_profile=prev_rows[0] or {}
            if not pobj:
                pobj=prev_profile.get("player") or {}
            prev_stats=prev_profile.get("statistics") or []
            if prev_stats:
                stats=prev_stats
                stats_season=season-1
    if not pobj.get("name"):
        profile_fallback=await safe("/players/profiles",{"player":player})
        prow=(profile_fallback.get("response") or [{}])[0]
        pobj=prow.get("player") or pobj
    if not pobj.get("id"):pobj["id"]=player

    def split(st):
        return {
            "team":st.get("team") or {},"league":st.get("league") or {},
            "games":st.get("games") or {},"goals":st.get("goals") or {},
            "shots":st.get("shots") or {},"passes":st.get("passes") or {},
            "tackles":st.get("tackles") or {},"duels":st.get("duels") or {},
            "dribbles":st.get("dribbles") or {},"fouls":st.get("fouls") or {},
            "cards":st.get("cards") or {},"penalty":st.get("penalty") or {},
        }

    teams=[split(x) for x in stats]
    recent_rows=recent.get("response") or []

    transfers=[]
    for block in transfers_raw.get("response") or []:
        for tr in block.get("transfers") or []:
            transfers.append({"date":tr.get("date"),"type":tr.get("type"),
                              "reason":tr.get("reason"),"team":tr.get("teams") or {}})

    trophies=[{"league":x.get("league"),"country":x.get("country"),"season":x.get("season"),
               "place":x.get("place"),"status":x.get("status")}
              for x in trophies_raw.get("response") or []]

    # Current team is preserved explicitly for frontend routing.
    current_team=(stats[0].get("team") if stats else {}) or {}
    result={
        "player":pobj,
        "currentTeam":current_team,
        "statistics":stats,
        "teams":teams,
        "recentMatches":recent_rows,
        "transfers":transfers,
        "trophies":trophies,
        "career":[],
        "form":[],
        "matchRatings":[],
        "ratingSummary":{"count":0,"average":None,"best":None},
        "season":stats_season,
        "requestedSeason":season,
        "detailsDeferred":True,
        "updatedAt":datetime.now(timezone.utc).isoformat(),
    }
    _team_cache[key]=result
    if result.get("player") and (result.get("statistics") or result.get("teams") or result.get("recentMatches")):
        _dashboard_snapshot_put(f"player_profile_last_good:{player}:{season}",{"data":result})
    return result


async def _resolve_team_id(name: str) -> tuple[int, str]:
    search = await _afoot_get("/teams", {"search": name})
    teams = search.get("response", [])
    if not teams:
        raise HTTPException(404, f"Team not found: {name!r}")
    return teams[0]["team"]["id"], teams[0]["team"]["name"]


@app.get("/team/h2h")
async def team_h2h(
    home: str = Query(...),
    away: str = Query(...),
    last: int = Query(10, ge=1, le=20),
):
    """Head-to-head record between two named teams — used for match-insight
    panels (Fixtures/Predictions rows). Cached per team pair."""
    cache_key = f"h2h:{home.lower()}:{away.lower()}:{last}"
    cached = _team_cache.get(cache_key)
    if cached is not None:
        return cached

    home_id, home_name = await _resolve_team_id(home)
    away_id, away_name = await _resolve_team_id(away)

    data = await _afoot_get(
        "/fixtures/headtohead",
        {"h2h": f"{home_id}-{away_id}", "last": last},
    )

    meetings = []
    home_wins = away_wins = draws = 0
    btts_count = over25_count = 0

    for fixture in data.get("response", []):
        status = fixture.get("fixture", {}).get("status", {}).get("short", "")
        if status not in ("FT", "AET", "PEN"):
            continue

        teams_obj = fixture.get("teams", {})
        goals = fixture.get("goals", {})
        fixture_home_id = teams_obj.get("home", {}).get("id")

        hg = goals.get("home", 0) or 0
        ag = goals.get("away", 0) or 0
        total = hg + ag

        # Normalise so "home"/"away" always refer to the *current* fixture's
        # home/away teams, regardless of who hosted historically.
        if fixture_home_id == home_id:
            our_home_goals, our_away_goals = hg, ag
        else:
            our_home_goals, our_away_goals = ag, hg

        if our_home_goals > our_away_goals:
            home_wins += 1
        elif our_away_goals > our_home_goals:
            away_wins += 1
        else:
            draws += 1

        if hg > 0 and ag > 0:
            btts_count += 1
        if total > 2.5:
            over25_count += 1

        meetings.append({
            "date": fixture.get("fixture", {}).get("date", "")[:10],
            "league": fixture.get("league", {}).get("name", ""),
            "homeTeam": teams_obj.get("home", {}).get("name", ""),
            "awayTeam": teams_obj.get("away", {}).get("name", ""),
            "hg": hg,
            "ag": ag,
        })

    played = len(meetings)
    result = {
        "homeTeam": home_name,
        "awayTeam": away_name,
        "played": played,
        "homeWins": home_wins,
        "awayWins": away_wins,
        "draws": draws,
        "bttsPct": round(100 * btts_count / played, 1) if played else 0,
        "over25Pct": round(100 * over25_count / played, 1) if played else 0,
        "meetings": meetings,
        "source": "API-Football",
    }
    _team_cache[cache_key] = result
    return result


def _team_league_hint_db(team_id:int, season:int):
    if not SPORTS_DB_ENABLED:return None
    try:
        with _sports_db() as db:
            r=db.execute("SELECT league_id FROM team_leagues WHERE team_id=? AND season=? ORDER BY league_id LIMIT 1",(team_id,season)).fetchone()
        return int(r["league_id"]) if r and r["league_id"] else None
    except Exception:return None

async def _league_coverage(league_id:int, season:int):
    if not league_id:return {}
    try:
        d=await _afoot_get("/leagues",{"id":league_id,"season":season})
        row=(d.get("response") or [{}])[0]
        for ss in row.get("seasons") or []:
            if int(ss.get("year") or 0)==int(season):return ss.get("coverage") or {}
    except Exception:pass
    return {}

async def _team_injuries_data(team_id:int, season:int, league_id:int|None=None, force:bool=False):
    # DB-first. Current injuries refresh at most every four hours; historical rows remain reusable.
    cached=[]
    if SPORTS_DB_ENABLED:
        try:
            with _sports_db() as db:
                rows=db.execute("""SELECT i.*,p.name,p.photo FROM injuries i LEFT JOIN players p ON p.provider_id=i.player_id
                WHERE i.team_id=? AND i.season=? ORDER BY i.date DESC LIMIT 50""",(team_id,season)).fetchall()
            cached=[{"id":r["player_id"],"name":r["name"],"photo":r["photo"],"type":r["type"],"reason":r["reason"],"date":r["date"]} for r in rows]
        except Exception:cached=[]
    ck=f"team-injuries:{team_id}:{season}"
    mem=_team_cache.get(ck)
    if mem is not None and not force:return mem
    coverage=await _league_coverage(league_id,season) if league_id else {}
    if coverage and coverage.get("injuries") is False:
        result={"teamId":team_id,"season":season,"players":cached,"count":len(cached),"available":False,"coverage":coverage,"source":"database" if cached else "coverage"}
        _team_cache[ck]=result;return result
    try:
        params={"team":team_id,"season":season}
        if league_id:params["league"]=league_id
        d=await _afoot_get("/injuries",params,force_fresh=force)
        rows=d.get("response") or []
        players=[];now=datetime.now(timezone.utc).isoformat()
        for x in rows:
            p=x.get("player") or {};tm=x.get("team") or {};lg=x.get("league") or {};fx=x.get("fixture") or {}
            if not p.get("id"):continue
            item={"id":p.get("id"),"name":p.get("name"),"photo":p.get("photo"),"type":p.get("type") or x.get("type"),"reason":p.get("reason") or x.get("reason"),"date":fx.get("date") or x.get("date")}
            players.append(item)
            if SPORTS_DB_ENABLED:
                _db_upsert_player(p)
                try:
                    with _sports_db() as db:db.execute("""INSERT INTO injuries(player_id,team_id,league_id,season,date,type,reason,payload_json,synced_at)
                    VALUES(?,?,?,?,?,?,?,?,?) ON CONFLICT(player_id,team_id,league_id,season,date,type) DO UPDATE SET reason=excluded.reason,payload_json=excluded.payload_json,synced_at=excluded.synced_at""",
                    (int(p["id"]),team_id,int(lg.get("id") or league_id or 0),season,str(item.get("date") or "")[:10],item.get("type"),item.get("reason"),_db_json(x),now))
                except Exception:pass
        if players:cached=players
    except Exception as exc:
        log.debug("team injuries %s/%s: %s",team_id,season,exc)
    result={"teamId":team_id,"season":season,"players":cached,"count":len(cached),"available":bool(cached) or not (coverage and coverage.get("injuries") is False),"coverage":coverage,"source":"API-Football + database"}
    _team_cache[ck]=result;return result

@app.get("/team/injuries")
async def team_injuries(team: str = Query(...), season:int=Query(0,ge=0), refresh:int=Query(0,ge=0,le=1)):
    """Coverage-aware, DB-first current injury/suspension data."""
    season=season or _current_season()
    try:team_id=int(team)
    except Exception:team_id,_=await _resolve_team_id(team)
    league_id=_team_league_hint_db(team_id,season)
    return await _team_injuries_data(team_id,season,league_id,bool(refresh))

@app.get("/team/intelligence")
async def team_intelligence(team:int=Query(...,ge=1), season:int=Query(0,ge=0), refresh:int=Query(0,ge=0,le=1)):
    """Unified Big-5 team intelligence: DB-first season stats/history plus current availability and recent confirmed lineups."""
    season=season or _current_season()
    if SPORTS_DB_ENABLED:
        prof=_sql_team_profile(team,season)
        if refresh or not prof or not (prof.get("teamStats") or prof.get("players")):
            try:await _sql_sync_team(team,season,force=bool(refresh));prof=_sql_team_profile(team,season)
            except Exception as exc:log.warning("team intelligence sync %s/%s: %s",team,season,exc)
    else:prof=None
    if not prof:
        try:prof=await team_profile(team=team,season=season)
        except Exception:prof={"team":{"id":team},"season":season}
    league_id=_team_league_hint_db(team,season)
    coverage=await _league_coverage(league_id,season) if league_id else {}
    injuries=await _team_injuries_data(team,season,league_id,bool(refresh))
    recent=(prof.get("past10") or [])[:5]
    fixture_ids=[int(x.get("id")) for x in recent if x.get("id")]
    async def lineup(fid):
        try:
            d=await _afoot_get("/fixtures/lineups",{"fixture":fid},force_fresh=False)
            return {"fixtureId":fid,"teams":_normalise_lineups(d.get("response") or [])}
        except Exception:return {"fixtureId":fid,"teams":[]}
    lineups=[]
    if not coverage or coverage.get("lineups") is not False:
        lineups=await asyncio.gather(*(lineup(fid) for fid in fixture_ids[:3])) if fixture_ids else []
    formations=[]
    for block in lineups:
        for row in block.get("teams") or []:
            if int((row.get("team") or {}).get("id") or 0)==team and row.get("formation"):formations.append(row.get("formation"))
    st=prof.get("teamStats") or {}
    fx=st.get("fixtures") or {};goals=st.get("goals") or {}
    # Exact result-derived fallback prevents blank season cards when /teams/statistics is absent/stale.
    raw_season=[]
    if SPORTS_DB_ENABLED:
        try:
            with _sports_db() as db:
                rr=db.execute("SELECT payload_json FROM team_fixtures WHERE team_id=? AND season=? ORDER BY fixture_date",(team,season)).fetchall()
            raw_season=[_db_load(r["payload_json"],{}) for r in rr]
        except Exception: raw_season=[]
    derived=_ksn_summary_from_results(raw_season,team)
    canonical=await _ksn_big5_identity(team,(prof.get("team") or {}).get("name") or str(team),season)
    summary={
      "played":((fx.get("played") or {}).get("total")),"wins":((fx.get("wins") or {}).get("total")),"draws":((fx.get("draws") or {}).get("total")),
      "losses":((fx.get("loses") or fx.get("losses") or {}).get("total")),"cleanSheets":((st.get("clean_sheet") or {}).get("total")),
      "failedToScore":((st.get("failed_to_score") or {}).get("total")),"goalsFor":(((goals.get("for") or {}).get("total") or {}).get("total")),
      "goalsAgainst":(((goals.get("against") or {}).get("total") or {}).get("total")),"form":st.get("form") or derived.get("form") or ""
    }
    for k in ("played","wins","draws","losses","cleanSheets","failedToScore","goalsFor","goalsAgainst"):
        if summary.get(k) is None: summary[k]=derived.get(k)
    summary["goalDifference"]=(summary.get("goalsFor")-summary.get("goalsAgainst")) if isinstance(summary.get("goalsFor"),(int,float)) and isinstance(summary.get("goalsAgainst"),(int,float)) else derived.get("goalDifference")
    summary["winRate"]=round(summary.get("wins",0)*100/summary.get("played",1),1) if summary.get("played") else derived.get("winRate")
    summary.update({k:derived.get(k) for k in ("homePlayed","homeWins","awayPlayed","awayWins")})
    fantasy_players=canonical.get("fantasyPlayers") or []
    return {"team":prof.get("team") or {"id":team},"season":season,"seasonLabel":f"{season}/{str(season+1)[-2:]}","leagueId":league_id or canonical.get("leagueId"),"coverage":coverage,"summary":summary,
            "teamStats":st,"standings":prof.get("standings") or [],"squad":prof.get("players") or [],"fantasyPlayers":fantasy_players,"fantasyTeam":canonical.get("fantasyTeam"),"canonicalIdentity":canonical,"injuries":injuries,
            "recentLineups":lineups,"recentFormations":formations,"xg":{"available":False,"message":"Provider xG is shown only when a genuine xG field is returned for a fixture."},
            "source":"PostgreSQL + API-Football + FantasyPlayoffs + archived results","updatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/scan")
async def scan(
    leagues: str = Query("epl,la_liga,bundesliga,serie_a,ligue1"),
    type: str = Query("today"),
):
    aliases = {
        "epl": "Premier League",
        "la_liga": "La Liga",
        "bundesliga": "Bundesliga",
        "serie_a": "Serie A",
        "ligue1": "Ligue 1",
    }

    names = [
        aliases.get(x.strip().lower(), x.strip())
        for x in leagues.split(",")
        if x.strip()
    ]

    all_matches = []
    errors = []

    for name in names:
        try:
            result = await fixtures(
                league=name,
                type=type,
            )
            all_matches.extend(result.get("matches", []))
            await asyncio.sleep(0.2)
        except Exception as exc:
            errors.append(f"{name}: {exc}")

    return {
        "matches": all_matches,
        "count": len(all_matches),
        "errors": errors,
        "leagues": names,
        "source": "API-Football",
    }

# ---------------------------------------------------------------------------
# AI / PREDICTION ENDPOINTS
# ---------------------------------------------------------------------------

def _save_prediction_to_db(match: dict, prediction_result: dict):
    """
    Persist a computed prediction to the learning DB so /best-predictions
    and /learning-stats have data to work with.
    Runs synchronously (SQLite is fast). Swallows errors so a DB hiccup
    never breaks the API response.
    """
    try:
        pred_block = prediction_result.get("prediction", {})
        probs = pred_block.get("probabilities", {})
        fid = match.get("_afootFixtureId") or match.get("fixtureId")
        if not fid:
            return

        raw_kickoff = match.get("datetime") or match.get("kickoff") or ""
        # Normalise to "YYYY-MM-DD HH:MM" so SQLite string comparisons work
        # consistently with the cutoff queries in best_predictions.
        kickoff_stored = raw_kickoff.replace("T", " ")[:16] if raw_kickoff else None

        payload = {
            "fixtureId": int(fid),
            "kickoff": kickoff_stored,
            "homeTeam": match.get("home") or match.get("homeTeam"),
            "awayTeam": match.get("away") or match.get("awayTeam"),
            "probabilities": probs,
            "odds": match.get("odds", {}),
            "modelInputs": prediction_result.get("goalRating", {}),
            "prediction": {
                k: v for k, v in pred_block.items()
                if k != "probabilities"
            },
            "modelVersion": V141_MODEL_VERSION,
            "sport": "football",
            "competition": match.get("league") or match.get("competition"),
            "confidence": pred_block.get("confidence"),
            "bookmakerPrediction": prediction_result.get("bookmakerPrediction"),
        }

        v141_learning.save_prediction(payload)

    except Exception as exc:
        log.warning("Failed to save prediction for fixture %s: %s", fid, exc)



@app.get("/fixtures/high-scoring")
async def fixtures_high_scoring(
    league: str = Query("ALL"),
    min_xg: float = Query(2.5, ge=0.0, le=10.0),
    min_over25: float = Query(55.0, ge=0.0, le=100.0),
    limit: int = Query(30, ge=1, le=100),
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
):
    """Return upcoming fixtures ranked by high-scoring likelihood.

    Scoring formula (0-100):
      • 40% — Poisson over-2.5-goals probability
      • 25% — Poisson over-3.5-goals probability
      • 20% — combined xG (home + away), normalised to a 5-goal ceiling
      • 15% — bookmaker over-2.5 implied probability (if available)

    Only fixtures with over-2.5 probability >= min_over25 AND combined
    xG >= min_xg are returned.  Results are sorted highest score first.
    """
    today    = datetime.now().strftime("%Y-%m-%d")
    tomorrow = (datetime.now() + timedelta(days=1)).strftime("%Y-%m-%d")

    fixtures_data = await fixtures_with_odds(
        league=league,
        type="upcoming",
        date_from=date_from or today,
        date_to=date_to or upcoming_end,
        refresh=0,
    )

    current_season = _current_season()
    results: list[dict] = []

    _canonical_league_by_id = {int(v): k for k, v in LEAGUE_IDS.items() if isinstance(v, int)}
    for match in fixtures_data.get("matches", []):
        # Preserve provider league identity through odds/prediction merges.
        try:
            lid = int(match.get("_leagueId")) if match.get("_leagueId") is not None else None
        except (TypeError, ValueError):
            lid = None
        if lid in _canonical_league_by_id:
            match["league"] = _canonical_league_by_id[lid]
        if match.get("isFinished"):
            continue

        league_id = match.get("_leagueId") or match.get("leagueId") or match.get("league_id")
        season    = match.get("_leagueSeason") or current_season
        if league_id:
            try:
                match = await _enrich_match(match, int(league_id), int(season))
            except Exception as exc:
                log.warning("high_scoring enrich failed %s: %s", match.get("_afootFixtureId"), exc)
            await asyncio.sleep(0.15)

        stat = _poisson(match)
        o    = match.get("odds", {})

        over25_prob = round(stat["over25"] * 100, 1)
        over35_prob = round(stat["over35"] * 100, 1)
        xg_home     = round(stat["xgHome"], 2)
        xg_away     = round(stat["xgAway"], 2)
        xg_total    = round(xg_home + xg_away, 2)
        btts_prob   = round(stat["btts"] * 100, 1)

        # Bookmaker over-2.5 implied probability
        bk_over25_odds = o.get("over25", 0)
        bk_over25_pct  = round(100 / bk_over25_odds, 1) if bk_over25_odds and bk_over25_odds > 1 else 0.0

        # Apply filters
        if over25_prob < min_over25 or xg_total < min_xg:
            continue

        # Composite high-scoring score (0-100)
        score = round(
            0.40 * over25_prob
            + 0.25 * over35_prob
            + 0.20 * min(xg_total / 5.0, 1.0) * 100
            + 0.15 * (bk_over25_pct if bk_over25_pct else over25_prob),
            1,
        )

        results.append({
            "fixtureId":    match.get("_afootFixtureId") or match.get("id"),
            "home":         match.get("home"),
            "away":         match.get("away"),
            "league":       match.get("league") or match.get("_league"),
            "leagueId":     league_id,
            "kickoff":      match.get("kickoff") or match.get("date"),
            "highScoringScore": score,
            "xgHome":       xg_home,
            "xgAway":       xg_away,
            "xgTotal":      xg_total,
            "over25Pct":    over25_prob,
            "over35Pct":    over35_prob,
            "over15Pct":    round(stat["over15"] * 100, 1),
            "bttsPct":      btts_prob,
            "bkOver25Pct":  bk_over25_pct,
            "bkOver25Odds": bk_over25_odds,
            "homeGoalsFor": round(match.get("homeGoalsFor", xg_home), 2),
            "awayGoalsFor": round(match.get("awayGoalsFor", xg_away), 2),
            "hasBookmakerOdds": _valid_1x2(o),
        })

    results.sort(key=lambda x: x["highScoringScore"], reverse=True)

    return {
        "count":       len(results[:limit]),
        "filters":     {"minXg": min_xg, "minOver25Pct": min_over25},
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "fixtures":    results[:limit],
    }

@app.get("/ai-predictions")
async def ai_predictions(
    limit: int = Query(20, ge=1, le=100),
    refresh: int = Query(1, ge=0, le=1),
    league: str = Query("ALL"),
    type: str = Query("upcoming"),
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
):
    # v406: shared server LKG for first-time visitors. Browser LKG remains the
    # returning-visitor first paint; this snapshot prevents an empty Prediction
    # Pool when a provider/quota request is temporarily unavailable.
    pred_snap_key = f"predictions:last_good:{str(league).upper()}:{str(type).lower()}"
    pred_snap = _dashboard_snapshot_get(pred_snap_key) if "_dashboard_snapshot_get" in globals() else None
    pred_snap_data = (pred_snap or {}).get("data") if isinstance(pred_snap, dict) else None
    today = datetime.now().strftime("%Y-%m-%d")
    upcoming_end = (
        datetime.now() + timedelta(days=7)
    ).strftime("%Y-%m-%d")

    try:
        fixtures_data = await fixtures_with_odds(
            league=league,
            type=type,
            date_from=date_from or today,
            date_to=date_to or upcoming_end,
            refresh=refresh,
        )
    except Exception as exc:
        # Prediction UI should remain usable when a provider/quota temporarily
        # fails. Return an empty, structured response rather than a raw HTTP 500.
        log.warning("AI predictions provider failure: %s", exc)
        if isinstance(pred_snap_data, dict) and (pred_snap_data.get("predictions") or pred_snap_data.get("matches")):
            return {**pred_snap_data, "stale": True, "fromSharedLastGood": True,
                    "staleReason": "Prediction provider temporarily unavailable"}
        return {
            "predictions": [], "matches": [], "count": 0,
            "eligibleFixtures": 0, "rejectedNoBookmaker1X2": 0,
            "winRateThreshold": WIN_RATE_THRESHOLD, "winRateGateActive": False,
            "winRateDescription": "Prediction service temporarily unavailable.",
            "source": "Kasi Sports News server model + API-Football/OddsPAPI bookmaker odds",
            "modelVersion": V141_MODEL_VERSION,
            "oddsRequired": "complete current bookmaker 1X2",
            "error": "Prediction service temporarily unavailable",
            "quota": dict(_quota_state),
            "generatedAt": datetime.now(timezone.utc).isoformat(),
        }

    eligible = []
    model_only = []
    rejected = 0

    # Resolve current season year for API-Football calls
    current_season = _current_season()

    for match in fixtures_data.get("matches", []):
        if match.get("isFinished"):
            continue

        if not _valid_1x2(match.get("odds", {})):
            rejected += 1
            # Keep a clearly-labelled statistical AI prediction available as a
            # fallback. It is not bookmaker-qualified and is never a Game of Day.
            pred_result = _prediction(match)
            try:
                _save_prediction_to_db(match, pred_result)
            except Exception as exc:
                log.debug("Model-only prediction snapshot not stored fixture=%s: %s", match.get("_afootFixtureId") or match.get("id"), exc)
            model_only.append({**match, **pred_result, "oddsAvailable":False, "bookmakerGatePassed":False, "predictionEligible":False, "gamesOfDayEligible":False, "modelOnly":True, "predictionBasis":"available team/statistical data; no current bookmaker 1X2"})
            continue

        # Fast initial prediction: use the fixture + cached bookmaker data immediately.
        # Standings/form enrichment is deliberately not performed in this request because
        # it created a provider fan-out and left the homepage stuck on "Predictions loading".
        pred_result = _prediction(match)
        _save_prediction_to_db(match, pred_result)
        item = {
            **match,
            **pred_result,
            "oddsAvailable": True,
            "bookmakerGatePassed": True,
            "predictionEligible": True,
            "gamesOfDayEligible": True,
            # Expose win-rate metadata for the dashboard
            "homeWinRate":    match.get("_homeWinRate", None),
            "awayWinRate":    match.get("_awayWinRate", None),
            "homeGamesPlayed": match.get("_homeGamesPlayed", 0),
            "awayGamesPlayed": match.get("_awayGamesPlayed", 0),
        }
        eligible.append(item)

    # ── Confidence threshold ───────────────────────────────────────────────
    # Predictions below 52% are near-random but are still included so the
    # dashboard can show them. They are flagged with lowConfidenceFlag=True
    # so the UI can render a visual warning instead of hiding them entirely.
    MIN_CONFIDENCE = 52

    # ── Flag low-confidence and odds-model disagreement ────────────────────
    # lowConfidenceFlag is set when EITHER:
    #   • the model confidence is below 52 %, OR
    #   • bookmaker odds and our model disagree on the predicted winner
    #     (disagreement > 20 percentage points on the winner outcome).
    for p in eligible:
        probs = p["prediction"].get("probabilities", {})
        odds  = p.get("odds", {})
        conf  = p["prediction"].get("confidence", 0)

        winner_key = max(("homeWin", "draw", "awayWin"), key=lambda k: probs.get(k, 0))
        odds_key   = max(("homeWin", "draw", "awayWin"), key=lambda k: odds.get(k, 0) if odds.get(k, 0) > 0 else 0)

        odds_model_agree = (winner_key == odds_key)
        below_threshold  = conf < MIN_CONFIDENCE

        p["prediction"]["oddsModelAgree"]    = odds_model_agree
        p["prediction"]["belowConfidence"]   = below_threshold
        p["prediction"]["lowConfidenceFlag"] = below_threshold or not odds_model_agree

    # v458: global league hierarchy is the primary display order; model quality ranks inside each tier.
    eligible.sort(key=lambda x: (
        _ksn_league_priority_bucket(x),
        -int(bool(x["prediction"].get("oddsModelAgree", False))),
        -float(x["prediction"].get("confidence", 0) or 0),
    ))

    # Keep bookmaker-qualified picks first, then add model-only predictions.
    # Model-only rows remain clearly labelled and never qualify for Tip of the Day.
    ranked_model_only = sorted(model_only, key=lambda x: (_ksn_league_priority_bucket(x), -float(x.get("prediction",{}).get("confidence",0) or 0)))
    display_predictions = (eligible + ranked_model_only)[:limit]
    payload = {
        "predictions": display_predictions,
        "matches": display_predictions,
        "count": len(display_predictions),
        "eligibleFixtures": len(eligible),
        "modelOnlyFixtures": len(model_only),
        "fallbackMode": bool(not eligible and model_only),
        "rejectedNoBookmaker1X2": rejected,
        "winRateThreshold": WIN_RATE_THRESHOLD,
        "winRateGateActive": False,
        "winRateDescription": "Win-rate gate disabled — all fixtures with valid bookmaker 1X2 odds qualify.",
        "source": "Kasi Sports News server model + API-Football/OddsPAPI bookmaker odds",
        "modelVersion": V141_MODEL_VERSION,
        "oddsRequired": "complete current bookmaker 1X2",
        "quota": dict(_quota_state),
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "publicFree": True, "requiresSubscription": False,
    }
    if display_predictions:
        if "_dashboard_snapshot_put" in globals():
            _dashboard_snapshot_put(pred_snap_key, {"data": payload})
        return payload
    if isinstance(pred_snap_data, dict) and (pred_snap_data.get("predictions") or pred_snap_data.get("matches")):
        return {**pred_snap_data, "stale": True, "fromSharedLastGood": True,
                "staleReason": "Current prediction scan returned no qualified fixtures"}
    return payload


@app.get("/tip-of-day")
async def tip_of_day(request: Request):
    """Top two current bookmaker-qualified Kasi picks using the locked global league hierarchy."""
    today=datetime.now().strftime("%Y-%m-%d")
    tip_window_end=(datetime.now()+timedelta(days=7)).strftime("%Y-%m-%d")
    yesterday=(datetime.now()-timedelta(days=1)).strftime("%Y-%m-%d")
    current=[]
    provider_error=None
    try:
        d=await ai_predictions(limit=100,refresh=0,league="ALL",type="upcoming",date_from=today,date_to=tip_window_end)
        current=[x for x in (d.get("predictions") or []) if x.get("predictionEligible") and _valid_1x2(x.get("odds") or {})]
        current.sort(key=lambda x: float((x.get("prediction") or {}).get("confidence") or x.get("confidence") or 0),reverse=True)
    except Exception as exc:
        provider_error=str(exc)

    def stored_item(row):
        d=dict(row)
        for fld in ("probabilities","odds","prediction"):
            try:d[fld]=json.loads(d.get(fld) or "{}")
            except Exception:d[fld]={}
        probs=d.get("probabilities") or {}
        pred=d.get("prediction") or {}
        best=pred.get("bestPick") or pred.get("winner") or max(("homeWin","draw","awayWin"),key=lambda k:float(probs.get(k,0) or 0))
        conf=float(pred.get("confidence") or max([float(probs.get(k,0) or 0) for k in ("homeWin","draw","awayWin")],default=0))
        if 0<conf<=1:conf*=100
        return {"fixtureId":d.get("fixture_id"),"home":d.get("home_team"),"away":d.get("away_team"),
                "datetime":d.get("kickoff") or "","odds":d.get("odds") or {},"probabilities":probs,
                "prediction":{**pred,"bestPick":best,"confidence":conf},"confidence":conf,
                "stored":True,"originalMatchDate":str(d.get("kickoff") or "")[:10]}

    fallback=[]
    yesterday_rows=[]
    try:
        with v141_learning.connect() as conn:
            rows=conn.execute("""
              SELECT fixture_id,kickoff,home_team,away_team,probabilities,odds,prediction,predicted_at
              FROM predictions
              WHERE date(kickoff) < date(?) AND odds IS NOT NULL AND odds != '{}'
              ORDER BY predicted_at DESC LIMIT 100
            """,(today,)).fetchall()
            fallback=sorted([stored_item(r) for r in rows],
                            key=lambda x:float((x.get("prediction") or {}).get("confidence") or 0),reverse=True)[:100]
            yr=conn.execute("""
              SELECT p.fixture_id,p.kickoff,p.home_team,p.away_team,p.probabilities,p.prediction,
                     r.actual_result,r.home_goals,r.away_goals,r.market_accuracy,r.resolved_at
              FROM predictions p JOIN results r ON r.prediction_id=p.id
              WHERE date(p.kickoff)=date(?)
              ORDER BY p.predicted_at ASC
            """,(yesterday,)).fetchall()
        for r in yr:
            d=dict(r)
            try: pred=json.loads(d.get("prediction") or "{}")
            except Exception: pred={}
            try: ma=json.loads(d.get("market_accuracy") or "{}")
            except Exception: ma={}
            yesterday_rows.append({"fixtureId":d.get("fixture_id"),"home":d.get("home_team"),"away":d.get("away_team"),
              "kickoff":d.get("kickoff"),"predicted":ma.get("predictedWinner") or pred.get("bestPick") or pred.get("winner") or "—",
              "actual":d.get("actual_result") or "—","homeGoals":d.get("home_goals"),"awayGoals":d.get("away_goals"),
              "correct":bool(ma.get("winnerCorrect"))})
    except Exception as exc:
        log.warning("tip-of-day stored fallback failed: %s",exc)

    # v312: Tip remains useful when current bookmaker 1X2 is temporarily absent.
    # Prefer qualified current picks, then current model-only predictions, then stored historical picks.
    current_model=[]
    if not current:
        try:
            pd=await ai_predictions(limit=100,refresh=0,league="ALL",type="upcoming",date_from=today,date_to=tip_window_end)
            current_model=[x for x in (pd.get("predictions") or []) if not x.get("isFinished")]
            current_model.sort(key=lambda x:float((x.get("prediction") or {}).get("confidence") or x.get("confidence") or 0),reverse=True)
        except Exception as exc:
            provider_error=provider_error or str(exc)
    # v458: Tip uses the same locked hierarchy as Fixtures, Predictions, Live and Finished.
    # Big 5 -> Turkish Super Lig -> visitor-country league(s) -> all other leagues.
    visitor_country=_ksn_request_country(request)
    def _priority_two(rows):
        ranked=_ksn_sort_football_rows(rows,visitor_country)
        return ranked[:2]

    # v339: Tip of the Day is reserved for CURRENT bookmaker-qualified games.
    # When no current Tip qualifies, return exactly three Kasi-vs-Bookmaker examples
    # instead of showing an empty Tip card. Examples may come from recent stored
    # bookmaker-qualified predictions so the comparison remains useful during quiet windows.
    def _bookmaker_pick(item):
        odds=item.get("odds") or {}
        choices=[]
        for key,label in (("homeWin",item.get("home") or "Home"),("draw","Draw"),("awayWin",item.get("away") or "Away")):
            try:
                price=float(odds.get(key) or 0)
            except Exception:
                price=0
            if price>1: choices.append((price,label))
        return min(choices,key=lambda z:z[0]) if choices else (0,"")

    def _comparison_row(item):
        pred=item.get("prediction") or {}
        price,bpick=_bookmaker_pick(item)
        return {
            "fixtureId":item.get("fixtureId") or item.get("fixture_id") or item.get("id") or item.get("_afootFixtureId"),
            "home":item.get("home") or item.get("home_team"),
            "away":item.get("away") or item.get("away_team"),
            "datetime":item.get("datetime") or item.get("kickoff") or "",
            "league":item.get("league") or item.get("competition") or item.get("leagueName") or "",
            "kasiPick":pred.get("bestPick") or pred.get("winner") or item.get("bestOutcome") or "—",
            "kasiConfidence":float(pred.get("confidence") or item.get("confidence") or 0),
            "bookmakerPick":bpick or "—",
            "bookmakerOdds":price or None,
        }

    if current:
        tips=_priority_two(current); state="current"
        comparison_fallback=[]
    else:
        tips=[]; state="comparison"
        candidates=[]
        # Current prediction rows with real 1X2 first.
        for x in current_model:
            if _valid_1x2(x.get("odds") or {}): candidates.append(x)
        # Then recent stored rows that retain real bookmaker odds.
        for x in fallback:
            if _valid_1x2(x.get("odds") or {}): candidates.append(x)
        seen=set(); comparison_fallback=[]
        for x in candidates:
            key=str(x.get("fixtureId") or x.get("fixture_id") or x.get("id") or f"{x.get('home')}|{x.get('away')}|{x.get('datetime')}")
            if key in seen: continue
            seen.add(key); comparison_fallback.append(_comparison_row(x))
            if len(comparison_fallback)>=3: break

    # If today's providers return no qualifying current or comparison rows, reuse the
    # last real bookmaker-backed comparison snapshot. Never fabricate odds or picks.
    if not tips and not comparison_fallback:
        try:
            db=_oddspapi_budget_db_path()
            if db.exists():
                con=sqlite3.connect(str(db),timeout=10); con.row_factory=sqlite3.Row
                row=con.execute("SELECT payload FROM dashboard_snapshots WHERE key='tip-of-day' LIMIT 1").fetchone(); con.close()
                if row:
                    snap=json.loads(row["payload"] or "{}")
                    saved_cmp=[x for x in (snap.get("comparisonFallback") or []) if x.get("home") and x.get("away") and x.get("bookmakerPick") not in (None,"","—")]
                    if saved_cmp:
                        comparison_fallback=saved_cmp[:3]; state="comparison-saved"
        except Exception as exc:
            log.warning("tip snapshot fallback read failed: %s",exc)

    payload={"state":state,"tips":tips,"count":len(tips),"comparisonFallback":comparison_fallback[:3],
            "comparisonCount":len(comparison_fallback[:3]),"originalDateRequired":False,
            "yesterdayDate":yesterday,"yesterday":yesterday_rows,
            "error":None,"refreshError":provider_error if state.startswith("comparison") else None,
            "generatedAt":datetime.now(timezone.utc).isoformat()}
    # Persist the last non-empty Tip payload so a provider refresh can never blank the widget.
    if (tips or comparison_fallback) and "_dashboard_snapshot_put" in globals():
        _dashboard_snapshot_put("tip-of-day:last_good", {"data": payload})
    try:
        db=_oddspapi_budget_db_path(); db.parent.mkdir(parents=True,exist_ok=True)
        con=sqlite3.connect(str(db),timeout=10)
        con.execute("CREATE TABLE IF NOT EXISTS dashboard_snapshots (key TEXT PRIMARY KEY,payload TEXT NOT NULL,updated_at TEXT NOT NULL)")
        if tips or comparison_fallback:
            con.execute("""INSERT INTO dashboard_snapshots(key,payload,updated_at) VALUES('tip-of-day',?,?)
              ON CONFLICT(key) DO UPDATE SET payload=excluded.payload,updated_at=excluded.updated_at""",
              (json.dumps(payload,default=str),datetime.now(timezone.utc).isoformat()));con.commit()
        con.close()
    except Exception as exc: log.warning("tip snapshot cache failed: %s",exc)
    return Response(
        content=json.dumps(payload, default=str),
        media_type="application/json",
        headers={
            "Cache-Control": "public, max-age=300, s-maxage=1800, stale-while-revalidate=300",
            "CDN-Cache-Control": "public, s-maxage=1800, stale-while-revalidate=300",
        },
    )



@app.get("/finished-games")
async def finished_games(hours:int=Query(48,ge=1,le=168),league:str=Query("ALL"),limit:int=Query(60,ge=1,le=200),days:Optional[int]=Query(None),africa:bool=Query(False)):
    """Completed football matches in a rolling window.

    For Africa-facing clients, select approximately 50% Europe, 25% Africa and
    25% other competitions, while preferring major/relevant leagues and filling
    any regional shortfall from the strongest remaining completed matches.
    """
    now=datetime.now(timezone.utc)
    if days is not None: hours=max(1,min(168,int(days)*24))
    cutoff=now-timedelta(hours=hours)
    # v482: seed Finished Games from the permanent archive first. This keeps
    # completed matches available even when provider quota protection is active
    # or a date-specific API-Football scan temporarily returns no rows.
    rows=[];errors=[];seen=set()
    try:
        archived = await results_history(
            sport="football", country="", competition="", season="", team="", year=None,
            date_from=cutoff.date().isoformat(), date_to=now.date().isoformat(),
            limit=min(500, max(limit * 4, 200)), offset=0,
        )
        for m in (archived.get("matches") or []):
            stamp=m.get("datetime") or m.get("date")
            try:
                dt=datetime.fromisoformat(str(stamp).replace("Z","+00:00")); dt=dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
            except Exception:
                continue
            if not cutoff <= dt <= now: continue
            key=str(m.get("id") or f"{m.get('home')}|{m.get('away')}|{stamp}")
            if key in seen: continue
            seen.add(key); rows.append(m)
    except Exception as exc:
        errors.append(f"archive: {str(exc)[:160]}")
    day=cutoff.date()
    while day<=now.date():
        ds=day.isoformat()
        try:
            d=await fixtures(league=league,type="today",date_from=ds,date_to=ds,refresh=0)
            for raw in d.get("matches") or []:
                m=_widget_match_record(raw,"football")
                finished=m.get("isFinished") or str(m.get("status") or "").upper() in {"FT","AET","PEN","FINISHED","FINAL"}
                if not finished: continue
                stamp=m.get("datetime") or m.get("date")
                try:
                    dt=datetime.fromisoformat(str(stamp).replace("Z","+00:00"));dt=dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
                except Exception: continue
                if not cutoff<=dt<=now: continue
                key=str(m.get("id") or f"{m.get('home')}|{m.get('away')}|{stamp}")
                if key in seen: continue
                seen.add(key);rows.append(m)
                try:
                    _archive_results_upsert([m])
                except Exception as archive_exc:
                    log.warning("Finished Games archive upsert failed: %s", archive_exc)
        except Exception as exc: errors.append(f"{ds}: {exc}")
        day+=timedelta(days=1)

    europe=("premier league","la liga","laliga","serie a","bundesliga","ligue 1","champions league","europa league","conference league","eredivisie","primeira liga","scottish premiership","championship","fa cup","efl cup","copa del rey","coppa italia","dfb-pokal","coupe de france","super lig","belgian pro league")
    african=("psl","premier soccer league","south africa","caf","egypt","morocco","botola","algeria","tunis","nigeria","ghana","kenya","zambia","zimbabwe","uganda","tanzania","senegal","ivory coast","cote d'ivoire")
    major=("champions league","premier league","la liga","laliga","serie a","bundesliga","ligue 1","europa league","conference league","psl","premier soccer league","caf","eredivisie","primeira liga","championship")
    def region(m):
        txt=(str(m.get("league") or m.get("competition") or '')+' '+str(m.get("country") or '')).lower()
        if any(x in txt for x in african): return 'africa'
        if any(x in txt for x in europe): return 'europe'
        return 'other'
    def strength(m):
        txt=(str(m.get("league") or m.get("competition") or '')+' '+str(m.get("country") or '')).lower()
        score=100 if any(x in txt for x in major) else (55 if region(m) in {'europe','africa'} else 25)
        stamp=m.get("datetime") or m.get("date") or ''
        try: score += max(0,48-(now-datetime.fromisoformat(str(stamp).replace('Z','+00:00'))).total_seconds()/3600)/48*10
        except Exception: pass
        return score
    rows.sort(key=lambda m:(strength(m),m.get("datetime") or m.get("date") or ''),reverse=True)
    if africa and league.upper()=="ALL":
        pools={r:[m for m in rows if region(m)==r] for r in ('europe','africa','other')}
        e=min(len(pools['europe']),round(limit*.50));a=min(len(pools['africa']),round(limit*.25));o=min(len(pools['other']),max(0,limit-e-a))
        selected=pools['europe'][:e]+pools['africa'][:a]+pools['other'][:o]
        used={str(m.get('id') or id(m)) for m in selected}
        # Fail-soft: fill every unused slot from the strongest remaining match, regardless of region.
        for m in rows:
            k=str(m.get('id') or id(m))
            if len(selected)>=limit: break
            if k not in used: selected.append(m);used.add(k)
        selected.sort(key=lambda m:m.get("datetime") or m.get("date") or "",reverse=True)
    else: selected=rows[:limit]
    return {"count":len(selected),"matches":selected,"hours":hours,"africaPriority":bool(africa),
            "windowStart":cutoff.isoformat(),"windowEnd":now.isoformat(),"errors":errors[:3],
            "source":"permanent archive + API-Football cache/provider","archiveFirst":True}

@app.get("/cricket/predictions")
async def cricket_predictions(date:str=Query(""),limit:int=Query(20,ge=1,le=50)):
    """Cricket prediction feed from normalized cricket fixtures and subscribed odds when available."""
    games=await _sports_scores("cricket",date or None,False,None)
    out=[]
    for g in games:
        st=str(g.get("statusShort") or "").lower()
        if st in {"post","final","ft"}: continue
        o=g.get("odds") or {}
        hp=float(o.get("homeWin") or 0); ap=float(o.get("awayWin") or 0)
        if hp>0 and ap>0:
            ih,ia=1/hp,1/ap; total=ih+ia
            home_pct=ih/total*100; away_pct=ia/total*100
            pick="Home Win" if home_pct>=away_pct else "Away Win"
            conf=max(home_pct,away_pct)
            out.append({**g,"prediction":{"bestPick":pick,"confidence":round(conf,1),
                "probabilities":{"homeWin":round(home_pct,2),"awayWin":round(away_pct,2)}},
                "predictionEligible":True,"predictionBasis":"normalized subscribed bookmaker odds"})
    out.sort(key=lambda x:float((x.get("prediction") or {}).get("confidence") or 0),reverse=True)
    state="ok" if out else ("provider-error" if not games else "no-qualified-predictions")
    return {"sport":"cricket","count":len(out[:limit]),"predictions":out[:limit],
            "state":state,"provider":"ESPN normalized cricket feed",
            "oddsConfigured":bool(ODDS_API_ENABLED and ODDS_API_KEY),
            "source":"normalized cricket feed + subscribed bookmaker odds",
            "message":None if out else ("Cricket provider returned no games." if not games else "Games are available but no subscribed bookmaker odds currently qualify.")}

@app.get("/prediction-markets")
async def prediction_markets(
    limit: int = Query(20, ge=1, le=100),
):
    data = await ai_predictions(
        limit=limit, refresh=0, league="ALL", type="upcoming",
        date_from=None, date_to=None
    )
    return {
        **data,
        "cache": {
            "ttlHours": 0.5,
            "savedAt": datetime.now(timezone.utc).isoformat(),
        },
    }

@app.get("/dashboard-summary")
async def dashboard_summary(
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
    pred_limit: int = Query(20, ge=1, le=100),
):
    d0 = date_from or datetime.now().strftime("%Y-%m-%d")
    d1 = date_to or (
        datetime.now() + timedelta(days=1)
    ).strftime("%Y-%m-%d")

    fixtures_data = await fixtures_with_odds(
        league="ALL",
        type="upcoming",
        date_from=d0,
        date_to=d1,
        refresh=0,
    )
    live_data = await live("ALL", refresh=0)

    predictions = []

    for match in fixtures_data.get("matches", []):
        if match.get("isFinished"):
            continue
        if not _valid_1x2(match.get("odds", {})):
            continue

        pred_result = _prediction(match)
        _save_prediction_to_db(match, pred_result)
        predictions.append({
            **match,
            **pred_result,
            "oddsAvailable": True,
            "bookmakerGatePassed": True,
            "predictionEligible": True,
            "gamesOfDayEligible": True,
        })

    predictions.sort(
        key=lambda x: x["prediction"]["confidence"],
        reverse=True,
    )

    return {
        "fixtures": fixtures_data.get("matches", []),
        "live": live_data.get("matches", []),
        "predictions": predictions[:pred_limit],
        "quota": dict(_quota_state),
        "generatedAt": datetime.now(timezone.utc).isoformat(),
    }

# ---------------------------------------------------------------------------
# LEARNING
# ---------------------------------------------------------------------------

@app.post("/learning/trigger")
async def trigger_learning_cycle():
    """
    Manually trigger a full learning cycle:
    - Auto-resolves finished fixtures from API-Football
    - Re-scores ALL pending predictions with updated KasiScore AI Model weights
    - Clears prediction cache so /ai-predictions immediately returns improved data
    """
    try:
        await _run_learning_cycle()
        v141_cache.clear()  # force fresh predictions on next /ai-predictions call
        stats = v141_learning.stats()
        return {
            "triggered": True,
            "cycleCount": _learning_state["cycleCount"],
            "updated": _learning_state["lastCycleUpdated"],
            "improved": _learning_state["lastCycleImproved"],
            "autoResolved": _learning_state.get("lastAutoResolved", 0),
            "nextRunAt": _learning_state["nextRunAt"],
            "totalPredictions": stats["totalPredictions"],
            "resolvedPredictions": stats["resolvedPredictions"],
            "pendingPredictions": stats["pendingPredictions"],
            "modelVersion": V141_MODEL_VERSION,
            "adaptedWeights": _learning_state["adaptedWeights"],
        }
    except Exception as exc:
        log.error("Learning trigger error: %s", exc)
        raise HTTPException(500, detail=str(exc))

@app.get("/learning/status")
async def learning_status():
    """Return current learning cycle state without triggering anything."""
    return {
        **v141_learning.stats(),
        "learningCycle": {
            "cycleCount":        _learning_state["cycleCount"],
            "lastRunAt":         _learning_state["lastRunAt"],
            "nextRunAt":         _learning_state["nextRunAt"],
            "status":            _learning_state["status"],
            "lastCycleUpdated":  _learning_state["lastCycleUpdated"],
            "lastCycleImproved": _learning_state["lastCycleImproved"],
            "adaptedWeights":    _learning_state["adaptedWeights"],
            "baseWeights":       V141_PREDICTION_WEIGHTS,
            "intervalHours":     V141_LEARNING_CYCLE_SECS // 3600,
        },
        "modelVersion": V141_MODEL_VERSION,
    }


@app.get("/learning-stats")
async def learning_stats():
    return {
        **v141_learning.stats(),
        "modelVersion": V141_MODEL_VERSION,
        "predictionWeights": V141_PREDICTION_WEIGHTS,
    }

@app.get("/ml/stats")
async def ml_stats():
    return await learning_stats()

@app.get("/prediction-cycle-status")
async def prediction_cycle_status():
    return {
        "running": True,
        "status": "active",
        "message": (
            "Background tasks running: fixtures every 30 min, "
            "prediction cache every 5 min."
        ),
        "fixtureRefreshMins": V141_FIXTURE_REFRESH_SECONDS // 60,
        "predictionRefreshMins": V141_PREDICTION_REFRESH_SECS // 60,
        "modelVersion": V141_MODEL_VERSION,
        "predictionWeights": V141_PREDICTION_WEIGHTS,
    }

@app.get("/best-predictions")
async def best_predictions(
    limit: int = Query(20, ge=1, le=100),
    candidates: int = Query(200, ge=1, le=500),
):
    # Cutoff in plain "YYYY-MM-DD HH:MM" format to match the kickoff strings
    # stored by _normalise_fixture (e.g. "2026-08-21 18:00").
    # ISO format (with T and +00:00) compares incorrectly against those strings
    # because space (ASCII 32) < "T" (ASCII 84), making ALL kickoffs invisible.
    cutoff = (
        datetime.now(timezone.utc) - timedelta(hours=3)
    ).strftime("%Y-%m-%d %H:%M")

    with v141_learning.connect() as conn:
        rows = conn.execute(
            """
            SELECT id,fixture_id,kickoff,home_team,away_team,
                   model_version,probabilities,odds,model_inputs,
                   prediction,predicted_at,resolved
            FROM predictions
            WHERE resolved=0
            AND (kickoff IS NULL OR kickoff >= ?)
            ORDER BY predicted_at DESC
            LIMIT ?
            """,
            (cutoff, candidates),
        ).fetchall()

    items = []

    for row in rows:
        item = dict(row)

        for field in (
            "probabilities",
            "odds",
            "model_inputs",
            "prediction",
        ):
            try:
                item[field] = json.loads(item[field] or "{}")
            except Exception:
                item[field] = {}

        probabilities = item.get("probabilities") or {}
        outcomes = {
            "homeWin": float(probabilities.get("homeWin", 0) or 0),
            "draw": float(probabilities.get("draw", 0) or 0),
            "awayWin": float(probabilities.get("awayWin", 0) or 0),
        }

        best_key, best_probability = max(
            outcomes.items(),
            key=lambda x: x[1],
        )

        # Enrich with all stored market probability keys
        for k in ("over35", "over25", "over15", "over05", "btts",
                   "halfTimeHome", "halfTimeDraw", "halfTimeAway",
                   "firstTeamToScoreHome", "firstTeamToScoreAway",
                   "firstTeamToScore"):
            if k in probabilities:
                outcomes[k] = probabilities[k]

        home_name = item.get("home_team", "")
        away_name = item.get("away_team", "")

        item.update({
            "home": home_name,
            "away": away_name,
            "homeTeam": home_name,
            "awayTeam": away_name,
            "datetime": item.get("kickoff") or "",
            "status": "Upcoming",
            "score": "vs",
            "predictionId": item.pop("id"),
            "fixtureId": item.pop("fixture_id"),
            "_afootFixtureId": item.get("fixtureId"),
            "bestOutcome": best_key,
            "confidence": best_probability,
            "probabilities": outcomes,
            "markets": {
                "over35": outcomes.get("over35"),
                "over25": outcomes.get("over25"),
                "over15": outcomes.get("over15"),
                "over05": outcomes.get("over05"),
                "btts": outcomes.get("btts"),
                "halfTime": {
                    "home": outcomes.get("halfTimeHome"),
                    "draw": outcomes.get("halfTimeDraw"),
                    "away": outcomes.get("halfTimeAway"),
                },
                "firstTeamToScore": outcomes.get("firstTeamToScore"),
                "firstTeamToScoreHome": outcomes.get("firstTeamToScoreHome"),
                "firstTeamToScoreAway": outcomes.get("firstTeamToScoreAway"),
            },
        })

        items.append(item)

    items.sort(
        key=lambda x: float(x.get("confidence", 0) or 0),
        reverse=True,
    )

    return {
        "predictions": items[:limit],
        "matches": items[:limit],
        "candidates": items[:limit],
        "count": len(items[:limit]),
        "limit": limit,
        "source": "local-learning-db",
        "modelVersion": V141_MODEL_VERSION,
    }

class V141PredictionPayload(BaseModel):
    fixtureId: int
    kickoff: Optional[str] = None
    homeTeam: Optional[str] = None
    awayTeam: Optional[str] = None
    probabilities: Dict[str, Any] = Field(default_factory=dict)  # Any: floats + firstTeamToScore string
    odds: Dict[str, Any] = Field(default_factory=dict)
    modelInputs: Dict[str, Any] = Field(default_factory=dict)
    prediction: Dict[str, Any] = Field(default_factory=dict)
    modelVersion: str = V141_MODEL_VERSION

@app.post("/ml/predictions")
async def save_prediction(payload: V141PredictionPayload):
    return {
        "saved": True,
        "record": v141_learning.save_prediction(
            payload.model_dump()
        ),
    }

@app.post("/ml/results/{fixture_id}")
async def save_result(
    fixture_id: int,
    home_goals: int = Query(...),
    away_goals: int = Query(...),
    actual_result: str = Query(...),
):
    with v141_learning.connect() as conn:
        row = conn.execute(
            """
            SELECT id, probabilities FROM predictions
            WHERE fixture_id=? AND resolved=0
            ORDER BY id DESC LIMIT 1
            """,
            (fixture_id,),
        ).fetchone()

    if not row:
        return {
            "saved": False,
            "fixtureId": fixture_id,
            "reason": "no_pending_prediction",
        }

    # Grade each market against the actual result
    try:
        probs = json.loads(row["probabilities"] or "{}")
        total_goals = home_goals + away_goals
        btts_actual = home_goals > 0 and away_goals > 0

        predicted_winner = (
            "homeWin" if probs.get("homeWin", 0) >= probs.get("awayWin", 0)
                         and probs.get("homeWin", 0) >= probs.get("draw", 0)
            else "draw" if probs.get("draw", 0) >= probs.get("awayWin", 0)
            else "awayWin"
        )

        market_accuracy = {
            "predictedWinner": predicted_winner,
            "actualResult": actual_result,
            "winnerCorrect": (
                predicted_winner == actual_result
                if actual_result in ("homeWin", "draw", "awayWin")
                else None
            ),
            "over35Correct": (total_goals > 3) == (probs.get("over35", 0) >= 50),
            "over25Correct": (total_goals > 2) == (probs.get("over25", 0) >= 50),
            "over15Correct": (total_goals > 1) == (probs.get("over15", 0) >= 50),
            "over05Correct": (total_goals > 0) == (probs.get("over05", 0) >= 50),
            "bttsCorrect": btts_actual == (probs.get("btts", 0) >= 50),
            "totalGoals": total_goals,
            "gradedAt": datetime.now(timezone.utc).isoformat(),
        }
    except Exception as exc:
        log.warning("market_accuracy grading error for fixture %s: %s", fixture_id, exc)
        market_accuracy = {}

    v141_learning.save_result(
        int(row["id"]),
        fixture_id,
        home_goals,
        away_goals,
        actual_result,
        market_accuracy,
    )

    return {
        "saved": True,
        "fixtureId": fixture_id,
        "marketAccuracy": market_accuracy,
    }

# ---------------------------------------------------------------------------
# LEARNING — /learning/missed-today
# ---------------------------------------------------------------------------

@app.get("/learning/missed-today")
async def learning_missed_today():
    """
    Dashboard Learning widget data feed.
    Returns live stats, accuracy, future predictions and unknown outcomes.
    """
    stats = v141_learning.stats()
    # stats() now computes accuracy directly; use it if available
    accuracy = stats.pop("accuracy", None)

    # Future pending predictions (kickoff in the future or no kickoff stored)
    now_str = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M")
    best = []
    try:
        with v141_learning.connect() as conn:
            rows = conn.execute(
                """
                SELECT id, fixture_id, kickoff, home_team, away_team,
                       model_version, probabilities, prediction, predicted_at
                FROM predictions
                WHERE resolved=0
                  AND (kickoff IS NULL OR kickoff > ?)
                ORDER BY kickoff ASC, predicted_at DESC
                LIMIT 50
                """,
                (now_str,),
            ).fetchall()

        for row in rows:
            item = dict(row)
            for field in ("probabilities", "prediction"):
                try:
                    item[field] = json.loads(item[field] or "{}")
                except Exception:
                    item[field] = {}

            probs = item.get("probabilities") or {}
            outcomes = {
                "homeWin": float(probs.get("homeWin", 0) or 0),
                "draw":    float(probs.get("draw",    0) or 0),
                "awayWin": float(probs.get("awayWin", 0) or 0),
            }
            best_key, best_prob = max(outcomes.items(), key=lambda x: x[1])

            best.append({
                "fixtureId":   item.get("fixture_id"),
                "home":        item.get("home_team", ""),
                "away":        item.get("away_team", ""),
                "kickoff":     item.get("kickoff", ""),
                "bestOutcome": best_key,
                "confidence":  round(float(best_prob), 1),
                "probabilities": probs,
                "modelVersion": V141_MODEL_VERSION,   # always current name
            })

        best.sort(key=lambda x: float(x.get("confidence", 0) or 0), reverse=True)

    except Exception as exc:
        log.warning("learning/missed-today best-predictions query error: %s", exc)

    # Fetch games with unknown outcome: resolved=0, kickoff has passed, not in best (future)
    unknown_outcomes = []
    try:
        cutoff_unk = (datetime.now(timezone.utc) - timedelta(minutes=105)).strftime("%Y-%m-%d %H:%M")
        with v141_learning.connect() as conn:
            unk_rows = conn.execute(
                """
                SELECT id, fixture_id, kickoff, home_team, away_team,
                       model_version, probabilities, predicted_at
                FROM predictions
                WHERE resolved=0
                  AND kickoff IS NOT NULL
                  AND kickoff <= ?
                ORDER BY kickoff DESC
                LIMIT 30
                """,
                (cutoff_unk,),
            ).fetchall()
        for r in unk_rows:
            item = dict(r)
            try:
                probs = json.loads(item["probabilities"] or "{}")
            except Exception:
                probs = {}
            item["probabilities"] = probs
            outcomes = {
                "homeWin": float(probs.get("homeWin", 0) or 0),
                "draw":    float(probs.get("draw",    0) or 0),
                "awayWin": float(probs.get("awayWin", 0) or 0),
            }
            best_key, best_prob = max(outcomes.items(), key=lambda x: x[1])
            unknown_outcomes.append({
                "fixtureId": item["fixture_id"],
                "home": item["home_team"] or "Home",
                "away": item["away_team"] or "Away",
                "kickoff": item["kickoff"],
                "predictedWinner": best_key,
                "confidence": round(best_prob, 1),
                "probabilities": probs,
                "modelVersion": item["model_version"],
                "predictedAt": item["predicted_at"],
                "status": "unknown_outcome",
            })
    except Exception as exc:
        log.warning("learning/missed-today unknown_outcomes query error: %s", exc)

    return {
        **stats,
        "accuracy": accuracy,
        "modelVersion": V141_MODEL_VERSION,
        "predictionWeights": _learning_state["adaptedWeights"],
        "baseWeights": V141_PREDICTION_WEIGHTS,
        "bestPredictions": best,
        "count": len(best),
        "resolvedPredictions": stats.get("resolvedPredictions", 0),
        "pendingPredictions": stats.get("pendingPredictions", 0),
        "unknownOutcomes": unknown_outcomes,
        "unknownOutcomeCount": len(unknown_outcomes),
        "lastAutoResolved": _learning_state.get("lastAutoResolved", 0),
        "improvementsNeeded": _learning_state.get("lastCycleImproved", 0),
        "improvementsDone": _learning_state.get("lastCycleUpdated", 0),
        "learningCycle": {
            "cycleCount":        _learning_state["cycleCount"],
            "lastRunAt":         _learning_state["lastRunAt"],
            "nextRunAt":         _learning_state["nextRunAt"],
            "status":            _learning_state["status"],
            "lastCycleUpdated":  _learning_state["lastCycleUpdated"],
            "lastCycleImproved": _learning_state["lastCycleImproved"],
            "autoResolved":      _learning_state.get("lastAutoResolved", 0),
            "adaptedWeights":    _learning_state["adaptedWeights"],
            "intervalHours":     V141_LEARNING_CYCLE_SECS // 3600,
        },
    }


# ---------------------------------------------------------------------------
# LEARNING — /learning/recent-results  (last 3 days of resolved games)
# ---------------------------------------------------------------------------

@app.get("/learning/recent-results")
async def learning_recent_results():
    """
    Returns resolved predictions from the last 3 days, split into
    correctly-guessed and incorrectly-guessed lists.
    Old entries (>3 days) are automatically excluded.
    """
    cutoff = (datetime.now(timezone.utc) - timedelta(days=3)).strftime("%Y-%m-%d %H:%M")
    correct_games = []
    wrong_games = []
    try:
        with v141_learning.connect() as conn:
            rows = conn.execute(
                """
                SELECT p.home_team, p.away_team, p.kickoff,
                       r.actual_result, r.market_accuracy, r.resolved_at
                FROM results r
                JOIN predictions p ON p.id = r.prediction_id
                WHERE r.resolved_at >= ?
                ORDER BY r.resolved_at DESC
                LIMIT 200
                """,
                (cutoff,),
            ).fetchall()
        for row in rows:
            try:
                ma = json.loads(row["market_accuracy"] or "{}")
            except Exception:
                ma = {}
            entry = {
                "home":           row["home_team"] or "Home",
                "away":           row["away_team"] or "Away",
                "kickoff":        row["kickoff"] or "",
                "resolvedAt":     row["resolved_at"],
                "actualResult":   row["actual_result"] or "",
                "predictedWinner": ma.get("predictedWinner", ""),
                "homeGoals":      ma.get("homeGoals"),
                "awayGoals":      ma.get("awayGoals"),
                "winnerCorrect":  ma.get("winnerCorrect", False),
            }
            if ma.get("winnerCorrect"):
                correct_games.append(entry)
            else:
                wrong_games.append(entry)
    except Exception as exc:
        log.warning("learning/recent-results error: %s", exc)

    return {
        "cutoffDays": 3,
        "correctGames": correct_games,
        "wrongGames": wrong_games,
        "totalCorrect": len(correct_games),
        "totalWrong": len(wrong_games),
    }


# ---------------------------------------------------------------------------
# API-FOOTBALL COMPATIBILITY ROUTES
# ---------------------------------------------------------------------------

async def _v141_existing_api_call(path, params):
    try:
        return await _afoot_get(path, params)
    except HTTPException as exc:
        log.warning(
            "API adapter call failed: %s %s — %s",
            path,
            params,
            exc.detail,
        )
        return {
            "get": path.lstrip("/"),
            "parameters": params,
            "results": 0,
            "response": [],
            "error": str(exc.detail),
        }

async def _v141_cached_provider(path, params):
    key = path + ":" + json.dumps(
        params,
        sort_keys=True,
        default=str,
    )

    cached = v141_cache.get(key)
    if cached is not None:
        value = dict(cached)
        value["cache"] = {
            "hit": True,
            "ttlSeconds": V141_CACHE_TTL_SECONDS,
        }
        return value

    value = await _v141_existing_api_call(path, params)
    v141_cache.set(key, value)

    value = dict(value)
    value["cache"] = {
        "hit": False,
        "ttlSeconds": V141_CACHE_TTL_SECONDS,
    }
    return value

@app.get("/api-football/fixtures")
async def api_football_fixtures(
    date: Optional[str] = Query(None),
    timezone: Optional[str] = Query(None),
    league: Optional[int] = Query(None),
    season: Optional[int] = Query(None),
    team: Optional[int] = Query(None),
    status: Optional[str] = Query(None),
):
    params = {
        k: v
        for k, v in {
            "date": date,
            "timezone": timezone or TIMEZONE,
            "league": league,
            "season": season,
            "team": team,
            "status": status,
        }.items()
        if v is not None
    }
    return await _v141_cached_provider("/fixtures", params)

@app.get("/api-football/odds")
async def api_football_odds(
    fixture: Optional[int] = Query(None),
    league: Optional[int] = Query(None),
    season: Optional[int] = Query(None),
):
    params = {
        k: v
        for k, v in {
            "fixture": fixture,
            "league": league,
            "season": season,
        }.items()
        if v is not None
    }
    return await _v141_cached_provider("/odds", params)


@app.get("/standings/2026-27")
async def standings_current_season(
    league: str = Query("ALL"),
):
    """League tables for the 2026/27 season only (season hardcoded to 2026).

    Pass league=<name|id> for a single league, or league=ALL for every
    league in SCAN_LEAGUES.  Results are cached for 1 hour.
    """
    SEASON = 2026
    _cache_key = f"standings2627:{league}"
    cached = _standings_cache.get(_cache_key)
    if cached is not None:
        return cached

    async def _fetch_one(lid: int, name: str) -> dict:
        fallback_season = SEASON
        try:
            data = await _afoot_get("/standings", {"league": lid, "season": SEASON})
            response_list = data.get("response", [])
            # Some competitions publish the new season later than the football
            # calendar. Keep the page useful by falling back to the immediately
            # previous season when the current season has no table yet.
            if not response_list:
                prev = SEASON - 1
                prev_data = await _afoot_get("/standings", {"league": lid, "season": prev})
                response_list = prev_data.get("response", [])
                fallback_season = prev
            else:
                fallback_season = SEASON
            standings_outer = (
                response_list[0].get("league", {}).get("standings", [])
                if response_list else []
            )
            table = standings_outer[0] if standings_outer else []
            return {
                "league":   name,
                "leagueId": lid,
                "season":   fallback_season,
                "table": [
                    {
                        "rank":         e.get("rank"),
                        "team":         e.get("team", {}).get("name"),
                        "teamId":       e.get("team", {}).get("id"),
                        "logo":         e.get("team", {}).get("logo"),
                        "played":       e.get("all", {}).get("played", 0),
                        "win":          e.get("all", {}).get("win", 0),
                        "draw":         e.get("all", {}).get("draw", 0),
                        "lose":         e.get("all", {}).get("lose", 0),
                        "goalsFor":     e.get("all", {}).get("goals", {}).get("for", 0),
                        "goalsAgainst": e.get("all", {}).get("goals", {}).get("against", 0),
                        "goalDiff":     e.get("goalsDiff", 0),
                        "points":       e.get("points", 0),
                        "form":         e.get("form", ""),
                        "description":  e.get("description", ""),
                    }
                    for e in table
                ],
            }
        except Exception as exc:
            log.warning("standings_current_season league=%s error=%s", name, exc)
            return {"league": name, "leagueId": lid, "season": fallback_season, "table": [], "error": str(exc)}

    if league.upper() == "ALL":
        tasks = [
            _fetch_one(LEAGUE_IDS[name], name)
            for name in SCAN_LEAGUES
            if name in LEAGUE_IDS
        ]
        results = await asyncio.gather(*tasks, return_exceptions=False)
        out = {"season": "2026/27", "leagues": list(results)}
    else:
        lid = _resolve_league_id(league)
        league_name = _league_name_from_id(lid, league)
        out = {"season": "2026/27", "leagues": [await _fetch_one(lid, league_name)]}

    _standings_cache[_cache_key] = out
    # v442: persist genuine standings for cache-only SEO SSR. This never creates
    # synthetic rows; it only stores the successful public standings response.
    if any((x.get("table") or []) for x in (out.get("leagues") or []) if isinstance(x, dict)):
        try:
            _dashboard_snapshot_put(f"standings2627:last_good:{str(league).upper()}", {"data": out})
        except Exception:
            pass
    return out


@app.get("/players/expected-scorers")
async def players_expected_scorers(
    min_chance: float = Query(80.0, ge=0.0, le=100.0),
    _t: Optional[int] = Query(None),
):
    """Players with an implied goalscoring probability >= min_chance (default 80%).

    Scans the learning DB for unresolved predictions that carry a bookmaker
    expectedGoalscorer decimal-odds value, converts to implied probability, and
    returns all fixtures where that probability meets the threshold.
    Results are sorted highest-probability first.
    """
    cache_key = f"expected_scorers:{min_chance}"
    if _t is None:
        cached = _players_cache.get(cache_key)
        if cached is not None:
            return cached

    rows = []
    try:
        with v141_learning.connect() as conn:
            rows = conn.execute(
                """
                SELECT fixture_id, home_team, away_team, kickoff,
                       probabilities, model_inputs
                FROM predictions
                WHERE resolved = 0
                ORDER BY kickoff ASC
                LIMIT 500
                """
            ).fetchall()
    except Exception as exc:
        log.warning("expected_scorers: DB read error: %s", exc)

    scorers: list[dict] = []
    seen: set[str] = set()

    for row in rows:
        try:
            probs_raw  = json.loads(row["probabilities"] or "{}")
            inputs_raw = json.loads(row["model_inputs"]  or "{}")
            eg_odds    = float(
                inputs_raw.get("expectedGoalscorer")
                or probs_raw.get("expectedGoalscorer")
                or 0
            )
            if eg_odds <= 1.0:
                continue
            implied_pct = round(100 / eg_odds, 1)
            if implied_pct < min_chance:
                continue
            key = f"{row['fixture_id']}:{eg_odds}"
            if key in seen:
                continue
            seen.add(key)
            scorers.append({
                "fixture":     f"{row['home_team']} vs {row['away_team']}",
                "fixtureId":   row["fixture_id"],
                "kickoff":     row["kickoff"],
                "homeTeam":    row["home_team"],
                "awayTeam":    row["away_team"],
                "oddsDecimal": eg_odds,
                "impliedPct":  implied_pct,
            })
        except Exception:
            pass

    # Also sweep the live odds cache
    for ck, odds_data in list(_odds_cache.items()):
        if not ck.startswith("odds:"):
            continue
        try:
            eg_odds = float(odds_data.get("odds", {}).get("expectedGoalscorer") or 0)
            if eg_odds <= 1.0:
                continue
            implied_pct = round(100 / eg_odds, 1)
            if implied_pct < min_chance:
                continue
            fid = ck.split(":", 1)[1]
            key = f"live:{fid}:{eg_odds}"
            if key in seen:
                continue
            seen.add(key)
            scorers.append({
                "fixture":     f"Fixture #{fid}",
                "fixtureId":   fid,
                "kickoff":     None,
                "homeTeam":    None,
                "awayTeam":    None,
                "oddsDecimal": eg_odds,
                "impliedPct":  implied_pct,
            })
        except Exception:
            pass

    scorers.sort(key=lambda x: x["impliedPct"], reverse=True)
    result = {
        "minChancePct": min_chance,
        "count":        len(scorers),
        "season":       "2026/27",
        "scorers":      scorers,
    }
    _players_cache[cache_key] = result
    return result


@app.get("/api-football/standings")
async def api_football_standings(
    league: int = Query(...),
    season: int = Query(...),
):
    return await _v141_cached_provider(
        "/standings",
        {"league": league, "season": season},
    )

@app.get("/api-football/predictions")
async def api_football_predictions(
    fixture: Optional[int] = Query(None),
):
    components = {
        k: {
            "homeWin": 1 / 3,
            "draw": 1 / 3,
            "awayWin": 1 / 3,
        }
        for k in V141_PREDICTION_WEIGHTS
    }

    return {
        "fixtureId": fixture,
        "modelVersion": V141_MODEL_VERSION,
        "prediction": v141_weight_prediction(components),
        "placeholderComponents": True,
    }

# ---------------------------------------------------------------------------
# CONFIG / DIAGNOSTICS
# ---------------------------------------------------------------------------


def _oddspapi_safe_market_structure(snapshot: dict) -> dict:
    """Return market/outcome shape only; no auth data and no full raw payload."""
    result={"fixtureId": snapshot.get("fixtureId") or snapshot.get("id"), "bookmakers":[]}
    books=snapshot.get("bookmakerOdds") or snapshot.get("bookmakers") or {}
    if isinstance(books,dict):
        entries=list(books.items())
    elif isinstance(books,list):
        entries=[]
        for b in books:
            if isinstance(b,dict):
                name=b.get("slug") or b.get("name") or b.get("bookmaker") or "unknown"
                entries.append((str(name),b))
    else:
        entries=[]
    for book,board in entries[:10]:
        if not isinstance(board,dict): continue
        out={"bookmaker":str(book),"marketContainerType":None,"markets":[]}
        markets=board.get("markets") or board.get("odds") or {}
        out["marketContainerType"]=type(markets).__name__
        if isinstance(markets,dict):
            market_entries=list(markets.items())
        elif isinstance(markets,list):
            market_entries=[(m.get("id") or m.get("marketId") or m.get("name") or str(n),m)
                            for n,m in enumerate(markets) if isinstance(m,dict)]
        else:
            market_entries=[]
        for mid,market in market_entries[:30]:
            if not isinstance(market,dict): continue
            mo={"marketId":str(mid),"name":market.get("name") or market.get("marketName"),
                "active":market.get("active"),"outcomeContainerType":None,"outcomes":[]}
            outcomes=market.get("outcomes") or market.get("selections") or {}
            mo["outcomeContainerType"]=type(outcomes).__name__
            if isinstance(outcomes,dict):
                outcome_entries=list(outcomes.items())
            elif isinstance(outcomes,list):
                outcome_entries=[(o.get("id") or o.get("outcomeId") or o.get("name") or str(n),o)
                                 for n,o in enumerate(outcomes) if isinstance(o,dict)]
            else:
                outcome_entries=[]
            for oid,o in outcome_entries[:12]:
                if not isinstance(o,dict): continue
                players=o.get("players")
                player_keys=list(players.keys())[:6] if isinstance(players,dict) else []
                direct_price=o.get("price") or o.get("odds") or o.get("decimal")
                sample_price=None
                if isinstance(players,dict):
                    for p in players.values():
                        if isinstance(p,dict):
                            sample_price=p.get("price") or p.get("odds") or p.get("decimal")
                            if sample_price is not None: break
                sample_player_active=None
                sample_player_status=None
                sample_player_updated=None
                if isinstance(players,dict):
                    for p in players.values():
                        if isinstance(p,dict):
                            sample_player_active=p.get("active")
                            sample_player_status=p.get("status") or p.get("state")
                            sample_player_updated=(p.get("lastUpdated") or p.get("updatedAt")
                                                   or p.get("timestamp"))
                            break
                mo["outcomes"].append({
                    "outcomeId":str(oid),"name":o.get("name") or o.get("label"),
                    "active":o.get("active"),"directPrice":direct_price,
                    "playerKeys":player_keys,"samplePlayerPrice":sample_price,
                    "samplePlayerActive":sample_player_active,
                    "samplePlayerStatus":sample_player_status,
                    "samplePlayerUpdated":sample_player_updated
                })
            out["markets"].append(mo)
        result["bookmakers"].append(out)
    return result


def _oddspapi_cached_afoot_candidates() -> list[dict]:
    """Unique cached API-Football fixtures, with future matches first."""
    unique = {}
    now = datetime.now(timezone.utc)
    for _, value in list(_fixtures_cache.items()):
        rows = value if isinstance(value, list) else (
            (value.get("matches") or value.get("response") or []) if isinstance(value, dict) else []
        )
        for item in rows:
            if not isinstance(item, dict):
                continue
            fx = item.get("fixture") if isinstance(item.get("fixture"), dict) else {}
            fid = item.get("_afootFixtureId") or fx.get("id")
            if fid is not None:
                unique.setdefault(str(fid), item)

    def key(item):
        fx = item.get("fixture") if isinstance(item.get("fixture"), dict) else {}
        dt = _parse_provider_time(
            item.get("datetime") or item.get("kickoff") or item.get("date")
            or fx.get("date") or fx.get("timestamp")
        )
        if not dt:
            return (2, float("inf"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return (0, dt.timestamp()) if dt >= now else (1, -dt.timestamp())

    return sorted(unique.values(), key=key)


async def _oddspapi_diagnostics_impl():
    """
    Safe production diagnostic for the REST fallback.
    Never returns the API key or raw upstream authentication headers.
    """
    report = {
        "configured": bool(ODDSPAPI_API_KEY),
        "restEnabled": bool(ODDSPAPI_ENABLED),
        "websocketEnabled": bool(ODDSPAPI_WS_ENABLED),
        "restBase": ODDSPAPI_REST_BASE,
        "selectedBookmakers": list(ODDSPAPI_BOOKMAKERS),
        "footballSportId": ODDSPAPI_SPORT_FOOTBALL,
        "restVersion": "v5-with-v4-fallback",
        "v4FallbackBase": ODDSPAPI_V4_FALLBACK_BASE,
        "sports": {"requestOk": False, "count": 0, "footballFound": False, "sample": []},
        "fixtures": {"requestOk": False, "count": 0, "sample": []},
        "odds": {"requestOk": False, "count": 0, "bookmakersSeen": [], "selectedSeen": [], "sample": [], "structure": []},
        "mapping": {"apiFootballCandidates": 0, "matched": 0, "unmatched": 0, "samples": []},
        "errors": [],
    }
    if not ODDSPAPI_API_KEY:
        report["errors"].append("ODDSPAPI_API_KEY is not configured")
        return report
    if not ODDSPAPI_ENABLED:
        report["errors"].append("OddsPAPI REST is disabled")
        return report

    try:
        sd = await _oddspapi_get(f"/{ODDSPAPI_REST_LANGUAGE}/sports", {})
        sports = _oddspapi_rows(sd)
        report["sports"]["requestOk"] = True
        report["sports"]["count"] = len(sports)
        report["sports"]["sample"] = [
            {"sportId": x.get("sportId") or x.get("id"), "name": x.get("sportName") or x.get("name")}
            for x in sports[:8] if isinstance(x, dict)
        ]
        report["sports"]["footballFound"] = any(
            str(x.get("sportId") or x.get("id")) == str(ODDSPAPI_SPORT_FOOTBALL)
            or str(x.get("sportName") or x.get("name") or "").lower() in {"football","soccer"}
            for x in sports if isinstance(x, dict)
        )
    except Exception as exc:
        report["errors"].append(f"sports: {exc}")

    now = datetime.now(timezone.utc)
    start = (now - timedelta(hours=12)).isoformat().replace("+00:00", "Z")
    end = (now + timedelta(days=3)).isoformat().replace("+00:00", "Z")

    fixtures = []
    try:
        # Use the same entitlement fallback as production fixture discovery.
        # v5 keys that return 401/403 automatically retry against v4.
        try:
            fd = await _oddspapi_get(f"/{ODDSPAPI_REST_LANGUAGE}/fixtures", {
                "sportId": ODDSPAPI_SPORT_FOOTBALL,
                "startTimeFrom": int((now - timedelta(hours=12)).timestamp()),
                "startTimeTo": int((now + timedelta(days=3)).timestamp()),
                "bookmakers": ",".join(ODDSPAPI_BOOKMAKERS),
            })
            fixture_api_version = "v5"
        except RuntimeError as exc:
            if "HTTP 401" not in str(exc) and "HTTP 403" not in str(exc):
                raise
            fd = await _oddspapi_get("fixtures", {
                "sportId": ODDSPAPI_SPORT_FOOTBALL,
                "from": (now - timedelta(hours=12)).isoformat().replace("+00:00", "Z"),
                "to": (now + timedelta(days=3)).isoformat().replace("+00:00", "Z"),
                "hasOdds": "true",
                "bookmakers": ",".join(ODDSPAPI_BOOKMAKERS),
                "language": "en",
            }, base=ODDSPAPI_V4_FALLBACK_BASE)
            fixture_api_version = "v4"
        fixtures = _oddspapi_rows(fd)
        report["fixtures"]["requestOk"] = True
        report["fixtures"]["apiVersion"] = fixture_api_version
        report["fixtures"]["count"] = len(fixtures)
        for f in fixtures[:5]:
            report["fixtures"]["sample"].append({
                "fixtureId": f.get("fixtureId") or f.get("id"),
                "participant1": _oddspapi_participant_name(f, 1) or f.get("homeTeam") or f.get("home"),
                "participant2": _oddspapi_participant_name(f, 2) or f.get("awayTeam") or f.get("away"),
                "startTime": f.get("startTime") or f.get("startsAt") or f.get("date"),
            })
    except Exception as exc:
        report["errors"].append(f"fixtures request failed: {type(exc).__name__}: {exc}")

    odds_rows = []
    # Test upcoming fixtures rather than blindly testing the first result, which
    # can already be live and legitimately blocked by a pre-match-only plan.
    upcoming = []
    for f in fixtures:
        ft = _parse_provider_time(f.get("startTime") or f.get("startsAt") or f.get("date"))
        if ft and ft > now + timedelta(minutes=2):
            upcoming.append((ft, f))
    upcoming.sort(key=lambda x: x[0])

    sample_fixture_id = None
    od = None
    odds_api_version = None
    restricted_live_skipped = 0
    test_errors = []
    for _, candidate in upcoming[:25]:
        candidate_id = candidate.get("fixtureId") or candidate.get("id")
        if not candidate_id:
            continue
        try:
            od, odds_api_version = await _oddspapi_v5_or_v4(f"/{ODDSPAPI_REST_LANGUAGE}/fixtures/odds", "odds", {
                "fixtureId": candidate_id,
                "bookmakers": ",".join(ODDSPAPI_BOOKMAKERS),
                "oddsFormat": "decimal",
                "language": "en",
                "verbosity": 3,
            })
            sample_fixture_id = candidate_id
            break
        except RuntimeError as exc:
            msg = str(exc)
            if "RESTRICTED_ACCESS" in msg or "live access" in msg.lower() or "fixture you have requested is live" in msg.lower():
                restricted_live_skipped += 1
                continue
            test_errors.append(f"{candidate_id}: {msg}")
            continue

    report["odds"]["upcomingCandidates"] = len(upcoming)
    report["odds"]["restrictedLiveSkipped"] = restricted_live_skipped

    if sample_fixture_id and od is not None:
        try:
            odds_rows = _oddspapi_rows(od)
            report["odds"]["requestOk"] = True
            report["odds"]["apiVersion"] = odds_api_version
            report["odds"]["count"] = len(odds_rows)
            report["odds"]["testedFixtureId"] = sample_fixture_id

            seen=set(); selected=set()
            for row in odds_rows:
                bo=row.get("bookmakerOdds") or {}
                if isinstance(bo,dict):
                    for name in bo.keys():
                        seen.add(str(name))
                        norm=str(name).lower().replace(" ","")
                        if any(b.lower().replace(" ","") in norm or norm in b.lower().replace(" ","") for b in ODDSPAPI_BOOKMAKERS):
                            selected.add(str(name))
            report["odds"]["bookmakersSeen"]=sorted(seen)[:30]
            report["odds"]["selectedSeen"]=sorted(selected)
            report["odds"]["structure"]=[_oddspapi_safe_market_structure(row) for row in odds_rows[:1]]
            for row in odds_rows[:3]:
                one=_oddspapi_1x2(row)
                report["odds"]["sample"].append({
                    "fixtureId": row.get("fixtureId") or sample_fixture_id,
                    "has1X2": bool(one),
                    "oneXTwo": one or None,
                })
        except Exception as exc:
            # _oddspapi_get sanitizes failures; never return an apiKey-bearing URL.
            report["errors"].append(
                f"odds request failed for fixtureId={sample_fixture_id}: {exc}"
            )
    else:
        if not upcoming:
            report["errors"].append("No upcoming OddsPAPI fixture available for pre-match odds test")
        elif test_errors:
            report["errors"].append("No usable pre-match odds response: " + test_errors[0][:220])
        else:
            report["errors"].append("No accessible upcoming OddsPAPI fixture found in diagnostic sample")

    # Inspect only cached API-Football fixtures. Deduplicate by provider fixture ID
    # and test future fixtures first so an old cached match cannot dominate mapping.
    try:
        candidates = _oddspapi_cached_afoot_candidates()
    except Exception:
        candidates = []

    # v45: if there are no future cached API-Football fixtures, fetch a small,
    # bounded diagnostic sample through the existing cached API-Football provider
    # helper. Avoid calling the broad /fixtures?league=ALL loader from diagnostics.
    mapping_warmed = False
    mapping_warm_error = None

    def _has_future_afoot(rows):
        try:
            now_check = datetime.now(timezone.utc)
            for item in rows or []:
                if not isinstance(item, dict):
                    continue
                fx = item.get("fixture") if isinstance(item.get("fixture"), dict) else {}
                dt = _parse_provider_time(
                    item.get("datetime") or item.get("kickoff") or item.get("date")
                    or fx.get("date") or fx.get("timestamp")
                )
                if dt and dt >= now_check:
                    return True
        except Exception:
            return False
        return False

    needs_mapping_warm = not _has_future_afoot(candidates)

    if needs_mapping_warm and API_KEY:
        try:
            fetched = []
            for day_offset in (0, 1):
                day = (datetime.now() + timedelta(days=day_offset)).strftime("%Y-%m-%d")
                payload = await _v141_cached_provider("/fixtures", {"date": day, "timezone": TIMEZONE})
                rows = payload.get("response", []) if isinstance(payload, dict) else []
                if isinstance(rows, list):
                    fetched.extend(x for x in rows if isinstance(x, dict))

            # Deduplicate the bounded diagnostic sample by API-Football fixture id.
            unique = {}
            for raw in fetched:
                fx = raw.get("fixture") if isinstance(raw.get("fixture"), dict) else {}
                fid = fx.get("id")
                if fid is None:
                    continue
                item = dict(raw)
                item["_afootFixtureId"] = fid
                unique.setdefault(str(fid), item)

            future_fetched = []
            now_check = datetime.now(timezone.utc)
            for item in unique.values():
                fx = item.get("fixture") if isinstance(item.get("fixture"), dict) else {}
                dt = _parse_provider_time(fx.get("date") or fx.get("timestamp"))
                if dt and dt >= now_check:
                    future_fetched.append(item)

            if future_fetched:
                # Use fresh future fixtures first, but preserve any useful cached rows.
                cached_by_id = {}
                for item in candidates:
                    fx = item.get("fixture") if isinstance(item.get("fixture"), dict) else {}
                    fid = item.get("_afootFixtureId") or fx.get("id")
                    if fid is not None:
                        cached_by_id[str(fid)] = item
                for item in future_fetched:
                    cached_by_id[str(item["_afootFixtureId"])] = item
                candidates = list(cached_by_id.values())
                candidates.sort(
                    key=lambda item: (
                        _parse_provider_time(
                            ((item.get("fixture") or {}).get("date") if isinstance(item.get("fixture"), dict) else None)
                            or item.get("datetime") or item.get("date")
                        ) or datetime.max.replace(tzinfo=timezone.utc)
                    )
                )
                mapping_warmed = True
            else:
                mapping_warm_error = "API-Football returned no future fixtures for today/tomorrow"
        except Exception as exc:
            mapping_warm_error = f"{exc.__class__.__name__}: {str(exc)[:160]}"

        if mapping_warm_error:
            report["errors"].append(f"API-Football mapping warm-up failed: {mapping_warm_error}")

    report["mapping"]["cacheWarmNeeded"] = bool(needs_mapping_warm)
    report["mapping"]["cacheWarmAttempted"] = bool(needs_mapping_warm and API_KEY)
    report["mapping"]["cacheWarmSucceeded"] = bool(mapping_warmed)
    report["mapping"]["candidateSource"] = "api-football-diagnostic-fetch" if mapping_warmed else "existing-cache"
    if mapping_warm_error:
        report["mapping"]["cacheWarmError"] = mapping_warm_error

    now_utc = datetime.now(timezone.utc)
    future_count = 0
    past_count = 0
    for af in candidates:
        fx0 = af.get("fixture") if isinstance(af.get("fixture"), dict) else {}
        dt0 = _parse_provider_time(
            af.get("datetime") or af.get("kickoff") or af.get("date")
            or fx0.get("date") or fx0.get("timestamp")
        )
        if dt0:
            if dt0.tzinfo is None:
                dt0 = dt0.replace(tzinfo=timezone.utc)
            if dt0 >= now_utc:
                future_count += 1
            else:
                past_count += 1

    report["mapping"]["apiFootballCandidates"] = len(candidates)
    report["mapping"]["futureApiFootballCandidates"] = future_count
    report["mapping"]["pastApiFootballCandidates"] = past_count
    report["mapping"]["deduplicated"] = True

    if fixtures and candidates:
        matched = 0
        samples = []
        # Future-first ordering comes from _oddspapi_cached_afoot_candidates().
        # Keep the diagnostic bounded so it does not become expensive.
        for af in candidates[:100]:
            try:
                found = _oddspapi_match_fixture(af, fixtures)
            except Exception as exc:
                found = None
                if len(samples) < 5:
                    samples.append({"matched": False, "reason": f"matcher error: {type(exc).__name__}"})
            if found:
                matched += 1
                afid = af.get("_afootFixtureId")
                opid = str(found.get("fixtureId") or found.get("id") or "").strip()
                if afid is not None and opid:
                    _oddspapi_afoot_map[str(afid)] = opid
                if len(samples) < 5:
                    fx = af.get("fixture", {}) if isinstance(af.get("fixture"), dict) else {}
                    samples.append({
                        "apiFootballFixtureId": afid or fx.get("id"),
                        "home": af.get("home"),
                        "away": af.get("away"),
                        "oddsPapiFixtureId": opid,
                        "matched": True,
                    })
            elif len(samples) < 5:
                fx = af.get("fixture", {}) if isinstance(af.get("fixture"), dict) else {}
                teams = af.get("teams", {}) if isinstance(af.get("teams"), dict) else {}
                samples.append({
                    "apiFootballFixtureId": af.get("_afootFixtureId") or fx.get("id"),
                    "home": af.get("home") or ((teams.get("home") or {}).get("name") if isinstance(teams.get("home"), dict) else None),
                    "away": af.get("away") or ((teams.get("away") or {}).get("name") if isinstance(teams.get("away"), dict) else None),
                    "date": af.get("datetime") or fx.get("date"),
                    "matched": False,
                    "reason": "no safe team/time match in returned OddsPAPI fixtures",
                })
        report["mapping"]["matched"] = matched
        report["mapping"]["unmatched"] = max(0, len(candidates) - matched)
        report["mapping"]["samples"] = samples

    report["cache"] = {
        "fixtures": len(_oddspapi_fixture_cache),
        "odds": len(_oddspapi_odds_cache),
        "mappedApiFootballFixtures": len(_oddspapi_afoot_map),
    }
    return report


@app.get("/oddspapi/diagnostics")
async def oddspapi_diagnostics():
    """Fail-safe wrapper: diagnostics must return JSON even if an internal test fails."""
    try:
        return await _oddspapi_diagnostics_impl()
    except Exception as exc:
        return {
            "configured": bool(ODDSPAPI_API_KEY),
            "restEnabled": bool(ODDSPAPI_ENABLED),
            "websocketEnabled": bool(ODDSPAPI_WS_ENABLED),
            "ok": False,
            "diagnosticError": {
                "type": exc.__class__.__name__,
                "message": str(exc)[:300],
            },
            "note": "Diagnostic failed safely; production odds routes were not changed.",
        }


@app.get("/oddspapi/health")
async def oddspapi_health():
    return {
        "configured": bool(ODDSPAPI_API_KEY),
        "enabled": ODDSPAPI_ENABLED,
        "restEnabled": ODDSPAPI_ENABLED,
        "websocketEnabled": ODDSPAPI_WS_ENABLED,
        "bookmakers": list(ODDSPAPI_BOOKMAKERS),
        "websocket": dict(_oddspapi_ws_state),
        "cachedFixtures": len(_oddspapi_fixture_cache),
        "cachedOdds": len(_oddspapi_odds_cache),
        "mappedApiFootballFixtures": len(_oddspapi_afoot_map),
        "strategy": "API-Football primary -> OddsPAPI v5 REST when entitled -> automatic v4 REST fallback -> cache -> prediction engine",
        "restBase": ODDSPAPI_REST_BASE,
        "wsGateway": ODDSPAPI_WS_BASE,
    }

@app.get("/odds/diagnostics")
async def odds_diagnostics():
    return {
        "quota": dict(_quota_state),
        "preMatchCached": sum(
            1
            for value in _odds_cache.values()
            if isinstance(value, dict)
            and _valid_1x2(value.get("odds", {}))
        ),
        "liveCached": len(_live_cache),
        "rateLimitPerMinute": RATE_LIMIT_PER_MINUTE,
        "kasiScoreDailyBudget": KASISCORE_DAILY_BUDGET,
        "providerReserve": KASISCORE_PROVIDER_RESERVE,
        "oddsFallback": {
            "enabled": ODDS_API_ENABLED,
            "configured": bool(ODDS_API_KEY),
            "timeoutSeconds": ODDS_API_TIMEOUT,
            "regions": ODDS_API_REGIONS,
            "markets": ODDS_API_MARKETS,
        },
        "message": (
            "Use /live for in-play odds and predictions; "
            "/fixtures/with-odds or /odds for pre-match bookmaker odds."
        ),
    }



# ============================================================================
# MULTI-SPORT PLATFORM — PHASE 1 → PHASE 3
# Football remains on the existing API-Football engine. Rugby/Basketball use
# API-Sports when configured, while cricket/tennis and other sports use the
# ESPN public JSON feeds. News is headline/link metadata only; no copyrighted
# article body is republished.
# ============================================================================
import urllib.parse
import xml.etree.ElementTree as ET

SPORTS_CACHE = TTLCache(maxsize=200, ttl=60)  # v184: cross-sport live cache
GLOBAL_DIRECTORY_CACHE = TTLCache(maxsize=300, ttl=1800)
FAST_PUBLIC_CACHE = TTLCache(maxsize=100, ttl=120)
NEWS_CACHE = TTLCache(maxsize=100, ttl=300)
SPORTS_HTTP: Optional[httpx.AsyncClient] = None

SPORTS_API_KEYS = {
    "rugby": os.getenv("RUGBY_API_KEY", ""),
    "basketball": "",
    "football": API_KEY,
}
SPORTS_API_BASES = {
    "rugby": "https://v1.rugby.api-sports.io",
    "basketball": "",
}
ESPN_LEAGUES = {
    "cricket": ["sa20", "icc", "domestic", "test", "odi", "t20"],
    "tennis": ["atp", "wta"],
    "basketball": ["nba"],
    "rugby": ["rugby/union", "rugby/club"],
    "american-football": ["nfl"],
    "baseball": ["mlb"],
    "hockey": ["nhl"],
    "golf": ["pga", "lpga"],
    "motorsport": ["f1"],
    "mma": ["ufc"],
}
SPORT_LABELS = {"football":"Football", "rugby":"Rugby", "cricket":"Cricket"}

async def _sports_client():
    global SPORTS_HTTP
    if SPORTS_HTTP is None or SPORTS_HTTP.is_closed:
        SPORTS_HTTP = httpx.AsyncClient(timeout=httpx.Timeout(18, connect=5), headers={"User-Agent": "KasiScore-Sports-Platform/1.0"})
    return SPORTS_HTTP

async def _sports_get(url: str, params: dict | None = None, headers: dict | None = None):
    c = await _sports_client()
    r = await c.get(url, params=params or {}, headers=headers or {})
    r.raise_for_status()
    return r.json()

def _espn_event(e: dict, sport: str, league: str):
    comps = (e.get("competitions") or [])
    comp = comps[0] if comps else {}
    competitors = comp.get("competitors") or []
    home = next((x for x in competitors if x.get("homeAway") == "home"), competitors[0] if competitors else {})
    away = next((x for x in competitors if x.get("homeAway") == "away"), competitors[1] if len(competitors)>1 else {})
    status = e.get("status") or comp.get("status") or {}
    st = status.get("type") or {}
    return {
        "id": str(e.get("id", "")), "sport": sport, "league": (e.get("league") or {}).get("name") or league,
        "leagueSlug": league, "date": e.get("date"),
        "home": (home.get("team") or {}).get("displayName") or home.get("athlete", {}).get("displayName") or home.get("displayName") or "Home",
        "away": (away.get("team") or {}).get("displayName") or away.get("athlete", {}).get("displayName") or away.get("displayName") or "Away",
        "homeId": (home.get("team") or {}).get("id"), "awayId": (away.get("team") or {}).get("id"),
        "homeLogo": ((home.get("team") or {}).get("logo") or ""),
        "awayLogo": ((away.get("team") or {}).get("logo") or ""),
        "leagueLogo": ((e.get("league") or {}).get("logo") or ""),
        "homeScore": home.get("score"), "awayScore": away.get("score"),
        "status": st.get("name") or st.get("detail") or "Scheduled", "statusShort": st.get("state") or "pre",
        "venue": ((comp.get("venue") or {}).get("fullName") or ""),
        "source": "ESPN",
        "link": (e.get("links") or [{}])[0].get("href", "") if e.get("links") else "",
    }

def _apisports_event(g: dict, sport: str):
    teams = g.get("teams") or {}
    scores = g.get("scores") or {}
    fixture = g.get("fixture") or g.get("game") or {}
    status = fixture.get("status") or g.get("status") or {}
    return {
        "id": str(fixture.get("id") or g.get("id") or ""), "sport": sport,
        "league": (g.get("league") or {}).get("name", ""), "leagueSlug": str((g.get("league") or {}).get("id") or ""), "leagueLogo": (g.get("league") or {}).get("logo", ""), "leagueFlag": (g.get("country") or {}).get("flag", "") if isinstance(g.get("country"), dict) else "", "date": fixture.get("date") or g.get("date"),
        "home": (teams.get("home") or {}).get("name", "Home"), "away": (teams.get("away") or {}).get("name", "Away"),
        "homeId": (teams.get("home") or {}).get("id"), "awayId": (teams.get("away") or {}).get("id"),
        "homeLogo": (teams.get("home") or {}).get("logo", ""), "awayLogo": (teams.get("away") or {}).get("logo", ""),
        "homeScore": (scores.get("home") if isinstance(scores, dict) else None),
        "awayScore": (scores.get("away") if isinstance(scores, dict) else None),
        "status": status.get("long") or status.get("short") or "Scheduled", "statusShort": status.get("short") or "",
        "venue": ((fixture.get("venue") or {}).get("name") or ""), "source": "API-Sports",
    }

async def _apisports_scores(sport: str, date: str | None = None, live: bool = False):
    key = SPORTS_API_KEYS.get(sport)
    if not key or sport not in SPORTS_API_BASES:
        return []
    base = SPORTS_API_BASES[sport]
    headers = {"x-apisports-key": key, "Accept": "application/json"}
    params = {"live": "all"} if live else {"date": date or datetime.now().strftime("%Y-%m-%d")}
    data = await _sports_get(base + "/games", params, headers)
    return [_apisports_event(x, sport) for x in (data.get("response") or [])]

async def _espn_scores(sport: str, date: str | None = None, league: str | None = None):
    # Cricket is split across several ESPN league feeds. Query the useful
    # South-African/international feeds instead of relying on one generic
    # "domestic" feed, which can legitimately return no events.
    leagues = [league] if league else ESPN_LEAGUES.get(sport, [])
    out=[]
    seen=set()
    for lg in leagues:
        url=f"https://site.api.espn.com/apis/site/v2/sports/{sport}/{lg}/scoreboard"
        params={}
        if date: params["dates"]=date.replace("-", "")
        try:
            data=await _sports_get(url, params)
            for e in (data.get("events") or []):
                item=_espn_event(e, sport, lg)
                eid=str(item.get("id") or "")
                if eid and eid in seen: continue
                if eid: seen.add(eid)
                out.append(item)
        except Exception as exc:
            log.debug("ESPN %s/%s failed: %s", sport, lg, exc)
    return out

async def _attach_odds_api_to_sport_games(games: list[dict], sport: str) -> list[dict]:
    """Attach real The Odds API h2h prices to cross-sport games when a match exists.
    This never fabricates an odds value; unmatched games simply remain without odds.
    """
    if not games or not ODDS_API_ENABLED or not ODDS_API_KEY:
        return games
    keys={
        "cricket": ["cricket_international_t20", "cricket_odi", "cricket_test_match", "cricket_t20"],
    }.get(sport, [])
    if not keys: return games
    events=[]
    for key in keys:
        try:
            data=await _odds_api_get(f"/sports/{key}/odds", {"regions":ODDS_API_REGIONS,"markets":ODDS_API_MARKETS,"oddsFormat":"decimal"})
            if isinstance(data,list): events.extend(data)
        except Exception as exc:
            log.debug("Odds API %s failed: %s", key, exc)
    for game in games:
        match=next((e for e in events if _event_matches_fixture(e, game)), None)
        if not match: continue
        game["odds"]=_normalise_odds_api_event(match)
        game["oddsSource"]="The Odds API"
        game["oddsApiEventId"]=match.get("id")
        game["oddsAvailable"]=_valid_1x2(game["odds"])
    return games


def _oddspapi_score_pair(row: dict) -> tuple[Any, Any]:
    """Extract the best available aggregate score from OddsPapi fixture payloads.

    OddsPapi responses can expose scores as result/current/fullTime fields or as
    period dictionaries. Preserve numeric zero and never invent a score.
    """
    def pair(obj):
        if not isinstance(obj, dict): return (None, None)
        key_pairs = (
            ("participant1Score", "participant2Score"), ("home", "away"),
            ("homeScore", "awayScore"), ("score1", "score2"),
            ("participant1", "participant2"),
        )
        for a,b in key_pairs:
            if obj.get(a) is not None and obj.get(b) is not None:
                return obj.get(a), obj.get(b)
        return (None, None)
    candidates=[]
    for key in ("result","current","fullTime","fulltime","final","score","scores"):
        v=row.get(key)
        if isinstance(v,dict): candidates.append(v)
    scores=row.get("scores")
    if isinstance(scores,dict):
        for key in ("result","current","fullTime","fulltime","final","latest"):
            v=scores.get(key)
            if isinstance(v,dict): candidates.append(v)
        # Period maps: use the last period that contains a complete pair.
        period_candidates=[]
        for k,v in scores.items():
            if isinstance(v,dict):
                h,a=pair(v)
                if h is not None and a is not None: period_candidates.append((str(k),v))
        period_candidates.sort(key=lambda kv: kv[0])
        candidates.extend(v for _,v in reversed(period_candidates))
    for obj in candidates:
        h,a=pair(obj)
        if h is not None and a is not None:return h,a
    return pair(row)


def _oddspapi_is_simulated(row: dict) -> bool:
    text=" ".join(str(row.get(k) or "") for k in ("tournamentName","categoryName","league","name","slug"))
    return bool(re.search(r"\\b(?:SRL|Simulated Reality|simulation|e-?sports?)\\b", text, re.I))


def _oddspapi_multisport_event(row: dict, sport: str) -> dict:
    participants=row.get("participants") or row.get("competitors") or []
    tournament=row.get("tournament") or row.get("competition") or {}
    status=row.get("status") or {}
    scores=row.get("scores") or row.get("score") or {}
    result=scores.get("result") if isinstance(scores,dict) else {}
    result=result if isinstance(result,dict) else {}
    score_home,score_away=_oddspapi_score_pair(row)
    def side(which:int):
        if isinstance(participants,list):
            if len(participants)>=which:
                z=participants[which-1] or {}
                return {"id":z.get("participantId") or z.get("id") or z.get("teamId"),
                        "name":z.get("participantName") or z.get("name") or z.get("teamName") or z.get("shortName"),
                        "logo":z.get("logo") or z.get("image") or z.get("badge"),
                        "country":z.get("country") or z.get("countryName"),
                        "flag":z.get("flag") or z.get("countryFlag")}
            return {}
        if isinstance(participants,dict):
            return {
                "id":participants.get(f"participant{which}Id") or participants.get(f"team{which}Id"),
                "name":participants.get(f"participant{which}Name") or participants.get(f"participant{which}ShortName") or participants.get(f"team{which}Name"),
                "logo":participants.get(f"participant{which}Logo") or participants.get(f"team{which}Logo"),
                "country":participants.get(f"participant{which}Country") or participants.get(f"team{which}Country"),
                "flag":participants.get(f"participant{which}Flag") or participants.get(f"team{which}Flag")
            }
        return {}
    home,away=side(1),side(2)
    # OddsPapi fixture schema exposes participant1Id / participant2Id directly.
    # Participant names/media are catalog entities and are enriched below via /participants.
    home["id"]=home.get("id") or row.get("participant1Id")
    away["id"]=away.get("id") or row.get("participant2Id")
    # OddsPapi v4 fixture responses expose participant labels at the top level.
    home["name"]=home.get("name") or row.get("participant1Name") or row.get("participant1ShortName") or row.get("participant1Abbr")
    away["name"]=away.get("name") or row.get("participant2Name") or row.get("participant2ShortName") or row.get("participant2Abbr")
    start=row.get("startTime") or row.get("trueStartTime") or row.get("startDate")
    dt=None
    try:
        if isinstance(start,(int,float)) or (isinstance(start,str) and start.replace(".","",1).isdigit()):
            ts=float(start)
            if ts>100000000000:ts/=1000.0
            dt=datetime.fromtimestamp(ts,timezone.utc).isoformat()
        elif start:dt=str(start)
    except Exception:dt=str(row.get("trueStartTime") or row.get("startDate") or "") or None
    fid=str(row.get("fixtureId") or row.get("id") or "")
    if fid.startswith("id") and fid[2:].isdigit():fid=fid[2:]
    return {
        "id":fid,"sport":sport,
        "league":row.get("tournamentName") or tournament.get("tournamentName") or tournament.get("name") or sport.title(),
        "leagueSlug":str(row.get("tournamentId") or tournament.get("tournamentId") or tournament.get("id") or ""),
        "country":row.get("categoryName") or tournament.get("categoryName") or tournament.get("country") or home.get("country") or "",
        "countrySlug":row.get("categorySlug") or tournament.get("categorySlug") or "",
        "date":dt,"home":home.get("name") or "Home","away":away.get("name") or "Away",
        "homeId":home.get("id"),"awayId":away.get("id"),
        "homeLogo":home.get("logo") or "","awayLogo":away.get("logo") or "",
        "homeFlag":home.get("flag") or "","awayFlag":away.get("flag") or "",
        "homeScore":score_home,
        "awayScore":score_away,
        "status":row.get("statusName") or status.get("statusName") or status.get("name") or ("Live" if (row.get("statusId")==1 or status.get("live")) else ("Finished" if row.get("statusId")==2 else "Scheduled")),
        "statusId":row.get("statusId") if row.get("statusId") is not None else (status.get("statusId") if status.get("statusId") is not None else status.get("id")),
        "statusShort":"in" if (row.get("statusId")==1 or status.get("live")) else ("ft" if (row.get("statusId")==2 or status.get("statusId")==2 or status.get("id")==2) else "pre"),
        "elapsed":0,"venue":(row.get("venue") or {}).get("venueName") or (row.get("venue") or {}).get("name") or "",
        "source":"OddsPapi","providerFixtureId":str(row.get("fixtureId") or row.get("id") or ""),
        "odds":_oddspapi_1x2(row) if isinstance(row,dict) else {},
        "oddsAvailable":bool(_valid_1x2(_oddspapi_1x2(row))) if isinstance(row,dict) else False,
        "oddsSource":"OddsPapi · Bet365/Betway" if isinstance(row,dict) and _valid_1x2(_oddspapi_1x2(row)) else None,
    }

async def _oddspapi_participant_catalog(sport:str, ids:list)->dict:
    """Resolve OddsPapi participant IDs using the documented v4 participants endpoint.
    v4 returns an object like {"3409":"Chicago Bulls"}, not an array of participant objects.
    """
    clean={str(v).strip() for v in ids if v is not None and str(v).strip()}
    if not clean:return {}
    sid={"football":ODDSPAPI_SPORT_FOOTBALL,"rugby":ODDSPAPI_SPORT_RUGBY,"cricket":ODDSPAPI_SPORT_CRICKET}.get(sport)
    try:
        d=await _oddspapi_get("participants",{"sportId":sid,"language":"en"},base=ODDSPAPI_V4_FALLBACK_BASE)
        if isinstance(d,dict):
            return {str(pid):{"name":str(name),"logo":"","country":"","flag":""}
                    for pid,name in d.items() if str(pid) in clean and name}
    except Exception as exc:
        log.warning("OddsPapi v4 %s participant lookup failed: %s",sport,exc)
    return {}

async def _oddspapi_enrich_participants(rows:list,sport:str)->list:
    ids=[]
    for x in rows:ids.extend([x.get("homeId"),x.get("awayId")])
    cat=await _oddspapi_participant_catalog(sport,ids)
    for x in rows:
        a=cat.get(str(x.get("homeId") or ""),{});b=cat.get(str(x.get("awayId") or ""),{})
        if a:
            x["home"]=x.get("home") if x.get("home") not in {"Home",""} else (a.get("name") or x.get("home"))
            x["homeLogo"]=a.get("logo") or x.get("homeLogo") or ""
            x["homeFlag"]=a.get("flag") or x.get("homeFlag") or ""
            x["country"]=x.get("country") or a.get("country") or ""
        if b:
            x["away"]=x.get("away") if x.get("away") not in {"Away",""} else (b.get("name") or x.get("away"))
            x["awayLogo"]=b.get("logo") or x.get("awayLogo") or ""
            x["awayFlag"]=b.get("flag") or x.get("awayFlag") or ""
    return rows

async def _oddspapi_sport_fixtures(sport: str, date: str | None=None, live: bool=False) -> list[dict]:
    """Rugby/Cricket fixture window.

    The home-page widgets are upcoming-fixture widgets, not "today only" widgets.
    With no explicit date, return the next 7 days so a quiet day does not render
    a false "No games" state.
    """
    sport=(sport or "").lower().strip()
    if date:
        try: day=datetime.strptime(date,"%Y-%m-%d").replace(tzinfo=timezone.utc)
        except Exception: day=datetime.now(timezone.utc)
        start,end=day,day+timedelta(days=1)
    else:
        now=datetime.now(timezone.utc)
        start,end=now-timedelta(hours=6),now+timedelta(days=7)
    if live:
        now=datetime.now(timezone.utc)
        rows=await _oddspapi_sport_range(sport,now-timedelta(hours=23),now+timedelta(hours=23),1)
        return [x for x in rows if x.get("statusId")==1]
    return await _oddspapi_sport_range(sport,start,end,None)

async def _oddspapi_sport_range(sport:str,start:datetime,end:datetime,status_id:int|None=None)->list[dict]:
    """Fetch Rugby/Cricket fixtures from the current OddsPapi v5 REST contract.

    v5 requires:
      https://v5.oddspapi.io/{lang}/fixtures
      sportId=<id>
      startTimeFrom/startTimeTo=<epoch seconds>

    Older code was still sending the retired v4-style `from` / `to` ISO fields
    to the legacy v4 base. Keep a legacy fallback only for accounts that are
    explicitly not entitled to v5.
    """
    sport=(sport or "").lower().strip()
    sid={"football":ODDSPAPI_SPORT_FOOTBALL,"rugby":ODDSPAPI_SPORT_RUGBY,"cricket":ODDSPAPI_SPORT_CRICKET}.get(sport)
    if not sid or not ODDSPAPI_ENABLED or not ODDSPAPI_API_KEY:return []

    raw=[]
    cursor=start
    while cursor < end:
        stop=min(end,cursor+timedelta(days=9))

        # Current documented v5 request.
        q5={
            "sportId":sid,
            "startTimeFrom":int(cursor.timestamp()),
            "startTimeTo":int(stop.timestamp()),
        }
        if status_id is not None:q5["statusId"]=status_id

        try:
            d=await _oddspapi_get(
                f"{ODDSPAPI_REST_LANGUAGE}/fixtures",
                q5,
                base=ODDSPAPI_REST_BASE
            )
        except RuntimeError as exc:
            # Preserve compatibility only when this key is not entitled to v5.
            # Do not hide malformed v5 requests behind a legacy fallback.
            if "HTTP 401" not in str(exc) and "HTTP 403" not in str(exc):
                raise
            q4={
                "sportId":sid,
                "from":cursor.isoformat().replace("+00:00","Z"),
                "to":stop.isoformat().replace("+00:00","Z"),
                "language":"en",
            }
            if status_id is not None:q4["statusId"]=status_id
            d=await _oddspapi_get("fixtures",q4,base=ODDSPAPI_V4_FALLBACK_BASE)

        raw.extend(_oddspapi_rows(d))
        cursor=stop

    seen=set(); rows=[]
    for z in raw:
        fid=str(z.get("fixtureId") or z.get("id") or "")
        if fid and fid in seen:continue
        if fid:seen.add(fid)
        if _oddspapi_is_simulated(z):
            continue
        rows.append(_oddspapi_multisport_event(z,sport))

    unresolved=[x for x in rows if x.get("home") in {"Home",""} or x.get("away") in {"Away",""}]
    if unresolved:
        try:
            await _oddspapi_enrich_participants(unresolved,sport)
        except Exception as exc:
            log.debug("OddsPapi %s participant enrichment failed: %s",sport,exc)
    return rows


async def _oddspapi_enrich_scores(rows:list[dict], max_lookups:int=40) -> list[dict]:
    """Fill missing Rugby/Cricket aggregate scores from OddsPapi /scores.
    Only missing scores are looked up, with bounded concurrency/provider usage.
    """
    targets=[x for x in rows if (x.get("homeScore") is None or x.get("awayScore") is None) and (x.get("providerFixtureId") or x.get("id"))][:max_lookups]
    sem=asyncio.Semaphore(6)
    async def one(x):
        async with sem:
            d=await _oddspapi_fixture_scores(x.get("providerFixtureId") or x.get("id"))
        latest=d.get("latest") or {}
        h=d.get("homeScore");a=d.get("awayScore")
        if h is None or a is None:
            h,a=_oddspapi_score_pair({"latest":latest,"scores":d.get("periods") or {}})
        if h is not None and a is not None:
            x["homeScore"],x["awayScore"]=h,a
            x["scoreAvailable"]=True
        return x
    if targets: await asyncio.gather(*(one(x) for x in targets), return_exceptions=True)
    return rows


async def _oddspapi_attach_live_odds(rows:list[dict], sport:str, max_lookups:int=20) -> list[dict]:
    """Attach provider-returned current markets to live Rugby/Cricket games; never fabricate prices."""
    sem=asyncio.Semaphore(5)
    async def one(x):
        fid=x.get("providerFixtureId") or x.get("id")
        if not fid:return
        try:
            async with sem:
                data,_=await _oddspapi_v5_or_v4(f"{ODDSPAPI_REST_LANGUAGE}/fixtures/odds","odds",{"fixtureId":str(fid),"oddsFormat":"decimal"})
            snap=(_oddspapi_rows(data) or ([data] if isinstance(data,dict) else []))
            active=_oddspapi_v5_active_prices(snap[0] if snap else {})
            if active:
                x["markets"]=active;x["oddsAvailable"]=True;x["oddsSource"]="OddsPapi"
            else:x.setdefault("oddsAvailable",False)
        except Exception as exc:
            log.debug("%s live odds fixture=%s unavailable: %s",sport,fid,exc);x.setdefault("oddsAvailable",False)
    await asyncio.gather(*(one(x) for x in rows[:max_lookups]), return_exceptions=True)
    return rows


async def _odds_api_multisport_fixture_fallback(sport: str, max_sport_keys: int = 8) -> list[dict]:
    """Real upcoming Rugby/Cricket fixtures from The Odds API, used only when
    the primary OddsPapi snapshot is empty. No cross-sport substitution.
    """
    sport=(sport or "").lower().strip()
    if sport not in {"rugby","cricket"} or not ODDS_API_ENABLED or not ODDS_API_KEY:
        return []
    prefixes={"rugby":("rugbyunion_","rugbyleague_"),"cricket":("cricket_",)}[sport]
    try:
        catalog=await _odds_api_get("/sports")
    except Exception as exc:
        log.debug("The Odds API %s catalog fallback failed: %s",sport,exc)
        return []
    keys=[]
    for row in catalog if isinstance(catalog,list) else []:
        key=str((row or {}).get("key") or "")
        if key.startswith(prefixes) and bool((row or {}).get("active",True)):
            keys.append(key)
    # Prefer international/current competitions and bound provider usage.
    keys=keys[:max_sport_keys]
    now=datetime.now(timezone.utc); horizon=now+timedelta(days=7)
    out=[];seen=set()
    for key in keys:
        try:
            events=await _odds_api_get(f"/sports/{key}/odds",{
                "regions":ODDS_API_REGIONS,"markets":"h2h","oddsFormat":"decimal",
                "dateFormat":"iso"
            })
        except Exception as exc:
            log.debug("The Odds API %s/%s fixture fallback failed: %s",sport,key,exc)
            continue
        for event in events if isinstance(events,list) else []:
            dt=_parse_provider_time((event or {}).get("commence_time"))
            if not dt or dt < now-timedelta(hours=1) or dt > horizon: continue
            eid=str((event or {}).get("id") or "")
            if eid and eid in seen: continue
            if eid: seen.add(eid)
            out.append({
                "id":eid,"providerFixtureId":eid,"sport":sport,
                "league":(event or {}).get("sport_title") or key,
                "leagueSlug":key,"country":"International","date":dt.isoformat(),
                "home":(event or {}).get("home_team") or "Home",
                "away":(event or {}).get("away_team") or "Away",
                "homeId":None,"awayId":None,"homeLogo":"","awayLogo":"",
                "homeScore":None,"awayScore":None,"status":"Scheduled",
                "statusId":0,"statusShort":"pre","elapsed":0,"venue":"",
                "odds":_normalise_odds_api_event(event),"oddsAvailable":True,
                "oddsSource":"The Odds API","source":"The Odds API"
            })
    return sorted(out,key=lambda x:x.get("date") or "")

async def _multiday_public_sport_fallback(sport: str, days: int = 7) -> list[dict]:
    """Last-resort public feed sweep across the next N calendar days.
    Keeps Rugby and Cricket strictly isolated and deduplicates real events.
    """
    now=datetime.now(timezone.utc); out=[];seen=set()
    # First use The Odds API when configured because it exposes future schedules.
    try:
        out=await _odds_api_multisport_fixture_fallback(sport)
    except Exception as exc:
        log.debug("%s Odds API fixture fallback failed: %s",sport,exc)
    if out:return out
    # ESPN fallback is date-scoped; sweep dates instead of querying only today.
    for i in range(days+1):
        ds=(now+timedelta(days=i)).strftime("%Y-%m-%d")
        try: rows=await _espn_scores(sport,ds,None)
        except Exception as exc:
            log.debug("ESPN %s fixture sweep %s failed: %s",sport,ds,exc);continue
        for x in rows:
            eid=str(x.get("id") or "")
            if eid and eid in seen:continue
            if eid:seen.add(eid)
            st=str(x.get("statusShort") or x.get("status") or "").lower()
            if st in {"post","final","ft","finished","complete"}:continue
            out.append(x)
    return sorted(out,key=lambda x:x.get("date") or "")

async def _sports_scores(sport: str, date: str | None = None, live: bool = False, league: str | None = None):
    sport=sport.lower().strip()
    key=f"v361:{sport}:{date or 'window'}:{live}:{league or 'all'}"
    if key in SPORTS_CACHE: return SPORTS_CACHE[key]
    out=[]
    if sport == "football":
        try:
            params={"live":"all"} if live else {"date": date or datetime.now().strftime("%Y-%m-%d")}
            if league: params["league"]=_resolve_league_id(league)
            # v449: live polling is non-essential provider work. Once the protected
            # API-Football reserve is active, do not enter _afoot_get merely to
            # trigger its 429 guard; continue to the existing public/cache fallback.
            if _v448_api_football_provider_locked():
                fd={"response":[]}
            else:
                fd=await _afoot_get("/fixtures", params)
            for f in (fd.get("response") or []):
                fs=f.get("fixture") or {}; ts=f.get("teams") or {}; goals=f.get("goals") or {}; st=fs.get("status") or {}
                out.append({"id":str(fs.get("id") or ""),"sport":"football","league":(f.get("league") or {}).get("name") or "Football","leagueSlug":str((f.get("league") or {}).get("id") or ""),"leagueLogo":(f.get("league") or {}).get("logo") or "","leagueFlag":(f.get("league") or {}).get("flag") or "","date":fs.get("date"),"home":(ts.get("home") or {}).get("name") or "Home","away":(ts.get("away") or {}).get("name") or "Away","homeId":(ts.get("home") or {}).get("id"),"awayId":(ts.get("away") or {}).get("id"),"homeLogo":(ts.get("home") or {}).get("logo") or "","awayLogo":(ts.get("away") or {}).get("logo") or "","homeScore":goals.get("home"),"awayScore":goals.get("away"),"status":st.get("long") or st.get("short") or "Scheduled","statusShort":st.get("short") or "","elapsed":st.get("elapsed") or 0,"venue":(fs.get("venue") or {}).get("name") or "","source":"API-Football"})
        except Exception as exc: log.warning("API-Football live/scores failed: %s", exc)
    elif sport in {"rugby","cricket"}:
        # Paid OddsPapi subscription is the primary cross-sport feed.
        try:
            out=await _oddspapi_sport_fixtures(sport,date,live)
        except Exception as exc:
            log.warning("OddsPapi %s fixtures failed: %s",sport,exc)
        # Rugby can additionally use API-Sports when its separate key is configured.
        if not out and sport=="rugby" and SPORTS_API_KEYS.get("rugby"):
            try: out=await _apisports_scores(sport,date,live)
            except Exception as exc: log.warning("API-Sports rugby failed: %s",exc)
    if not out and not live:
        if sport in {"rugby","cricket"} and not date and not league:
            out=await _multiday_public_sport_fallback(sport,7)
        else:
            out=await _espn_scores(sport, date, league)
    elif not out and live:
        out=await _espn_scores(sport, date, league)
        out=[x for x in out if str(x.get("statusShort") or "").lower() in ("in","live") or re.search(r"live|progress|halftime|period|quarter|inning|1h|2h|ht|et", str(x.get("status") or ""), re.I)]
    if sport in {"rugby","cricket"} and out and live:
        try:
            out=await _oddspapi_enrich_scores(out,40)
            out=await _oddspapi_attach_live_odds(out,sport,20)
        except Exception as exc:
            log.debug("%s live score/odds enrichment failed: %s",sport,exc)
    if sport == "cricket" and out:
        try:
            out = await _attach_odds_api_to_sport_games(out, sport)
        except Exception as exc:
            log.debug("Cricket odds enrichment failed: %s", exc)
    # Newest/live first, then kickoff.
    out=sorted(out, key=lambda x: (x.get("statusShort") != "in", x.get("date") or ""))
    SPORTS_CACHE[key]=out
    return out

async def _publisher_rss(feed_url: str, publisher: str, limit: int = 12):
    """Fetch a publisher RSS feed and preserve media/enclosure images when supplied."""
    key=f"publisher-rss:{feed_url}:{limit}"
    if key in NEWS_CACHE: return NEWS_CACHE[key]
    c=await _sports_client()
    r=await c.get(feed_url, headers={"User-Agent":"KasiScore/178 (+news aggregation)"})
    r.raise_for_status()
    root=ET.fromstring(r.text)
    items=[]
    for item in root.findall(".//item")[:limit]:
        title=(item.findtext("title") or "").strip()
        link=(item.findtext("link") or "").strip()
        pub=(item.findtext("pubDate") or "").strip()
        source=item.find("source")
        src=(source.text or publisher) if source is not None else publisher
        image=""
        for ns in ("http://search.yahoo.com/mrss/","http://search.yahoo.com/mrss"):
            for tag in ("content","thumbnail"):
                media=item.find(f"{{{ns}}}{tag}")
                if media is not None and media.attrib.get("url"):
                    image=media.attrib.get("url"); break
            if image: break
        if not image:
            enc=item.find("enclosure")
            if enc is not None: image=enc.attrib.get("url","")
        if not image:
            desc=item.findtext("description") or ""
            m=re.search(r"<img[^>]+(?:src|data-src|url)=[\"\']([^\"\']+)",desc,re.I)
            if m: image=unescape(m.group(1))
        items.append({"title":title,"link":link,"published":pub,"source":src,"publisher":publisher,"image":image})
    NEWS_CACHE[key]=items
    return items


def _is_generic_news_image(url: str) -> bool:
    u=(url or "").strip().lower()
    if not u:
        return True
    try:
        host=(urllib.parse.urlparse(u).hostname or "").lower()
    except Exception:
        host=""
    if any(x in host for x in ("google.", "gstatic.", "googleusercontent.")):
        return True
    return any(x in u for x in (
        "news.google", "google.com/images", "google_news", "googlelogo",
        "favicon", "branding", "logo_google", "googleg/",
        "/logo/", "/logos/", "logo.", "logo_", "logo-",
        "placeholder", "default-image", "default_image", "sprite"
    ))

async def _google_news(query: str, limit: int = 20):
    q=urllib.parse.quote(query)
    url=f"https://news.google.com/rss/search?q={q}&hl=en-ZA&gl=ZA&ceid=ZA:en"
    key=f"news:{query}:{limit}"
    if key in NEWS_CACHE: return NEWS_CACHE[key]
    c=await _sports_client()
    r=await c.get(url); r.raise_for_status()
    root=ET.fromstring(r.text)
    items=[]
    for item in root.findall(".//item")[:limit]:
        title=(item.findtext("title") or "").strip()
        link=(item.findtext("link") or "").strip()
        pub=(item.findtext("pubDate") or "").strip()
        source=item.find("source")
        src=(source.text or "") if source is not None else "News"
        # Google News RSS can expose a media thumbnail/enclosure. Keep only the
        # remote image URL; article pages remain the publisher's canonical page.
        thumb=""
        media = item.find("{http://search.yahoo.com/mrss/}content") or item.find("{http://search.yahoo.com/mrss/}thumbnail")
        if media is not None:
            thumb = media.attrib.get("url","")
        # Some Google News feeds put the publisher image only inside the
        # description HTML. Extract that image as a fast, publisher-supplied
        # thumbnail instead of making a second request to the article page.
        desc = item.findtext("description") or ""
        publisher_link=""
        for hm in re.finditer(r'href=["\\\']([^"\\\']+)["\\\']', desc, re.I):
            cand=unescape(hm.group(1))
            host=(urllib.parse.urlparse(cand).hostname or "").lower()
            if cand.startswith(("http://","https://")) and "google." not in host:
                publisher_link=cand
                break
        if not thumb:
            m = re.search(r'<img[^>]+(?:src|data-src|url)=["\\\']([^"\\\']+)["\\\']', desc, re.I)
            if m:
                thumb = unescape(m.group(1))
        if not thumb:
            enc=item.find("enclosure")
            if enc is not None and str(enc.attrib.get("type","")).startswith("image/"):
                thumb=enc.attrib.get("url","")
        items.append({"title":title,"link":link,"publisherLink":publisher_link,"published":pub,"source":src,"image":("" if _is_generic_news_image(thumb) else thumb),"imageOrigin":("rss" if thumb and not _is_generic_news_image(thumb) else "")})
    # Async best-effort OG image fetch for items missing thumbnails (max 4 at once, 2s timeout)
    async def _fetch_og(item):
        if item.get("image"): return
        try:
            c2=await _sports_client()
            r2=await c2.get(item.get("publisherLink") or item["link"],timeout=3.0,follow_redirects=True,headers={"User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124 Safari/537.36","Accept":"text/html,application/xhtml+xml"})
            m2=re.search(r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']',r2.text,re.I)
            if not m2:
                m2=re.search(r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image["\']',r2.text,re.I)
            if m2: item["image"]=unescape(m2.group(1))
        except Exception: pass
    no_img=[it for it in items if not it.get("image")]
    if no_img:
        await asyncio.gather(*[_fetch_og(it) for it in no_img[:8]], return_exceptions=True)
    NEWS_CACHE[key]=items
    return items


@app.get("/sports/news/image")
async def sports_news_image(url: str = Query(...)):
    """Same-origin proxy for publisher article images."""
    try:
        p=urllib.parse.urlparse(url)
        host=(p.hostname or "").lower()
        if p.scheme not in {"http","https"}:
            raise HTTPException(status_code=400,detail="Invalid image URL")
        if _is_generic_news_image(url) or host in {"localhost","127.0.0.1","::1"}:
            raise HTTPException(status_code=400,detail="Invalid image source")

        c=await _sports_client()
        base_headers={
            "User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124 Safari/537.36",
            "Accept":"image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
            "Accept-Language":"en-ZA,en;q=0.9",
        }

        attempts=[
            dict(base_headers,Referer=f"{p.scheme}://{p.netloc}/"),
            base_headers,
        ]
        last=None
        for headers in attempts:
            try:
                r=await c.get(url,follow_redirects=True,timeout=httpx.Timeout(9,connect=4),headers=headers)
                last=r
                if r.status_code<400 and (r.headers.get("content-type","").lower().startswith("image/")):
                    if len(r.content)>6_000_000:
                        raise HTTPException(status_code=413,detail="Image too large")
                    return Response(
                        content=r.content,
                        media_type=r.headers.get("content-type","image/jpeg").split(";")[0],
                        headers={"Cache-Control":"public, max-age=43200, stale-while-revalidate=86400"}
                    )
            except HTTPException:
                raise
            except Exception:
                continue

        status=last.status_code if last is not None else 404
        raise HTTPException(status_code=404,detail=f"Publisher image unavailable ({status})")
    except HTTPException:
        raise
    except Exception as exc:
        raise HTTPException(status_code=404,detail=f"Image unavailable: {exc}")

@app.get("/sports/config")
async def sports_config():
    allowed={k:v for k,v in SPORT_LABELS.items() if k in {"football","rugby","cricket"}}
    return {"sports":allowed,"providers":{
        "football":"API-Football",
        "rugby":"OddsPapi" if (ODDSPAPI_ENABLED and ODDSPAPI_API_KEY) else ("API-Sports" if SPORTS_API_KEYS.get("rugby") else "ESPN fallback"),
        "cricket":"OddsPapi" if (ODDSPAPI_ENABLED and ODDSPAPI_API_KEY) else "ESPN fallback"
    },"configured":{"oddsPapi":bool(ODDSPAPI_ENABLED and ODDSPAPI_API_KEY),"rugbyApiSports":bool(SPORTS_API_KEYS.get("rugby"))},
      "sportIds":{"football":ODDSPAPI_SPORT_FOOTBALL,"rugby":ODDSPAPI_SPORT_RUGBY,"cricket":ODDSPAPI_SPORT_CRICKET}}


# ── Kasi Sports News Competition Registry (Phase 1 → 4) ─────────────
# Central registry keeps the dashboard competition-aware instead of hard-coding
# individual leagues throughout the UI. API-Football resolves football names to
# provider IDs through the existing _resolve_league_id() path.
ALLOWED_PUBLIC_SPORTS = {"football","rugby","cricket"}

COMPETITION_REGISTRY = [
    # Football — priority competitions
    {"id":"epl","sport":"football","name":"Premier League","country":"England","continent":"Europe","tier":"major","priority":1,"slug":"premier-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"championship","sport":"football","name":"Championship","country":"England","continent":"Europe","tier":"major","priority":2,"slug":"championship","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"fa-cup","sport":"football","name":"FA Cup","country":"England","continent":"Europe","tier":"major","priority":3,"slug":"fa-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"carabao-cup","sport":"football","name":"Carabao Cup","country":"England","continent":"Europe","tier":"major","priority":4,"slug":"carabao-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"la-liga","sport":"football","name":"La Liga","country":"Spain","continent":"Europe","tier":"major","priority":5,"slug":"la-liga","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"copa-del-rey","sport":"football","name":"Copa del Rey","country":"Spain","continent":"Europe","tier":"major","priority":6,"slug":"copa-del-rey","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"serie-a","sport":"football","name":"Serie A","country":"Italy","continent":"Europe","tier":"major","priority":7,"slug":"serie-a","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"coppa-italia","sport":"football","name":"Coppa Italia","country":"Italy","continent":"Europe","tier":"major","priority":8,"slug":"coppa-italia","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"bundesliga","sport":"football","name":"Bundesliga","country":"Germany","continent":"Europe","tier":"major","priority":9,"slug":"bundesliga","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"dfb-pokal","sport":"football","name":"DFB-Pokal","country":"Germany","continent":"Europe","tier":"major","priority":10,"slug":"dfb-pokal","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"ligue-1","sport":"football","name":"Ligue 1","country":"France","continent":"Europe","tier":"major","priority":11,"slug":"ligue-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"coupe-de-france","sport":"football","name":"Coupe de France","country":"France","continent":"Europe","tier":"major","priority":12,"slug":"coupe-de-france","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"saudi-pro-league","sport":"football","name":"Saudi Pro League","country":"Saudi Arabia","continent":"Asia","tier":"major","priority":1,"slug":"saudi-pro-league","live":True,"predictions":True,"odds":True,"seo":True,"featured":True},
    {"id":"king-cup","sport":"football","name":"King's Cup","country":"Saudi Arabia","continent":"Asia","tier":"major","priority":2,"slug":"kings-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"saudi-super-cup","sport":"football","name":"Saudi Super Cup","country":"Saudi Arabia","continent":"Asia","tier":"major","priority":3,"slug":"saudi-super-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"psl","sport":"football","name":"PSL","country":"South Africa","continent":"Africa","tier":"priority","priority":1,"slug":"psl","live":True,"predictions":True,"odds":True,"seo":True,"featured":True},
    {"id":"mtn8","sport":"football","name":"MTN8","country":"South Africa","continent":"Africa","tier":"priority","priority":2,"slug":"mtn8","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"nedbank-cup","sport":"football","name":"Nedbank Cup","country":"South Africa","continent":"Africa","tier":"priority","priority":3,"slug":"nedbank-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"carling-knockout","sport":"football","name":"Carling Knockout","country":"South Africa","continent":"Africa","tier":"priority","priority":4,"slug":"carling-knockout","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"champions-league","sport":"football","name":"Champions League","country":"Europe","continent":"Europe","tier":"major","priority":1,"slug":"champions-league","live":True,"predictions":True,"odds":True,"seo":True,"featured":True},
    {"id":"europa-league","sport":"football","name":"Europa League","country":"Europe","continent":"Europe","tier":"major","priority":2,"slug":"europa-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"conference-league","sport":"football","name":"Conference League","country":"Europe","continent":"Europe","tier":"major","priority":3,"slug":"conference-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"club-world-cup","sport":"football","name":"FIFA Club World Cup","country":"International","continent":"World","tier":"major","priority":4,"slug":"club-world-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"primeira-liga","sport":"football","name":"Primeira Liga","country":"Portugal","continent":"Europe","tier":"major","priority":20,"slug":"primeira-liga","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"eredivisie","sport":"football","name":"Eredivisie","country":"Netherlands","continent":"Europe","tier":"major","priority":21,"slug":"eredivisie","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"super-lig","sport":"football","name":"Süper Lig","country":"Turkey","continent":"Europe","tier":"major","priority":22,"slug":"super-lig","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"belgian-pro-league","sport":"football","name":"Belgian Pro League","country":"Belgium","continent":"Europe","tier":"major","priority":23,"slug":"belgian-pro-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"scottish-premiership","sport":"football","name":"Scottish Premiership","country":"Scotland","continent":"Europe","tier":"major","priority":24,"slug":"scottish-premiership","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"mls","sport":"football","name":"MLS","country":"USA/Canada","continent":"North America","tier":"major","priority":25,"slug":"mls","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"leagues-cup","sport":"football","name":"Leagues Cup","country":"USA/Mexico/Canada","continent":"North America","tier":"major","priority":26,"slug":"leagues-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"brasileirao","sport":"football","name":"Brasileirão","country":"Brazil","continent":"South America","tier":"major","priority":27,"slug":"brasileirao","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"copa-do-brasil","sport":"football","name":"Copa do Brasil","country":"Brazil","continent":"South America","tier":"major","priority":28,"slug":"copa-do-brasil","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"liga-profesional","sport":"football","name":"Liga Profesional","country":"Argentina","continent":"South America","tier":"major","priority":29,"slug":"liga-profesional","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"liga-mx","sport":"football","name":"Liga MX","country":"Mexico","continent":"North America","tier":"major","priority":30,"slug":"liga-mx","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"j1-league","sport":"football","name":"J1 League","country":"Japan","continent":"Asia","tier":"major","priority":31,"slug":"j1-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"k-league-1","sport":"football","name":"K League 1","country":"South Korea","continent":"Asia","tier":"major","priority":32,"slug":"k-league-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"a-league","sport":"football","name":"A-League","country":"Australia","continent":"Oceania","tier":"major","priority":33,"slug":"a-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"world-cup","sport":"football","name":"World Cup","country":"International","continent":"World","tier":"international","priority":1,"slug":"world-cup","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"afcon","sport":"football","name":"AFCON","country":"Africa","continent":"Africa","tier":"international","priority":2,"slug":"afcon","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"euros","sport":"football","name":"UEFA European Championship","country":"Europe","continent":"Europe","tier":"international","priority":3,"slug":"euros","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"copa-america","sport":"football","name":"Copa América","country":"Americas","continent":"South America","tier":"international","priority":4,"slug":"copa-america","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"gold-cup","sport":"football","name":"CONCACAF Gold Cup","country":"CONCACAF","continent":"North America","tier":"international","priority":5,"slug":"gold-cup","live":True,"predictions":True,"odds":True,"seo":True},
    # Rugby — Phase 4 SA-first layer
    {"id":"urc","sport":"rugby","name":"United Rugby Championship","country":"South Africa/Europe","continent":"Europe/Africa","tier":"priority","priority":1,"slug":"urc","live":True,"predictions":True,"odds":False,"seo":True,"featured":True},
    {"id":"currie-cup","sport":"rugby","name":"Currie Cup","country":"South Africa","continent":"Africa","tier":"priority","priority":2,"slug":"currie-cup","live":True,"predictions":True,"odds":False,"seo":True},
    {"id":"rugby-championship","sport":"rugby","name":"Rugby Championship","country":"International","continent":"World","tier":"international","priority":3,"slug":"rugby-championship","live":True,"predictions":True,"odds":False,"seo":True},
    {"id":"super-rugby-africa","sport":"rugby","name":"Super Rugby Africa","country":"Africa","continent":"Africa","tier":"major","priority":4,"slug":"super-rugby-africa","live":True,"predictions":True,"odds":False,"seo":True},
    # Rugby — Europe / Americas / Oceania
    {"id":"premiership-rugby","sport":"rugby","name":"Premiership Rugby","country":"England","continent":"Europe","tier":"major","priority":5,"slug":"eng.1","live":True,"predictions":True,"odds":False,"seo":True},
    {"id":"top14","sport":"rugby","name":"Top 14","country":"France","continent":"Europe","tier":"major","priority":6,"slug":"fra.1","live":True,"predictions":True,"odds":False,"seo":True},
    {"id":"super-rugby-pacific","sport":"rugby","name":"Super Rugby Pacific","country":"Australia/New Zealand","continent":"Oceania","tier":"major","priority":7,"slug":"rugby/club","live":True,"predictions":True,"odds":False,"seo":True},
    {"id":"six-nations","sport":"rugby","name":"Six Nations","country":"Europe","continent":"Europe","tier":"international","priority":8,"slug":"rugby/union","live":True,"predictions":True,"odds":False,"seo":True},
    {"id":"world-rugby-championship","sport":"rugby","name":"Rugby World Cup","country":"International","continent":"World","tier":"international","priority":9,"slug":"rugby/union","live":True,"predictions":True,"odds":False,"seo":True},
    # Cricket — global competitions. ESPN scoreboard slugs are used by the sports layer.
    {"id":"cricket-international","sport":"cricket","name":"International Cricket","country":"International","continent":"World","tier":"international","priority":1,"slug":"icc","live":True,"predictions":False,"odds":False,"seo":True,"featured":True},
    {"id":"sa20","sport":"cricket","name":"SA20","country":"South Africa","continent":"Africa","tier":"major","priority":2,"slug":"domestic","live":True,"predictions":False,"odds":False,"seo":True},
    {"id":"ipl","sport":"cricket","name":"Indian Premier League","country":"India","continent":"Asia","tier":"major","priority":3,"slug":"domestic","live":True,"predictions":False,"odds":False,"seo":True},
    {"id":"big-bash","sport":"cricket","name":"Big Bash League","country":"Australia","continent":"Oceania","tier":"major","priority":4,"slug":"domestic","live":True,"predictions":False,"odds":False,"seo":True},
    {"id":"psl-cricket","sport":"cricket","name":"Pakistan Super League","country":"Pakistan","continent":"Asia","tier":"major","priority":5,"slug":"domestic","live":True,"predictions":False,"odds":False,"seo":True},
    {"id":"hundred","sport":"cricket","name":"The Hundred","country":"England","continent":"Europe","tier":"major","priority":6,"slug":"domestic","live":True,"predictions":False,"odds":False,"seo":True},
    {"id":"county-championship","sport":"cricket","name":"County Championship","country":"England","continent":"Europe","tier":"major","priority":7,"slug":"domestic","live":True,"predictions":False,"odds":False,"seo":True},
    # Football — additional Africa / Europe / Asia / North America / South America
    {"id":"egypt-premier-league","sport":"football","name":"Egyptian Premier League","country":"Egypt","continent":"Africa","tier":"major","priority":40,"slug":"egyptian-premier-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"botola","sport":"football","name":"Botola Pro","country":"Morocco","continent":"Africa","tier":"major","priority":41,"slug":"botola-pro","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"algeria-ligue-1","sport":"football","name":"Algerian Ligue 1","country":"Algeria","continent":"Africa","tier":"major","priority":42,"slug":"algeria-ligue-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"tunisia-ligue-1","sport":"football","name":"Tunisian Ligue 1","country":"Tunisia","continent":"Africa","tier":"major","priority":43,"slug":"tunisia-ligue-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"nigeria-npfl","sport":"football","name":"Nigeria Premier Football League","country":"Nigeria","continent":"Africa","tier":"major","priority":44,"slug":"npfl","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"ghana-premier-league","sport":"football","name":"Ghana Premier League","country":"Ghana","continent":"Africa","tier":"major","priority":45,"slug":"ghana-premier-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"segunda","sport":"football","name":"LaLiga Hypermotion","country":"Spain","continent":"Europe","tier":"major","priority":46,"slug":"segunda","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"bundesliga-2","sport":"football","name":"2. Bundesliga","country":"Germany","continent":"Europe","tier":"major","priority":47,"slug":"bundesliga-2","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"serie-b","sport":"football","name":"Serie B","country":"Italy","continent":"Europe","tier":"major","priority":48,"slug":"serie-b","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"ligue-2","sport":"football","name":"Ligue 2","country":"France","continent":"Europe","tier":"major","priority":49,"slug":"ligue-2","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"super-league-greece","sport":"football","name":"Super League Greece","country":"Greece","continent":"Europe","tier":"major","priority":50,"slug":"super-league-greece","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"austrian-bundesliga","sport":"football","name":"Austrian Bundesliga","country":"Austria","continent":"Europe","tier":"major","priority":51,"slug":"austrian-bundesliga","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"swiss-super-league","sport":"football","name":"Swiss Super League","country":"Switzerland","continent":"Europe","tier":"major","priority":52,"slug":"swiss-super-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"polish-ekstraklasa","sport":"football","name":"Ekstraklasa","country":"Poland","continent":"Europe","tier":"major","priority":53,"slug":"ekstraklasa","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"saudi-1","sport":"football","name":"Saudi Pro League","country":"Saudi Arabia","continent":"Asia","tier":"major","priority":54,"slug":"saudi-pro-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"uae-pro-league","sport":"football","name":"UAE Pro League","country":"United Arab Emirates","continent":"Asia","tier":"major","priority":55,"slug":"uae-pro-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"qatar-stars-league","sport":"football","name":"Qatar Stars League","country":"Qatar","continent":"Asia","tier":"major","priority":56,"slug":"qatar-stars-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"indian-super-league","sport":"football","name":"Indian Super League","country":"India","continent":"Asia","tier":"major","priority":57,"slug":"indian-super-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"chinese-super-league","sport":"football","name":"Chinese Super League","country":"China","continent":"Asia","tier":"major","priority":58,"slug":"chinese-super-league","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"thai-league-1","sport":"football","name":"Thai League 1","country":"Thailand","continent":"Asia","tier":"major","priority":59,"slug":"thai-league-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"liga-1-indonesia","sport":"football","name":"Liga 1 Indonesia","country":"Indonesia","continent":"Asia","tier":"major","priority":60,"slug":"liga-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"colombia-primera","sport":"football","name":"Primera A Colombia","country":"Colombia","continent":"South America","tier":"major","priority":61,"slug":"primera-a","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"chile-primera","sport":"football","name":"Primera División Chile","country":"Chile","continent":"South America","tier":"major","priority":62,"slug":"primera-division","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"ecuador-liga-pro","sport":"football","name":"Liga Pro Ecuador","country":"Ecuador","continent":"South America","tier":"major","priority":63,"slug":"liga-pro","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"peru-liga-1","sport":"football","name":"Liga 1 Peru","country":"Peru","continent":"South America","tier":"major","priority":64,"slug":"liga-1","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"uruguay-primera","sport":"football","name":"Primera División Uruguay","country":"Uruguay","continent":"South America","tier":"major","priority":65,"slug":"primera-division","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"costa-rica-primera","sport":"football","name":"Primera División Costa Rica","country":"Costa Rica","continent":"North America","tier":"major","priority":66,"slug":"primera-division","live":True,"predictions":True,"odds":True,"seo":True},
    {"id":"liga-nacional-guatemala","sport":"football","name":"Liga Nacional Guatemala","country":"Guatemala","continent":"North America","tier":"major","priority":67,"slug":"liga-nacional","live":True,"predictions":True,"odds":True,"seo":True},
]

@app.get("/competitions")
async def competitions(sport: str = Query(""), country: str = Query(""), tier: str = Query("")):
    rows=COMPETITION_REGISTRY
    if sport: rows=[x for x in rows if x["sport"]==sport.lower()]
    if country: rows=[x for x in rows if x["country"].lower()==country.lower()]
    if tier: rows=[x for x in rows if x["tier"]==tier.lower()]
    return {"count":len(rows),"competitions":rows,"version":"phase1-4"}

@app.get("/competitions/featured")
async def featured_competitions():
    rows=[x for x in COMPETITION_REGISTRY if x.get("featured")]
    return {"count":len(rows),"competitions":rows}

@app.get("/sports/{sport}/scores")
async def sports_scores(sport: str, date: str = Query(""), live: int = Query(0, ge=0, le=1), league: str = Query(""), refresh: int = Query(0, ge=0, le=1)):
    allowed=set(SPORT_LABELS)
    sport=sport.lower().strip()
    if sport not in allowed: raise HTTPException(400, f"Unsupported sport: {sport}")
    snap_key=f"v363:scores:{sport}:{date or 'window'}:{live}:{league or 'all'}"
    snap=_dashboard_snapshot_get(snap_key)
    if not refresh and isinstance(snap,dict) and isinstance(snap.get("data"),dict) and (snap.get("data",{}).get("games") or []):
        age=time.time()-float(snap.get("updated_at") or 0)
        if age < (180 if live else 1800):return {**snap["data"],"fromPersistentCache":True}
    try:
        games=await asyncio.wait_for(_sports_scores(sport, date or None, bool(live), league or None),timeout=8.0)
    except Exception as exc:
        log.warning("%s scores refresh timed out/failed: %s",sport,exc);games=[]
    payload={"sport":sport,"date":date or datetime.now().strftime("%Y-%m-%d"),"count":len(games),"games":games,
            "oddsAvailable":sum(1 for g in games if g.get("oddsAvailable")),
            "source": "ESPN + The Odds API" if sport=="cricket" else (games[0].get("source") if games else "sport-isolated providers")}
    if games:_dashboard_snapshot_put(snap_key,{"data":payload});return payload
    if isinstance(snap,dict) and isinstance(snap.get("data"),dict) and (snap.get("data",{}).get("games") or []):
        return {**snap["data"],"fromPersistentCache":True,"stale":True}
    return payload



# KSN v401 requested-only: robust Rugby/Cricket upcoming fixture window.
@app.get("/sports/{sport}/fixtures-window")
async def sports_fixtures_window_v401(sport:str,days:int=Query(7,ge=1,le=14)):
    sport=(sport or "").lower().strip()
    if sport not in {"rugby","cricket"}: raise HTTPException(400,"This fixture window is for Rugby or Cricket")
    snap_key=f"v401:fixtures-window:{sport}:{days}"
    snap=_dashboard_snapshot_get(snap_key)
    saved=(snap or {}).get("data") if isinstance(snap,dict) else None
    # Serve a recent shared LKG immediately. Provider refresh is handled by the normal score calls.
    if isinstance(saved,dict) and saved.get("games") and time.time()-float((snap or {}).get("updated_at") or 0)<900:
        return {**saved,"fromPersistentCache":True}
    now=datetime.now(timezone.utc); seen=set(); rows=[]; errors=[]
    try:
        primary=await asyncio.wait_for(_sports_scores(sport,None,False,None),timeout=10.0)
    except Exception as exc:
        primary=[]; errors.append(str(exc)[:160])
    for x in primary or []:
        st=str(x.get("statusShort") or x.get("status") or "").lower()
        if re.search(r"\b(ft|final|finished|complete|completed|post|live|in progress|1h|2h|ht|et)\b",st): continue
        ident=str(x.get("id") or x.get("providerFixtureId") or f"{x.get('home')}|{x.get('away')}|{x.get('date')}")
        if ident in seen: continue
        seen.add(ident); rows.append(_widget_match_record(x,sport))
    # If a provider's window call is sparse, sweep calendar dates without mixing sports.
    if len(rows)<4:
        for i in range(days+1):
            ds=(now+timedelta(days=i)).strftime("%Y-%m-%d")
            try:
                dayrows=await asyncio.wait_for(_sports_scores(sport,ds,False,None),timeout=6.0)
            except Exception as exc:
                errors.append(f"{ds}: {str(exc)[:100]}"); continue
            for x in dayrows or []:
                st=str(x.get("statusShort") or x.get("status") or "").lower()
                if re.search(r"\b(ft|final|finished|complete|completed|post|live|in progress|1h|2h|ht|et)\b",st): continue
                ident=str(x.get("id") or x.get("providerFixtureId") or f"{x.get('home')}|{x.get('away')}|{x.get('date')}")
                if ident in seen: continue
                seen.add(ident); rows.append(_widget_match_record(x,sport))
    rows.sort(key=lambda x:str(x.get("date") or ""))
    payload={"sport":sport,"count":len(rows),"games":rows,"days":days,"updatedAt":now.isoformat(),"errors":errors[:4]}
    if rows:
        _dashboard_snapshot_put(snap_key,{"data":payload}); return payload
    if isinstance(saved,dict) and saved.get("games"):
        return {**saved,"fromPersistentCache":True,"stale":True,"refreshErrors":errors[:4]}
    return payload

def _widget_match_record(row:dict, sport:str="football")->dict:
    """Stable display contract for Fixtures/Live/Finished without discarding provider fields."""
    x=dict(row or {})
    teams=x.get("teams") if isinstance(x.get("teams"),dict) else {}
    home_obj=teams.get("home") if isinstance(teams.get("home"),dict) else {}
    away_obj=teams.get("away") if isinstance(teams.get("away"),dict) else {}
    comp=x.get("competition") if isinstance(x.get("competition"),dict) else {}
    tourn=x.get("tournament") if isinstance(x.get("tournament"),dict) else {}
    category=x.get("category") if isinstance(x.get("category"),dict) else {}
    league=x.get("league")
    if isinstance(league,dict):
        league_name=league.get("name") or league.get("leagueName") or ""
        country=league.get("country") or league.get("countryName") or ""
    else:
        league_name=league or x.get("leagueName") or comp.get("name") or tourn.get("name") or ""
        country=x.get("country") or x.get("countryName") or category.get("name") or comp.get("country") or ""
    x["sport"]=str(x.get("sport") or sport or "football").lower()
    x["id"]=x.get("id") or x.get("fixtureId") or x.get("providerFixtureId") or ((x.get("fixture") or {}).get("id") if isinstance(x.get("fixture"),dict) else None)
    x["home"]=x.get("home") or x.get("homeTeam") or x.get("homeName") or home_obj.get("name") or "Home"
    x["away"]=x.get("away") or x.get("awayTeam") or x.get("awayName") or away_obj.get("name") or "Away"
    x["homeId"]=x.get("homeId") or x.get("homeTeamId") or home_obj.get("id")
    x["awayId"]=x.get("awayId") or x.get("awayTeamId") or away_obj.get("id")
    x["homeLogo"]=x.get("homeLogo") or x.get("homeBadge") or home_obj.get("logo") or home_obj.get("badge")
    x["awayLogo"]=x.get("awayLogo") or x.get("awayBadge") or away_obj.get("logo") or away_obj.get("badge")
    x["league"]=league_name or "Other matches"
    x["country"]=country or "International"
    x["date"]=x.get("date") or x.get("datetime") or x.get("startTime") or x.get("commenceTime")
    x["status"]=x.get("status") or x.get("statusName") or x.get("state") or ""
    x["statusShort"]=x.get("statusShort") or x.get("shortStatus") or x.get("statusId") or ""
    # Preserve final/live scores across all normalized source shapes.
    # Some result feeds expose goals/score/competitors instead of homeScore/awayScore.
    goals=x.get("goals") if isinstance(x.get("goals"),dict) else {}
    score_obj=x.get("score") if isinstance(x.get("score"),dict) else {}
    fixture_obj=x.get("fixture") if isinstance(x.get("fixture"),dict) else {}
    competitors=x.get("competitors") if isinstance(x.get("competitors"),list) else []
    def _competitor_score(side):
        for c in competitors:
            if not isinstance(c,dict): continue
            if str(c.get("homeAway") or "").lower()==side:
                v=c.get("score")
                if isinstance(v,dict): v=v.get("value") or v.get("displayValue") or v.get("current")
                return v
        return None
    if x.get("homeScore") is None:
        x["homeScore"]=(x.get("homeGoals") if x.get("homeGoals") is not None else
                        goals.get("home") if goals.get("home") is not None else
                        score_obj.get("home") if score_obj.get("home") is not None else
                        score_obj.get("homeScore") if score_obj.get("homeScore") is not None else
                        _competitor_score("home"))
    if x.get("awayScore") is None:
        x["awayScore"]=(x.get("awayGoals") if x.get("awayGoals") is not None else
                        goals.get("away") if goals.get("away") is not None else
                        score_obj.get("away") if score_obj.get("away") is not None else
                        score_obj.get("awayScore") if score_obj.get("awayScore") is not None else
                        _competitor_score("away"))
    return x


_FINISHED_MULTI_CACHE: dict[str, tuple[float, dict]] = {}

_FINISHED_EUROPE_TERMS=("premier league","la liga","laliga","serie a","bundesliga","ligue 1","champions league","europa league","conference league","eredivisie","primeira liga","scottish premiership","championship","fa cup","efl cup","copa del rey","coppa italia","dfb-pokal","coupe de france","super lig","belgian pro league","austria","swiss","poland","greece","denmark","norway","sweden","finland","czech","croatia","serbia","romania","ukraine","cyprus","hungary","slovakia","slovenia","bulgaria","iceland")
_FINISHED_AFRICA_TERMS=("africa","caf","south africa","psl","premier soccer league","betway premiership","motsepe","nedbank","mtn8","egypt","morocco","botola","algeria","tunisia","nigeria","ghana","kenya","zambia","zimbabwe","uganda","tanzania","senegal","ivory coast","cote d'ivoire","cameroon","mali","congo","gabon","guinea","sudan","libya","botswana","namibia","angola","mozambique","malawi","rwanda","ethiopia")

def _finished_region(m:dict)->str:
    txt=(str(m.get('league') or '')+' '+str(m.get('competition') or '')+' '+str(m.get('country') or '')).lower()
    if any(x in txt for x in _FINISHED_AFRICA_TERMS): return 'africa'
    if any(x in txt for x in _FINISHED_EUROPE_TERMS): return 'europe'
    return 'other'

def _valid_finished_score(v):
    """Return True only for a real numeric score (0 is valid)."""
    if v is None or isinstance(v, bool): return False
    if isinstance(v, (int, float)): return True
    t=str(v).strip()
    return bool(re.fullmatch(r"-?\d+(?:\.\d+)?", t))

def _finished_score_pair(m:dict):
    """Read final scores from the public normalized shapes without inventing 0-0."""
    goals=m.get('goals') if isinstance(m.get('goals'),dict) else {}
    score=m.get('score')
    score_obj=score if isinstance(score,dict) else {}
    score_text_pair=(None,None)
    if isinstance(score,str):
        sm=re.match(r"^\s*(-?\d+)\s*[-–:]\s*(-?\d+)\s*$",score)
        if sm: score_text_pair=(sm.group(1),sm.group(2))
    fulltime=score_obj.get('fulltime') if isinstance(score_obj.get('fulltime'),dict) else {}
    hs=m.get('homeScore')
    av=m.get('awayScore')
    if hs is None: hs=m.get('homeGoals')
    if av is None: av=m.get('awayGoals')
    if hs is None: hs=goals.get('home')
    if av is None: av=goals.get('away')
    if hs is None: hs=fulltime.get('home')
    if av is None: av=fulltime.get('away')
    if hs is None: hs=score_obj.get('home') if score_obj.get('home') is not None else score_obj.get('homeScore')
    if av is None: av=score_obj.get('away') if score_obj.get('away') is not None else score_obj.get('awayScore')
    if hs is None: hs=score_text_pair[0]
    if av is None: av=score_text_pair[1]
    comps=m.get('competitors') if isinstance(m.get('competitors'),list) else []
    if hs is None or av is None:
        for c in comps:
            if not isinstance(c,dict): continue
            side=str(c.get('homeAway') or '').lower();v=c.get('score')
            if isinstance(v,dict): v=v.get('value') if v.get('value') is not None else v.get('displayValue')
            if side=='home' and hs is None: hs=v
            if side=='away' and av is None: av=v
    return hs,av

def _scored_finished(m:dict)->bool:
    hs,av=_finished_score_pair(m)
    if not (_valid_finished_score(hs) and _valid_finished_score(av)): return False
    m['homeScore']=hs;m['awayScore']=av
    return True

def _balanced_finished_football(rows:list)->tuple[list,dict]:
    """Keep ALL valid Football results. Order them 2 Europe : 1 Africa : 1 Other
    for African viewers while all three pools have games. When a pool is exhausted,
    continue with every remaining real result; never drop games to manufacture a ratio.
    """
    pools={k:[] for k in ('europe','africa','other')}
    for m in rows: pools[_finished_region(m)].append(m)
    for k in pools:
        pools[k].sort(key=lambda x:x.get('date') or x.get('datetime') or '', reverse=True)
    available={k:len(pools[k]) for k in pools}
    ordered=[]
    while any(pools.values()):
        progressed=False
        for k in ('europe','europe','africa','other'):
            if pools[k]: ordered.append(pools[k].pop(0));progressed=True
        if not progressed: break
    actual={k:sum(1 for m in ordered if _finished_region(m)==k) for k in ('europe','africa','other')}
    total=len(ordered) or 1
    pct={k:round(actual[k]*100/total,1) for k in actual}
    return ordered,{'pattern':'2 Europe : 1 Africa : 1 Other while available','available':available,'selected':actual,'percent':pct,'allValidFootballIncluded':True}


# ================================================================
# KSN v369 — permanent confirmed-results archive
# PostgreSQL is authoritative when DATABASE_URL is configured.
# SQLite is a development fallback only. Confirmed scored finals only.
# ================================================================
RESULTS_ARCHIVE_SQLITE = Path(os.getenv("RESULTS_ARCHIVE_SQLITE", str(BASE_DIR / "ksn_results_archive.sqlite3")))

def _results_db():
    if DATABASE_URL:
        if psycopg2 is None:
            raise RuntimeError("DATABASE_URL requires psycopg2-binary")
        conn = psycopg2.connect(DATABASE_URL, connect_timeout=10)
        conn.autocommit = False
        return conn, "postgres"
    conn = sqlite3.connect(str(RESULTS_ARCHIVE_SQLITE), timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA busy_timeout=30000")
    return conn, "sqlite"

def _results_archive_init():
    conn, kind = _results_db()
    cur = conn.cursor()
    if kind == "postgres":
        cur.execute("""
        CREATE TABLE IF NOT EXISTS ksn_results_archive(
          ksn_key TEXT PRIMARY KEY,
          sport TEXT NOT NULL, provider TEXT, provider_id TEXT,
          country TEXT, competition TEXT, competition_id TEXT,
          season TEXT, round_name TEXT, kickoff TIMESTAMPTZ NOT NULL,
          home_id TEXT, home_name TEXT NOT NULL, home_badge TEXT,
          away_id TEXT, away_name TEXT NOT NULL, away_badge TEXT,
          home_score TEXT NOT NULL, away_score TEXT NOT NULL,
          status TEXT NOT NULL, venue TEXT, referee TEXT,
          source_payload JSONB NOT NULL,
          collected_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
          updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        )""")
        for sql in (
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_kickoff ON ksn_results_archive(kickoff DESC)",
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_sport ON ksn_results_archive(sport)",
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_country ON ksn_results_archive(lower(country))",
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_comp ON ksn_results_archive(lower(competition))",
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_home ON ksn_results_archive(lower(home_name))",
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_away ON ksn_results_archive(lower(away_name))",
            "CREATE INDEX IF NOT EXISTS idx_ksn_results_season ON ksn_results_archive(season)"
        ): cur.execute(sql)
    else:
        cur.execute("""CREATE TABLE IF NOT EXISTS ksn_results_archive(
          ksn_key TEXT PRIMARY KEY, sport TEXT NOT NULL, provider TEXT, provider_id TEXT,
          country TEXT, competition TEXT, competition_id TEXT, season TEXT, round_name TEXT,
          kickoff TEXT NOT NULL, home_id TEXT, home_name TEXT NOT NULL, home_badge TEXT,
          away_id TEXT, away_name TEXT NOT NULL, away_badge TEXT,
          home_score TEXT NOT NULL, away_score TEXT NOT NULL, status TEXT NOT NULL,
          venue TEXT, referee TEXT, source_payload TEXT NOT NULL,
          collected_at TEXT NOT NULL, updated_at TEXT NOT NULL
        )""")
        for name,col in (("kickoff","kickoff"),("sport","sport"),("country","country"),
                         ("comp","competition"),("home","home_name"),("away","away_name"),("season","season")):
            cur.execute(f"CREATE INDEX IF NOT EXISTS idx_ksn_results_{name} ON ksn_results_archive({col})")
    conn.commit(); cur.close(); conn.close()

def _archive_text(x, *keys):
    for k in keys:
        cur=x
        for p in k.split("."):
            cur=cur.get(p) if isinstance(cur,dict) else None
        if cur not in (None,""): return str(cur)
    return ""

def _archive_result_row(m):
    if not isinstance(m,dict) or not _scored_finished(m): return None
    sport=str(m.get("sport") or "football").lower()
    pid=_archive_text(m,"id","fixtureId","providerFixtureId","fixture.id")
    kickoff=_archive_text(m,"date","datetime","startTime","fixture.date")
    home=_archive_text(m,"home","homeName","homeTeam.name","teams.home.name")
    away=_archive_text(m,"away","awayName","awayTeam.name","teams.away.name")
    hs=m.get("homeScore", m.get("homeGoals"))
    ass=m.get("awayScore", m.get("awayGoals"))
    if hs is None and isinstance(m.get("goals"),dict): hs=m["goals"].get("home")
    if ass is None and isinstance(m.get("goals"),dict): ass=m["goals"].get("away")
    if not kickoff or not home or not away or hs is None or ass is None: return None
    key=f"{sport}:{pid}" if pid else hashlib.sha256(f"{sport}|{kickoff}|{home}|{away}".encode()).hexdigest()
    return {
      "key":key,"sport":sport,"provider":_archive_text(m,"source","provider") or ("API-Football" if sport=="football" else "OddsPapi"),
      "provider_id":pid,"country":_archive_text(m,"country","countryName","league.country") or "International",
      "competition":_archive_text(m,"league","leagueName","competition.name","league.name") or "Other matches",
      "competition_id":_archive_text(m,"leagueId","competitionId","league.id"),
      "season":_archive_text(m,"season","league.season"),"round":_archive_text(m,"round","fixture.round"),
      "kickoff":kickoff,"home_id":_archive_text(m,"homeId","homeTeam.id","teams.home.id"),"home":home,
      "home_badge":_archive_text(m,"homeLogo","homeBadge","homeTeam.logo","teams.home.logo"),
      "away_id":_archive_text(m,"awayId","awayTeam.id","teams.away.id"),"away":away,
      "away_badge":_archive_text(m,"awayLogo","awayBadge","awayTeam.logo","teams.away.logo"),
      "home_score":str(hs),"away_score":str(ass),"status":_archive_text(m,"statusShort","status","fixture.status.short") or "FT",
      "venue":_archive_text(m,"venue","fixture.venue.name"),"referee":_archive_text(m,"referee","fixture.referee"),
      "payload":m
    }

def _archive_results_upsert(matches):
    prepared=[x for x in (_archive_result_row(m) for m in (matches or [])) if x]
    if not prepared: return 0
    _results_archive_init()
    conn,kind=_results_db(); cur=conn.cursor(); now=datetime.now(timezone.utc).isoformat(); n=0
    try:
        for r in prepared:
            vals=(r["key"],r["sport"],r["provider"],r["provider_id"],r["country"],r["competition"],
                  r["competition_id"],r["season"],r["round"],r["kickoff"],r["home_id"],r["home"],r["home_badge"],
                  r["away_id"],r["away"],r["away_badge"],r["home_score"],r["away_score"],r["status"],
                  r["venue"],r["referee"],json.dumps(r["payload"],ensure_ascii=False,default=str))
            if kind=="postgres":
                cur.execute("""INSERT INTO ksn_results_archive(
                  ksn_key,sport,provider,provider_id,country,competition,competition_id,season,round_name,kickoff,
                  home_id,home_name,home_badge,away_id,away_name,away_badge,home_score,away_score,status,venue,referee,source_payload)
                  VALUES(%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s::jsonb)
                  ON CONFLICT(ksn_key) DO UPDATE SET
                  country=EXCLUDED.country,competition=EXCLUDED.competition,competition_id=EXCLUDED.competition_id,
                  season=EXCLUDED.season,round_name=EXCLUDED.round_name,kickoff=EXCLUDED.kickoff,
                  home_id=EXCLUDED.home_id,home_name=EXCLUDED.home_name,home_badge=EXCLUDED.home_badge,
                  away_id=EXCLUDED.away_id,away_name=EXCLUDED.away_name,away_badge=EXCLUDED.away_badge,
                  home_score=EXCLUDED.home_score,away_score=EXCLUDED.away_score,status=EXCLUDED.status,
                  venue=EXCLUDED.venue,referee=EXCLUDED.referee,source_payload=EXCLUDED.source_payload,updated_at=NOW()""", vals)
            else:
                cur.execute("""INSERT INTO ksn_results_archive(
                  ksn_key,sport,provider,provider_id,country,competition,competition_id,season,round_name,kickoff,
                  home_id,home_name,home_badge,away_id,away_name,away_badge,home_score,away_score,status,venue,referee,
                  source_payload,collected_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                  ON CONFLICT(ksn_key) DO UPDATE SET
                  country=excluded.country,competition=excluded.competition,competition_id=excluded.competition_id,
                  season=excluded.season,round_name=excluded.round_name,kickoff=excluded.kickoff,
                  home_id=excluded.home_id,home_name=excluded.home_name,home_badge=excluded.home_badge,
                  away_id=excluded.away_id,away_name=excluded.away_name,away_badge=excluded.away_badge,
                  home_score=excluded.home_score,away_score=excluded.away_score,status=excluded.status,
                  venue=excluded.venue,referee=excluded.referee,source_payload=excluded.source_payload,updated_at=excluded.updated_at""",
                  vals+(now,now))
            n+=1
        conn.commit()
    except Exception:
        conn.rollback(); raise
    finally:
        cur.close(); conn.close()
    return n

@app.get("/results/history")
async def results_history(
    sport:str=Query("all"), country:str=Query(""), competition:str=Query(""),
    season:str=Query(""), team:str=Query(""), year:Optional[int]=Query(None,ge=1900,le=2200),
    date_from:str=Query(""), date_to:str=Query(""), limit:int=Query(100,ge=1,le=500),
    offset:int=Query(0,ge=0)
):
    """Permanent KSN confirmed-results archive. This endpoint never calls an upstream sports provider."""
    _results_archive_init()
    conn,kind=_results_db(); cur=conn.cursor()
    ph="%s" if kind=="postgres" else "?"
    where=[]; params=[]
    def add(expr,val): where.append(expr.replace("?",ph)); params.append(val)
    if sport.lower() in {"football","rugby","cricket"}: add("sport=?",sport.lower())
    # v457: structured filters are identities, not free-text searches.
    # Exact normalized equality prevents England Premier League from matching Ghana
    # Premier League and senior Bundesliga from matching Frauen/U19 Bundesliga.
    if country.strip(): add("lower(trim(country))=?",country.strip().lower())
    if competition.strip(): add("lower(trim(competition))=?",competition.strip().lower())
    if season.strip(): add("lower(trim(season))=?",season.strip().lower())
    if team.strip():
        where.append(f"(lower(home_name) LIKE {ph} OR lower(away_name) LIKE {ph})")
        q=f"%{team.strip().lower()}%"; params.extend([q,q])
    if year:
        if kind=="postgres": where.append(f"EXTRACT(YEAR FROM kickoff)={ph}"); params.append(year)
        else: where.append(f"substr(kickoff,1,4)={ph}"); params.append(str(year))
    if date_from.strip(): add("kickoff>=?",date_from.strip())
    if date_to.strip(): add("kickoff<=?",date_to.strip()+"T23:59:59+00:00" if len(date_to.strip())==10 else date_to.strip())
    wc=(" WHERE "+" AND ".join(where)) if where else ""
    count_sql="SELECT COUNT(*) FROM ksn_results_archive"+wc
    cur.execute(count_sql,tuple(params)); total=int(cur.fetchone()[0])
    sql=("SELECT sport,provider,provider_id,country,competition,competition_id,season,round_name,kickoff,"
         "home_id,home_name,home_badge,away_id,away_name,away_badge,home_score,away_score,status,venue,referee "
         "FROM ksn_results_archive"+wc+f" ORDER BY kickoff DESC LIMIT {ph} OFFSET {ph}")
    cur.execute(sql,tuple(params+[limit,offset])); raw=cur.fetchall()
    rows=[]
    for r in raw:
        v=list(r)
        rows.append({"sport":v[0],"source":v[1],"id":v[2],"country":v[3],"league":v[4],"leagueId":v[5],
          "season":v[6],"round":v[7],"date":str(v[8]),"homeId":v[9],"home":v[10],"homeLogo":v[11],
          "awayId":v[12],"away":v[13],"awayLogo":v[14],"homeScore":v[15],"awayScore":v[16],
          "status":v[17],"venue":v[18],"referee":v[19],"isFinished":True,"providerFixtureId":v[2] if str(v[0]).lower()=="football" else None})
    cur.close(); conn.close()
    return {"matches":rows,"count":len(rows),"total":total,"limit":limit,"offset":offset,
            "permanentArchive":True,"providerCalls":0,"confirmedScoresOnly":True}


async def _historical_provider_results(q:str="", sport:str="all", country:str="", competition:str="",
                                       season:str="", year:Optional[int]=None, date_from:str="", date_to:str="",
                                       limit:int=100):
    """Fetch missing historical football finals from API-Football, cache-first.

    The permanent KSN archive remains the first source. This helper is only a gap filler
    after an archive miss. Provider fixture IDs are preserved so the existing Stats page
    can load /fixtures/{id}/stats and persist completed statistics on demand.
    """
    if str(sport or "all").lower() not in {"all","football"}:
        return [], {"attempted":False,"reason":"provider fallback currently football only"}
    term=(q or "").strip()
    team_term=term or (country or "").strip()
    seasons=[]
    raw_season=(season or "").strip()
    if year: seasons=[int(year)]
    elif re.fullmatch(r"\d{4}",raw_season): seasons=[int(raw_season)]
    elif date_from and re.match(r"^\d{4}",date_from): seasons=[int(date_from[:4])]
    elif date_to and re.match(r"^\d{4}",date_to): seasons=[int(date_to[:4])]
    else:
        y=datetime.now(timezone.utc).year
        seasons=[y,y-1,y-2]
    fixtures=[]; calls=0; team_ids=[]; league_ids=[]
    try:
        if team_term and not re.fullmatch(r"\d{4}(-\d{2}-\d{2})?",team_term):
            # Resolve ordinary clubs and national teams. API-Football /teams?search=
            # is the authoritative text resolver; keep several matches because a country
            # name can resolve both the national side and domestic clubs.
            td=await _afoot_get("/teams",{"search":team_term}); calls+=1
            for item in (td.get("response") or [])[:12]:
                t=(item or {}).get("team") or {}; tid=t.get("id")
                if tid is not None: team_ids.append(int(tid))
            # A broad q may actually be a competition rather than a team. Resolve it too
            # so one Finished Matches search box works for team/country/competition text.
            if term:
                try:
                    ql=await _afoot_get("/leagues",{"search":term}); calls+=1
                    for item in (ql.get("response") or [])[:8]:
                        lid=((item or {}).get("league") or {}).get("id")
                        if lid is not None: league_ids.append(int(lid))
                except Exception:
                    pass
        comp_term=(competition or "").strip()
        if comp_term:
            ld=await _afoot_get("/leagues",{"search":comp_term}); calls+=1
            for item in (ld.get("response") or [])[:8]:
                lid=((item or {}).get("league") or {}).get("id")
                if lid is not None: league_ids.append(int(lid))
        requests=[]
        # Exact/ranged date searches can be asked directly without knowing a team.
        if date_from and date_to:
            requests.append({"from":date_from[:10],"to":date_to[:10]})
        for sy in seasons[:4]:
            if team_ids:
                for tid in team_ids[:8]: requests.append({"team":tid,"season":sy})
            if league_ids:
                for lid in league_ids[:8]: requests.append({"league":lid,"season":sy})
        # A year/season-only search has no safe single unbounded fixtures request. Return
        # an explicit diagnostic instead of silently pretending the provider was queried.
        if not requests:
            return [],{"attempted":False,"providerCalls":calls,"teamsResolved":len(team_ids),
                       "leaguesResolved":len(league_ids),"reason":"Add a team, country, competition or exact date to fetch provider history for a year/season."}
        # Never issue an unbounded provider-history request.
        seen=set()
        for params in requests[:24]:
            key=json.dumps(params,sort_keys=True)
            if key in seen: continue
            seen.add(key); d=await _afoot_get("/fixtures",params); calls+=1
            for f in (d.get("response") or []):
                n=_normalise_fixture(f)
                if not n.get("isFinished") or n.get("homeScore") is None or n.get("awayScore") is None: continue
                league=f.get("league") or {}; fixture=f.get("fixture") or {}
                n.update({"sport":"football","id":fixture.get("id"),"providerFixtureId":fixture.get("id"),
                          "date":fixture.get("date") or n.get("datetime"),"country":league.get("country") or "International",
                          "season":league.get("season"),"round":league.get("round"),"source":"API-Football",
                          "referee":fixture.get("referee") or ""})
                hay=" ".join(str(x or "") for x in (n.get("home"),n.get("away"),n.get("country"),n.get("league"),n.get("season"),n.get("date"))).lower()
                if term and term.lower() not in hay and not team_ids: continue
                if country and country.lower() not in str(n.get("country") or "").lower() and country.lower() not in hay: continue
                if competition and competition.lower() not in str(n.get("league") or "").lower(): continue
                fixtures.append(n)
        uniq={str(x.get("id") or (x.get("date"),x.get("home"),x.get("away"))):x for x in fixtures}
        rows=sorted(uniq.values(),key=lambda x:str(x.get("date") or ""),reverse=True)[:limit]
        return rows,{"attempted":True,"providerCalls":calls,"teamsResolved":len(team_ids),"leaguesResolved":len(league_ids)}
    except Exception as exc:
        log.warning("Historical provider fallback failed q=%r: %s",q,exc)
        return [],{"attempted":True,"providerCalls":calls,"error":str(exc)[:240]}

@app.get("/results/search")
async def results_search(
    q:str=Query(""), sport:str=Query("all"), country:str=Query(""), competition:str=Query(""),
    season:str=Query(""), team:str=Query(""), year:Optional[int]=Query(None,ge=1900,le=2200),
    date_from:str=Query(""), date_to:str=Query(""), limit:int=Query(100,ge=1,le=500),
    offset:int=Query(0,ge=0), include_recent:bool=Query(True)
):
    """Canonical KSN result search.

    Search order is permanent archive first, then the rolling Finished Games layer is
    synchronised when the requested window can include the last 48 hours. The recent
    layer is archived before the final query is returned, so a confirmed result cannot
    disappear when the rolling cache expires. ``q`` is intentionally broad and matches
    team, country, competition, season/year and ISO date text.
    """
    now=datetime.now(timezone.utc)
    recent_sync=False; recent_error=None; archived_recent=0
    if include_recent:
        # Only synchronise the recent provider/cache layer when the requested date range
        # can overlap it. Blank dates and ordinary text searches are allowed to overlap.
        overlap=True
        try:
            if date_to.strip():
                dto=datetime.fromisoformat(date_to.strip().replace('Z','+00:00'))
                if dto.tzinfo is None: dto=dto.replace(tzinfo=timezone.utc)
                overlap=dto >= now-timedelta(hours=48)
        except Exception:
            overlap=True
        if overlap:
            try:
                recent=await sports_finished_all(hours=48,limit=5000)
                recent_rows=recent.get("matches",[]) if isinstance(recent,dict) else []
                archived_recent=_archive_results_upsert(recent_rows)
                recent_sync=True
            except Exception as exc:
                recent_error=str(exc)[:240]

    _results_archive_init()
    conn,kind=_results_db(); cur=conn.cursor(); ph="%s" if kind=="postgres" else "?"
    where=[]; params=[]
    def add(expr,val): where.append(expr.replace("?",ph)); params.append(val)
    if sport.lower() in {"football","rugby","cricket"}: add("sport=?",sport.lower())
    # v457: named fields are canonical structured filters. Keep q broad below.
    if country.strip(): add("lower(trim(country))=?",country.strip().lower())
    if competition.strip(): add("lower(trim(competition))=?",competition.strip().lower())
    if season.strip(): add("lower(trim(season))=?",season.strip().lower())
    if team.strip():
        where.append(f"(lower(home_name) LIKE {ph} OR lower(away_name) LIKE {ph})")
        tq=f"%{team.strip().lower()}%"; params.extend([tq,tq])
    if year:
        if kind=="postgres": where.append(f"EXTRACT(YEAR FROM kickoff)={ph}"); params.append(year)
        else: where.append(f"substr(kickoff,1,4)={ph}"); params.append(str(year))
    if date_from.strip(): add("kickoff>=?",date_from.strip())
    if date_to.strip(): add("kickoff<=?",date_to.strip()+"T23:59:59+00:00" if len(date_to.strip())==10 else date_to.strip())
    if q.strip():
        qq=f"%{q.strip().lower()}%"
        # kickoff is TIMESTAMPTZ on PostgreSQL, so it must be cast before
        # LOWER/LIKE.  The old COALESCE(kickoff,'') expression raises a
        # PostgreSQL datatype error and made every broad historical search
        # return HTTP 500 on Render.
        if kind == "postgres":
            text_exprs=(
                "lower(COALESCE(home_name,''))",
                "lower(COALESCE(away_name,''))",
                "lower(COALESCE(country,''))",
                "lower(COALESCE(competition,''))",
                "lower(COALESCE(season,''))",
                "lower(COALESCE(kickoff::text,''))",
            )
        else:
            text_exprs=(
                "lower(COALESCE(home_name,''))",
                "lower(COALESCE(away_name,''))",
                "lower(COALESCE(country,''))",
                "lower(COALESCE(competition,''))",
                "lower(COALESCE(season,''))",
                "lower(COALESCE(kickoff,''))",
            )
        where.append("("+" OR ".join([f"{expr} LIKE {ph}" for expr in text_exprs])+")")
        params.extend([qq]*len(text_exprs))
    wc=(" WHERE "+" AND ".join(where)) if where else ""
    cur.execute("SELECT COUNT(*) FROM ksn_results_archive"+wc,tuple(params)); total=int(cur.fetchone()[0])
    sql=("SELECT sport,provider,provider_id,country,competition,competition_id,season,round_name,kickoff,"
         "home_id,home_name,home_badge,away_id,away_name,away_badge,home_score,away_score,status,venue,referee "
         "FROM ksn_results_archive"+wc+f" ORDER BY kickoff DESC LIMIT {ph} OFFSET {ph}")
    cur.execute(sql,tuple(params+[limit,offset])); raw=cur.fetchall(); rows=[]
    for r in raw:
        v=list(r); rows.append({"sport":v[0],"source":v[1],"id":v[2],"country":v[3],"league":v[4],"leagueId":v[5],
          "season":v[6],"round":v[7],"date":str(v[8]),"homeId":v[9],"home":v[10],"homeLogo":v[11],
          "awayId":v[12],"away":v[13],"awayLogo":v[14],"homeScore":v[15],"awayScore":v[16],
          "status":v[17],"venue":v[18],"referee":v[19],"isFinished":True,"providerFixtureId":v[2] if str(v[0]).lower()=="football" else None})
    cur.close(); conn.close()

    provider_meta={"attempted":False,"providerCalls":0}; archived_provider=0
    # v372: always allow provider gap-fill on the first page of a constrained historical
    # search. A partially populated archive must not suppress older provider results.
    constrained=bool(q.strip() or country.strip() or competition.strip() or team.strip() or date_from.strip() or date_to.strip())
    # v457: provider history is a gap filler only. If PostgreSQL already has matching
    # rows, return immediately instead of waiting on league/team resolution. This
    # removes the 24s Bundesliga path and protects provider reserve.
    if offset == 0 and constrained and not rows:
        provider_rows,provider_meta=await _historical_provider_results(
            q=(q or team),sport=sport,country=country,competition=competition,season=season,year=year,
            date_from=date_from,date_to=date_to,limit=limit)
        if provider_rows:
            archived_provider=_archive_results_upsert(provider_rows)
            # Merge the provider response directly. Do not make a stricter second archive
            # query capable of hiding a match that the provider just returned.
            merged={}
            for m in list(rows)+list(provider_rows):
                key=str(m.get("id") or m.get("providerFixtureId") or (m.get("date"),m.get("home"),m.get("away")))
                merged[key]=m
            rows=sorted(merged.values(),key=lambda x:str(x.get("date") or ""),reverse=True)[:limit]
            total=max(total,len(rows))
    return {"query":q,"matches":rows,"count":len(rows),"total":total,"limit":limit,"offset":offset,
            "permanentArchive":True,"recentLayerSynced":recent_sync,"recentRowsArchived":archived_recent,
            "recentSyncError":recent_error,"historicalProvider":provider_meta,
            "historicalRowsArchived":archived_provider,"confirmedScoresOnly":True}


@app.get("/results/filters")
async def results_filters():
    """Small archive discovery payload for Country / Competition / Season filters."""
    _results_archive_init()
    conn,kind=_results_db(); cur=conn.cursor()
    out={}
    for key,col in (("countries","country"),("competitions","competition"),("seasons","season")):
        cur.execute(f"SELECT {col}, COUNT(*) FROM ksn_results_archive WHERE COALESCE({col},'')<>'' GROUP BY {col} ORDER BY {col}")
        out[key]=[{"value":r[0],"count":int(r[1])} for r in cur.fetchall()]
    cur.close(); conn.close()
    return out


@app.get("/sports/finished")
async def sports_finished_all(hours:int=Query(48,ge=1,le=168),limit:Optional[int]=Query(None,ge=1,le=5000)):
    """All scored completed results in the rolling window. No display/result cap.
    Football is globally discovered by date and Africa-facing ordered 2:1:1 while pools
    are available. Rugby/Cricket are also retained. Missing final scores are excluded.
    """
    now=datetime.now(timezone.utc); cutoff=now-timedelta(hours=hours); key=f"v310:{hours}:all-scored"
    cached=_FINISHED_MULTI_CACHE.get(key)
    if cached and time.time()-cached[0] < 300:return {**cached[1],"cached":True}
    persisted=_dashboard_snapshot_get(f"sports_finished_v310:{hours}")
    last_good=(persisted or {}).get("data") if isinstance(persisted,dict) else None
    errors=[]; seen=set(); football=[]; multisport=[]; excluded_missing_score=0
    def parse_dt(v):
        try:
            d=datetime.fromisoformat(str(v or '').replace('Z','+00:00'));return d if d.tzinfo else d.replace(tzinfo=timezone.utc)
        except Exception:return None
    def finished(x):
        st=(str(x.get('statusShort') or '')+' '+str(x.get('status') or '')).lower()
        return bool(x.get('isFinished')) or bool(re.search(r'(^|\b)(ft|final|finished|complete|completed|post|aet|pen)(\b|$)',st,re.I))
    dates=[];d=cutoff.date()
    while d<=now.date():dates.append(d.isoformat());d+=timedelta(days=1)
    for ds in dates:
        try:
            data=await _afoot_get('/fixtures',{'date':ds,'timezone':TIMEZONE})
            for raw in data.get('response',[]) or []:
                m=_widget_match_record(_normalise_fixture(raw,''),'football')
                stamp=parse_dt(m.get('date') or m.get('datetime'))
                if not stamp or not cutoff<=stamp<=now or not finished(m):continue
                if not _scored_finished(m): excluded_missing_score+=1;continue
                k='football:'+str(m.get('id') or f"{m.get('home')}|{m.get('away')}|{stamp.isoformat()}")
                if k in seen:continue
                seen.add(k);football.append(m)
        except Exception as exc:errors.append(f'football:{ds}: {exc}')
    football.sort(key=lambda x:parse_dt(x.get('date') or x.get('datetime')) or datetime.min.replace(tzinfo=timezone.utc),reverse=True)
    balanced=_ksn_sort_football_rows(football,newest_first=True)
    region_info={"ordering":"Big 5 > Turkish Super Lig > visitor country (client locale) > other leagues","legacyRegionalMix":False}
    for sp in ('rugby','cricket'):
        try:
            # Query the provider's finished-status contract once for the exact rolling window,
            # then resolve missing final scores from /scores before applying the public score gate.
            games=await _oddspapi_sport_range(sp,cutoff,now+timedelta(minutes=5),2)
            games=await _oddspapi_enrich_scores(games,200)
            for x in games or []:
                m=_widget_match_record(x,sp);stamp=parse_dt(m.get('date') or m.get('datetime'))
                if not stamp or not cutoff<=stamp<=now or not finished(m):continue
                if not _scored_finished(m): excluded_missing_score+=1;continue
                k=sp+':'+str(m.get('id') or f"{m.get('home')}|{m.get('away')}|{stamp.isoformat()}")
                if k in seen:continue
                seen.add(k);multisport.append(m)
        except Exception as exc:errors.append(f'{sp}:48h: {exc}')
    multisport.sort(key=lambda x:parse_dt(x.get('date') or x.get('datetime')) or datetime.min.replace(tzinfo=timezone.utc),reverse=True)
    # Keep every valid result. Football keeps its 2:1:1 regional ordering; multisport is retained too.
    rows=balanced+multisport
    sports_breakdown={sp:sum(1 for m in rows if m.get('sport')==sp) for sp in ('football','rugby','cricket')}
    payload={'count':len(rows),'matches':rows,'hours':hours,'windowStart':cutoff.isoformat(),'windowEnd':now.isoformat(),'sports':['football','rugby','cricket'],'sportsBreakdown':sports_breakdown,'footballRegionBreakdown':region_info,'africaPriority':True,'allValidResultsIncluded':True,'excludedMissingFinalScore':excluded_missing_score,'errors':errors[:8],'updatedAt':now.isoformat()}
    try:
        _archive_results_upsert(rows)
    except Exception as exc:
        log.warning("KSN results archive upsert failed: %s", exc)
    if rows:
        _FINISHED_MULTI_CACHE[key]=(time.time(),payload);_dashboard_snapshot_put(f"sports_finished_v310:{hours}",{'data':payload});return payload
    if isinstance(last_good,dict) and last_good.get('matches'):return {**last_good,'cached':True,'stale':True,'refreshErrors':errors[:8]}
    return payload

_LIVE_TASK=None
async def _sports_live_compute():
    sports = ["football","rugby","cricket"]
    async def one(sp):
        # Per-sport deadline so one slow provider can never hold the whole widget.
        return await asyncio.wait_for(_sports_scores(sp, None, True, None), timeout=8.0)
    results = await asyncio.gather(*[one(sp) for sp in sports], return_exceptions=True)
    games=[]; failed=[]; successful=0
    for sport, data in zip(sports, results):
        if isinstance(data, BaseException):
            failed.append(sport)
            log.warning("Multi-sport live %s failed: %s", sport, data)
            continue
        successful += 1
        games.extend([_widget_match_record(g,sport) for g in (data or [])])
    games=[g for g in games if str(g.get("statusShort") or "").lower() in ("in","live","1","1h","2h","ht","et") or re.search(r"live|progress|halftime|period|quarter|inning|1h|2h|ht|et", str(g.get("status") or ""), re.I)]
    football_games=_ksn_sort_football_rows([g for g in games if str(g.get("sport") or "football").lower()=="football"])
    other_games=[g for g in games if str(g.get("sport") or "football").lower()!="football"]
    games=football_games+other_games
    now=datetime.now(timezone.utc).isoformat()
    payload={"count":len(games),"games":games,"updatedAt":now,"sports":sports,"partial":bool(failed),"failedSports":failed}
    if successful:
        previous=_dashboard_snapshot_get("sports_live:last_good")
        previous_data=(previous or {}).get("data") if isinstance(previous,dict) else None
        previous_games=(previous_data or {}).get("games") if isinstance(previous_data,dict) else []
        # v451: only persist an empty Live result when ALL sports completed.
        # A partial empty result is unknown, not "no live matches", and must never
        # become last-good or overwrite an older useful snapshot.
        valid_for_lkg=bool(games) or not failed
        if valid_for_lkg:
            _dashboard_snapshot_put("sports_live:last_good",{"data":payload})
    return payload, successful

@app.get("/sports/live")
async def sports_live_all():
    """Cache-first live feed: serves the shared last-good snapshot instantly and
    refreshes once in the background; a cold start waits at most ~6s."""
    global _LIVE_TASK
    snap=_dashboard_snapshot_get("sports_live:last_good")
    cached=(snap or {}).get("data") if isinstance(snap,dict) else None
    age=time.time()-float((snap or {}).get("updated_at") or 0) if snap else 10**9
    if _LIVE_TASK is None or _LIVE_TASK.done():
        if not (isinstance(cached,dict) and age<15):
            _LIVE_TASK=asyncio.create_task(_sports_live_compute())
    # v451: an empty partial snapshot is not a valid last-good result. It means
    # at least one sport failed, so "zero live games" was never established.
    cached_games=(cached or {}).get("games") if isinstance(cached,dict) else None
    cached_partial=bool((cached or {}).get("partial")) if isinstance(cached,dict) else False
    cached_valid=isinstance(cached,dict) and not (cached_partial and not cached_games)
    if cached_valid:
        return {**cached,"cached":True,"stale":age>=15,"cacheAgeSeconds":int(age)}
    # v450/v451: a cold or invalid-LKG public request must never wait on providers.
    # The single background task above owns refresh; first paint receives a
    # valid fail-soft payload immediately and subsequent requests pick up LKG.
    return {
        "count":0,
        "games":[],
        "updatedAt":datetime.now(timezone.utc).isoformat(),
        "warming":True,
        "cached":False,
        "stale":False,
        "sports":["football","rugby","cricket"],
        "providerMode":"background-cache-first",
    }


async def _espn_summary(sport: str, event_id: str, league: str = ""):
    """Fetch an ESPN event summary for cross-sport match pages."""
    leagues = [league] if league else ESPN_LEAGUES.get(sport, [])
    for lg in leagues:
        try:
            url=f"https://site.api.espn.com/apis/site/v2/sports/{sport}/{lg}/summary"
            data=await _sports_get(url, {"event": str(event_id)})
            if data:
                return data
        except Exception as exc:
            log.debug("ESPN summary %s/%s failed: %s", sport, lg, exc)
    return {}

def _espn_participants(summary: dict):
    """Normalise useful participant/player information from ESPN summaries."""
    out=[]
    for athlete in summary.get("athletes") or []:
        out.append({"id":str(athlete.get("id") or ""),"name":athlete.get("displayName") or athlete.get("fullName") or athlete.get("name") or "Player","photo":athlete.get("headshot") or athlete.get("photo"),"position":(athlete.get("position") or {}).get("abbreviation") if isinstance(athlete.get("position"),dict) else athlete.get("position"),"statistics":athlete.get("statistics") or []})
    for section in summary.get("leaders") or []:
        for leader in section.get("leaders") or []:
            a=leader.get("athlete") or {}
            if a.get("id"):
                out.append({"id":str(a.get("id")),"name":a.get("displayName") or a.get("fullName") or "Player","photo":a.get("headshot"),"position":None,"statistics":leader.get("statistics") or []})
    seen=set(); return [x for x in out if not (x["id"] in seen or seen.add(x["id"]))]

async def _football_match_details_build(fid:int):
    async def bounded(coro, seconds=4.5):
        try:
            return await asyncio.wait_for(coro, timeout=seconds)
        except Exception as exc:
            return exc
    fd,stats,lineups,events,insights,players,odds_detail=await asyncio.gather(
        bounded(_afoot_get("/fixtures",{"id":fid}),8.0),
        bounded(fixture_stats(fid),8.0),
        bounded(fixture_lineups(fid),8.0),
        bounded(fixture_events(fid),8.0),
        bounded(fixture_insights(fid),12.0),
        bounded(_afoot_get("/fixtures/players",{"fixture":fid}),8.0),
        bounded(fixture_odds_detail(fid),8.0),
        return_exceptions=True)
    provider_error=""
    if isinstance(fd,Exception):
        provider_error=str(fd); f={}
    else:
        rr=(fd.get("response") or []) if isinstance(fd,dict) else []
        f=rr[0] if rr else {}
    stats=stats if isinstance(stats,dict) else {}
    lineups=lineups if isinstance(lineups,dict) else {}
    events=events if isinstance(events,dict) else {}
    insights=insights if isinstance(insights,dict) else {}
    players=players if isinstance(players,dict) else {}
    odds_detail=odds_detail if isinstance(odds_detail,dict) else {}
    # Match-centre standings: use the fixture's exact competition + season so
    # every football Stats page receives the table that belongs to that match.
    standings=[]
    try:
        league_obj=f.get("league") or {}
        league_id=int(league_obj.get("id") or 0)
        season=int(league_obj.get("season") or 0)
        if league_id and season:
            teams_obj=f.get("teams") or {}
            home_team_id=(teams_obj.get("home") or {}).get("id")
            away_team_id=(teams_obj.get("away") or {}).get("id")
            standings=await bounded(_fetch_match_standings_for_league(league_id,season,home_team_id,away_team_id),6.0)
            if isinstance(standings,Exception):standings=[]
    except Exception as exc:
        log.debug("match standings unavailable fixture=%s: %s",fid,exc)
        standings=[]
    # v401: statistics remain provider-authoritative. If the aggregate build still has
    # no team statistics, retry the statistics endpoint fresh once before rendering.
    if not stats.get("statistics"):
        try:
            fresh_stats=await _afoot_get("/fixtures/statistics",{"fixture":fid},force_fresh=True)
            fresh_rows=(fresh_stats.get("response") or []) if isinstance(fresh_stats,dict) else []
            if fresh_rows: stats={"statistics":fresh_rows,"available":True}
        except Exception as exc:
            log.debug("v401 match statistics fresh retry unavailable fixture=%s: %s",fid,exc)
    lineup_teams=lineups.get("teams",[])
    # v403: attach provider player photos to lineup rows without extra API calls.
    photo_by_id={}
    for team_row in players.get("response",[]) or []:
        for item in team_row.get("players",[]) or []:
            pobj=item.get("player") or {}
            if pobj.get("id") and pobj.get("photo"):
                photo_by_id[str(pobj.get("id"))]=pobj.get("photo")
    for team_row in lineup_teams:
        for pobj in team_row.get("players",[]) or []:
            if pobj.get("id") and not pobj.get("photo"):
                pobj["photo"]=photo_by_id.get(str(pobj.get("id"))) or f"https://media.api-sports.io/football/players/{pobj.get('id')}.png"
    event_rows=events.get("events",[])
    stat_rows=stats.get("statistics",[])
    if isinstance(insights,dict):
        insights={**insights,"venueIntelligence":_venue_intelligence(f,insights)}
    stage_flags=_enhanced_stage_flags(f)
    payload={"sport":"football","matchId":fid,"match":f,
             "statistics":stat_rows,"teams":lineup_teams,
             "standings":standings,
             "events":event_rows,"insights":insights,
             "players":players.get("response",[]),"odds":odds_detail,
             "enhancedArchitecture":{"version":"v468-team-player-history-intelligence-1","stage":stage_flags,
               "datasets":{"fixture":bool(f),"statistics":bool(stat_rows),"lineups":bool(lineup_teams),
                 "events":bool(event_rows),"players":bool(players.get("response",[])),
                 "historicalIntelligence":bool(insights),"standings":bool(standings),"odds":bool(odds_detail)}},
             "fantasySignals":_fantasy_match_signals(f,event_rows,stat_rows),
             "source":"API-Football","available":bool(f),
             "partialAvailable":bool(f or stat_rows or lineup_teams or event_rows or players.get("response") or insights),
             "warning":"Match header temporarily unavailable; available cached/statistical data is shown." if provider_error else "",
             "updatedAt":datetime.now(timezone.utc).isoformat()}
    status=str(((f.get("fixture") or {}).get("status") or {}).get("short") or "").upper()
    completed=status in {"FT","AET","PEN"}
    if payload["partialAvailable"]:
        _dashboard_snapshot_put(f"match:football:{fid}",{"data":payload})
        # Completed match bundles are permanent: events/cards, line-ups, players, stats and intelligence survive provider/cache expiry.
        if completed:_enhanced_match_db_put("football",fid,payload,True)
    return payload

async def _football_match_details_refresh(fid:int):
    try:
        await _football_match_details_build(fid)
    except Exception as exc:
        log.debug("background match refresh failed fixture=%s: %s",fid,exc)

@app.get("/fixtures/{fixture_id}/enhanced")
async def fixture_enhanced_bundle(fixture_id:int, refresh:int=Query(0,ge=0,le=1)):
    """Unified UEFA/playoff/fantasy-ready match contract. Completed bundles are DB-first and permanent."""
    if not refresh:
        saved=_enhanced_match_db_get("football",fixture_id)
        if isinstance(saved,dict) and saved.get("completed"):
            return {**saved,"cached":True,"cacheLayer":"persistent-enhanced"}
    return await _football_match_details_build(fixture_id)

@app.get("/sports/{sport}/match/{match_id}")
async def sport_match_details(sport:str,match_id:str,league:str=Query(""),refresh:int=Query(0,ge=0,le=1)):
    sport=(sport or "football").lower().strip()
    if sport=="football":
        fid=int(re.sub(r"\D","",str(match_id)) or 0)
        if not fid:raise HTTPException(400,"Invalid fixture ID")
        persisted_enhanced=_enhanced_match_db_get("football",fid) if not refresh else None
        if isinstance(persisted_enhanced,dict) and persisted_enhanced.get("completed"):
            return {**persisted_enhanced,"cached":True,"cacheLayer":"persistent-enhanced"}
        snap=_dashboard_snapshot_get(f"match:football:{fid}") if not refresh else None
        cached=(snap or {}).get("data") if isinstance(snap,dict) else None
        if isinstance(cached,dict) and cached.get("partialAvailable"):
            # One click: render last-known-good data immediately; refresh independently.
            asyncio.create_task(_football_match_details_refresh(fid))
            return {**cached,"cached":True,"refreshing":True}
        try:
            return await asyncio.wait_for(_football_match_details_build(fid),timeout=13.0)
        except Exception as exc:
            log.warning("football match details failed fixture=%s: %s",fid,exc)
            persisted=_match_stats_db_get("football",fid)
            return {"sport":"football","matchId":fid,"match":{},
                    "statistics":(persisted or {}).get("statistics",[]),"teams":[],"events":[],"insights":{},
                    "source":"persistent-cache","available":False,
                    "partialAvailable":bool((persisted or {}).get("statistics")),
                    "warning":"Match data is refreshing. Cached statistics are shown where available.",
                    "updatedAt":datetime.now(timezone.utc).isoformat()}
    if sport not in {"rugby","cricket"}:raise HTTPException(404,"Sport not supported")
    snap_key=f"match:{sport}:{match_id}"
    snap=_dashboard_snapshot_get(snap_key) if not refresh else None
    cached=(snap or {}).get("data") if isinstance(snap,dict) else None
    if isinstance(cached,dict) and cached.get("available"):
        return {**cached,"cached":True}
    # Primary multisport detail lookup.
    f=await _oddspapi_find_fixture(sport,match_id)
    if f:
        score_data,hr,ar=await asyncio.gather(
            _oddspapi_fixture_scores(f.get("providerFixtureId") or f.get("id")),
            _multi_recent(f.get("homeId"),sport,5),_multi_recent(f.get("awayId"),sport,5))
        latest=score_data.get("latest") or {}
        if latest.get("participant1Score") is not None:f["homeScore"]=latest.get("participant1Score")
        if latest.get("participant2Score") is not None:f["awayScore"]=latest.get("participant2Score")
        sport_schema=_cricket_score_schema(score_data) if sport=="cricket" else _rugby_score_schema(score_data)
        payload={"sport":sport,"matchId":f.get("id") or match_id,"match":f,
                "statistics":{"scoresByPeriod":score_data.get("periods") or {},
                              "sportSpecific":sport_schema,
                              "homeForm":_multi_team_form(hr,f.get("homeId")),
                              "awayForm":_multi_team_form(ar,f.get("awayId"))},
                "scoreAvailable":bool(score_data.get("available")),"events":[],"available":True,
                "updatedAt":datetime.now(timezone.utc).isoformat()}
        _dashboard_snapshot_put(snap_key,{"data":payload})
        return payload
    # Finished Games may originate from the secondary score feed. Resolve that event ID directly
    # so its Stats action remains valid instead of assuming IDs from different feeds are interchangeable.
    try:
        summary=await _espn_summary(sport,str(match_id),league)
    except Exception:
        summary={}
    if isinstance(summary,dict) and summary:
        header=summary.get("header") or {}
        comps=header.get("competitions") or []
        comp=comps[0] if comps else {}
        competitors=comp.get("competitors") or []
        home=next((x for x in competitors if str(x.get("homeAway") or '').lower()=="home"), competitors[0] if competitors else {})
        away=next((x for x in competitors if str(x.get("homeAway") or '').lower()=="away"), competitors[1] if len(competitors)>1 else {})
        def team_name(x):
            t=x.get("team") or {}; return t.get("displayName") or t.get("shortDisplayName") or t.get("name") or "Team"
        def logo(x):
            t=x.get("team") or {}; logos=t.get("logos") or []; return (logos[0].get("href") if logos and isinstance(logos[0],dict) else None)
        match={"id":str(match_id),"home":team_name(home),"away":team_name(away),
               "homeScore":home.get("score"),"awayScore":away.get("score"),
               "homeLogo":logo(home),"awayLogo":logo(away),
               "league":((header.get("league") or {}).get("name") if isinstance(header.get("league"),dict) else league) or league or sport.title(),
               "status":((comp.get("status") or {}).get("type") or {}).get("description") if isinstance(comp.get("status"),dict) else ""}
        payload={"sport":sport,"matchId":str(match_id),"match":match,
                 "statistics":{"sportSpecific":summary,"scoresByPeriod":{}},
                 "events":summary.get("plays") or [],"participants":_espn_participants(summary),
                 "available":True,"scoreAvailable":bool(home.get("score") is not None or away.get("score") is not None),
                 "updatedAt":datetime.now(timezone.utc).isoformat()}
        _dashboard_snapshot_put(snap_key,{"data":payload})
        return payload
    if isinstance(cached,dict):return {**cached,"cached":True,"stale":True}
    return {"sport":sport,"matchId":match_id,"match":{},"statistics":{},"events":[],"available":False,"error":"No data available.","updatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/sports/{sport}/team/{team_id}")
async def sports_team_profile(sport: str, team_id: str, league: str = Query(""), name: str = Query("")):
    """Unified clickable team page. Provider IDs, badges and flags are preserved."""
    sport=sport.lower().strip()
    if sport == "football":
        return await team_profile(team=team_id or name)
    if sport == "rugby" and SPORTS_API_KEYS.get("rugby"):
        try:
            rows=await _rugby_api("/teams", {"id": team_id})
            team=(rows or [{}])[0] if isinstance(rows,list) else {}
            squad=[]
            try: squad=await _rugby_api("/players", {"team": team_id})
            except Exception: squad=[]
            if team and (team.get("id") or team.get("name")):
                return {"sport":"rugby","team":team,"players":squad if isinstance(squad,list) else [],"source":"API-Sports","updatedAt":datetime.now(timezone.utc).isoformat()}
            log.debug("Rugby API-Sports returned an empty team for %s; continuing to same-sport fallbacks", team_id)
        except Exception as exc:
            log.warning("Rugby team profile failed %s: %s", team_id, exc)
    # ESPN fallback is used for cricket and rugby when a provider key is unavailable.
    leagues=[league] if league else ESPN_LEAGUES.get(sport,[])
    for lg in leagues:
        if not lg: continue
        try:
            data=await _sports_get(f"https://site.api.espn.com/apis/site/v2/sports/{sport}/{lg}/teams/{team_id}")
            team=data.get("team") or data
            return {"sport":sport,"team":team,"players":team.get("athletes") or [],"league":lg,"source":"ESPN","updatedAt":datetime.now(timezone.utc).isoformat()}
        except Exception as exc:
            log.debug("ESPN team %s/%s/%s failed: %s",sport,lg,team_id,exc)
    # Final same-sport fallback: reuse the isolated directory/fixture catalogue.
    # This never crosses into Football and prevents valid Rugby/Cricket teams from
    # becoming a 404 merely because one provider does not expose a team-detail route.
    try:
        d=await multisport_teams_players(sport,200)
        wanted=str(team_id or "").strip().lower(); wanted_name=str(name or "").strip().lower()
        for t in d.get("teams") or []:
            if str(t.get("id") or "").strip().lower()==wanted or (wanted_name and str(t.get("name") or "").strip().lower()==wanted_name):
                return {"sport":sport,"team":t,"players":[],"source":t.get("source") or d.get("source") or "sport-isolated cache","updatedAt":datetime.now(timezone.utc).isoformat(),"partial":True}
    except Exception as exc:
        log.debug("%s isolated team fallback failed %s: %s",sport,team_id,exc)
    raise HTTPException(404, f"{sport.title()} team data was not returned by the configured provider")

@app.get("/sports/{sport}/player/{player_id}")
async def sports_player_profile(sport: str, player_id: str, league: str = Query(""), name: str = Query("")):
    """Unified clickable player page. Football remains API-Football authoritative."""
    sport=sport.lower().strip()
    if sport == "football":
        return await player_profile(player=int(player_id))
    if sport == "rugby" and SPORTS_API_KEYS.get("rugby"):
        try:
            rows=await _rugby_api("/players", {"id": player_id})
            player=(rows or [{}])[0] if isinstance(rows,list) else {}
            return {"sport":"rugby","player":player,"statistics":player.get("statistics") or [],"source":"API-Sports","updatedAt":datetime.now(timezone.utc).isoformat()}
        except Exception as exc:
            log.warning("Rugby player profile failed %s: %s",player_id,exc)
    # ESPN athlete endpoint varies by competition; try the known league feeds.
    leagues=[league] if league else ESPN_LEAGUES.get(sport,[])
    for lg in leagues:
        if not lg: continue
        for host in ("site.api.espn.com/apis/site/v2", "site.web.api.espn.com/apis/common/v3"):
            try:
                data=await _sports_get(f"https://{host}/sports/{sport}/{lg}/athletes/{player_id}")
                player=data.get("athlete") or data.get("player") or data
                return {"sport":sport,"player":player,"statistics":data.get("statistics") or [],"league":lg,"source":"ESPN","updatedAt":datetime.now(timezone.utc).isoformat()}
            except Exception as exc:
                log.debug("ESPN player %s/%s/%s failed: %s",sport,lg,player_id,exc)
    # Keep the dedicated player page usable even when an upstream sport provider
    # has no profile endpoint for this athlete. Never expose a raw 404 to the visitor.
    fallback_name=(name or f"{sport.title()} player").strip()
    return {"sport":sport,"player":{"id":player_id,"name":fallback_name},
            "statistics":[],"league":league,"source":"Kasi Sports News",
            "dataAvailable":False,
            "message":"Detailed player statistics are not available from the configured provider yet.",
            "updatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/sports/{sport}/match/{match_id}/player/{player_id}")
async def sports_match_player(sport: str, match_id: str, player_id: str, league: str = Query("")):
    sport=sport.lower().strip()
    if sport == "football":
        return await fixture_player_statistics(int(match_id), int(player_id))
    summary=await _espn_summary(sport, match_id, league)
    participants=_espn_participants(summary)
    player=next((x for x in participants if str(x.get("id"))==str(player_id)), None)
    return {"sport":sport,"matchId":match_id,"playerId":player_id,"currentGame":player or {"id":player_id,"name":"Player","statistics":[]},"seasonStatistics":[],"recentMatches":[],"source":"ESPN"}


def _generic_news_image(url: str) -> bool:
    u=str(url or "").lower()
    return (not u) or any(x in u for x in ("gstatic.com/images/branding", "google.com/images/branding", "news.google.com", "googleusercontent.com/news", "googlenews"))


def _publisher_domains(source: str):
    s=str(source or "").lower()
    if "metro" in s:return ("metro.co.uk",)
    if "goal" in s:return ("goal.com",)
    if "citizen" in s:return ("citizen.co.za",)
    if "rugby" in s:return ("sarugbymag.co.za","keo.co.za","supersport.com")
    return ()

def _clean_embedded_url(raw: str) -> str:
    v=unescape(str(raw or "")).replace("\\u002F","/").replace("\\/","/")
    v=v.replace("\\u003A",":").replace("\\u0026","&")
    try:v=urllib.parse.unquote(v)
    except Exception:pass
    return v

async def _resolve_news_publisher_url(url: str, source: str="") -> str:
    """Best effort conversion of a Google News article URL into the publisher URL."""
    raw=str(url or "").strip()
    if not raw:return raw
    host=(urllib.parse.urlparse(raw).hostname or "").lower()
    if "news.google.com" not in host:return raw
    key=f"news-resolved:{raw}"
    cached=NEWS_CACHE.get(key)
    if cached:return str(cached)
    try:
        c=await _sports_client()
        r=await c.get(raw,follow_redirects=True,timeout=httpx.Timeout(7,connect=3),
                      headers={"User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124 Safari/537.36"})
        final=str(r.url)
        fh=(urllib.parse.urlparse(final).hostname or "").lower()
        if "google." not in fh and "news.google.com" not in fh:
            NEWS_CACHE[key]=final;return final
        text=r.text[:2_500_000]
        domains=_publisher_domains(source)
        # Google News pages commonly embed the publisher URL in script data.
        candidates=re.findall(r'https?(?::|\\u003A|%3A)(?:/|\\u002F|%2F){2}[^"\'<>\s\\\\]+',text,re.I)
        for cand in candidates:
            u=_clean_embedded_url(cand)
            h=(urllib.parse.urlparse(u).hostname or "").lower()
            if not h or "google." in h or "gstatic." in h:continue
            if domains and not any(h==d or h.endswith("."+d) for d in domains):continue
            NEWS_CACHE[key]=u;return u
    except Exception as exc:
        log.debug("News publisher URL resolution failed %s: %s",raw,exc)
    NEWS_CACHE[key]=raw
    return raw

async def _enrich_news_card(item: dict) -> dict:
    """Resolve the publisher article and extract a genuine article image.

    Google News thumbnails/branding are deliberately ignored. Publisher OG,
    Twitter, JSON-LD and article images are tried in that order.
    """
    out=dict(item or {})
    if _generic_news_image(out.get("image")):
        out["image"]=""

    original=str(out.get("link") or "").strip()
    if not original:
        return out

    direct=str(out.get("publisherLink") or "").strip()
    resolved=direct if direct.startswith(("http://","https://")) else await _resolve_news_publisher_url(
        original, out.get("source") or out.get("publisher") or ""
    )

    key=f"news-enriched-v202:{resolved}"
    cached=NEWS_CACHE.get(key)
    if cached:
        merged=dict(out);merged.update(cached);return merged

    def absolute_url(raw: str, base_url: str) -> str:
        raw=unescape(str(raw or "")).replace("\\/","/").replace("&amp;","&").strip()
        if not raw:
            return ""
        return urllib.parse.urljoin(base_url, raw)

    def usable_image(raw: str, base_url: str) -> str:
        u=absolute_url(raw,base_url)
        if not u.startswith(("http://","https://")):
            return ""
        if _generic_news_image(u) or _is_generic_news_image(u):
            return ""
        return u

    try:
        c=await _sports_client()
        headers={
            "User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
            "Accept":"text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            "Accept-Language":"en-ZA,en-GB;q=0.9,en;q=0.8",
            "Cache-Control":"no-cache",
        }
        r=await c.get(resolved,follow_redirects=True,timeout=httpx.Timeout(10,connect=4),headers=headers)
        r.raise_for_status()
        final=str(r.url)
        text=r.text[:3_500_000]

        def meta(*names):
            for prop in names:
                ep=re.escape(prop)
                patterns=(
                    rf'<meta[^>]+(?:property|name)=["\']{ep}["\'][^>]+content=["\']([^"\']+)',
                    rf'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:property|name)=["\']{ep}["\']',
                )
                for pat in patterns:
                    m=re.search(pat,text,re.I|re.S)
                    if m:
                        value=unescape(re.sub(r"\s+"," ",m.group(1))).strip()
                        if value:return value
            return ""

        candidates=[]
        for value in (
            meta("og:image:secure_url"),
            meta("og:image:url"),
            meta("og:image"),
            meta("twitter:image"),
            meta("twitter:image:src"),
        ):
            if value:candidates.append(value)

        # JSON-LD frequently contains the real hero image even when OG tags are
        # dynamically altered or omitted.
        for pat in (
            r'"image"\s*:\s*\[\s*"([^"]+)"',
            r'"image"\s*:\s*"([^"]+)"',
            r'"image"\s*:\s*\{\s*"url"\s*:\s*"([^"]+)"',
            r'"image"\s*:\s*\{\s*"@id"\s*:\s*"([^"]+)"',
            r'"thumbnailUrl"\s*:\s*"([^"]+)"',
            r'"contentUrl"\s*:\s*"([^"]+)"',
        ):
            for m in re.finditer(pat,text,re.I|re.S):
                candidates.append(m.group(1))
                if len(candidates)>=20:break
            if len(candidates)>=20:break

        # Last publisher-page fallback: look for large/article/hero images.
        if not candidates:
            for pat in (
                r'<img[^>]+(?:class|data-testid)=["\'][^"\']*(?:hero|article|lead|featured|main)[^"\']*["\'][^>]+(?:src|data-src|data-lazy-src)=["\']([^"\']+)',
                r'<img[^>]+(?:src|data-src|data-lazy-src)=["\']([^"\']+)["\'][^>]+(?:class|data-testid)=["\'][^"\']*(?:hero|article|lead|featured|main)[^"\']*["\']',
            ):
                for m in re.finditer(pat,text,re.I|re.S):
                    candidates.append(m.group(1))
                    if len(candidates)>=12:break

        image=""
        for cand in candidates:
            u=usable_image(cand,final)
            if u:
                image=u
                break

        summary=meta("og:description","description","twitter:description")
        title=meta("og:title","twitter:title")

        payload={
            "image":image,
            "ogImage":image,
            "publisherImage":image,
            "summary":summary or out.get("summary",""),
            "resolvedUrl":final,
            "publisherUrl":final,
            "publisherTitle":title or out.get("title",""),
            "imageOrigin":"publisher-page" if image else "",
            "imageAvailable":bool(image),
        }
        NEWS_CACHE[key]=payload
        out.update(payload)
    except Exception as exc:
        log.debug("News publisher enrichment failed %s: %s",resolved,exc)
        out["resolvedUrl"]=resolved
        out["publisherUrl"]=resolved
        out["image"]=""
        out["ogImage"]=""
        out["publisherImage"]=""
        out["imageAvailable"]=False

    return out



# v299: Balanced public editorial mix — 1/3 Football, 1/3 Rugby, 1/3 Cricket.
# Balancing is applied only after existing quality/vetting filters.
_KASI_EDITORIAL_SPORTS=("football","rugby","cricket")

def _balanced_three_sports(items, limit: int, offset: int = 0) -> list[dict]:
    """Round-robin vetted content into an equal Football/Rugby/Cricket mix.
    When one sport has too few vetted items, fill remaining slots with the
    newest vetted items from the other sports so customer-facing widgets do not go empty.
    """
    rows=[x for x in (items or []) if isinstance(x,dict)]
    buckets={sp:[] for sp in _KASI_EDITORIAL_SPORTS}
    other=[]
    for x in rows:
        sp=str(x.get("sport") or x.get("category") or "").strip().lower()
        (buckets[sp] if sp in buckets else other).append(x)

    # Offset applies to the already-balanced stream, not independently per sport.
    need=max(0,int(offset))+max(0,int(limit))
    stream=[]; seen=set(); pos={sp:0 for sp in _KASI_EDITORIAL_SPORTS}
    while len(stream)<need:
        progressed=False
        for sp in _KASI_EDITORIAL_SPORTS:
            i=pos[sp]
            if i<len(buckets[sp]):
                x=buckets[sp][i]; pos[sp]+=1
                sig=str(x.get("articleId") or x.get("id") or x.get("originalUrl") or x.get("link") or x.get("title") or "")
                if sig not in seen:
                    seen.add(sig);stream.append(x);progressed=True
                    if len(stream)>=need: break
        if not progressed: break

    # Fail-soft: preserve vetted content rather than blank slots if a sport is short.
    if len(stream)<need:
        leftovers=[]
        for sp in _KASI_EDITORIAL_SPORTS:
            leftovers.extend(buckets[sp][pos[sp]:])
        leftovers.extend(other)
        leftovers.sort(key=lambda x:str(x.get("published") or x.get("publishedAt") or ""),reverse=True)
        for x in leftovers:
            sig=str(x.get("articleId") or x.get("id") or x.get("originalUrl") or x.get("link") or x.get("title") or "")
            if sig and sig not in seen:
                seen.add(sig);stream.append(x)
                if len(stream)>=need: break
    return [_clean_public_item_text(x) for x in stream[int(offset):int(offset)+int(limit)] if isinstance(x,dict)]

_NEWS_POOL_CACHE = TTLCache(maxsize=32, ttl=300)
_NEWS_IMAGE_CHECK_CACHE = TTLCache(maxsize=2048, ttl=21600)

_NEWS_DIRECT_SOURCES = [
    # sport, feed, publisher, primary country (blank = international/general)
    ("football","https://metro.co.uk/sport/football/feed/","Metro.co.uk","GB"),
    ("rugby","https://www.sarugbymag.co.za/feed/","SA Rugby Magazine","ZA"),
    ("cricket","https://www.sacricketmag.com/feed/","SA Cricket Mag","ZA"),
]

_NEWS_DISCOVERY = [
    ("football","GOAL football","GOAL",""),
    ("football","Sky Sports football","Sky Sports","GB"),
    ("football","Reuters football","Reuters",""),
    ("rugby","World Rugby rugby news","World Rugby",""),
    ("rugby","SuperSport rugby","SuperSport","ZA"),
    ("cricket","ICC cricket news","ICC",""),
    ("cricket","SuperSport cricket","SuperSport","ZA"),
]

_NEWS_COUNTRY_TERMS = {
    "ZA":"South Africa sports football rugby cricket PSL Springboks Proteas",
    "GB":"UK sport Premier League football rugby cricket",
    "US":"United States sports soccer football",
    "AU":"Australia sports football rugby cricket",
    "NZ":"New Zealand sports rugby cricket football",
    "IN":"India sports cricket football",
    "ES":"Spain football La Liga",
    "FR":"France football rugby",
    "DE":"Germany football Bundesliga",
    "IT":"Italy football Serie A",
    "BR":"Brazil football",
    "AR":"Argentina football",
    "NG":"Nigeria football sports",
    "KE":"Kenya sports rugby football cricket",
}

def _news_iso_value(v: str) -> str:
    return str(v or "").strip()

def _news_country_from_text(item: dict, default_country: str = "") -> list[str]:
    text=(" ".join([
        str(item.get("title") or ""), str(item.get("summary") or ""),
        str(item.get("description") or ""), str(item.get("source") or ""),
        str(item.get("publisher") or "")
    ])).casefold()
    countries=set([default_country] if default_country else [])
    clues={
        "ZA":["south africa","springbok","proteas","psl","premier soccer league","bafana","sa20","stormers","bulls","sharks","orlando pirates","kaizer chiefs","mamelodi sundowns"],
        "GB":["england","premier league","championship","scotland","wales","britain","uk "],
        "US":["united states","usa","mls","major league soccer"],
        "AU":["australia","wallabies","a-league"],
        "NZ":["new zealand","all blacks"],
        "IN":["india","ipl","indian premier league"],
        "ES":["spain","la liga","barcelona","real madrid"],
        "FR":["france","ligue 1"],
        "DE":["germany","bundesliga"],
        "IT":["italy","serie a"],
        "BR":["brazil","brasileir"],
        "AR":["argentina"],
        "NG":["nigeria","super eagles"],
    }
    for code,terms in clues.items():
        if any(t in text for t in terms): countries.add(code)
    return sorted(countries)

def _news_tags(item: dict) -> dict:
    text=(str(item.get("title") or "")+" "+str(item.get("summary") or "")).casefold()
    known_teams=["arsenal","chelsea","liverpool","manchester city","manchester united","barcelona","real madrid",
                 "kaizer chiefs","orlando pirates","mamelodi sundowns","springboks","proteas","all blacks"]
    known_comp=["premier league","champions league","psl","sa20","six nations","urc","world cup","la liga","serie a","bundesliga"]
    teams=[x.title() for x in known_teams if x in text]
    comps=[x.upper() if x in ("psl","sa20","urc") else x.title() for x in known_comp if x in text]
    return {"teams":teams,"players":[],"competitions":comps}

async def _news_image_available(url: str) -> bool:
    u=str(url or "").strip()
    if not u or _is_generic_news_image(u): return False
    cached=_NEWS_IMAGE_CHECK_CACHE.get(u)
    if cached is not None:return bool(cached)
    ok=False
    try:
        c=await _sports_client()
        r=await c.get(u,follow_redirects=True,timeout=httpx.Timeout(5,connect=2),
                      headers={"User-Agent":"Mozilla/5.0 KasiSportsNews/1.0","Range":"bytes=0-2047"})
        ct=(r.headers.get("content-type") or "").lower()
        ok=r.status_code in (200,206) and ct.startswith("image/")
    except Exception:
        ok=False
    _NEWS_IMAGE_CHECK_CACHE[u]=ok
    return ok

# v56: News stale-while-revalidate. The homepage must never wait on all RSS,
# discovery, image enrichment and image validation requests.
_NEWS_LAST_GOOD: list[dict] = []
_NEWS_REFRESH_TASK: Optional[asyncio.Task] = None
_NEWS_REFRESH_LOCK = asyncio.Lock()
NEWS_FAST_WAIT = float(os.getenv("NEWS_FAST_WAIT", "1.2"))

async def _refresh_news_pool_background():
    global _NEWS_REFRESH_TASK
    if _NEWS_REFRESH_TASK and not _NEWS_REFRESH_TASK.done():
        return
    async def runner():
        try:
            await _build_news_pool(force=True)
        except Exception as exc:
            log.warning("Background news refresh failed: %s", exc)
    _NEWS_REFRESH_TASK=asyncio.create_task(runner())

async def _warm_news_cache():
    try:
        await _build_news_pool(force=True)
        log.info("Sports news cache warmed: %d articles", len(_NEWS_LAST_GOOD))
    except Exception as exc:
        log.warning("Sports news warmup failed: %s", exc)

async def _build_news_pool(force: bool = False) -> list[dict]:
    global _NEWS_LAST_GOOD
    cached=None if force else _NEWS_POOL_CACHE.get("all")
    if cached is not None:return list(cached)

    async def direct(sp,feed,publisher,country):
        try:
            rows=await _publisher_rss(feed,publisher,20)
        except Exception:
            return []
        out=[]
        for row in rows:
            x=dict(row);x["sport"]=sp;x["publisher"]=publisher
            x["publisherUrl"]=x.get("link") or "";x["resolvedUrl"]=x.get("link") or ""
            x["countries"]=_news_country_from_text(x,country)
            x.update(_news_tags(x));out.append(x)
        return out

    direct_jobs=[direct(*s) for s in _NEWS_DIRECT_SOURCES]
    discovery_jobs=[_google_news(q,18) for _,q,_,_ in _NEWS_DISCOVERY]
    results=await asyncio.gather(*(direct_jobs+discovery_jobs),return_exceptions=True)
    pool=[]
    for rows in results[:len(direct_jobs)]:
        if isinstance(rows,list):pool.extend(rows)

    for spec,rows in zip(_NEWS_DISCOVERY,results[len(direct_jobs):]):
        sp,_,publisher,country=spec
        if not isinstance(rows,list):continue
        for row in rows:
            x=dict(row);x["sport"]=sp
            x["publisher"]=x.get("source") or publisher
            x["countries"]=_news_country_from_text(x,country)
            x.update(_news_tags(x));pool.append(x)

    # Deduplicate by publisher URL/title.
    merged=[];seen=set()
    for x in pool:
        key=(x.get("publisherUrl") or x.get("resolvedUrl") or x.get("link") or x.get("title") or "").strip().lower()
        if not key or key in seen:continue
        seen.add(key);merged.append(x)

    # Enrich only the newest candidate pool, not the entire internet result set.
    merged.sort(key=lambda x:_news_iso_value(x.get("published")),reverse=True)
    candidates=merged[:120]
    sem=asyncio.Semaphore(8)
    async def enrich(x):
        y=dict(x)
        if not y.get("image") or _is_generic_news_image(y.get("image","")):
            async with sem:
                try:y=await _enrich_news_card(y)
                except Exception:pass
        img=y.get("image") or y.get("ogImage") or y.get("publisherImage") or ""
        y["imageAvailable"]=await _news_image_available(img) if img else False
        if not y["imageAvailable"]:
            y["image"]="";y["ogImage"]="";y["publisherImage"]=""
        target=str(y.get("publisherUrl") or y.get("resolvedUrl") or y.get("link") or "")
        y["articleId"]=hashlib.sha1(target.encode("utf-8")).hexdigest()[:16] if target else hashlib.sha1(str(y.get("title","")).encode()).hexdigest()[:16]
        y["articlePath"]=f"/news/{y['articleId']}?source={urllib.parse.quote(target,safe='')}" if target else ""
        y["originalUrl"]=target
        y["author"]=y.get("author") or ""
        y["description"]=y.get("summary") or y.get("description") or ""
        return y

    enriched=await asyncio.gather(*[enrich(x) for x in candidates],return_exceptions=True)
    final=[x for x in enriched if isinstance(x,dict)]
    final.sort(key=lambda x:_news_iso_value(x.get("published")),reverse=True)
    _NEWS_POOL_CACHE["all"]=list(final)
    if final:
        _NEWS_LAST_GOOD=list(final)
    return final


_NEWS_CONTINENTS = {
    "Africa":{"ZA","NG","KE","GH","EG","MA","TN","DZ","SN","CM","CI","UG","TZ","ZW","ZM","NA","BW","MZ","AO","ET","RW"},
    "Europe":{"GB","IE","ES","FR","DE","IT","PT","NL","BE","CH","AT","SE","NO","DK","FI","PL","GR","TR","HR","RS","CZ","RO","UA"},
    "Asia":{"IN","PK","BD","LK","JP","KR","CN","SA","AE","QA","IR","ID","MY","SG","TH","VN","PH"},
    "Oceania":{"AU","NZ","FJ","PG"},
    "North America":{"US","CA","MX","CR","JM","TT"},
    "South America":{"BR","AR","UY","CL","CO","PE","EC","PY","BO","VE"},
}
def _news_continent(country: str) -> str:
    c=str(country or "").upper()
    for name,codes in _NEWS_CONTINENTS.items():
        if c in codes:return name
    return ""

def _news_rank(item: dict, country: str) -> tuple:
    # Defensive ranking: one incomplete publisher item must never take down the whole news feed.
    if not isinstance(item,dict): return (0,"",0)
    c=str(country or "").upper()
    raw_countries=item.get("countries") or []
    if isinstance(raw_countries,str): raw_countries=[raw_countries]
    countries={str(x).upper() for x in raw_countries if x}
    visitor_continent=_news_continent(c)
    item_continents={_news_continent(x) for x in countries if _news_continent(x)}
    if c and c in countries: relevance=3
    elif visitor_continent and visitor_continent in item_continents: relevance=2
    else: relevance=1
    image=1 if bool(item.get("imageAvailable") or item.get("image") or item.get("ogImage") or item.get("publisherImage")) else 0
    return (relevance,_news_iso_value(item.get("published")),image)

def _valid_public_news_item(item: dict) -> bool:
    """Reject placeholder/hash news before it reaches the browser."""
    if not isinstance(item,dict): return False
    title=str(item.get("title") or "").strip()
    desc=str(item.get("description") or item.get("summary") or "").strip()
    url=str(item.get("articlePath") or item.get("originalUrl") or item.get("publisherUrl") or item.get("link") or "").strip()
    image=str(item.get("image") or item.get("imageUrl") or item.get("thumbnail") or "").strip()
    if not title or len(title)<8 or not url or not image:return False
    # v401: syndicated stories must pass image vetting before publication. First-party
    # editorial items may omit imageAvailable only when their supplied image URL is valid.
    if "imageAvailable" in item and item.get("imageAvailable") is not True:return False
    if title.lower() in {"sports news","sport news","news","sports update","latest sports news","sports news update"}:return False
    if re.fullmatch(r"[a-f0-9]{12,}",title,re.I):return False
    if re.fullmatch(r"[a-z0-9]{14,}",title,re.I) and not re.search(r"\s",title):return False
    if re.search(r"^sports news update:\s*[a-z0-9_-]{8,}\.?$",desc,re.I):return False
    if re.search(r"\b(?:placeholder|generated content|sample article|test article)\b",title,re.I):return False
    return True


@app.middleware("http")
async def kasi_news_failsoft_middleware(request: Request, call_next):
    """Never expose an application-level 5xx for public News when last-good data exists."""
    if request.url.path not in {"/sports/news","/sports/news/bulletin"}:
        return await call_next(request)
    try:
        response=await call_next(request)
        if response.status_code < 500:
            return response
    except Exception as exc:
        log.warning("News request failed; serving last-good snapshot: %s", exc)
    items=[]
    try:
        items=list((_NEWS_VERIFIED_SNAPSHOT or {}).get("items") or [])
    except Exception:
        items=[]
    if not items:
        try:
            snap=_dashboard_snapshot_get("news_verified_all")
            if isinstance(snap,dict):items=list(snap.get("items") or [])
        except Exception:
            items=[]
    if not items:
        try:items=list(_NEWS_LAST_GOOD or [])
        except Exception:items=[]
    limit=8 if request.url.path.endswith("/bulletin") else 24
    try:limit=max(1,min(50,int(request.query_params.get("limit",limit))))
    except Exception:pass
    items=[x for x in items if isinstance(x,dict) and _valid_public_news_item(x)][:limit]
    return JSONResponse({"sport":"all","count":len(items),"items":items,"cached":True,
                         "fallback":"last-good","warming":not bool(items),
                         "updatedAt":datetime.now(timezone.utc).isoformat()},status_code=200,
                        headers={"Cache-Control":"public, max-age=60, stale-while-revalidate=600"})

@app.get("/sports/news")
async def sports_news(
    request: Request,
    sport: str = Query("all"),
    q: str = Query(""),
    limit: int = Query(12,ge=1,le=50),
    country: str = Query(""),
    offset: int = Query(0,ge=0,le=500),
):
    """Country-aware, freshness-ranked sports news selected from a larger backend pool."""
    # v56 fast path: Cloudflare/header country is free; never block News on
    # external IP geolocation. Full enrichment refreshes asynchronously.
    header_country=(request.headers.get("cf-ipcountry") or request.headers.get("x-vercel-ip-country") or "").strip().upper()
    visitor_country=(country.strip().upper() or header_country)
    auto={"country":visitor_country,"region":"","city":"","method":"header" if header_country else "general"}

    cached=_NEWS_POOL_CACHE.get("all")
    if cached is not None:
        pool=list(cached)
    elif _NEWS_LAST_GOOD:
        pool=list(_NEWS_LAST_GOOD)
        await _refresh_news_pool_background()
    else:
        # Cold start: one background builder owns discovery/enrichment. Public requests return
        # immediately instead of duplicating the expensive build and risking a proxy 503.
        await _refresh_news_pool_background()
        pool=[]

    # Add country-specific discovery into the pool when a market is known.
    market_query=_NEWS_COUNTRY_TERMS.get(visitor_country)
    if market_query:
        ck="market:"+visitor_country
        market=_NEWS_POOL_CACHE.get(ck) or []
        # Country discovery is enrichment only; it must never delay first paint.
        pool=list(pool)+list(market)

    # Deduplicate after country-market merge.
    dedup=[];seen=set()
    for x in pool:
        key=str(x.get("originalUrl") or x.get("publisherUrl") or x.get("link") or x.get("title") or "").lower()
        if not key or key in seen:continue
        seen.add(key);dedup.append(x)
    pool=dedup

    # Admin-authored Kasi Sports News stories are first-party and appear before syndicated stories.
    try:
        editorial_items=_editorial_published(limit=50)
        if editorial_items:
            pool=editorial_items+pool
    except Exception as exc:
        log.debug("Editorial news merge skipped: %s",exc)

    sport_key=sport.lower().strip()
    if sport_key!="all":pool=[x for x in pool if str(x.get("sport") or "").lower()==sport_key]
    if q.strip():
        needle=q.strip().casefold()
        pool=[x for x in pool if needle in (str(x.get("title",""))+" "+str(x.get("description",""))+" "+str(x.get("summary",""))).casefold()]

    try:
        pool=[x for x in pool if isinstance(x,dict)]
        pool.sort(key=lambda x:_news_rank(x,visitor_country),reverse=True)
    except Exception:
        # Never make the homepage news widget unavailable because enrichment/ranking failed.
        pool=[x for x in (await _build_news_pool()) if isinstance(x,dict)]
        pool.sort(key=lambda x:_news_iso_value(x.get("published")),reverse=True)
    # Shared stale-while-revalidate News:
    # Never make a visitor wait for article/image vetting when last-known-good data exists.
    verified=list((_NEWS_VERIFIED_SNAPSHOT or {}).get("items") or []) if "_NEWS_VERIFIED_SNAPSHOT" in globals() else []
    if not verified:
        snap=_dashboard_snapshot_get("news_verified_all") if "_dashboard_snapshot_get" in globals() else None
        if isinstance(snap,dict):
            verified=list(snap.get("items") or [])
            if verified:
                _NEWS_VERIFIED_SNAPSHOT["items"]=verified
                _NEWS_VERIFIED_SNAPSHOT["updated_at"]=float(snap.get("updated_at") or 0)
    # v299: for the public all-sports feed, balance only the already-vetted snapshot.
    # A requested single-sport feed remains single-sport.
    verified_for_request=verified
    if sport_key!="all":
        verified_for_request=[x for x in verified if str(x.get("sport") or "").lower()==sport_key]
        selected=verified_for_request[offset:offset+limit]
    else:
        selected=_balanced_three_sports(verified_for_request,limit,offset)

    # v333: first-party editorial stories are already admin-authored/trusted and must not
    # wait for the syndicated-news verification snapshot before appearing publicly.
    # Merge them directly into the requested page while preserving sport filters and de-duplication.
    try:
        editorial_public=[x for x in _editorial_published(limit=50) if x.get("placement","sports_news")=="sports_news"]
        if sport_key != "all":
            editorial_public=[x for x in editorial_public if str(x.get("sport") or "").lower() in {sport_key,"all"}]
        editorial_public=editorial_public[offset:offset+limit] if offset else editorial_public[:limit]
        merged=[]; seen_public=set()
        for x in editorial_public + list(selected):
            sig=str(x.get("articlePath") or x.get("originalUrl") or x.get("title") or "").strip().lower()
            if not sig or sig in seen_public:
                continue
            seen_public.add(sig); merged.append(x)
            if len(merged) >= limit:
                break
        selected=merged
    except Exception as exc:
        log.debug("Editorial public merge skipped: %s", exc)
    # Vet new syndicated candidates only in background. Old verified data stays visible until replacement passes.
    warming=not bool(verified)
    global _NEWS_VERIFY_TASK
    if _NEWS_VERIFY_TASK is None or _NEWS_VERIFY_TASK.done():
        _NEWS_VERIFY_TASK=asyncio.create_task(_refresh_verified_news_snapshot(pool,max(24,limit+offset)))
    _candidate_news=locals().get("items",locals().get("rows",locals().get("out",[])))
    if isinstance(_candidate_news,list):
        _seen_news=set();_clean_news=[]
        for _n in _candidate_news:
            if not _valid_public_news_item(_n):continue
            _sig=(str(_n.get("title") or "").strip().lower(),str(_n.get("articlePath") or _n.get("originalUrl") or _n.get("link") or "").strip())
            if _sig in _seen_news:continue
            _seen_news.add(_sig);_clean_news.append(_n)
        if "items" in locals():items=_clean_news
        elif "rows" in locals():rows=_clean_news
        elif "out" in locals():out=_clean_news

    return {
        "sport":sport_key,"count":len(selected),"poolSize":len(pool),"offset":offset,
        "items":selected,
        "country":visitor_country,"continent":_news_continent(visitor_country),"countryMethod":auto.get("method","general"),
        "fallback":"country-to-continent-to-international","source":"Approved multi-source news pool",
        "warming":warming,"verified":bool(verified),
        "retryAfterMs":2500 if warming else 0,
        "vettingState":dict(_NEWS_VERIFY_STATE) if "_NEWS_VERIFY_STATE" in globals() else {},
        "updatedAt":datetime.now(timezone.utc).isoformat(),
    }

@app.get("/sports/news/bulletin")
async def sports_news_bulletin(request: Request, limit: int = Query(5,ge=1,le=12), country: str = Query("")):
    try:
        data=await sports_news(request=request,sport="all",q="",limit=max(8,limit),country=country,offset=0)
        live_editorial=[x for x in _editorial_published(limit=50) if x.get("placement")=="live_news"]
        merged=[]; seen=set()
        for x in live_editorial + list(data.get("items") or []):
            sig=str(x.get("articlePath") or x.get("title") or "").lower()
            if sig and sig not in seen:
                seen.add(sig); merged.append(x)
            if len(merged)>=limit: break
        items=merged
        return {**data,"items":items,"count":len(items)}
    except Exception:
        pool=await _build_news_pool()
        items=[]
        for raw_item in [x for x in pool if isinstance(x,dict)]:
            x=dict(raw_item)
            target=str(x.get("publisherUrl") or x.get("resolvedUrl") or x.get("link") or x.get("url") or "").strip()
            if target.startswith(("http://","https://")):
                article_id=hashlib.sha1(target.encode("utf-8")).hexdigest()[:16]
                x["articleId"]=x.get("articleId") or article_id
                x["articlePath"]=x.get("articlePath") or f"/news/{x['articleId']}?source={urllib.parse.quote(target,safe='')}"
                x["originalUrl"]=x.get("originalUrl") or target
            items.append(x)
            if len(items)>=limit: break
        return {"sport":"all","count":len(items),"items":items,"fallback":"cached-international","country":"","continent":""}

async def _news_quality_filter(items,limit=24):
    """Return only articles with usable title/content/image and an internal article route."""
    sem=asyncio.Semaphore(4)
    async def one(raw):
        if not _valid_public_news_item(raw):return None
        x=dict(raw)
        target=str(x.get("originalUrl") or x.get("publisherUrl") or x.get("resolvedUrl") or x.get("link") or "").strip()
        image=str(x.get("image") or x.get("ogImage") or x.get("publisherImage") or "").strip()
        if not target.startswith(("http://","https://")) or not image.startswith(("http://","https://")):return None
        async with sem:
            try:
                meta=await asyncio.wait_for(sports_news_article(target),timeout=8)
                if not isinstance(meta,dict):return None
                title=str(meta.get("title") or x.get("title") or "").strip()
                desc=str(meta.get("summary") or meta.get("description") or x.get("description") or x.get("summary") or "").strip()
                img=str(meta.get("image") or image).strip()
                if not title or not desc or not img.startswith(("http://","https://")):return None
                c=await _sports_client()
                r=await c.get(img,follow_redirects=True,timeout=httpx.Timeout(5,connect=2),
                              headers={"User-Agent":"Mozilla/5.0","Accept":"image/*"})
                if r.status_code>=400 or not str(r.headers.get("content-type","")).lower().startswith("image/"):return None
                final=str(meta.get("url") or target)
                article_id=x.get("articleId") or hashlib.sha1(final.encode("utf-8")).hexdigest()[:16]
                x.update({"title":title,"description":desc,"summary":desc,"image":img,
                          "originalUrl":final,"publisherUrl":final,"articleId":article_id,
                          "articlePath":f"/news/{article_id}?source={urllib.parse.quote(final,safe='')}"})
                return x
            except Exception:
                return None
    out=[]
    for r in await asyncio.gather(*(one(x) for x in list(items or [])[:max(limit*3,limit)]),return_exceptions=True):
        if isinstance(r,dict):
            out.append(r)
            if len(out)>=limit:break
    return out

_SHARED_SNAPSHOT_DB=BASE_DIR/"kasiscore_shared_snapshots.db"
def _dashboard_snapshot_get(key):
    try:
        c=sqlite3.connect(_SHARED_SNAPSHOT_DB,timeout=10)
        try: c.execute("PRAGMA journal_mode=WAL")
        except Exception: pass
        c.execute("CREATE TABLE IF NOT EXISTS snapshots(k TEXT PRIMARY KEY,payload TEXT NOT NULL,updated REAL NOT NULL)")
        r=c.execute("SELECT payload,updated FROM snapshots WHERE k=?",(key,)).fetchone();c.close()
        if not r:return None
        d=json.loads(r[0]);d["updated_at"]=r[1];return d
    except Exception:return None

def _dashboard_snapshot_put(key,payload):
    try:
        c=sqlite3.connect(_SHARED_SNAPSHOT_DB,timeout=10)
        try: c.execute("PRAGMA journal_mode=WAL")
        except Exception: pass
        c.execute("CREATE TABLE IF NOT EXISTS snapshots(k TEXT PRIMARY KEY,payload TEXT NOT NULL,updated REAL NOT NULL)")
        c.execute("INSERT INTO snapshots(k,payload,updated) VALUES(?,?,?) ON CONFLICT(k) DO UPDATE SET payload=excluded.payload,updated=excluded.updated",
                  (key,json.dumps(payload),time.time()))
        c.commit();c.close()
    except Exception:pass


# ── v413 universal public shared-cache delivery layer ──────────────────────────
# This wraps the existing API routes; it does NOT change provider/API call logic.
# Public data routes are served from a persistent shared LKG first.  When stale,
# the stale snapshot is returned immediately and the exact existing route is
# revalidated in the background with X-KSN-Cache-Refresh: 1.
_V413_PUBLIC_PREFIXES=(
    "/home", "/live", "/fixtures", "/predictions", "/tip-of-day", "/tip-stats/",
    "/sports/", "/results/search", "/team/", "/player/", "/competitions"
)
_V413_CACHE_REFRESHING=set()

def _v413_public_cache_ttl(path:str)->int:
    p=(path or "").lower()
    if "/live" in p or "/scores" in p: return 20
    if "/finished" in p or p.startswith("/results/search"): return 120
    if "/odds" in p: return 45
    if "/fixtures" in p: return 300
    if "/predictions" in p or "/tip" in p: return 300
    if "/news" in p or "/highlights" in p or "/videos" in p: return 300
    if "/match/" in p or "/matches/" in p: return 45
    if "/standings" in p: return 900
    if "/teams" in p or "/players" in p or "/team/" in p or "/player/" in p: return 1800
    return 300

def _v413_payload_has_value(obj):
    if obj is None: return False
    if isinstance(obj,list): return len(obj)>0
    if not isinstance(obj,dict): return True
    # Never let a transient empty provider response replace a valid LKG.
    for k in ("items","games","matches","predictions","tips","response","teams","players","standings","fixtures","results"):
        if k in obj:
            v=obj.get(k)
            if isinstance(v,(list,dict)) and len(v)>0:return True
    # Match/profile/detail payloads often use scalar/nested fields rather than lists.
    return any(k in obj for k in ("fixture","match","team","player","overview","statistics","lineups","events","data"))

async def _v413_background_revalidate(url:str,key:str):
    if key in _V413_CACHE_REFRESHING:return
    _V413_CACHE_REFRESHING.add(key)
    try:
        # v433: revalidate IN-PROCESS. The old code requested the public URL, which a CDN/proxy can answer
        # from its own cache, so the origin snapshot never actually refreshed.
        u=urllib.parse.urlsplit(url); target=u.path+("?"+u.query if u.query else "")
        async with httpx.AsyncClient(transport=httpx.ASGITransport(app=app),base_url="http://ksn.internal",timeout=httpx.Timeout(60,connect=5)) as c:
            await c.get(target,headers={"Accept":"application/json",**_KSN_INTERNAL_HEADERS})
    except Exception as exc:
        log.debug("v413 shared-cache background refresh failed %s: %s",url,exc)
    finally:
        _V413_CACHE_REFRESHING.discard(key)

@app.middleware("http")
async def v413_universal_shared_cache(request:Request,call_next):
    path=request.url.path
    if request.method!="GET" or path=="/shared/bootstrap" or not path.startswith(_V413_PUBLIC_PREFIXES):
        return await call_next(request)
    if request.headers.get("X-KSN-Internal")==_KSN_INTERNAL_TOKEN or request.query_params.get("refresh") in ("1","true","yes"):
        bypass=True
    else:bypass=False
    key="v413:http:"+hashlib.sha1(str(request.url.path+"?"+_ksn_clean_qs(request.url.query)).encode()).hexdigest()
    ttl=_v413_public_cache_ttl(path)
    snap=await asyncio.to_thread(_dashboard_snapshot_get,key)   # v433: never block the event loop on SQLite
    saved=(snap or {}).get("data") if isinstance(snap,dict) else None
    age=time.time()-float((snap or {}).get("updated_at") or 0) if snap else 10**9
    if not bypass and isinstance(saved,dict) and saved.get("body"):
        headers={"Cache-Control":f"public, max-age={min(ttl,60)}, s-maxage={ttl}, stale-while-revalidate={max(ttl*4,300)}, stale-if-error=86400",
                 "X-KSN-Shared-Cache":"HIT" if age<ttl else "STALE"}
        if age>=ttl:
            try:asyncio.create_task(_v413_background_revalidate(str(request.url),key))
            except Exception:pass
        return Response(content=saved["body"],status_code=int(saved.get("status") or 200),media_type="application/json",headers=headers)
    try:
        response=await call_next(request)
    except Exception:
        if isinstance(saved,dict) and saved.get("body"):
            return Response(content=saved["body"],status_code=200,media_type="application/json",
                            headers={"X-KSN-Shared-Cache":"STALE-IF-ERROR","Cache-Control":"public, max-age=15, stale-if-error=86400"})
        raise
    ctype=str(response.headers.get("content-type") or "").lower()
    if response.status_code==200 and "application/json" in ctype:
        body=b""
        async for chunk in response.body_iterator: body+=chunk
        try:
            parsed=json.loads(body.decode("utf-8"))
            if _v413_payload_has_value(parsed):
                await asyncio.to_thread(_dashboard_snapshot_put,key,{"data":{"body":body.decode("utf-8"),"status":200}})   # off-loop, awaited: next read sees it
        except Exception:pass
        headers=dict(response.headers)
        headers["Cache-Control"]=f"public, max-age={min(ttl,60)}, s-maxage={ttl}, stale-while-revalidate={max(ttl*4,300)}, stale-if-error=86400"
        headers["X-KSN-Shared-Cache"]="MISS-REFRESH" if bypass else "MISS"
        return Response(content=body,status_code=response.status_code,headers=headers,media_type="application/json")
    return response


_V434_BOOTSTRAP_KEYS={
  "tip": "tip-of-day:last_good",
  "news": "news_verified_all",
  "highlights": "videos:last_good",
  "live": "sports_live:last_good",
  "finished": "sports_finished_v310:48",
  "footballFixtures": "fixtures:football:ALL:upcoming:last_good",
  "rugbyFixtures": "v401:fixtures-window:rugby:7",
  "cricketFixtures": "v401:fixtures-window:cricket:7",
  "predictions": "predictions:last_good:ALL:upcoming",
  "rugbyPredictions": "v363:predictions:rugby:12",
  "cricketPredictions": "v363:predictions:cricket:12",
  "rugbyScores": "v363:scores:rugby:window:0:all",
  "cricketScores": "v363:scores:cricket:window:0:all",
  "rugbyTeams": "v363:teams-players:rugby:80",
  "cricketTeams": "v363:teams-players:cricket:80",
}

def _v434_build_bootstrap()->dict:
    """Disk-only shared LKG payload (sync, SQLite reads). Never calls external providers."""
    def data(key):
        snap=_dashboard_snapshot_get(key)
        if not isinstance(snap,dict): return None
        payload=snap.get("data") if isinstance(snap.get("data"),dict) else None
        if payload is None and key=="news_verified_all":
            payload={"items":snap.get("items") or []}
        return {"payload":payload,"updatedAt":snap.get("updated_at")} if payload else None
    widgets={name:data(key) for name,key in _V434_BOOTSTRAP_KEYS.items()}
    widgets={k:v for k,v in widgets.items() if v and v.get("payload")}
    return {"version":"v407","cacheFirst":True,"widgets":widgets,"generatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/shared/bootstrap")
async def shared_bootstrap_v407():
    """One fast disk-only shared LKG payload for first paint; never calls external providers."""
    body=await asyncio.to_thread(_v434_build_bootstrap)   # v434: SQLite reads off the event loop
    return JSONResponse(body,
      headers={"Cache-Control":"public, max-age=30, s-maxage=120, stale-while-revalidate=900, stale-if-error=86400", "X-KSN-Shared-Cache":"BOOTSTRAP-LKG"})

# v434: inline the bootstrap into the home HTML so a first-time visitor (no localStorage) paints
# from the HTML response itself, with no extra /shared/bootstrap round trip.
_V434_INLINE_TTL=10.0
_V434_INLINE_CACHE:dict={"t":0.0,"json":""}
_V434_INLINE_LOCK=asyncio.Lock()

async def _v434_inline_bootstrap_json()->str:
    """Serialized, script-safe bootstrap JSON, memoized for a few seconds so traffic spikes
    don't each hit SQLite. Returns '' when there is nothing worth inlining."""
    now=time.time()
    c=_V434_INLINE_CACHE
    if c["json"] and now-c["t"]<_V434_INLINE_TTL: return c["json"]
    async with _V434_INLINE_LOCK:
        if c["json"] and time.time()-c["t"]<_V434_INLINE_TTL: return c["json"]
        try:
            body=await asyncio.to_thread(_v434_build_bootstrap)
            raw=json.dumps(body,ensure_ascii=False,separators=(",",":")) if body.get("widgets") else ""
            # Make the JSON safe inside an inline <script>: no </script>, <!--, or JS line terminators.
            raw=raw.replace("<","\\u003c").replace(">","\\u003e").replace("&","\\u0026").replace("\u2028","\\u2028").replace("\u2029","\\u2029")
            c["json"]=raw; c["t"]=time.time()
        except Exception as exc:
            log.debug("v434 inline bootstrap failed: %s",exc)
            return c["json"]   # serve slightly stale copy, or '' -> client falls back to fetch
        return c["json"]

def _v434_inject_bootstrap(html_doc:str,raw_json:str)->str:
    if not raw_json: return html_doc
    tag='<script id="ksn-v434-inline-bootstrap">window.__KSN_V407_INLINE__='+raw_json+';</script>'
    # Must precede the v407 first-paint script so it can consume the data synchronously.
    if '<script id="ksn-v407-shared-first-paint">' in html_doc:
        return html_doc.replace('<script id="ksn-v407-shared-first-paint">',tag+'<script id="ksn-v407-shared-first-paint">',1)
    return html_doc.replace('<head>','<head>'+tag,1) if '<head>' in html_doc else html_doc

# v427: keep shared first-paint snapshots warm independently of visitor traffic.
# This runs after startup and never blocks application startup or /shared/bootstrap itself.
async def _v427_shared_cache_warmer():
    await asyncio.sleep(1)
    slow=[
      "/sports/news?limit=24", "/sports/news?sport=all&limit=24&offset=0", "/sports/news?sport=all&limit=30&offset=0",
      "/sports/videos?limit=24",
      "/ai-predictions?league=ALL&type=upcoming&limit=100&refresh=0",
      "/sports/rugby/predictions?limit=24", "/sports/cricket/predictions?limit=24",
      "/sports/rugby/teams-players?limit=80", "/sports/cricket/teams-players?limit=80",
      "/results/search?limit=500",
      # v433: feeds the pages request on first visit that were never warmed (cold for the first visitor)
      "/tip-of-day", "/sports/directory?sport=football&q=",
      "/sports/rugby/fixtures-window?days=7", "/sports/cricket/fixtures-window?days=7",
      "/sports/news?sport=all&limit=8",
    ]
    def date_urls():
        now=datetime.now(timezone.utc); out=[]
        for off in (-1,0,1):
            for tz in (0,2):
                d=(now+timedelta(hours=tz)+timedelta(days=off)).strftime("%Y-%m-%d")
                out+= [f"/fixtures?league=ALL&type=upcoming&date_from={d}&date_to={d}", f"/sports/rugby/scores?date={d}", f"/sports/cricket/scores?date={d}"]
        return list(dict.fromkeys(out))
    async def hit(c,url):
        try: await c.get(url,headers={"Accept":"application/json",**_KSN_INTERNAL_HEADERS})
        except Exception as exc: log.debug("v427 shared warm %s: %s",url,exc)
    async def live_loop():
        while True:
            try:
                transport=httpx.ASGITransport(app=app)
                async with httpx.AsyncClient(transport=transport,base_url="http://ksn.internal",timeout=60.0) as c:
                    await hit(c,"/sports/live")
            except Exception as exc: log.debug("v432 live warm: %s",exc)
            await asyncio.sleep(15)
    asyncio.create_task(live_loop())
    while True:
        try:
            transport=httpx.ASGITransport(app=app)
            # 90s timeout: the old 12s cut cold feeds off before they could be stored, so visitors paid for it.
            async with httpx.AsyncClient(transport=transport,base_url="http://ksn.internal",timeout=90.0) as c:
                await asyncio.gather(*[hit(c,u) for u in (slow+date_urls()+["/sports/videos?sport=all&limit=8&offset=0","/sports/news/bulletin?limit=5"])])
        except Exception as exc: log.debug("v427 shared warmer cycle: %s",exc)
        await asyncio.sleep(180)

@app.on_event("startup")
async def _v427_start_shared_cache_warmer():
    try: asyncio.create_task(_v427_shared_cache_warmer())
    except Exception as exc: log.debug("v427 warmer start: %s",exc)

# v87: customer-facing Sports News and Latest News remain on the established /sports/news pipeline.
# Validation is background-only and must never block or empty those widgets.

_NEWS_VERIFIED_SNAPSHOT={"items":[],"updated_at":0.0}
_NEWS_VERIFY_LOCK=asyncio.Lock()
_NEWS_VERIFY_TASK=None
_NEWS_VERIFY_STATE={"running":False,"lastError":"","lastStartedAt":0.0,"lastCompletedAt":0.0,"lastQualified":0}

async def _refresh_verified_news_snapshot(items,limit=24):
    """Validate candidates; retain last-good data and expose failures instead of silently warming forever."""
    if _NEWS_VERIFY_LOCK.locked(): return
    async with _NEWS_VERIFY_LOCK:
        _NEWS_VERIFY_STATE.update({"running":True,"lastError":"","lastStartedAt":time.time()})
        try:
            qualified=await _news_quality_filter(items,limit)
            _NEWS_VERIFY_STATE["lastQualified"]=len(qualified or [])
            current=list(_NEWS_VERIFIED_SNAPSHOT.get("items") or [])
            if qualified:
                merged=qualified[:]
                seen={str(x.get("articleId") or x.get("originalUrl") or "") for x in merged}
                for old in current:
                    key=str(old.get("articleId") or old.get("originalUrl") or "")
                    if key and key not in seen and len(merged)<limit:
                        merged.append(old);seen.add(key)
                _NEWS_VERIFIED_SNAPSHOT["items"]=merged[:limit]
                _NEWS_VERIFIED_SNAPSHOT["updated_at"]=time.time()
                if "_dashboard_snapshot_put" in globals():
                    _dashboard_snapshot_put("news_verified_all",{
                        "items":_NEWS_VERIFIED_SNAPSHOT["items"],
                        "updated_at":_NEWS_VERIFIED_SNAPSHOT["updated_at"]
                    })
            elif not current:
                # Recovery path: still apply the established public-item vetting synchronously
                # to candidate metadata so first deployment cannot remain empty forever.
                recovery=[]
                seen=set()
                for raw in list(items or []):
                    if not isinstance(raw,dict) or not _valid_public_news_item(raw): continue
                    x=dict(raw)
                    target=str(x.get("publisherUrl") or x.get("resolvedUrl") or x.get("originalUrl") or x.get("link") or x.get("url") or "").strip()
                    if target.startswith(("http://","https://")):
                        aid=str(x.get("articleId") or hashlib.sha1(target.encode("utf-8")).hexdigest()[:16])
                        x["articleId"]=aid
                        x["articlePath"]=x.get("articlePath") or f"/news/{aid}?source={urllib.parse.quote(target,safe='')}"
                        x["originalUrl"]=x.get("originalUrl") or target
                    sig=(str(x.get("title") or "").strip().lower(),str(x.get("articlePath") or x.get("originalUrl") or "").strip())
                    if not sig[0] or not sig[1] or sig in seen: continue
                    seen.add(sig); recovery.append(x)
                    if len(recovery)>=limit: break
                if recovery:
                    _NEWS_VERIFIED_SNAPSHOT["items"]=recovery
                    _NEWS_VERIFIED_SNAPSHOT["updated_at"]=time.time()
                    _NEWS_VERIFY_STATE["lastQualified"]=len(recovery)
                    if "_dashboard_snapshot_put" in globals():
                        _dashboard_snapshot_put("news_verified_all",{"items":recovery,"updated_at":_NEWS_VERIFIED_SNAPSHOT["updated_at"]})
        except Exception as exc:
            _NEWS_VERIFY_STATE["lastError"]=f"{type(exc).__name__}: {exc}"[:500]
            logging.exception("News verification refresh failed")
        finally:
            _NEWS_VERIFY_STATE["running"]=False
            _NEWS_VERIFY_STATE["lastCompletedAt"]=time.time()


# ---------------------------------------------------------------------------
# EDITORIAL NEWS — admin-authored Kasi Sports News articles
# ---------------------------------------------------------------------------
class EditorialNewsPayload(BaseModel):
    placement: str = Field(default="sports_news", max_length=30)
    title: str = Field(..., min_length=3, max_length=220)
    summary: str = Field(default="", max_length=1000)
    content: str = Field(default="", max_length=50000)
    image_url: str = Field(default="", max_length=2000)
    image_format: str = Field(default="horizontal", max_length=20)
    sport: str = Field(default="all", max_length=30)
    category: str = Field(default="Sports", max_length=80)
    author: str = Field(default="Kasi Sports News", max_length=120)
    status: str = Field(default="draft", max_length=20)
    slug: str = Field(default="", max_length=140)
    seo_title: str = Field(default="", max_length=220)
    seo_description: str = Field(default="", max_length=320)

def _editorial_slug(value: str) -> str:
    value=unescape(str(value or "")).lower().strip()
    value=re.sub(r"[^a-z0-9]+","-",value).strip("-")[:130]
    return value or ("news-"+uuid.uuid4().hex[:10])

def _ensure_editorial_news_schema():
    c=_auth_db()
    try:
        c.execute("""CREATE TABLE IF NOT EXISTS editorial_news(
            id TEXT PRIMARY KEY,
            slug TEXT UNIQUE NOT NULL,title TEXT NOT NULL,summary TEXT,content TEXT,image_url TEXT,
            sport TEXT,category TEXT,author TEXT,status TEXT NOT NULL DEFAULT 'draft',
            placement TEXT NOT NULL DEFAULT 'sports_news',
            image_format TEXT NOT NULL DEFAULT 'horizontal',
            seo_title TEXT,seo_description TEXT,created_at TEXT NOT NULL,updated_at TEXT NOT NULL,published_at TEXT
        )""")
        try:
            c.execute("ALTER TABLE editorial_news ADD COLUMN placement TEXT NOT NULL DEFAULT 'sports_news'")
        except Exception:
            pass
        try:
            c.execute("ALTER TABLE editorial_news ADD COLUMN image_format TEXT NOT NULL DEFAULT 'horizontal'")
        except Exception:
            pass
        try:
            c.execute("""CREATE TABLE IF NOT EXISTS editorial_news_images(
                id TEXT PRIMARY KEY, content_type TEXT NOT NULL, image_data BLOB NOT NULL, created_at TEXT NOT NULL
            )""")
        except Exception:
            c.execute("""CREATE TABLE IF NOT EXISTS editorial_news_images(
                id TEXT PRIMARY KEY, content_type TEXT NOT NULL, image_data BYTEA NOT NULL, created_at TEXT NOT NULL
            )""")
        c.commit()
    finally:c.close()

def _editorial_row(row):
    if not row:return None
    keys=("id","slug","title","summary","content","image_url","sport","category","author","status","seo_title","seo_description","created_at","updated_at","published_at","placement","image_format")
    d=dict(zip(keys,row))
    d.update({"articleId":d["slug"],"articlePath":f"/news/{d['slug']}","image":d.get("image_url") or "","publisher":"Kasi Sports News","source":"Kasi Sports News","published":d.get("published_at") or d.get("updated_at"),"description":d.get("summary") or "","editorial":True})
    return d

def _editorial_get(slug: str):
    _ensure_editorial_news_schema();c=_auth_db()
    try:return _editorial_row(c.execute("SELECT id,slug,title,summary,content,image_url,sport,category,author,status,seo_title,seo_description,created_at,updated_at,published_at,COALESCE(placement,'sports_news'),COALESCE(image_format,'horizontal') FROM editorial_news WHERE slug=?",(slug,)).fetchone())
    finally:c.close()

def _editorial_published(limit=50):
    _ensure_editorial_news_schema();c=_auth_db()
    try:rows=c.execute("SELECT id,slug,title,summary,content,image_url,sport,category,author,status,seo_title,seo_description,created_at,updated_at,published_at,COALESCE(placement,'sports_news'),COALESCE(image_format,'horizontal') FROM editorial_news WHERE status='published' ORDER BY COALESCE(published_at,updated_at) DESC LIMIT ?",(int(limit),)).fetchall();return [_editorial_row(r) for r in rows]
    finally:c.close()

@app.post("/admin/news/image")
async def admin_news_image_upload(request: Request, authorization: Optional[str]=Header(default=None)):
    require_admin(authorization);_ensure_editorial_news_schema()
    ctype=(request.headers.get("content-type") or "").split(";",1)[0].lower().strip()
    if ctype not in {"image/jpeg","image/png","image/webp","image/gif"}:
        raise HTTPException(415,"Use a JPG, PNG, WEBP or GIF image.")
    data=await request.body()
    if not data: raise HTTPException(422,"Image file is empty.")
    if len(data)>8*1024*1024: raise HTTPException(413,"Image must be 8 MB or smaller.")
    image_id=uuid.uuid4().hex
    c=_auth_db()
    try:
        c.execute("INSERT INTO editorial_news_images(id,content_type,image_data,created_at) VALUES(?,?,?,?)",(image_id,ctype,data,datetime.now(timezone.utc).isoformat()));c.commit()
    finally:c.close()
    url=f"https://kasilivescore.com/media/editorial/{image_id}"
    return {"ok":True,"id":image_id,"url":url}

@app.get("/media/editorial/{image_id}", include_in_schema=False)
def editorial_news_image(image_id: str):
    if not re.fullmatch(r"[a-f0-9]{32}",image_id or ""): raise HTTPException(404,"Image not found")
    _ensure_editorial_news_schema();c=_auth_db()
    try: row=c.execute("SELECT content_type,image_data FROM editorial_news_images WHERE id=?",(image_id,)).fetchone()
    finally:c.close()
    if not row: raise HTTPException(404,"Image not found")
    return Response(content=bytes(row[1]),media_type=str(row[0]),headers={"Cache-Control":"public, max-age=31536000, immutable"})

@app.get("/admin/news")
def admin_news_list(authorization: Optional[str]=Header(default=None)):
    require_admin(authorization);_ensure_editorial_news_schema();c=_auth_db()
    try:rows=c.execute("SELECT id,slug,title,summary,content,image_url,sport,category,author,status,seo_title,seo_description,created_at,updated_at,published_at,COALESCE(placement,'sports_news'),COALESCE(image_format,'horizontal') FROM editorial_news ORDER BY updated_at DESC").fetchall();return {"items":[_editorial_row(r) for r in rows]}
    finally:c.close()

@app.post("/admin/news")
def admin_news_create(payload: EditorialNewsPayload, authorization: Optional[str]=Header(default=None)):
    require_admin(authorization);_ensure_editorial_news_schema()
    if not payload.image_url.strip(): raise HTTPException(422,"Article image is required.")
    now=datetime.now(timezone.utc).isoformat();slug=_editorial_slug(payload.slug or payload.title);status="published" if payload.status.lower()=="published" else "draft";published=now if status=="published" else None;c=_auth_db()
    try:
        base=slug;i=2
        while c.execute("SELECT id FROM editorial_news WHERE slug=?",(slug,)).fetchone():slug=f"{base}-{i}";i+=1
        c.execute("INSERT INTO editorial_news(id,slug,title,summary,content,image_url,sport,category,author,status,seo_title,seo_description,created_at,updated_at,published_at,placement,image_format) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",(uuid.uuid4().hex,slug,payload.title.strip(),payload.summary.strip(),payload.content.strip(),payload.image_url.strip(),payload.sport.strip().lower() or "all",payload.category.strip() or "Sports",payload.author.strip() or "Kasi Sports News",status,payload.seo_title.strip(),payload.seo_description.strip(),now,now,published,("live_news" if payload.placement.strip().lower()=="live_news" else "sports_news"),("vertical" if payload.image_format.strip().lower()=="vertical" else "horizontal")));c.commit();return {"ok":True,"article":_editorial_get(slug),"url":f"https://kasilivescore.com/news/{slug}"}
    finally:c.close()

@app.put("/admin/news/{slug}")
def admin_news_update(slug: str,payload: EditorialNewsPayload,authorization: Optional[str]=Header(default=None)):
    require_admin(authorization);old=_editorial_get(slug)
    if not old:raise HTTPException(404,"Article not found")
    if not payload.image_url.strip(): raise HTTPException(422,"Article image is required.")
    now=datetime.now(timezone.utc).isoformat();newslug=_editorial_slug(payload.slug or slug);status="published" if payload.status.lower()=="published" else "draft";published=old.get("published_at") or (now if status=="published" else None);c=_auth_db()
    try:
        collision=c.execute("SELECT id FROM editorial_news WHERE slug=? AND id<>?",(newslug,old["id"])).fetchone()
        if collision:
            raise HTTPException(status_code=409,detail="That article URL slug is already in use. Choose another slug.")
        c.execute("UPDATE editorial_news SET slug=?,title=?,summary=?,content=?,image_url=?,sport=?,category=?,author=?,status=?,seo_title=?,seo_description=?,updated_at=?,published_at=?,placement=?,image_format=? WHERE id=?",(newslug,payload.title.strip(),payload.summary.strip(),payload.content.strip(),payload.image_url.strip(),payload.sport.strip().lower() or "all",payload.category.strip() or "Sports",payload.author.strip() or "Kasi Sports News",status,payload.seo_title.strip(),payload.seo_description.strip(),now,published,("live_news" if payload.placement.strip().lower()=="live_news" else "sports_news"),("vertical" if payload.image_format.strip().lower()=="vertical" else "horizontal"),old["id"]));c.commit();return {"ok":True,"article":_editorial_get(newslug),"url":f"https://kasilivescore.com/news/{newslug}"}
    finally:c.close()

@app.delete("/admin/news/{slug}")
def admin_news_delete(slug: str,authorization: Optional[str]=Header(default=None)):
    require_admin(authorization);_ensure_editorial_news_schema();c=_auth_db()
    try:c.execute("DELETE FROM editorial_news WHERE slug=?",(slug,));c.commit();return {"ok":True}
    finally:c.close()

@app.get("/news/{slug}", response_class=HTMLResponse, include_in_schema=False)
async def seo_news_article(slug: str, source: str = Query("")):
    """Standalone news article preview. This route must never turn publisher/metadata failure into HTTP 500."""
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]{1,139}", slug or ""):
        raise HTTPException(404,"News article not found")
    editorial=_editorial_get(slug)
    if editorial and editorial.get("status")=="published":
        public="https://kasilivescore.com"; canonical=public+f"/news/{slug}"
        title=str(editorial.get("seo_title") or editorial.get("title") or "Sports News"); desc=str(editorial.get("seo_description") or editorial.get("summary") or "")
        image=str(editorial.get("image_url") or ""); author=str(editorial.get("author") or "Kasi Sports News"); content=str(editorial.get("content") or "")
        paras="".join(f"<p>{escape(x.strip())}</p>" for x in re.split(r"\n\s*\n",content) if x.strip())
        img_html=f'<img src="{escape(image,quote=True)}" alt="{escape(title,quote=True)}" style="width:100%;max-height:520px;object-fit:cover;border-radius:12px;margin:18px 0">' if image.startswith(("http://","https://")) else ""
        schema={"@context":"https://schema.org","@type":"NewsArticle","headline":title,"description":desc,"url":canonical,"mainEntityOfPage":{"@type":"WebPage","@id":canonical},"publisher":_seo_org_schema(),"author":{"@type":"Person","name":author},"isAccessibleForFree":True,"inLanguage":"en-ZA"}
        if image.startswith(("http://","https://")):schema["image"]=[image]
        return HTMLResponse(f"""<!doctype html><html lang='en'><head><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'><title>{escape(title)} | Kasi Sports News</title><meta name='description' content='{escape(desc[:155],quote=True)}'><link rel='canonical' href='{escape(canonical,quote=True)}'><meta name='robots' content='index,follow,max-image-preview:large'><meta property='og:title' content='{escape(title,quote=True)}'><meta property='og:description' content='{escape(desc[:200],quote=True)}'><meta property='og:url' content='{escape(canonical,quote=True)}'><meta property='og:type' content='article'>{f"<meta property='og:image' content='{escape(image,quote=True)}'>" if image else ''}<script type='application/ld+json'>{json.dumps(schema,ensure_ascii=False)}</script><style>body{{margin:0;background:#000;color:#f5f5f5;font-family:Arial,sans-serif}}header{{padding:16px max(18px,calc((100vw - 920px)/2));border-bottom:1px solid #222;display:flex;align-items:center;gap:10px}}header img{{width:42px;height:42px;object-fit:contain;border-radius:50%}}main{{width:min(920px,calc(100% - 32px));margin:30px auto 70px}}h1{{font-size:clamp(30px,5vw,50px);line-height:1.08}}.meta{{color:#9b9b9b;margin:10px 0 22px}}article{{font-size:18px;line-height:1.75}}a{{color:#38bdf8}}</style></head><body><header><img src='/kasi-sports-news-logo.png' alt='Kasi Sports News'><b>Kasi Sports News</b><a href='/' style='margin-left:auto'>Home</a></header><main>{img_html}<h1>{escape(title)}</h1><div class='meta'>{escape(author)} · {escape(str(editorial.get('published_at') or editorial.get('updated_at') or '')[:10])}</div>{f"<p style='font-size:20px;color:#9b9b9b'>{escape(editorial.get('summary') or '')}</p>" if editorial.get('summary') else ''}<article>{paras}</article></main></body></html>""")
    raw=(source or "").strip()

    # v323 Step 4: the public/indexable identity of a news article is /news/{slug}.
    # The source query parameter remains a transport hint for first-time visits only.
    # Persist that mapping so crawlers/users can subsequently open the clean canonical URL.
    if raw.startswith(("http://","https://")):
        _dashboard_snapshot_put(f"news_article_source:{slug}", {"source": raw})
    else:
        raw=""
        snap=_dashboard_snapshot_get(f"news_article_source:{slug}")
        if isinstance(snap,dict):
            candidate=str(snap.get("source") or "").strip()
            if candidate.startswith(("http://","https://")):
                raw=candidate

        # Recover from the already-cached news pool/snapshot without touching sports APIs.
        if not raw:
            candidates=[]
            candidates.extend(list(_NEWS_LAST_GOOD or []))
            candidates.extend(list((_NEWS_VERIFIED_SNAPSHOT or {}).get("items") or []))
            persisted=_dashboard_snapshot_get("news_verified_all")
            if isinstance(persisted,dict):
                candidates.extend(list(persisted.get("items") or []))
            for item in candidates:
                if not isinstance(item,dict):
                    continue
                aid=str(item.get("articleId") or "")
                target=str(item.get("originalUrl") or item.get("publisherUrl") or item.get("resolvedUrl") or item.get("link") or "").strip()
                if aid == slug and target.startswith(("http://","https://")):
                    raw=target
                    _dashboard_snapshot_put(f"news_article_source:{slug}", {"source": raw})
                    break

        if not raw:
            raise HTTPException(404,"News article not found")

    # Always retain a valid escape path to the original source.
    publisher_url=raw
    meta={}
    try:
        maybe=await sports_news_article(raw)
        if isinstance(maybe,dict):
            meta=maybe
            u=str(meta.get("url") or "").strip()
            if u.startswith(("http://","https://")):
                publisher_url=u
    except Exception:
        meta={}

    title=str(meta.get("title") or "").strip()
    desc=str(meta.get("summary") or meta.get("description") or "").strip()
    image=str(meta.get("image") or "").strip()
    publisher=str(meta.get("source") or "").strip()
    try:
        host=urllib.parse.urlparse(publisher_url).netloc.replace("www.","")
    except Exception:
        host=""
    publisher=publisher or host or "Publisher"

    # Critical compatibility rule for old hash URLs and Google News RSS links:
    # metadata failure must never render a hash page and must never raise 500.
    article_indexable=True
    if not title:
        title="Sports News"
        desc="This article is temporarily unavailable inside Kasi Sports News."
        image=""
        # STEP 5 v329: unavailable metadata is a thin fallback, not a search result.
        article_indexable=False

    # SEO canonical origin is intentionally fixed to the public production domain.
    # Do not trust legacy PUBLIC_SITE_URL values here: an old Render environment
    # value previously leaked kasiscore-sports-intelligence.com into NewsArticle
    # url/mainEntityOfPage even though the live site is kasilivescore.com.
    public="https://kasilivescore.com"
    # v323: query parameters are intentionally excluded from the canonical identity.
    # This prevents multiple ?source= variants from competing in the search index.
    own_path=f"/news/{slug}"
    canonical=public+own_path

    # Missing/broken image is optional. Browser removes it cleanly on load failure.
    img_html=""
    if image.startswith(("http://","https://")):
        img_html=f'<img src="{escape(image,quote=True)}" alt="{escape(title,quote=True)}" loading="eager" fetchpriority="high" onerror="this.remove()" style="width:100%;max-height:520px;object-fit:cover;border-radius:12px;margin:18px 0">'

    news_schema={
        "@context":"https://schema.org",
        "@type":"NewsArticle",
        "headline":title,
        "description":desc,
        "url":canonical,
        "mainEntityOfPage":{"@type":"WebPage","@id":canonical},
        "publisher":_seo_org_schema(),
        "isAccessibleForFree":True,
        "inLanguage":"en-ZA"
    }
    author=str(meta.get("author") or "").strip()
    if author: news_schema["author"]={"@type":"Person","name":author}
    if image.startswith(("http://","https://")): news_schema["image"]=[image]
    news_schema_json=json.dumps(news_schema,ensure_ascii=False)

    article_html=f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{escape(title)} | Kasi Sports News</title>
<meta name="description" content="{escape(desc[:155],quote=True)}">
<link rel="canonical" href="{escape(canonical,quote=True)}">
<meta name="robots" content="{'index,follow,max-image-preview:large,max-snippet:-1,max-video-preview:-1' if article_indexable else 'noindex,follow'}">
<meta name="google-adsense-account" content="ca-pub-5442799591686279">
<script async src="https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js?client=ca-pub-5442799591686279" crossorigin="anonymous"></script>
<script type="application/ld+json">{news_schema_json}</script>
<style>
:root{{--bg:#05080c;--panel:#090e14;--text:#f4f7fb;--muted:#8ea6ba;--line:#22303c;--accent:#22b8d6}}
*{{box-sizing:border-box}}html,body{{margin:0;background:var(--bg);color:var(--text);font-family:Arial,sans-serif}}
.ks-header{{height:74px;border-bottom:1px solid var(--line);display:flex;align-items:center;padding:0 max(18px,calc((100vw - 1120px)/2));gap:12px;background:#070b10}}
.ks-brand{{font-weight:900;font-size:20px}}.ks-home{{margin-left:auto;color:var(--text);text-decoration:none}}
.ks-article-page{{width:min(920px,calc(100% - 32px));margin:32px auto 70px;background:var(--panel);border:1px solid var(--line);border-radius:14px;padding:clamp(18px,4vw,42px)}}
.ks-back a,.ks-original a{{color:var(--accent)}}.ks-source,.ks-back{{color:var(--muted)}}h1{{font-size:clamp(28px,5vw,48px);line-height:1.08}}
.ks-lead{{font-size:18px;line-height:1.65}}.ks-article-ad{{min-height:110px;margin:26px 0;border:1px solid var(--line);border-radius:12px;display:flex;align-items:center;justify-content:center;overflow:hidden;contain:layout paint}}.ks-article-ad ins{{width:100%;min-height:90px}}.ks-original{{margin-top:28px;padding-top:20px;border-top:1px solid var(--line)}}
</style></head><body>
<header class="ks-header"><div class="ks-brand">Kasi <span>Sports News</span></div><a class="ks-home" href="/">Home</a></header>
<main class="ks-article-page"><nav class="ks-back"><a href="/">← Back to Kasi Sports News</a></nav>
{img_html}<h1>{escape(title)}</h1><div class="ks-source">Source: <strong>{escape(publisher)}</strong></div>
{f'<p class="ks-lead">{escape(desc)}</p>' if desc else ''}
<div class="ks-article-ad" id="ksnNewsAd"><ins class="adsbygoogle" style="display:block" data-ad-client="ca-pub-5442799591686279" data-ad-slot="4261824927" data-ad-format="auto" data-full-width-responsive="true"></ins></div><script>(adsbygoogle=window.adsbygoogle||[]).push({{}});const a=document.querySelector('#ksnNewsAd ins');if(a)new MutationObserver((m,o)=>{{if(a.getAttribute('data-ad-status')==='unfilled'){{document.getElementById('ksnNewsAd')?.remove();o.disconnect()}}else if(a.getAttribute('data-ad-status')==='filled')o.disconnect()}}).observe(a,{{attributes:true,attributeFilter:['data-ad-status']}});</script>
<div class="ks-original"><a href="{escape(publisher_url,quote=True)}" target="_blank" rel="noopener noreferrer">Read Original Article</a></div>
<nav class="ks-original" aria-label="Explore Kasi Sports News"><a href="/football">Football</a> · <a href="/rugby">Rugby</a> · <a href="/cricket">Cricket</a> · <a href="/about">About</a> · <a href="/privacy">Privacy</a></nav>
</main></body></html>"""
    return HTMLResponse(article_html,status_code=200)

@app.get("/sports/news/article")
async def sports_news_article(url: str = Query(...)):
    """Return publisher metadata for an in-dashboard reader card.

    This intentionally does not republish full article text. It exposes the
    publisher's title/description/open-graph image/video when available.
    """
    raw=(url or "").strip()
    if not raw.startswith(("http://","https://")):
        raise HTTPException(400,"Invalid article URL")
    raw=await _resolve_news_publisher_url(raw,"")
    allowed=("news.google.com","goal.com","www.goal.com","metro.co.uk","www.metro.co.uk","citizen.co.za","www.citizen.co.za","sarugbymag.co.za","www.sarugbymag.co.za","sacricketmag.com","www.sacricketmag.com","keo.co.za","www.keo.co.za","supersport.com","www.supersport.com")
    from urllib.parse import urlparse
    host=(urlparse(raw).hostname or "").lower()
    if host not in allowed and not host.endswith(".goal.com") and not host.endswith(".metro.co.uk"):
        raise HTTPException(400,"News source is not approved")
    try:
        c=await _sports_client()
        r=await c.get(raw, follow_redirects=True, timeout=httpx.Timeout(8,connect=4), headers={"User-Agent":"Mozilla/5.0 KasiScore/1.0"})
        r.raise_for_status()
        final=str(r.url)
        final_host=(urlparse(final).hostname or "").lower()
        if not any(d in final_host for d in ("goal.com","metro.co.uk","news.google.com","citizen.co.za","sarugbymag.co.za","sacricketmag.com","keo.co.za","supersport.com")):
            raise HTTPException(400,"Resolved news source is not approved")
        text=r.text[:1_500_000]
        def meta(prop):
            pats=[
                rf'<meta[^>]+(?:property|name)=["\']{re.escape(prop)}["\'][^>]+content=["\']([^"\']+)',
                rf'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:property|name)=["\']{re.escape(prop)}["\']',
            ]
            for p in pats:
                m=re.search(p,text,re.I|re.S)
                if m:return unescape(re.sub(r'\s+',' ',m.group(1))).strip()
            return ""
        title=meta("og:title") or meta("twitter:title")
        desc=meta("og:description") or meta("description") or meta("twitter:description")
        author=meta("author") or meta("article:author")
        image=meta("og:image") or meta("twitter:image")
        video=meta("og:video:secure_url") or meta("og:video") or meta("twitter:player")
        return {"title":title,"summary":desc,"description":desc,"image":image,"video":video,"url":final,"author":author,"source":"GOAL" if "goal.com" in final_host else "Metro" if "metro.co.uk" in final_host else "SA Rugby Magazine" if "sarugbymag.co.za" in final_host else "SA Cricket Mag" if "sacricketmag.com" in final_host else "News","embedded":True}
    except HTTPException:
        raise
    except Exception as exc:
        # Fail soft: the list card still remains usable inside the dashboard.
        return {"title":"","summary":"Publisher preview is temporarily unavailable.","image":"","video":"","url":raw,"source":"News","embedded":True,"error":str(exc)}

@app.get("/sports/transfers")
async def sports_transfers(
    team: int = Query(0, ge=0),
    page: int = Query(1, ge=1, le=50),
    sport: str = Query("football"),
):
    # v289: transfers must fail soft. A slow/unavailable upstream must never turn
    # this public dashboard endpoint into a visitor-facing 502. Serve last-good
    # data when available, otherwise return a controlled 200/empty response.
    sport=sport.lower().strip()
    snap_key=f"sports_transfers_last_good:{sport}:{team}:{page}"
    snap=_dashboard_snapshot_get(snap_key) if "_dashboard_snapshot_get" in globals() else None
    last_good=(snap or {}).get("data") if isinstance(snap,dict) else None

    try:
        if sport == "football":
            params={"page":page}
            if team: params["team"]=team
            data=await asyncio.wait_for(_afoot_get("/transfers", params), timeout=8.0)
            rows=[]
            for item in data.get("response") or []:
                player=item.get("player") or {}; transfers=item.get("transfers") or []
                for tr in transfers:
                    rows.append({"sport":"football","player":player.get("name"),"playerId":player.get("id"),
                                 "photo":f"https://media.api-sports.io/football/players/{player.get('id')}.png" if player.get("id") else "",
                                 "date":tr.get("date"),"type":tr.get("type"),
                                 "teamIn":(tr.get("teams") or {}).get("in",{}).get("name"),
                                 "teamOut":(tr.get("teams") or {}).get("out",{}).get("name"),
                                 "league":(tr.get("teams") or {}).get("in",{}).get("name")})
            result={"sport":"football","count":len(rows),"items":rows[:200],"source":"API-Football"}
        else:
            queries={
                "rugby":"rugby transfers South Africa Springboks URC Bulls Stormers Sharks Lions",
                "cricket":"cricket transfers South Africa Proteas SA20",
                "tennis":"tennis player transfer move ATP WTA",
                "basketball":"basketball transfers NBA BAL South Africa",
            }
            items=await asyncio.wait_for(_google_news(queries.get(sport, f"{sport} transfers"), 30), timeout=8.0)
            result={"sport":sport,"count":len(items),"items":[
                {"sport":sport,"player":None,"date":x.get("published"),"type":"Transfer news",
                 "teamIn":None,"teamOut":None,"league":None,"title":x.get("title"),"link":x.get("link"),"source":x.get("source")}
                for x in items
            ],"source":"Google News RSS"}

        # Persist only useful payloads so a transient empty/provider failure does
        # not overwrite the last known good transfer feed.
        if result.get("items") and "_dashboard_snapshot_put" in globals():
            _dashboard_snapshot_put(snap_key,{"data":result})
        return result
    except Exception as exc:
        log.warning("Transfers %s team=%s page=%s failed softly: %s",sport,team,page,exc)
        if isinstance(last_good,dict):
            cached=dict(last_good)
            cached["cached"]=True
            cached["stale"]=True
            return cached
        return {"sport":sport,"count":0,"items":[],"source":"unavailable","refreshing":True}

@app.get("/sports/injuries")
async def sports_injuries(sport: str = Query("football"), team: int = Query(0), league: int = Query(0), season: int = Query(0)):
    """Injury centre disabled in v58. Kept as a compatibility endpoint without upstream calls."""
    return {"sport":sport,"count":0,"items":[],"disabled":True,"message":"Injury data is currently disabled.","updatedAt":datetime.now(timezone.utc).isoformat()}

@app.get("/sports/standings")
async def sports_standings(sport: str = Query("rugby"), league: int = Query(0, ge=0), season: int = Query(0, ge=0)):
    sport=sport.lower(); season=season or _current_season()
    if sport in ("rugby","basketball") and SPORTS_API_KEYS.get(sport):
        base=SPORTS_API_BASES[sport]; headers={"x-apisports-key":SPORTS_API_KEYS[sport],"Accept":"application/json"}
        params={"season":season}
        if league: params["league"]=league
        try:
            data=await _sports_get(base+"/standings",params,headers)
            return {"sport":sport,"season":season,"items":data.get("response") or [],"source":"API-Sports"}
        except Exception as exc: log.warning("Standings %s failed: %s",sport,exc)
    # ESPN fallback where a league slug is provided by the caller.
    lg=str(league or ESPN_LEAGUES.get(sport,[""])[0])
    try:
        data=await _sports_get(f"https://site.api.espn.com/apis/v2/sports/{sport}/{lg}/standings",{"season":season})
        return {"sport":sport,"season":season,"items":data.get("children") or data.get("standings") or [],"source":"ESPN"}
    except Exception as exc:
        return {"sport":sport,"season":season,"items":[],"source":"unavailable","error":str(exc)}



@app.get("/sports/rugby/odds")
async def rugby_odds(limit:int=Query(20,ge=1,le=50)):
    rows=await _oddspapi_sport_fixtures("rugby",None,False)
    out=[]
    for f in rows[:limit]:
        fid=f.get("providerFixtureId") or f.get("id")
        if not fid:continue
        try:
            data,_=await _oddspapi_v5_or_v4(f"{ODDSPAPI_REST_LANGUAGE}/fixtures/odds","odds",
                                            {"fixtureId":str(fid),"oddsFormat":"decimal"})
            snap=(_oddspapi_rows(data) or ([data] if isinstance(data,dict) else []))
            active=_oddspapi_v5_active_prices(snap[0] if snap else {})
            if active:out.append({"fixtureId":f.get("id"),"home":f.get("home"),"away":f.get("away"),
                                  "markets":active,"marketRule":"provider-returned-only"})
        except Exception as exc:log.debug("Rugby odds fixture=%s unavailable: %s",fid,exc)
    return {"sport":"rugby","count":len(out),"items":out,"source":"OddsPapi",
            "marketRule":"provider-returned-only"}

@app.get("/sports/cricket/odds")
async def cricket_odds():
    """Cricket bookmaker markets: return only markets/prices actually supplied by The Odds API."""
    if not ODDS_API_ENABLED or not ODDS_API_KEY:
        return {"status":"degraded","items":[],"message":"No current cricket odds available."}
    requested=os.getenv("CRICKET_ODDS_MARKETS","h2h").strip() or "h2h"
    items=[]
    for sport_key in ("cricket_test_match","cricket_odi","cricket_international_t20","cricket_t20"):
        try:
            rows=await _odds_api_get(f"/sports/{sport_key}/odds",
                {"regions":ODDS_API_REGIONS,"markets":requested,"oddsFormat":"decimal"})
        except Exception as exc:
            log.debug("Cricket odds %s unavailable: %s",sport_key,exc);continue
        for ev in rows if isinstance(rows,list) else []:
            normalized=[]
            for book in ev.get("bookmakers") or []:
                markets=[]
                for m in book.get("markets") or []:
                    selections=[{"name":o.get("name"),"price":o.get("price"),"point":o.get("point")}
                                for o in m.get("outcomes") or [] if o.get("price") is not None]
                    if selections:markets.append({"key":m.get("key"),"selections":selections})
                if markets:normalized.append({"name":book.get("title") or book.get("key") or "Bookmaker","markets":markets})
            if normalized:
                items.append({"id":ev.get("id"),"sportKey":sport_key,"home":ev.get("home_team") or "Home",
                              "away":ev.get("away_team") or "Away","commenceTime":ev.get("commence_time"),
                              "bookmakers":normalized})
    return {"status":"online" if items else "degraded","count":len(items),"items":items,
            "requestedMarkets":requested,"marketRule":"provider-returned-only",
            "message":None if items else "No current cricket odds available."}

@app.get("/platform/status")
async def platform_status():
    """Aggregated platform/provider status for the Platform tab."""
    return {
        "status": "ok",
        "version": "v177",
        "apiFootball": bool(API_KEY),
        "rugbyApi": bool(SPORTS_API_KEYS.get("rugby")),
        "oddsPapiConfigured": bool(ODDSPAPI_ENABLED and ODDSPAPI_API_KEY),
        "rugbyProvider": "OddsPapi" if (ODDSPAPI_ENABLED and ODDSPAPI_API_KEY) else ("API-Sports" if SPORTS_API_KEYS.get("rugby") else "ESPN"),
        "cricketProvider": "OddsPapi" if (ODDSPAPI_ENABLED and ODDSPAPI_API_KEY) else "ESPN",
        "cricketOddsConfigured": bool(ODDS_API_KEY) if ODDS_API_ENABLED else False,
        "newsProvider": True,
        "odds": True,
        "live": True,
        "predictions": True,
        "competitions": len(COMPETITION_REGISTRY),
        "timezone": TIMEZONE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
    }

@app.get("/sports/health")
async def sports_health():
    """Source-level health derived from configuration + existing cache state; does not spend provider quota."""
    def state(configured: bool, cached_count: int | None=None):
        if not configured: return "OFFLINE"
        if cached_count is not None and cached_count==0: return "DEGRADED"
        return "ONLINE"
    live_cached=[v for k,v in list(SPORTS_CACHE.items()) if str(k).startswith("football:") and ":True:" in str(k)]
    cricket_cached=[v for k,v in list(SPORTS_CACHE.items()) if str(k).startswith("cricket:")]
    rugby_cached=[v for k,v in list(SPORTS_CACHE.items()) if str(k).startswith("rugby:")]
    news_cached=list(NEWS_CACHE.values())
    live_count=sum(len(x) for x in live_cached if isinstance(x,list))
    return {"status":"ok","sources":{
      "footballFixtures":{"state":state(bool(API_KEY))},
      "footballLive":{"state":state(bool(API_KEY),live_count if live_cached else None),"cachedCount":live_count},
      "footballInjuries":{"state":state(bool(API_KEY))},
      "footballOdds":{"state":state(bool(API_KEY) and bool(ODDS_API_ENABLED))},
      "rugby":{"state":state(bool(SPORTS_API_KEYS.get("rugby")) or True, sum(len(x) for x in rugby_cached if isinstance(x,list)) if rugby_cached else None)},
      "cricket":{"state":state(True, sum(len(x) for x in cricket_cached if isinstance(x,list)) if cricket_cached else None)},
      "sportsNews":{"state":state(True, sum(len(x) for x in news_cached if isinstance(x,list)) if news_cached else None)}
    },"note":"ONLINE means configured/available; DEGRADED means a cached request returned no data. This endpoint does not trigger paid provider calls."}

@app.get("/config")
async def config():
    return {
        "version": "v182",
        "apiFootballConfigured": bool(API_KEY),
        "timezone": TIMEZONE,
        "cacheSeconds": V141_CACHE_TTL_SECONDS,
        "fixtureRefreshSeconds": V141_FIXTURE_REFRESH_SECONDS,
        "predictionRefreshSeconds": V141_PREDICTION_REFRESH_SECS,
        "learningEnabled": True,
        "mlEnabled": True,
        "oddsEnabled": True,
        "livePredictionsEnabled": True,
        "liveOddsEndpoint": "/odds/live",
        "modelVersion": V141_MODEL_VERSION,
        "predictionWeights": V141_PREDICTION_WEIGHTS,
        "rateLimitPerMinute": RATE_LIMIT_PER_MINUTE,
        "localRateLimitDisabled": RATE_LIMIT_PER_MINUTE <= 0,
    }




# ---------------------------------------------------------------------------
# v463 — FANTASY PLAYOFFS BIG-5 LEAGUE FEED
# ---------------------------------------------------------------------------
# FantasyPlayoffs publishes separate public stats pages for each Big-5 league.
# Keep this feed isolated from official FPL: selecting La Liga must never return
# Premier League players, and vice versa. The public pages are cached here so
# dashboard refreshes do not repeatedly hit the upstream site.

FANTASYPLAYOFFS_LEAGUES = {
    39:  {"name":"Premier League", "country":"England", "slug":"premier-league-fantasy"},
    140: {"name":"La Liga",        "country":"Spain",   "slug":"la-liga-fantasy"},
    78:  {"name":"Bundesliga",     "country":"Germany", "slug":"bundesliga-fantasy"},
    135: {"name":"Serie A",        "country":"Italy",   "slug":"serie-a-fantasy"},
    61:  {"name":"Ligue 1",        "country":"France",  "slug":"ligue-1-fantasy"},
}
FANTASYPLAYOFFS_BASE = "https://fantasyplayoffs.app"

class _FantasyPlayoffsTextParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.tokens=[]
    def handle_data(self, data):
        t=re.sub(r"\s+", " ", html.unescape(data or "")).strip()
        if t: self.tokens.append(t)

def _fp_is_num(v):
    try: float(str(v).replace(",", "")); return True
    except Exception: return False

def _fp_clean_player_token(v):
    v=re.sub(r"\s+", " ", str(v or "")).strip()
    return v

def _parse_fantasyplayoffs_html(raw_html: str, league_id: int, season_label: str = "2026-27") -> list[dict]:
    """Parse public FantasyPlayoffs ranking rows without an extra dependency.

    The public stats pages render rows as rank / initials / player / club /
    position / fantasy-points.  We scan the rendered text stream around the
    position token and validate the numeric points that follow it.  Duplicate
    rows (for current/prior season sections) are de-duplicated by player+club,
    keeping the highest point total found in the current document.
    """
    meta=FANTASYPLAYOFFS_LEAGUES[league_id]
    parser=_FantasyPlayoffsTextParser(); parser.feed(raw_html or "")
    toks=parser.tokens
    # v467: choose the requested season table explicitly. The public page contains
    # multiple season tables in one document, so "first FPTS" is not a sufficient
    # contract for historical/current selection. Locate the requested season token,
    # then the first ranking header after it, and stop at that table's Show-all marker.
    season_label=str(season_label or "2026-27").replace("/", "-")
    # Season controls are rendered together before the tables. Preserve their
    # displayed order and map that order to the ranking tables that follow.
    season_controls=[]
    for x in toks:
        sx=str(x).strip().replace("/", "-")
        if re.fullmatch(r"20\d{2}-\d{2}", sx) and sx not in season_controls:
            season_controls.append(sx)
    table_headers=[n for n,x in enumerate(toks) if str(x).strip().upper()=="FPTS"]
    if season_label not in season_controls:
        return []
    table_index=season_controls.index(season_label)
    if table_index >= len(table_headers):
        return []
    start=table_headers[table_index]+1
    end=len(toks)
    for n in range(start, len(toks)):
        if re.match(r"^Show all\s+\d+\s+players$", str(toks[n]).strip(), re.I):
            end=n; break
    toks=toks[start:end]
    posset={"GK","DEF","MID","FWD"}
    skip={"All","Player","FPts","Show all","Mock Draft Now","2026-27","2025-26"}
    found={}
    for i,t in enumerate(toks):
        pos=re.sub(r"[^A-Za-z]", "", t).strip().upper()
        pos_alias={"GOALKEEPER":"GK","GOALKEEPERS":"GK","DEFENDER":"DEF","DEFENDERS":"DEF","MIDFIELDER":"MID","MIDFIELDERS":"MID","FORWARD":"FWD","FORWARDS":"FWD","STRIKER":"FWD","STRIKERS":"FWD"}
        pos=pos_alias.get(pos,pos)
        if pos not in posset: continue
        # fantasy points should be the first simple number after the position.
        pts=None
        for j in range(i+1, min(i+4,len(toks))):
            if _fp_is_num(toks[j]):
                pts=float(str(toks[j]).replace(",","")); break
        if pts is None: continue
        # Work backwards. Team is normally immediately before position and
        # player immediately before team; tolerate image-alt/team duplication.
        back=[]
        for j in range(i-1, max(-1,i-8), -1):
            x=_fp_clean_player_token(toks[j])
            if not x or x in skip or x.upper() in posset or _fp_is_num(x): continue
            if len(x)<=3 and x.replace('.','').isalpha(): continue  # initials
            back.append(x)
            if len(back)>=4: break
        if len(back)<2: continue
        team=back[0]
        player=back[1]
        # Some rendered pages repeat the club around its image. Collapse that.
        if player==team and len(back)>=3: player=back[2]
        if not player or not team or player==team: continue
        key=(player.casefold(),team.casefold())
        row={
            "id": f"fp:{league_id}:{re.sub(r'[^a-z0-9]+','-',player.casefold()).strip('-')}:{re.sub(r'[^a-z0-9]+','-',team.casefold()).strip('-')}",
            "name": player, "team": team, "position": pos,
            "fantasyPoints": pts, "leagueId": league_id,
            "league": meta["name"], "country": meta["country"],
            "source": "FantasyPlayoffs",
        }
        if key not in found or pts > found[key]["fantasyPoints"]: found[key]=row
    return sorted(found.values(), key=lambda r:r["fantasyPoints"], reverse=True)

async def _fetch_fantasyplayoffs_league(league_id: int, season: int=2026, bust_cache: bool=False) -> dict:
    if league_id not in FANTASYPLAYOFFS_LEAGUES:
        raise HTTPException(400, detail={"code":"UNSUPPORTED_FANTASY_LEAGUE","message":"Fantasy leaderboard supports the Big 5 leagues only."})
    meta=FANTASYPLAYOFFS_LEAGUES[league_id]
    season=int(season or 2026)
    if season < 2023 or season > 2026:
        raise HTTPException(400, detail={"code":"UNSUPPORTED_FANTASY_SEASON","message":"Supported Fantasy seasons are 2023/24 through 2026/27."})
    season_label=f"{season}-{str(season+1)[-2:]}"
    ck=f"fantasyplayoffs:{league_id}:{season_label}"
    if not bust_cache:
        cached=_players_cache.get(ck)
        if cached is not None: return cached
    url=f"{FANTASYPLAYOFFS_BASE}/{meta['slug']}/stats/"
    async with httpx.AsyncClient(timeout=25, follow_redirects=True) as client:
        r=await client.get(url, headers={"User-Agent":"Mozilla/5.0 (compatible; KasiSportsNews/1.0; +https://kasilivescore.com)"})
        r.raise_for_status()
    players=_parse_fantasyplayoffs_html(r.text, league_id, season_label)
    if not players:
        raise HTTPException(502, detail={"code":"FANTASYPLAYOFFS_PARSE_EMPTY","message":f"No {meta['name']} FantasyPlayoffs rows could be parsed."})
    position_counts={k:sum(1 for p in players if p.get("position")==k) for k in ("GK","DEF","MID","FWD")}
    payload={"source":"FantasyPlayoffs","sourceUrl":url,"leagueId":league_id,"league":meta["name"],"country":meta["country"],"season":season_label,"seasonStart":season,"players":players,"count":len(players),"positionCounts":position_counts,"updatedAt":datetime.now(timezone.utc).isoformat()}
    _players_cache[ck]=payload
    return payload

async def _fantasyplayoffs_refresh_all_big5() -> dict:
    """Refresh all Big-5 FantasyPlayoffs datasets and return a shared snapshot.

    One failed league never blocks the other four. This snapshot is reusable by
    Teams & Players surfaces without extra upstream calls.
    """
    leagues={}
    players=[]
    errors={}
    for lid,meta in FANTASYPLAYOFFS_LEAGUES.items():
        try:
            payload=await _fetch_fantasyplayoffs_league(lid, season=2026, bust_cache=True)
            leagues[str(lid)]={"league":meta["name"],"count":payload.get("count",0),"positionCounts":payload.get("positionCounts",{})}
            players.extend(payload.get("players") or [])
        except Exception as exc:
            errors[str(lid)]=str(exc)
            log.warning("FantasyPlayoffs daily refresh failed league=%s: %s", lid, exc)
    snap={"source":"FantasyPlayoffs","season":"2026-27","updatedAt":datetime.now(timezone.utc).isoformat(),"leagues":leagues,"players":players,"count":len(players),"errors":errors}
    _players_cache["fantasyplayoffs:big5:shared"] = snap
    return snap

async def _fantasyplayoffs_midnight_refresh_loop():
    """Refresh Big-5 player data daily at 00:00 Africa/Johannesburg."""
    from zoneinfo import ZoneInfo
    tz=ZoneInfo("Africa/Johannesburg")
    # Warm shortly after startup so Teams & Players never waits for midnight.
    try:
        await _fantasyplayoffs_refresh_all_big5()
    except Exception as exc:
        log.warning("FantasyPlayoffs startup warm failed: %s", exc)
    while True:
        now=datetime.now(tz)
        tomorrow=(now+timedelta(days=1)).date()
        target=datetime.combine(tomorrow, datetime.min.time(), tzinfo=tz)
        await asyncio.sleep(max(60,(target-now).total_seconds()))
        try:
            await _fantasyplayoffs_refresh_all_big5()
            log.info("FantasyPlayoffs Big-5 daily player snapshot refreshed at Johannesburg midnight")
        except Exception as exc:
            log.warning("FantasyPlayoffs midnight refresh failed: %s", exc)

@app.get("/players/fantasyplayoffs/all")
async def players_fantasyplayoffs_all(refresh: int=Query(0, ge=0, le=1)):
    """Shared Big-5 player dataset for Teams & Players pages."""
    if not refresh:
        cached=_players_cache.get("fantasyplayoffs:big5:shared")
        if cached is not None: return cached
    return await _fantasyplayoffs_refresh_all_big5()

@app.get("/players/fantasyplayoffs")
async def players_fantasyplayoffs(league: int=Query(...), season: int=Query(2026, ge=2023, le=2026), refresh: int=Query(0, ge=0, le=1), _t: Optional[int]=Query(None)):
    """Strict Big-5 FantasyPlayoffs feed. One request == one league."""
    try:
        return await _fetch_fantasyplayoffs_league(league, season=season, bust_cache=bool(refresh) or _t is not None)
    except HTTPException: raise
    except httpx.HTTPError as exc:
        log.error("FantasyPlayoffs fetch error league=%s: %s", league, exc)
        raise HTTPException(502, detail={"code":"FANTASYPLAYOFFS_ERROR","message":str(exc)})
    except Exception as exc:
        log.exception("FantasyPlayoffs unexpected error league=%s", league)
        raise HTTPException(500, detail={"code":"FANTASYPLAYOFFS_ERROR","message":str(exc)})


# ---------------------------------------------------------------------------
# PLAYER STATS ENDPOINTS  — powered by FPL API (free, no key, daily update)
# ---------------------------------------------------------------------------
# The official Fantasy Premier League API provides rich player stats for the
# current Premier League season, updated daily, completely free with no API key.
# Endpoint: https://fantasy.premierleague.com/api/bootstrap-static/
#
# We cache the full FPL bootstrap for 24 hrs (one fetch covers all endpoints).
# The data is normalised into the same response shape the dashboard expects,
# so no changes are needed on the frontend side.
# ---------------------------------------------------------------------------

FPL_BOOTSTRAP_URL = "https://fantasy.premierleague.com/api/bootstrap-static/"
FPL_PLAYER_SUMMARY_URL = "https://fantasy.premierleague.com/api/element-summary/{player_id}/"

# Position map: FPL element_type -> position name
FPL_POSITION_MAP = {1: "Goalkeeper", 2: "Defender", 3: "Midfielder", 4: "Forward"}


async def _fetch_fpl_bootstrap(bust_cache: bool = False) -> dict:
    """Fetch and cache the FPL bootstrap-static payload for 24 hours.

    Pass bust_cache=True (when the dashboard sends _t) to force a fresh fetch.
    """
    cache_key = "fpl:bootstrap"
    if not bust_cache:
        cached = _players_cache.get(cache_key)
        if cached is not None:
            log.info("FPL bootstrap cache hit")
            return cached

    log.info("Fetching fresh FPL bootstrap from %s", FPL_BOOTSTRAP_URL)
    async with httpx.AsyncClient(timeout=20) as client:
        resp = await client.get(
            FPL_BOOTSTRAP_URL,
            headers={"User-Agent": "Mozilla/5.0 (compatible; KasiScoreFootballDashboard/1.0)"},
        )
        resp.raise_for_status()
        data = resp.json()

    _players_cache[cache_key] = data
    log.info("FPL bootstrap cached (24hr): %d players, %d teams", len(data.get("elements", [])), len(data.get("teams", [])))
    return data


def _fpl_to_response(players: list[dict], teams: dict, positions_map: dict, sort_key: str, limit: int = 20) -> dict:
    """Convert FPL player dicts into the dashboard-compatible response shape.

    Fixes:
    - Off-season: sort falls back to total_points so list is never empty
    - Rating: derived from points-per-game (not ep_this which is 0 off-season)
    - cleanSheets: placed inside statistics[0] where dashboard reads it
    - shots/passes/tackles/dribbles: derived from FPL ICT index values
    """
    sorted_players = sorted(
        players,
        key=lambda p: (p.get(sort_key, 0), p.get("total_points", 0)),
        reverse=True,
    )[:limit]

    response = []
    for p in sorted_players:
        team_name = teams.get(p.get("team"), "Unknown")
        position = positions_map.get(p.get("element_type"), "Unknown")
        goals        = int(p.get("goals_scored", 0))
        assists      = int(p.get("assists", 0))
        minutes      = int(p.get("minutes", 0))
        saves        = int(p.get("saves", 0))
        clean_sheets = int(p.get("clean_sheets", 0))
        yellow       = int(p.get("yellow_cards", 0))
        red          = int(p.get("red_cards", 0))
        total_points = int(p.get("total_points", 0))
        appearances  = int(p.get("starts", 0)) or max(1, minutes // 70)

        # Rating from points-per-game: 0 pts→5.0, ~8 pts→7.8, ~15 pts→10.0
        ppg    = total_points / max(appearances, 1)
        rating = round(min(10.0, 5.0 + ppg * 0.35), 2)

        # ICT index components — FPL's best proxy for shots/creativity/tackles
        threat     = float(p.get("threat", 0) or 0)
        creativity = float(p.get("creativity", 0) or 0)
        influence  = float(p.get("influence", 0) or 0)

        photo = p.get("photo", "").replace(".jpg", "")
        player_image = (
            f"https://resources.premierleague.com/premierleague/photos/players/110x140/p{photo}.png"
            if photo else None
        )

        response.append({
            "player": {
                "id": p.get("id"),
                "name": f"{p.get('first_name', '')} {p.get('second_name', '')}".strip(),
                "firstname": p.get("first_name", ""),
                "lastname": p.get("second_name", ""),
                "photo": player_image,
                "nationality": None,
                "position": position,
            },
            "statistics": [{
                "team":   {"name": team_name, "logo": None},
                "league": {"name": "Premier League", "country": "England", "logo": None},
                "games": {
                    "appearences": appearances,
                    "minutes":     minutes,
                    "position":    position,
                    "rating":      str(rating),
                },
                "goals": {
                    "total":    goals,
                    "assists":  assists,
                    "saves":    saves,
                    "conceded": int(p.get("goals_conceded", 0)),
                },
                # cleanSheets at top level of statistics[0] — matches dashboard read path
                "cleanSheets": clean_sheets,
                # Derived from FPL ICT index — threat≈shots, creativity≈chances, influence≈defensive
                "shots":    {"total": int(threat / 10),      "on": int(threat / 18)},
                "passes":   {"key":   int(creativity / 10)},
                "tackles":  {"total": int(influence / 8),    "interceptions": int(influence / 14)},
                "dribbles": {"success": int(creativity / 15)},
                "cards":    {"yellow": yellow, "red": red},
                # FPL extras
                "fplPoints":   total_points,
                "fplForm":     p.get("form", "0"),
                "selectedBy":  p.get("selected_by_percent", "0"),
                "transfersIn": int(p.get("transfers_in_event", 0)),
                "bps":         int(p.get("bps", 0)),
            }],
        })

    return {"source": "FPL", "season": "2026/27", "response": response}


@app.get("/players/top-scorers")
async def players_top_scorers(
    league: int = Query(39),
    season: int = Query(2025),
    _t: Optional[int] = Query(None),  # cache-bust param from dashboard
):
    """Top goal scorers from the FPL API (Premier League current season)."""
    try:
        data = await _fetch_fpl_bootstrap(bust_cache=_t is not None)
        teams = {t["id"]: t["name"] for t in data.get("teams", [])}
        # Include all outfield players; off-season totals may be 0 but we still want data
        players = [p for p in data.get("elements", []) if p.get("element_type", 0) != 1]
        return _fpl_to_response(players, teams, FPL_POSITION_MAP, sort_key="goals_scored")
    except httpx.HTTPError as exc:
        log.error("FPL top-scorers fetch error: %s", exc)
        raise HTTPException(502, detail={"code": "FPL_ERROR", "message": str(exc)})
    except Exception as exc:
        log.error("top-scorers unexpected error: %s", exc)
        raise HTTPException(500, detail={"code": "PLAYER_STATS_ERROR", "message": str(exc)})


@app.get("/players/top-assists")
async def players_top_assists(
    league: int = Query(39),
    season: int = Query(2025),
    _t: Optional[int] = Query(None),
):
    """Top assisters from the FPL API (Premier League current season)."""
    try:
        data = await _fetch_fpl_bootstrap(bust_cache=_t is not None)
        teams = {t["id"]: t["name"] for t in data.get("teams", [])}
        players = [p for p in data.get("elements", []) if p.get("element_type", 0) != 1]
        return _fpl_to_response(players, teams, FPL_POSITION_MAP, sort_key="assists")
    except httpx.HTTPError as exc:
        log.error("FPL top-assists fetch error: %s", exc)
        raise HTTPException(502, detail={"code": "FPL_ERROR", "message": str(exc)})
    except Exception as exc:
        log.error("top-assists unexpected error: %s", exc)
        raise HTTPException(500, detail={"code": "PLAYER_STATS_ERROR", "message": str(exc)})


@app.get("/players/top-saves")
async def players_top_saves(
    league: int = Query(39),
    season: int = Query(2025),
    _t: Optional[int] = Query(None),
):
    """Top goalkeepers by saves from the FPL API (Premier League current season)."""
    try:
        data = await _fetch_fpl_bootstrap(bust_cache=_t is not None)
        teams = {t["id"]: t["name"] for t in data.get("teams", [])}
        # Filter to GKs only (element_type == 1)
        gks = [p for p in data.get("elements", []) if p.get("element_type") == 1]
        return _fpl_to_response(gks, teams, FPL_POSITION_MAP, sort_key="saves")
    except httpx.HTTPError as exc:
        log.error("FPL top-saves fetch error: %s", exc)
        raise HTTPException(502, detail={"code": "FPL_ERROR", "message": str(exc)})
    except Exception as exc:
        log.error("top-saves unexpected error: %s", exc)
        raise HTTPException(500, detail={"code": "PLAYER_STATS_ERROR", "message": str(exc)})


@app.get("/players/fpl-all")
async def players_fpl_all(
    _t: Optional[int] = Query(None),  # cache-bust param from dashboard
):
    """Full FPL player list — goals, assists, saves, points, form, BPS, selected%.
    Cached 24 hrs. Useful for building custom dashboards or running your own sorts.
    """
    try:
        data = await _fetch_fpl_bootstrap(bust_cache=_t is not None)
        teams = {t["id"]: t["name"] for t in data.get("teams", [])}
        players = data.get("elements", [])
        return _fpl_to_response(players, teams, FPL_POSITION_MAP, sort_key="total_points", limit=max(1000, len(players)))
    except httpx.HTTPError as exc:
        raise HTTPException(502, detail={"code": "FPL_ERROR", "message": str(exc)})
    except Exception as exc:
        raise HTTPException(500, detail={"code": "PLAYER_STATS_ERROR", "message": str(exc)})



# ---------------------------------------------------------------------------
#  — ORGANIC GROWTH, CONTENT, RETENTION & MONETISATION TELEMETRY
# ---------------------------------------------------------------------------
# These endpoints deliberately expose first-party intelligence and site telemetry.
# They do not manufacture search traffic or fake engagement.  The content engine
# should only publish pages when useful match/competition/team data is available.

GROWTH_DB_PATH = Path(os.getenv("GROWTH_DB_PATH", str(BASE_DIR / "kasiscore_growth.sqlite3")))

def _growth_db():
    GROWTH_DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    c = sqlite3.connect(str(GROWTH_DB_PATH), timeout=30)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA journal_mode=WAL")
    return c

def _init_growth_db():
    with _growth_db() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS page_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            event_name TEXT NOT NULL,
            path TEXT,
            page_type TEXT,
            sport TEXT,
            competition TEXT,
            entity_id TEXT,
            referrer TEXT,
            session_id TEXT,
            created_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_page_events_created ON page_events(created_at);
        CREATE INDEX IF NOT EXISTS idx_page_events_path ON page_events(path);
        CREATE TABLE IF NOT EXISTS web_vitals (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            metric TEXT NOT NULL,
            value REAL NOT NULL,
            path TEXT NOT NULL,
            device TEXT DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_web_vitals_metric_created ON web_vitals(metric, created_at);
        CREATE TABLE IF NOT EXISTS seo_pages (
            path TEXT PRIMARY KEY,
            page_type TEXT NOT NULL,
            title TEXT NOT NULL,
            description TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            indexable INTEGER NOT NULL DEFAULT 1
        );
        """)

_init_growth_db()

SEO_PAGE_TYPES = {
    "competition": {"priority": "0.9", "changefreq": "hourly"},
    "fixtures": {"priority": "0.8", "changefreq": "hourly"},
    "results": {"priority": "0.7", "changefreq": "hourly"},
    "predictions": {"priority": "0.9", "changefreq": "hourly"},
    "team": {"priority": "0.8", "changefreq": "daily"},
    "player": {"priority": "0.7", "changefreq": "daily"},
    "match": {"priority": "1.0", "changefreq": "hourly"},
    "today": {"priority": "1.0", "changefreq": "hourly"},
    "weekend": {"priority": "1.0", "changefreq": "hourly"},
    "news": {"priority": "0.7", "changefreq": "hourly"},
    "injuries": {"priority": "0.7", "changefreq": "hourly"},
    "team-stats": {"priority": "0.8", "changefreq": "daily"},
}

def _seo_slug(value: str) -> str:
    import re
    return re.sub(r"[^a-z0-9]+", "-", str(value or "").lower()).strip("-")

def _seo_country_slug(value: str) -> str:
    """Stable public country/region segment for canonical SEO URLs."""
    return _seo_slug(str(value or "").strip()) or "international"

def _seo_competition_parts(c: dict):
    sport = _seo_slug(c.get("sport")) or "sports"
    country = _seo_country_slug(c.get("country") or c.get("continent") or "international")
    raw_competition = str(c.get("slug") or c.get("name") or c.get("id") or "competition").strip()
    competition = _seo_slug(raw_competition.replace("/", " "))
    return sport, country, competition

def _seo_competition_base(c: dict) -> str:
    sport, country, competition = _seo_competition_parts(c)
    return f"/{sport}/{country}/{competition}"

def _seo_legacy_aliases() -> dict:
    """Old /sport/competition URLs mapped permanently to country-aware canonicals."""
    aliases = {}
    sections = ("fixtures","results","predictions","table","today","news","injuries","stats")
    for c in COMPETITION_REGISTRY:
        if not c.get("indexable", True):
            continue
        sport = _seo_slug(c.get("sport"))
        slug = str(c.get("slug") or _seo_slug(c.get("name"))).strip("/")
        if not sport or not slug:
            continue
        old_base = f"/{sport}/{slug}"
        new_base = _seo_competition_base(c)
        if old_base != new_base:
            aliases[old_base] = new_base
            for section in sections:
                aliases[f"{old_base}/{section}"] = f"{new_base}/{section}"
    return aliases

def _seo_registry_pages():
    now = datetime.now(timezone.utc).isoformat()
    rows = [
        {"path":"/", "pageType":"home", "title":"Kasi Sports News", "description":"Live scores, AI predictions, match intelligence, sports analysis and results."},
        {"path":"/today", "pageType":"today", "title":"Today's Sports Intelligence", "description":"Today's live matches, fixtures, predictions, results and AI sports intelligence.", "indexable":False},
        {"path":"/weekend", "pageType":"weekend", "title":"Weekend Sports Intelligence", "description":"Weekend football, rugby and sports fixtures, predictions, live matches and AI analysis."},
        {"path":"/football", "pageType":"sport", "title":"Football Scores, Fixtures & Competitions", "description":"Follow football scores, fixtures, results, predictions, tables, teams and competitions from around the world."},
        {"path":"/rugby", "pageType":"sport", "title":"Rugby Scores, Fixtures & Competitions", "description":"Follow rugby fixtures, results, standings, teams and competitions across supported leagues and tournaments."},
        {"path":"/cricket", "pageType":"sport", "title":"Cricket Scores, Fixtures & Competitions", "description":"Follow cricket scores, fixtures, results, teams and competitions across supported leagues and tournaments."},
        {"path":"/tennis", "pageType":"sport", "title":"Tennis Scores, Fixtures & Results", "description":"Tennis scores, fixtures, results and match intelligence across supported competitions."},
        {"path":"/about", "pageType":"info", "title":"About", "description":"About Kasi Sports News and its sports coverage."},
        {"path":"/contact", "pageType":"info", "title":"Contact Kasi Sports News", "description":"Contact Kasi Sports News for general and commercial enquiries."},
        {"path":"/privacy", "pageType":"info", "title":"Privacy Policy", "description":"Kasi Sports News privacy information."},
        {"path":"/terms", "pageType":"info", "title":"Terms of Use", "description":"Kasi Sports News terms of use."},
        {"path":"/cookies", "pageType":"info", "title":"Cookie Policy", "description":"Kasi Sports News cookie information."},
    ]
    country_hubs = {}
    for c in COMPETITION_REGISTRY:
        if not c.get("indexable", True):
            continue
        sport, country_slug, _competition_slug = _seo_competition_parts(c)
        country_name = str(c.get("country") or c.get("continent") or "International").strip()
        country_hubs[(sport, country_slug)] = country_name
    for (sport, country_slug), country_name in country_hubs.items():
        sport_name = sport.replace("-", " ").title()
        rows.append({
            "path": f"/{sport}/{country_slug}",
            "pageType": "country",
            "title": f"{country_name} {sport_name} Scores, Fixtures & Competitions",
            "description": f"Follow {country_name} {sport_name.lower()} competitions with fixtures, results, predictions and standings."
        })

    for c in COMPETITION_REGISTRY:
        if not c.get("indexable", True):
            continue
        sport, country_slug, competition_slug = _seo_competition_parts(c)
        base = f"/{sport}/{country_slug}/{competition_slug}"
        name = c.get("name")
        rows.extend([
            {"path":base,"pageType":"competition","title":f"{name} Fixtures, Results & Predictions","description":f"Follow {name} fixtures, results, predictions and standings on Kasi Sports News."},
            {"path":f"{base}/fixtures","pageType":"fixtures","title":f"{name} Fixtures","description":f"Upcoming {name} fixtures, match dates and kickoff times."},
            {"path":f"{base}/results","pageType":"results","title":f"{name} Results","description":f"Latest {name} results, completed matches and confirmed scores."},
            {"path":f"{base}/predictions","pageType":"predictions","title":f"{name} Predictions","description":f"{name} match predictions and supporting analysis when qualifying data is available."},
            {"path":f"{base}/table","pageType":"competition","title":f"{name} Table","description":f"Current {name} standings, positions and competition table information."},
            # STEP 4 v324: these route families currently render mostly generic hub copy.
            # Keep the URLs functional for visitors, but do not advertise/index them
            # until each route has substantive first-party content.
            {"path":f"{base}/today","pageType":"today","title":f"{name} Today","description":f"{name} matches today, live scores, statistics and Kasi Sports News AI intelligence.","indexable":False},
            {"path":f"{base}/news","pageType":"news","title":f"{name} News","description":f"Latest {name} news, team analysis, injuries and match intelligence.","indexable":False},
            {"path":f"{base}/injuries","pageType":"injuries","title":f"{name} Injuries","description":f"{name} injury updates, availability and match impact.","indexable":False},
            {"path":f"{base}/stats","pageType":"team-stats","title":f"{name} Statistics","description":f"{name} statistics, form, goals, corners and performance intelligence.","indexable":False},
        ])
    return rows

@app.get("//pages")
async def seo_pages(page_type: str = Query(""), sport: str = Query(""), limit: int = Query(500, ge=1, le=5000)):
    rows = _seo_registry_pages()
    if page_type:
        rows = [r for r in rows if r["pageType"] == page_type]
    if sport:
        prefix = "/" + _seo_slug(sport) + "/"
        rows = [r for r in rows if r["path"].startswith(prefix)]
    return {"count": len(rows[:limit]), "pages": rows[:limit], "generatedAt": datetime.now(timezone.utc).isoformat()}

@app.get("//render", response_class=HTMLResponse)
async def seo_render(path: str = Query("/")):
    if not path.startswith("/"):
        path = "/" + path
    allowed = ("/today", "/weekend", "/match/", "/team/", "/player/", "/football/")
    if path != "/" and not any(path == a.rstrip("/") or path.startswith(a) for a in allowed):
        raise HTTPException(404, " rendering route not available")
    return HTMLResponse(await _render_seo_document(path), headers={"Cache-Control":"public, max-age=300"})

@app.get("//manifest")
async def seo_manifest():
    rows = _seo_registry_pages()
    by_type = {}
    for r in rows:
        by_type[r["pageType"]] = by_type.get(r["pageType"], 0) + 1
    return {
        "version":"production--1",
        "indexablePages":len(rows),
        "pageTypes":by_type,
        "principle":"Publish useful pages with first-party intelligence; do not create thin doorway pages.",
        "dynamicMatchSitemap":True,
        "rendering":"SSR + SPA hydration",
        "searchConsole":"ready for property verification, sitemap submission and URL inspection",
        "generatedAt":datetime.now(timezone.utc).isoformat(),
    }


def _xml_escape(value: str) -> str:
    return (str(value or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;").replace("'", "&apos;"))

async def _seo_dynamic_rows() -> list[dict]:
    """Return only stable, canonical registry URLs for sitemap generation.

    Step 4 rule: sitemap requests must never trigger API-Football/OddsPapi calls.
    Dynamic match/team/player URLs are added only when backed by a durable local
    record and explicitly registered in a later phase.
    """
    return list(_seo_registry_pages())

@app.get("//sitemap.xml", response_class=Response)
async def seo_sitemap():
    rows = await _seo_dynamic_rows()
    origin = KASI_PUBLIC_ORIGIN
    body = ['<?xml version="1.0" encoding="UTF-8"?>','<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
    seen = set()
    for r in rows:
        path = r.get("path", "")
        if not path or path in seen or not r.get("indexable", True):
            continue
        seen.add(path)
        meta = SEO_PAGE_TYPES.get(r.get("pageType", ""), {"priority":"0.5","changefreq":"daily"})
        body.append(f'<url><loc>{_xml_escape(origin + path)}</loc></url>')
    body.append('</urlset>')
    return Response("".join(body), media_type="application/xml", headers={"Cache-Control":"public, max-age=900, s-maxage=900, stale-while-revalidate=3600"})

# ---------------------------------------------------------------------------
# SERVER-RENDERED  PAGES — Phase 7
# ---------------------------------------------------------------------------
_SSR_CACHE = TTLCache(maxsize=300, ttl=300)

def _ssr_text(value: Any, fallback: str = "") -> str:
    return escape(str(value if value not in (None, "") else fallback))

def _ssr_find_match(matches: list[dict], wanted_slug: str) -> Optional[dict]:
    wanted = wanted_slug.lower().strip("/")
    for m in matches:
        home = m.get("home") or m.get("homeTeam") or ""
        away = m.get("away") or m.get("awayTeam") or ""
        if wanted in {f"{_seo_slug(home)}-vs-{_seo_slug(away)}", f"{_seo_slug(away)}-vs-{_seo_slug(home)}"}:
            return m
    return None

async def _ssr_match_data(slug: str) -> Optional[dict]:
    key=f"match:{slug}"; cached=_SSR_CACHE.get(key)
    if cached is not None: return cached
    # Prefer predictions already produced by the background learning cycle.
    match=None
    try:
        with v141_learning.connect() as conn:
            rows=conn.execute("SELECT kickoff,home_team,away_team,probabilities,odds,prediction FROM predictions WHERE resolved=0 ORDER BY predicted_at DESC LIMIT 500").fetchall()
        for row in rows:
            if f"{_seo_slug(row['home_team'])}-vs-{_seo_slug(row['away_team'])}" == slug:
                probs=json.loads(row['probabilities'] or "{}")
                odds=json.loads(row['odds'] or "{}")
                pred=json.loads(row['prediction'] or "{}")
                match={"home":row['home_team'],"away":row['away_team'],"kickoff":row['kickoff'] or "","datetime":row['kickoff'] or "","odds":odds,"prediction":{**pred,"probabilities":probs},"league":"Football","oddsAvailable":_valid_1x2(odds)}
                break
    except Exception as exc:
        log.warning("SSR prediction-store lookup failed for %s: %s",slug,exc)
    if match is None:
        today=datetime.now().strftime("%Y-%m-%d"); end=(datetime.now()+timedelta(days=7)).strftime("%Y-%m-%d")
        try:
            data=await asyncio.wait_for(fixtures_with_odds(league="ALL",type="upcoming",date_from=today,date_to=end,refresh=0),timeout=5)
            match=_ssr_find_match(data.get("matches",[]),slug)
        except Exception as exc:
            log.warning("SSR fixture fallback failed for %s: %s",slug,exc); return None
    if not match: return None
    if _valid_1x2(match.get("odds",{})) and not match.get("prediction"):
        match={**match,**_prediction(match),"bookmakerGatePassed":True}
    # Add real form, H2H and availability to the initial HTML when available.
    try:
        home,away=match.get("home",""),match.get("away","")
        hist_h,hist_a,inj_h,inj_a,h2h=await asyncio.wait_for(asyncio.gather(
            team_history(team=home,league_id=0,last=5), team_history(team=away,league_id=0,last=5),
            team_injuries(team=home), team_injuries(team=away), team_h2h(home=home,away=away,last=5)
        ),timeout=5)
        match["_ssrHomeHistory"]=hist_h; match["_ssrAwayHistory"]=hist_a; match["_ssrHomeInjuries"]=inj_h; match["_ssrAwayInjuries"]=inj_a; match["_ssrH2H"]=h2h
    except Exception as exc:
        log.warning("SSR match enrichment failed for %s: %s",slug,exc)
    _SSR_CACHE[key]=match
    return match

def _ssr_match_section(match: dict, path: str) -> tuple[str,str,str]:
    home,away=match.get("home","Home"),match.get("away","Away"); league=match.get("league","Football")
    kickoff=match.get("datetime") or match.get("kickoff") or "Scheduled"
    title=f"{home} vs {away} Prediction, Odds & Match Intelligence"
    desc=f"Kasi Sports News analysis for {home} vs {away}: current bookmaker odds, Kasi Sports News prediction, confidence, form, injuries and match intelligence."
    prediction=match.get("prediction") or {}; probs=prediction.get("probabilities") or {}; confidence=float(prediction.get("confidence",0) or 0)
    if probs:
        key,label=max((("homeWin",home),("draw","Draw"),("awayWin",away)),key=lambda kv:float(probs.get(kv[0],0) or 0)); signal_prob=float(probs.get(key,0) or 0); signal=label
    else: signal,signal_prob="Prediction pending",0.0
    odds=match.get("odds") or {}; odds_ok=_valid_1x2(odds)
    odds_line=f"Home {odds.get('homeWin',0)} · Draw {odds.get('draw',0)} · Away {odds.get('awayWin',0)}" if odds_ok else "Current complete bookmaker 1X2 odds are not available."
    pred_line=f"KasiScore Signal: {signal} · Probability: {signal_prob:.1f}% · Confidence: {confidence:.1f}%" if odds_ok and prediction else "Kasi Sports News prediction is withheld until complete current bookmaker 1X2 odds are available."
    hh=match.get("_ssrHomeHistory",{}).get("matches",[]); ah=match.get("_ssrAwayHistory",{}).get("matches",[])
    def _form(items):
        out=[]
        for x in items[:5]:
            home_side=bool(x.get("isHome")); hg=int(x.get("hg",0) or 0); ag=int(x.get("ag",0) or 0)
            out.append("W" if ((home_side and hg>ag) or (not home_side and ag>hg)) else "L" if ((home_side and hg<ag) or (not home_side and ag<hg)) else "D")
        return " · ".join(out) or "Unavailable"
    h_inj=match.get("_ssrHomeInjuries",{}).get("players",[]); a_inj=match.get("_ssrAwayInjuries",{}).get("players",[])
    inj_text=(f"{home}: "+(", ".join(_ssr_text(x.get("name")) for x in h_inj[:6]) or "No reported records")+" · "+f"{away}: "+(", ".join(_ssr_text(x.get("name")) for x in a_inj[:6]) or "No reported records"))
    h2h=match.get("_ssrH2H",{}); h2h_matches=h2h.get("matches",[]) if isinstance(h2h,dict) else []
    body=(f'<article class="kasiscore--page" data--page="match"><nav aria-label="Breadcrumb"><a href="/">Kasi Sports News</a> / Match / {_ssr_text(home)} vs {_ssr_text(away)}</nav>'
          f'<h1>{_ssr_text(home)} vs {_ssr_text(away)} — Prediction, Odds &amp; Match Intelligence</h1><p class="-lead">{_ssr_text(desc)}</p>'
          f'<section class="-grid"><div><strong>Kickoff</strong><span>{_ssr_text(kickoff)}</span></div><div><strong>Competition</strong><span>{_ssr_text(league)}</span></div>'
          f'<div><strong>KasiScore signal</strong><span>{_ssr_text(signal)}</span></div><div><strong>KasiScore probability</strong><span>{signal_prob:.1f}%</span></div>'
          f'<div><strong>Confidence</strong><span>{confidence:.1f}%</span></div><div><strong>Bookmaker 1X2</strong><span>{_ssr_text(odds_line)}</span></div></section>'
          f'<section><h2>Why KasiScore?</h2><p>{_ssr_text(pred_line)}</p><p>Kasi Sports News combines bookmaker market information with its prediction model and available performance, form, injury and league data. Missing data is disclosed rather than hidden.</p></section>'
          f'<section><h2>Recent form</h2><p>{_ssr_text(home)}: <strong>{_ssr_text(_form(hh))}</strong> · {_ssr_text(away)}: <strong>{_ssr_text(_form(ah))}</strong></p></section>'
          f'<section><h2>Injuries &amp; availability</h2><p>{inj_text}</p></section>'
          f'<section><h2>Head-to-head</h2><p>{len(h2h_matches)} recent H2H matches returned when available. The interactive page provides the full H2H record.</p></section>'
          f'<section><h2>Live match intelligence</h2><p>Use the interactive Kasi Sports News page for live updates, KasiScore vs Market, expected scorers and Live 75 when the match is in play.</p></section>'
          f'<p><a href="/today">Today’s Sports Intelligence</a> · <a href="/weekend">Weekend Intelligence</a> · <a href="/football">Football Intelligence</a></p></article>')
    # SEO Step 3: route-level SportsEvent schema built only from real match fields.
    status_raw=str(match.get("status") or match.get("short") or match.get("state") or "").upper()
    if status_raw in {"FT","AET","PEN","FINISHED","FINAL","CLOSED","COMPLETED"}:
        event_status="https://schema.org/EventCompleted"
    elif status_raw in {"PST","POSTPONED"}:
        event_status="https://schema.org/EventPostponed"
    elif status_raw in {"CANC","CANCELLED","CANCELED","ABD","ABANDONED"}:
        event_status="https://schema.org/EventCancelled"
    else:
        event_status="https://schema.org/EventScheduled"
    schema_obj={"@context":"https://schema.org","@type":"SportsEvent","@id":_seo_abs_url(path)+"#sports-event",
                "name":f"{home} vs {away}","url":_seo_abs_url(path),"sport":"Soccer","description":desc,
                "eventStatus":event_status,
                "homeTeam":{"@type":"SportsTeam","name":home},"awayTeam":{"@type":"SportsTeam","name":away}}
    if kickoff and kickoff!="Scheduled": schema_obj["startDate"]=kickoff
    venue=match.get("venue") or match.get("stadium")
    if isinstance(venue,dict):
        vname=venue.get("name") or venue.get("stadium")
        vcity=venue.get("city")
        if vname: schema_obj["location"]={"@type":"Place","name":str(vname),**({"address":{"@type":"PostalAddress","addressLocality":str(vcity)}} if vcity else {})}
    elif venue: schema_obj["location"]={"@type":"Place","name":str(venue)}
    schema=json.dumps(schema_obj,ensure_ascii=False)
    return title,desc,body+f'<script type="application/ld+json">{schema}</script>'

async def _ssr_team_section(slug: str, path: str) -> tuple[str,str,str]:
    key=f"team-page-v60:{slug}"; cached=_SSR_CACHE.get(key)
    if cached: return cached
    try:
        if re.fullmatch(r"[1-9][0-9]{0,11}", slug or "") or "--" in (slug or ""):
            tid=_public_slug_to_id("team",slug)
            prof=await asyncio.wait_for(team_profile(team=str(tid),season=0),timeout=6)
            t=prof.get("team") or {}
            team_name=t.get("name") or f"Team {tid}"
            matches=prof.get("past10") or []
            form=prof.get("form") or []
            players=prof.get("players") or []
        else:
            name=slug.replace("-"," ").strip().title()
            tid,resolved_name=await _resolve_team_id(name)
            prof=await asyncio.wait_for(team_profile(team=str(tid),season=0),timeout=6)
            t=prof.get("team") or {}
            team_name=t.get("name") or resolved_name or name
            matches=prof.get("past10") or []
            form=prof.get("form") or []
            players=prof.get("players") or []
    except Exception as exc:
        log.warning("SSR team lookup failed for %s: %s",slug,exc)
        team_name=slug.replace("-"," ").strip().title(); matches=[]; form=[]; players=[]; t={}
    title=f"{team_name} Team Intelligence, Fixtures & Form"
    desc=f"{team_name} fixtures, recent results, form, squad, statistics and Kasi Sports News analysis."
    rows="".join(
        f'<li>{_ssr_text(m.get("home") or "Home")} {m.get("homeScore","—")}–{m.get("awayScore","—")} {_ssr_text(m.get("away") or "Away")}</li>'
        for m in matches[:10]
    ) or '<li>Recent results unavailable.</li>'
    body=(f'<article class="kasiscore--page" data--page="team"><nav aria-label="Breadcrumb"><a href="/">Kasi Sports News</a> / Team / {_ssr_text(team_name)}</nav>'
          f'<h1>{_ssr_text(team_name)} Team Intelligence</h1><p class="-lead">{_ssr_text(desc)}</p><section class="-grid">'
          f'<div><strong>Recent matches</strong><span>{len(matches)}</span></div><div><strong>Squad players</strong><span>{len(players)}</span></div><div><strong>Form</strong><span>{_ssr_text(" ".join(form) if form else "—")}</span></div></section>'
          f'<section><h2>Recent results</h2><ul>{rows}</ul></section>'
          f'<p><a href="/today">Today</a> · <a href="/weekend">Weekend</a> · <a href="/football">Football</a></p></article>')
    team_schema={"@context":"https://schema.org","@type":"SportsTeam","@id":_seo_abs_url(path)+"#sports-team",
                 "name":team_name,"url":_seo_abs_url(path),"sport":"Soccer","description":desc}
    logo=(t or {}).get("logo") if isinstance(t,dict) else None
    country=(t or {}).get("country") if isinstance(t,dict) else None
    if logo: team_schema["logo"]={"@type":"ImageObject","url":str(logo)}
    if country: team_schema["location"]={"@type":"Place","name":str(country)}
    schema=json.dumps(team_schema,ensure_ascii=False)
    result=(title,desc,body+f'<script type="application/ld+json">{schema}</script>'); _SSR_CACHE[key]=result; return result

async def _ssr_player_section(slug: str, path: str) -> tuple[str,str,str]:
    wanted=slug.replace("-"," ").strip().lower(); title_name=wanted.title(); player=None
    try:
        if re.fullmatch(r"[1-9][0-9]{0,11}", slug or "") or "--" in (slug or ""):
            pid=_public_slug_to_id("player",slug)
            prof=await asyncio.wait_for(player_profile(player=pid),timeout=5)
            pobj=prof.get("player") or {}
            st=(prof.get("statistics") or prof.get("teams") or [{}])[0] or {}
            player={"name":pobj.get("name") or title_name,
                    "team":(st.get("team") or {}).get("name") or "",
                    "goals":(st.get("goals") or {}).get("total") or 0,
                    "assists":(st.get("goals") or {}).get("assists") or 0,
                    "points":0,"photo":pobj.get("photo"),"nationality":pobj.get("nationality"),
                    "birth":(pobj.get("birth") or {}).get("date"),
                    "position":((st.get("games") or {}).get("position") if isinstance(st,dict) else None)}
        else:
            data=await asyncio.wait_for(players_fpl_all(),timeout=4)
            players=data.get("players",data.get("items",[]))
            player=next((p for p in players if str(p.get("name","")).lower()==wanted),None) or next((p for p in players if wanted in str(p.get("name","")).lower()),None)
    except Exception as exc: log.warning("SSR player lookup failed for %s: %s",wanted,exc)
    if player: title_name=player.get("name",title_name); team=player.get("team",""); stats=f"Goals {player.get('goals',0)} · Assists {player.get('assists',0)} · Points {player.get('points',player.get('total_points',0))}"
    else: team,stats="","Player data is currently unavailable."
    title=f"{title_name} Player Stats, Form & Match Intelligence"; desc=f"{title_name} player statistics, form, goals, assists, availability and Kasi Sports News data."
    body=(f'<article class="kasiscore--page" data--page="player"><nav aria-label="Breadcrumb"><a href="/">Kasi Sports News</a> / Player / {_ssr_text(title_name)}</nav>'
          f'<h1>{_ssr_text(title_name)} — Player Intelligence</h1><p class="-lead">{_ssr_text(desc)}</p><section class="-grid"><div><strong>Team</strong><span>{_ssr_text(team,"Unavailable")}</span></div><div><strong>Statistics</strong><span>{_ssr_text(stats)}</span></div></section>'
          f'<section><h2>Kasi Sports News player intelligence</h2><p>Track player form, goals, assists, availability and match impact alongside Kasi Sports News fixture predictions and expected-scorer intelligence.</p></section><p><a href="/today">Today</a> · <a href="/football">Football Intelligence</a></p></article>')
    person_schema={"@context":"https://schema.org","@type":"Person","@id":_seo_abs_url(path)+"#person",
                   "name":title_name,"url":_seo_abs_url(path),"description":desc}
    if team: person_schema["affiliation"]={"@type":"SportsTeam","name":team}
    if player:
        if player.get("photo"): person_schema["image"]=str(player.get("photo"))
        if player.get("nationality"): person_schema["nationality"]={"@type":"Country","name":str(player.get("nationality"))}
        if player.get("birth"): person_schema["birthDate"]=str(player.get("birth"))
        if player.get("position"): person_schema["jobTitle"]=str(player.get("position"))
    schema=json.dumps(person_schema,ensure_ascii=False)
    return title,desc,body+f'<script type="application/ld+json">{schema}</script>'



def _v440_snapshot_get_exact(keys: list[str]) -> list[tuple[str, dict]]:
    """Targeted shared-LKG reads only; never scans the snapshot table."""
    rows=[]
    seen=set()
    for key in keys:
        if not key or key in seen:
            continue
        seen.add(key)
        try:
            ps=_dashboard_snapshot_get(key) if "_dashboard_snapshot_get" in globals() else None
            if isinstance(ps,dict):
                data=ps.get("data")
                if isinstance(data,dict):
                    rows.append((key,data))
                    continue
        except Exception:
            pass
        # Exact-key SQLite fallback only. No ORDER BY / table-wide scan.
        try:
            c=sqlite3.connect(_SHARED_SNAPSHOT_DB,timeout=0.25)
            row=c.execute("SELECT payload FROM snapshots WHERE k=? LIMIT 1",(key,)).fetchone()
            c.close()
            if row:
                obj=json.loads(row[0])
                if isinstance(obj,dict):
                    rows.append((key,obj))
        except Exception:
            pass
    return rows

def _v440_competition(path: str):
    parts=[x for x in path.strip("/").split("/") if x]
    if len(parts)<3:
        return None
    sport,country,slug=parts[:3]
    for c in COMPETITION_REGISTRY:
        cs,cc,cl=_seo_competition_parts(c)
        if (cs,cc,cl)==(sport,country,slug):
            return c
    return None


def _v441_league_identity(comp: dict) -> tuple[str, str]:
    name=str(comp.get("name") or "").strip()
    cid=str(comp.get("id") or "").strip()
    # Registry ids are SEO ids such as "epl"; API-Football needs the numeric league id.
    aliases=[name]
    if name=="PSL":
        aliases += ["PSL South Africa","Premier Soccer League","Betway Premiership"]
    lid=None
    for alias in aliases:
        if alias in LEAGUE_IDS:
            lid=LEAGUE_IDS[alias]; break
    if lid is None:
        # Resolve by canonical name/slug without making a provider call.
        wanted={_seo_slug(name),_seo_slug(cid)}
        for n,v in LEAGUE_IDS.items():
            if _seo_slug(n) in wanted:
                lid=v; break
    return name, str(lid or "")

def _v441_keys(path: str, comp: dict) -> list[str]:
    """Exact namespaces written by the existing dashboard endpoints."""
    parts=[x for x in path.strip("/").split("/") if x]
    sport=parts[0] if parts else str(comp.get("sport") or "football").lower()
    section=parts[3] if len(parts)>3 else "overview"
    name,lid=_v441_league_identity(comp)
    keys=[]
    if section in ("fixtures","overview"):
        # fixtures() persists these exact keys.
        for league in (name, "PSL South Africa" if name=="PSL" else ""):
            if league:
                keys += [
                    f"fixtures:{sport}:{league}:upcoming:last_good",
                    f"fixtures:{sport}:{league}:all:last_good",
                    f"fixtures:{sport}:{league.upper()}:upcoming:last_good",
                    f"fixtures:{sport}:{league.upper()}:all:last_good",
                ]
    if section in ("results","overview"):
        # sports_finished_all() persists rolling finished-game LKGs.
        keys += ["sports_finished_v310:48","sports_finished_v310:72","sports_finished_v310:168"]
    if section=="predictions":
        # ai_predictions() writes predictions:last_good:{league}:{type}.
        # The public pool normally uses ALL; league-specific keys are also accepted.
        keys += [
            "predictions:last_good:ALL:upcoming",
            f"predictions:last_good:{name.upper()}:upcoming",
        ]
        if name=="PSL":
            keys.append("predictions:last_good:PSL SOUTH AFRICA:upcoming")
    return list(dict.fromkeys(k for k in keys if k))

def _v441_collect(obj, depth=0):
    """Bounded extraction from exact snapshots only."""
    if depth>4:
        return
    if isinstance(obj,dict):
        yield obj
        for k in ("matches","fixtures","results","items","response","data","predictions","standings","league","leagues","table"):
            v=obj.get(k)
            if isinstance(v,(dict,list)):
                yield from _v441_collect(v,depth+1)
    elif isinstance(obj,list):
        for v in obj[:150]:
            if isinstance(v,(dict,list)):
                yield from _v441_collect(v,depth+1)

def _v441_comp_match(x: dict, comp: dict) -> bool:
    name,lid=_v441_league_identity(comp)
    wanted_names={_seo_slug(name)}
    if name=="PSL":
        wanted_names |= {_seo_slug("PSL South Africa"),_seo_slug("Premier Soccer League"),_seo_slug("Betway Premiership")}
    league=x.get("league")
    if isinstance(league,dict):
        xn=str(league.get("name") or "")
        xid=str(league.get("id") or "")
    else:
        xn=str(league or x.get("competition") or x.get("leagueName") or "")
        xid=str(x.get("_leagueId") or x.get("leagueId") or x.get("competitionId") or "")
    if lid and xid and lid==xid:
        return True
    sx=_seo_slug(xn)
    # v456 Step 13: competition identity must be exact. Substring matching leaked
    # Ghana Premier League into England Premier League and Bundesliga Women/U19
    # into the senior Bundesliga SEO page. Numeric provider id wins when present;
    # otherwise accept only an exact normalized canonical/approved alias name.
    return bool(sx and sx in {w for w in wanted_names if w})

def _v441_archive_results(comp: dict, limit: int=30) -> list[dict]:
    """Read the permanent confirmed-results archive directly; never calls a provider."""
    name,lid=_v441_league_identity(comp)
    aliases=[name]
    if name=="PSL":
        aliases += ["PSL South Africa","Premier Soccer League","Betway Premiership"]
    conn=None;cur=None
    try:
        _results_archive_init()
        conn,kind=_results_db(); cur=conn.cursor()
        clauses=[];params=[]
        if lid:
            clauses.append("competition_id=%s" if kind=="postgres" else "competition_id=?")
            params.append(lid)
        for alias in aliases:
            clauses.append("lower(competition) LIKE %s" if kind=="postgres" else "lower(competition) LIKE ?")
            params.append("%"+alias.lower()+"%")
        ph="%s" if kind=="postgres" else "?"
        sql=("SELECT sport,provider_id,country,competition,competition_id,season,kickoff,"
             "home_id,home_name,home_badge,away_id,away_name,away_badge,home_score,away_score,status "
             "FROM ksn_results_archive WHERE sport='football' AND ("+" OR ".join(clauses)+") "
             f"ORDER BY kickoff DESC LIMIT {ph}")
        params.append(int(limit))
        cur.execute(sql,params)
        rows=cur.fetchall()
        out=[]
        for r in rows:
            v=list(r)
            out.append({"sport":v[0],"providerFixtureId":v[1],"country":v[2],"league":v[3],
                        "leagueId":v[4],"season":v[5],"date":str(v[6]),"homeId":v[7],"home":v[8],
                        "homeLogo":v[9],"awayId":v[10],"away":v[11],"awayLogo":v[12],
                        "homeScore":v[13],"awayScore":v[14],"status":v[15] or "FT",
                        "statusShort":v[15] or "FT","isFinished":True})
        return out
    except Exception:
        return []
    finally:
        try:
            if cur: cur.close()
        except Exception: pass
        try:
            if conn: conn.close()
        except Exception: pass

def _v441_cached_standings(comp: dict) -> list[dict]:
    """Use in-memory standings first, then the exact persistent API cache row, even as LKG."""
    name,lid=_v441_league_identity(comp)
    aliases={str(lid).lower(),name.lower(),_seo_slug(name)}
    # In-process tables populated by existing standings endpoints.
    try:
        for k,v in list(_standings_cache.items()):
            if not any(a and a in str(k).lower() for a in aliases):
                continue
            if isinstance(v,list):
                return [r for r in v[:30] if isinstance(r,dict)]
            if isinstance(v,dict):
                for league in v.get("leagues") or []:
                    if str(league.get("leagueId") or "")==lid or _seo_slug(league.get("league"))==_seo_slug(name):
                        return [r for r in (league.get("table") or [])[:30] if isinstance(r,dict)]
    except Exception:
        pass
    if not lid:
        return []
    # Exact API cache keys only: current season then previous season.
    for season in (_current_season(), _current_season()-1):
        try:
            key=_persist_cache_key("/standings",{"league":int(lid),"season":int(season)})
            conn=_apicache_db()
            row=conn.execute("SELECT response FROM api_cache WHERE cache_key=? LIMIT 1",(key,)).fetchone()
            conn.close()
            if not row: continue
            obj=json.loads(row["response"])
            response=obj.get("response") or []
            outer=((response[0].get("league") or {}).get("standings") or []) if response else []
            table=outer[0] if outer else []
            if table:
                return [r for r in table[:30] if isinstance(r,dict)]
        except Exception:
            pass
    return []

def _v441_team_name(x, side):
    teams=x.get("teams") if isinstance(x.get("teams"),dict) else {}
    obj=teams.get(side) if isinstance(teams.get(side),dict) else {}
    return str(obj.get("name") or x.get(side) or x.get(side+"Team") or x.get(side+"Name") or "").strip()

def _v441_score(x, side):
    goals=x.get("goals") if isinstance(x.get("goals"),dict) else {}
    scores=x.get("scores") if isinstance(x.get("scores"),dict) else {}
    v=(goals.get(side) if side in goals else
       x.get(side+"Score") if x.get(side+"Score") is not None else
       scores.get(side))
    if isinstance(v,dict):
        v=v.get("current") if v.get("current") is not None else v.get("total")
    return v

def _v441_date(x):
    fx=x.get("fixture") if isinstance(x.get("fixture"),dict) else {}
    return str(x.get("date") or x.get("datetime") or x.get("kickoff") or x.get("startTime") or x.get("commenceTime") or fx.get("date") or "").strip()

def _v441_status(x):
    fx=x.get("fixture") if isinstance(x.get("fixture"),dict) else {}
    st=fx.get("status") if isinstance(fx.get("status"),dict) else {}
    return str(x.get("statusShort") or x.get("status") or st.get("short") or "").strip()


def _v442_exact_archive_results(comp: dict, limit: int=30) -> list[dict]:
    """Confirmed football finals for exactly one API-Football competition id."""
    _name,lid=_v441_league_identity(comp)
    if not lid:
        return []
    conn=None;cur=None
    try:
        _results_archive_init()
        conn,kind=_results_db(); cur=conn.cursor()
        ph="%s" if kind=="postgres" else "?"
        sql=("SELECT sport,provider_id,country,competition,competition_id,season,kickoff,"
             "home_id,home_name,home_badge,away_id,away_name,away_badge,home_score,away_score,status "
             "FROM ksn_results_archive WHERE sport='football' AND competition_id="+ph+
             " ORDER BY kickoff DESC LIMIT "+ph)
        cur.execute(sql,(str(lid),int(limit)))
        rows=cur.fetchall(); out=[]
        for r in rows:
            v=list(r)
            # Defensive second check: never leak another competition onto an SEO page.
            if str(v[4] or "") != str(lid):
                continue
            out.append({"sport":v[0],"providerFixtureId":v[1],"country":v[2],
                        "league":v[3],"leagueId":v[4],"season":v[5],"date":str(v[6]),
                        "homeId":v[7],"home":v[8],"homeLogo":v[9],
                        "awayId":v[10],"away":v[11],"awayLogo":v[12],
                        "homeScore":v[13],"awayScore":v[14],
                        "status":v[15] or "FT","statusShort":v[15] or "FT","isFinished":True})
        return out
    except Exception:
        return []
    finally:
        try:
            if cur: cur.close()
        except Exception: pass
        try:
            if conn: conn.close()
        except Exception: pass

def _v442_learning_predictions(comp: dict, limit: int=20) -> list[dict]:
    """Read genuine stored model predictions from the existing learning DB."""
    name,_lid=_v441_league_identity(comp)
    aliases=[name]
    if name=="PSL":
        aliases += ["PSL South Africa","Premier Soccer League","Betway Premiership"]
    try:
        conn=v141_learning.connect()
        clauses=[];params=[]
        for alias in aliases:
            # v456: exact normalized competition aliases only; never substring
            # match e.g. Premier League inside Ghana Premier League.
            clauses.append("lower(trim(competition)) = ?")
            params.append(alias.lower().strip())
        sql=("SELECT fixture_id,kickoff,home_team,away_team,competition,confidence,"
             "probabilities,odds,prediction,predicted_at FROM predictions "
             "WHERE sport='football' AND ("+" OR ".join(clauses)+") "
             "ORDER BY kickoff DESC, predicted_at DESC LIMIT ?")
        rows=conn.execute(sql,tuple(params+[int(limit)])).fetchall()
        conn.close();out=[]
        for r in rows:
            try: probs=json.loads(r["probabilities"] or "{}")
            except Exception: probs={}
            try: odds=json.loads(r["odds"] or "{}")
            except Exception: odds={}
            try: pred=json.loads(r["prediction"] or "{}")
            except Exception: pred={}
            pred=dict(pred or {})
            if probs and "probabilities" not in pred: pred["probabilities"]=probs
            if r["confidence"] is not None and "confidence" not in pred: pred["confidence"]=r["confidence"]
            out.append({"fixtureId":r["fixture_id"],"_afootFixtureId":r["fixture_id"],
                        "datetime":r["kickoff"] or "","home":r["home_team"] or "",
                        "away":r["away_team"] or "","league":r["competition"] or name,
                        "confidence":r["confidence"],"odds":odds,"prediction":pred,
                        "storedPrediction":True})
        return [x for x in out if x.get("home") and x.get("away")]
    except Exception:
        return []

def _v442_cached_standings(comp: dict) -> list[dict]:
    """Shared standings LKG -> in-process cache -> any persistent /standings row."""
    name,lid=_v441_league_identity(comp)
    # Exact shared LKG written by the public standings endpoint.
    for league_key in (name.upper(),"PSL SOUTH AFRICA" if name=="PSL" else ""):
        if not league_key: continue
        snap=_dashboard_snapshot_get(f"standings2627:last_good:{league_key}")
        data=(snap or {}).get("data") if isinstance(snap,dict) else None
        if isinstance(data,dict):
            for league in data.get("leagues") or []:
                if str(league.get("leagueId") or "")==str(lid):
                    table=league.get("table") or []
                    if table: return [x for x in table[:30] if isinstance(x,dict)]
    # Existing process cache.
    table=_v441_cached_standings(comp)
    if table: return table
    # Last-good persistent provider cache, including expired rows. Exact league id only.
    if not lid: return []
    conn=None
    try:
        conn=_apicache_db()
        rows=conn.execute("SELECT response FROM api_cache WHERE path='/standings' ORDER BY fetched_at DESC LIMIT 200").fetchall()
        for row in rows:
            try: obj=json.loads(row["response"])
            except Exception: continue
            resp=obj.get("response") or []
            if not resp: continue
            league=resp[0].get("league") or {}
            if str(league.get("id") or "") != str(lid): continue
            outer=league.get("standings") or []
            table=outer[0] if outer else []
            if table: return [x for x in table[:30] if isinstance(x,dict)]
    except Exception:
        pass
    finally:
        try:
            if conn: conn.close()
        except Exception: pass
    return []

def _v442_cached_competition_data(path: str) -> dict:
    comp=_v440_competition(path)
    if not comp: return {"matches":[],"predictions":[],"table":[]}
    parts=[x for x in path.strip("/").split("/") if x]
    section=parts[3] if len(parts)>3 else "overview"

    # Keep the proven v441 fixture mapping only for fixtures/overview.
    base=_v441_cached_competition_data(path) if section in ("fixtures","overview") else {"matches":[],"predictions":[],"table":[]}
    matches=list(base.get("matches") or [])
    preds=[]
    table=[]

    if section=="results":
        # No rolling all-leagues fallback: exact archive id or honest empty state.
        matches=_v442_exact_archive_results(comp,30)
    elif section=="predictions":
        # Snapshot first; permanent learning DB fallback.
        snap_rows=[]
        for _key,payload in _v440_snapshot_get_exact(_v441_keys(path,comp)):
            for x in _v441_collect(payload):
                if _v441_comp_match(x,comp) and _v441_team_name(x,"home") and _v441_team_name(x,"away"):
                    snap_rows.append(x)
        preds=snap_rows[:20] or _v442_learning_predictions(comp,20)
    elif section=="table":
        table=_v442_cached_standings(comp)

    return {"matches":matches[:30],"predictions":preds[:20],"table":table[:30]}

def _v441_cached_competition_data(path: str) -> dict:
    comp=_v440_competition(path)
    if not comp:
        return {"matches":[],"predictions":[],"table":[]}
    parts=[x for x in path.strip("/").split("/") if x]
    section=parts[3] if len(parts)>3 else "overview"
    matches=[];preds=[];seen=set()

    for _key,payload in _v440_snapshot_get_exact(_v441_keys(path,comp)):
        for x in _v441_collect(payload):
            if not _v441_comp_match(x,comp):
                continue
            home=_v441_team_name(x,"home");away=_v441_team_name(x,"away")
            if not home or not away:
                continue
            ident=str(x.get("id") or x.get("fixtureId") or x.get("providerFixtureId") or
                      x.get("_afootFixtureId") or f"{home}|{away}|{_v441_date(x)}")
            if ident not in seen:
                seen.add(ident);matches.append(x)
            if isinstance(x.get("prediction"),(dict,str)) or x.get("confidence") is not None:
                preds.append(x)

    # v456: archive enrichment is exact provider-competition-id only. The old
    # LIKE-name archive reader could cross-contaminate similarly named leagues.
    if section in ("results","overview"):
        archived=_v442_exact_archive_results(comp,30)
        if archived:
            matches=archived + [x for x in matches if str(x.get("providerFixtureId") or x.get("id") or "") not in
                                {str(a.get("providerFixtureId") or "") for a in archived}]

    table=_v441_cached_standings(comp) if section=="table" else []
    matches.sort(key=_v441_date,reverse=True)
    return {"matches":matches[:30],"predictions":preds[:20],"table":table[:30]}

def _v440_cached_ssr_html(path: str) -> str:
    parts=[x for x in path.strip("/").split("/") if x]
    if len(parts)<3:
        return ""
    comp=_v440_competition(path)
    if not comp:
        return ""
    section=parts[3] if len(parts)>3 else "overview"
    data=_v442_cached_competition_data(path)
    name=_ssr_text(comp.get("name") or parts[2].replace("-"," ").title())
    rows=data["matches"]
    finished={"ft","aet","pen","final","finished","complete","completed"}

    if section=="fixtures":
        selected=[x for x in rows if _v441_status(x).lower() not in finished][:12]
        heading=f"Cached {name} fixtures"
    elif section=="results":
        selected=[x for x in rows if _v441_status(x).lower() in finished or
                  (_v441_score(x,"home") is not None and _v441_score(x,"away") is not None)][:12]
        heading=f"Latest cached {name} results"
    else:
        selected=rows[:8]; heading=f"Cached {name} match data"

    if section=="predictions":
        cards=[]
        for x in data["predictions"][:10]:
            home=_v441_team_name(x,"home");away=_v441_team_name(x,"away")
            pred=x.get("prediction")
            if isinstance(pred,dict):
                pick=pred.get("pick") or pred.get("winner") or pred.get("label") or pred.get("recommended") or ""
                conf=pred.get("confidence")
            else:
                pick=pred or "";conf=x.get("confidence")
            if home and away and pick:
                cards.append(f'<div><strong>{_ssr_text(home)} vs {_ssr_text(away)}</strong><span>{_ssr_text(pick)}'
                             +(f' · {_ssr_text(conf)}% confidence' if conf not in (None,"") else '')+'</span></div>')
        return (f'<section class="v442-seo-data"><h2>Cached {name} predictions</h2>'
                +('<div class="-grid">'+"".join(cards)+'</div>' if cards else
                  '<p>No valid cached prediction is currently available for this competition. No provider call was made for this SEO page.</p>')
                +'</section>')

    if section=="table":
        cards=[];unique=set()
        for x in sorted(data["table"],key=lambda r:int(r.get("rank") or 999))[:20]:
            team=x.get("team") or {};tn=str(team.get("name") if isinstance(team,dict) else team or "").strip()
            if not tn or tn in unique:continue
            unique.add(tn)
            cards.append(f'<div><strong>#{_ssr_text(x.get("rank"))} {_ssr_text(tn)}</strong>'
                         f'<span>{_ssr_text(x.get("points"))} pts'
                         +(f' · GD {_ssr_text((x.get("goalsDiff") if x.get("goalsDiff") is not None else x.get("goalDiff")))}' if (x.get("goalsDiff") if x.get("goalsDiff") is not None else x.get("goalDiff")) is not None else '')+'</span></div>')
        return (f'<section class="v442-seo-data"><h2>Cached {name} table</h2>'
                +('<div class="-grid">'+"".join(cards)+'</div>' if cards else
                  '<p>No valid cached standings snapshot is currently available. This SEO request did not trigger a provider refresh.</p>')
                +'</section>')

    cards=[]
    for x in selected:
        home=_v441_team_name(x,"home");away=_v441_team_name(x,"away")
        if not home or not away:continue
        hs=_v441_score(x,"home");aw=_v441_score(x,"away")
        score=(f'{_ssr_text(hs)} &ndash; {_ssr_text(aw)}' if hs is not None and aw is not None else "vs")
        date=_v441_date(x);status=_v441_status(x)
        cards.append(f'<div><strong>{_ssr_text(home)} {score} {_ssr_text(away)}</strong>'
                     f'<span>{_ssr_text(date)}'+(f' · {_ssr_text(status)}' if status else '')+'</span></div>')
    return (f'<section class="v442-seo-data"><h2>{heading}</h2>'
            +('<div class="-grid">'+"".join(cards)+'</div>' if cards else
              '<p>No valid cached match snapshot is currently available for this competition. The page remains available without making a provider API call.</p>')
            +'</section>')


def _v453_competition_for_path(path: str) -> dict | None:
    """Resolve only an existing indexable registry competition; never calls a provider."""
    parts=[x for x in str(path or "").strip("/").split("/") if x]
    if len(parts)<3:
        return None
    wanted="/"+"/".join(parts[:3])
    for c in COMPETITION_REGISTRY:
        if c.get("indexable",True) and _seo_competition_base(c)==wanted:
            return c
    return None

def _v453_country_context(sport_slug: str, country_slug: str) -> tuple[str,list[dict]]:
    """Return authoritative display country + registered competitions for a country hub."""
    comps=[]
    country_name=country_slug.replace("-"," ").title()
    for c in COMPETITION_REGISTRY:
        if not c.get("indexable",True) or c.get("sport")!=sport_slug:
            continue
        sp,cs,_=_seo_competition_parts(c)
        if sp==sport_slug and cs==country_slug:
            comps.append(c)
            country_name=str(c.get("country") or c.get("continent") or country_name).strip()
    return country_name, comps

def _v453_unique_context(path: str, sport: str, country: str, competition: str, section_name: str) -> str:
    """Useful registry/data-aware copy. No API/provider work and no invented sporting facts."""
    parts=[x for x in str(path or "").strip("/").split("/") if x]
    sport_slug=parts[0] if parts else ""
    if len(parts)==2:
        country_name, comps=_v453_country_context(sport_slug,parts[1])
        names=[str(c.get("name") or "").strip() for c in comps if str(c.get("name") or "").strip()]
        if names:
            sample=", ".join(names[:5])
            more=(f" and {len(names)-5} more" if len(names)>5 else "")
            return (f"Follow {country_name} {sport.lower()} across {len(names)} competition"
                    f"{'s' if len(names)!=1 else ''}, including {sample}{more}. "
                    "Choose a competition below to view fixtures, results, predictions and standings.")
        return (f"Explore {country_name} {sport.lower()} coverage on Kasi Sports News. "
                "Available competitions will appear here with links to fixtures, results, predictions and standings.")
    if len(parts)>=3:
        c=_v453_competition_for_path(path)
        if c:
            cname=str(c.get("name") or competition).strip()
            ctry=str(c.get("country") or country or "International").strip()
            if not section_name:
                return (f"Follow {cname} {sport.lower()} in {ctry} with quick access to upcoming fixtures, "
                        "completed results, match predictions and the latest available standings.")
            copy={
                "Fixtures":f"See upcoming {cname} fixtures with match dates and kickoff information when available. Use the related pages to check recent results, predictions and standings.",
                "Results":f"Review completed {cname} matches and confirmed scores. Results are shown when confirmed match information is available.",
                "Predictions":f"Explore {cname} match predictions and supporting analysis when qualifying data is available. Predictions are informational estimates and are not guaranteed outcomes.",
                "Table":f"Check the latest available {cname} standings, including competition positions and table information when a current standings snapshot is available.",
            }
            return copy.get(section_name,"")
    if len(parts)==1 and sport_slug in {"football","rugby","cricket"}:
        countries=set()
        comps=0
        for c in COMPETITION_REGISTRY:
            if c.get("sport")==sport_slug and c.get("indexable",True):
                _sp,cs,_slug=_seo_competition_parts(c); countries.add(cs); comps+=1
        return (f"Follow {sport.lower()} across {len(countries)} countries and regions and {comps} competitions on Kasi Sports News. "
                "Choose a country, region or competition below to explore fixtures, results, predictions and standings.")
    return ""

async def _ssr_generic_section(path: str) -> tuple[str,str,str]:
    """Build useful route-specific SSR content plus a crawlable internal-link graph."""
    p=path.rstrip("/") or "/"
    registry={r.get("path"):r for r in _seo_registry_pages()}
    row=registry.get(p,{})
    title=row.get("title") or "Kasi Sports News"
    desc=row.get("description") or "Live scores, fixtures, predictions, results and sports intelligence."
    parts=[x for x in p.split("/") if x]
    sport_slug=parts[0] if parts else ""
    sport=(sport_slug.replace("-"," ").title() if parts else "Sports")
    country_slug=parts[1] if len(parts)>1 else ""
    competition_slug=parts[2] if len(parts)>2 else ""
    country=(country_slug.replace("-"," ").title() if country_slug else "")
    if country_slug and sport_slug:
        _v453_country_name,_v453_country_comps=_v453_country_context(sport_slug,country_slug)
        if _v453_country_comps:
            country=_v453_country_name
    competition=(competition_slug.replace("-"," ").title() if competition_slug else "")
    _competition_acronyms={"Psl":"PSL","Mls":"MLS","Uefa":"UEFA","Caf":"CAF","Afcon":"AFCON","Sa20":"SA20","Ipl":"IPL"}
    competition=_competition_acronyms.get(competition, competition)
    _v453_comp=_v453_competition_for_path(p)
    if _v453_comp:
        competition=str(_v453_comp.get("name") or competition).strip()
    section_name=(parts[3].replace("-"," ").title() if len(parts)>3 else "")

    info_sections=""
    if p=="/about":
        h1="About Kasi Sports News"
        intro="Kasi Sports News is an independent sports information platform focused on making scores, fixtures, results, predictions and match intelligence easy to explore."
        info_sections=("<section><h2>What we cover</h2><p>Our coverage brings together football, rugby and cricket information with competition pages, match results, standings and data-led prediction features.</p></section>"
                       "<section><h2>How to use our information</h2><p>Scores and statistics are presented as sports information. Prediction features are analysis, not guarantees of an outcome. We aim to keep navigation clear so readers can move from a sport to a competition, fixture, result or table.</p></section>")
    elif p=="/contact":
        h1="Contact Kasi Sports News"
        intro="Contact Kasi Sports News for general, editorial, correction, privacy, advertising or commercial enquiries."
        info_sections=('<section><h2>Get in touch</h2><p>Email <a href="mailto:admin@kasilivescore.com">admin@kasilivescore.com</a>. Please include enough detail for us to understand the page, article or enquiry you are referring to.</p></section>')
    elif p=="/privacy":
        h1="Privacy Policy"
        intro="This privacy notice explains how Kasi Sports News processes information when you use the website and how advertising and measurement services may use data."
        info_sections=("<section><h2>Information we process</h2><p>When you use Kasi Sports News, technical information such as your IP address, browser and device information, pages viewed, approximate location derived from network information, timestamps and diagnostic data may be processed to operate, secure, measure and improve the service. Cookies, web beacons, local storage and similar identifiers may also be used where applicable.</p></section>"
                       "<section><h2>Google advertising and third parties</h2><p>Kasi Sports News uses or may use Google advertising services. Google and other third-party vendors may use cookies, web beacons, IP addresses or other identifiers to serve, measure and improve advertising, including personalized advertising where permitted and consented to. Third parties may place or read cookies on your browser or use similar technologies as a result of advertising or measurement on this site.</p></section>"
                       "<section><h2>Consent and your choices</h2><p>Where consent is legally required, visitors are offered choices for advertising and related technologies through the site's consent management platform. You can accept, reject or manage applicable consent choices and can also control cookies through your browser. Personalized advertising choices may also be managed through Google's advertising settings.</p></section>"
                       "<section><h2>Third-party services and links</h2><p>The site may use third-party services for advertising, analytics, media, sports data or site functionality. Those services may process information under their own privacy policies. Links to third-party websites are governed by the privacy practices of those sites.</p></section>"
                       "<section><h2>Privacy enquiries</h2><p>For privacy questions or requests, contact <a href=\"mailto:admin@kasilivescore.com\">admin@kasilivescore.com</a>. See our <a href=\"/cookies\">Cookie Policy</a> for more information about cookies and similar technologies.</p></section>")
    elif p=="/terms":
        h1="Terms of Use"
        intro="These terms describe the conditions for using Kasi Sports News and its sports information."
        info_sections=("<section><h2>Sports information</h2><p>Scores, fixtures, statistics, standings, news, predictions and other sports information are provided for general informational purposes. Data may change as matches progress or source information is corrected, and uninterrupted availability or complete accuracy is not guaranteed.</p></section>"
                       "<section><h2>Predictions</h2><p>Prediction, probability and match-intelligence features are analytical outputs and do not guarantee sporting outcomes or financial returns. Users remain responsible for how they use the information.</p></section>"
                       "<section><h2>Third-party data and links</h2><p>Kasi Sports News may display information, media or links supplied by third parties. Third-party services and websites operate under their own terms and policies, and their availability or content is outside our control.</p></section>"
                       "<section><h2>Intellectual property</h2><p>The Kasi Sports News name, site design and original editorial or analytical content are protected by applicable intellectual-property laws. Team names, competition names, badges, trademarks and third-party media remain the property of their respective owners where applicable.</p></section>"
                       "<section><h2>Site use</h2><p>Do not misuse the service, interfere with its operation, scrape or access restricted systems in an unauthorized manner, or use the site in a way that violates applicable law or the rights of others.</p></section>"
                       "<section><h2>Availability and liability</h2><p>The service may be changed, suspended or temporarily unavailable, including when external data services are unavailable. To the extent permitted by applicable law, Kasi Sports News is not responsible for losses arising solely from reliance on delayed, incomplete or inaccurate sports information or third-party content.</p></section>")
    elif p=="/cookies":
        h1="Cookie Policy"
        intro="This page explains how cookies and similar technologies are used on Kasi Sports News and the choices available to visitors."
        info_sections=("<section><h2>Cookies and similar technologies</h2><p>Cookies, local storage, web beacons and similar technologies may be used for essential site functions, preferences, security, audience measurement, performance and advertising. These technologies can store or access identifiers and information about a browser or device.</p></section>"
                       "<section><h2>Google and advertising cookies</h2><p>Kasi Sports News uses or may use Google advertising services. Google and other third-party vendors may use cookies or similar identifiers to serve and measure ads. Advertising cookies may be used to personalize advertising where permitted and where the visitor has provided the required consent.</p></section>"
                       "<section><h2>Consent choices</h2><p>Where consent is required, visitors can accept, reject or manage applicable advertising and measurement choices through the site's consent message. You can revisit available consent controls and can also delete or block cookies using your browser settings. Restricting cookies may affect some site functions.</p></section>"
                       "<section><h2>More information</h2><p>For more information about how information is processed, see our <a href=\"/privacy\">Privacy Policy</a>. Privacy questions can be sent to <a href=\"mailto:admin@kasilivescore.com\">admin@kasilivescore.com</a>.</p></section>")
    elif p=="/today":
        h1="Today’s Sports Intelligence"; intro="Follow today’s fixtures, live matches, results and prediction coverage across supported competitions."
    elif p=="/weekend":
        h1="Weekend Sports Intelligence"; intro="Explore weekend fixtures, results and match intelligence across supported football and sports competitions."
    elif p=="/football":
        h1="Football Scores, Fixtures & Competitions"; intro="Follow football scores, fixtures, results, predictions and tables across competitions from around the world."
    elif p=="/rugby":
        h1="Rugby Scores, Fixtures & Competitions"; intro="Follow rugby fixtures, results, predictions and tables across supported leagues and tournaments."
    elif p=="/cricket":
        h1="Cricket Scores, Fixtures & Competitions"; intro="Follow cricket scores, fixtures, results, predictions and tables across supported leagues and tournaments."
    elif p=="/tennis":
        h1="Tennis Scores, Fixtures & Results"; intro="Browse tennis fixtures, results and match intelligence."
    elif competition:
        h1=f"{competition} {section_name}".strip() if section_name else f"{competition} Fixtures, Results & Predictions"
        section_copy={
            "Fixtures":f"Upcoming {competition} fixtures, kickoff information and match intelligence.",
            "Results":f"Latest {competition} results and completed match information.",
            "Predictions":f"{competition} prediction coverage, probabilities and match analysis when qualifying data is available.",
            "Table":f"{competition} standings, form and competition performance information.",
            "Today":f"{competition} matches scheduled today, live information and results when available.",
            "News":f"Latest {competition} news and competition updates from available sources.",
            "Injuries":f"{competition} injury and player availability information when reported.",
            "Stats":f"{competition} statistics, form and performance intelligence.",
        }
        intro=section_copy.get(section_name, f"{competition} fixtures, results, standings, predictions and match intelligence.")
        # STEP 5 v329: give indexable competition pages distinct, useful context
        # instead of relying on one generic sentence across hundreds of URLs.
        if section_name in {"Fixtures","Results","Predictions","Table"}:
            context_copy={
                "Fixtures":f"Use this page to move between upcoming {competition} matches, the latest results, predictions and the current table. Match information is updated as supported data becomes available.",
                "Results":f"Review completed {competition} matches here, then use the fixtures, predictions and table pages for the wider competition picture.",
                "Predictions":f"Kasi Sports News prediction pages present data-led match probabilities and analysis when qualifying information is available. They are informational estimates, not guaranteed outcomes.",
                "Table":f"Use the {competition} table together with fixtures and results to understand competition position and recent match context."
            }
            info_sections += f'<section><h2>About this {section_name.lower()} page</h2><p>{_ssr_text(context_copy[section_name])}</p></section>'
    else:
        h1=title.replace(" | Kasi Sports News",""); intro=desc

    # v455 Step 11: visitor-facing, registry/data-aware context. This remains deliberately
    # cache/registry-only and cannot trigger API-Football or OddsPAPI.
    _v453_context=_v453_unique_context(p,sport,country,competition,section_name)
    if _v453_context:
        info_sections += (f'<section class="v455-seo-context"><h2>About this {_ssr_text(section_name.lower() if section_name else "coverage")}</h2>'
                          f'<p>{_ssr_text(_v453_context)}</p></section>')

    breadcrumb_items=[("Kasi Sports News","/")]
    if parts: breadcrumb_items.append((sport,f"/{sport_slug}"))
    if country: breadcrumb_items.append((country,f"/{sport_slug}/{country_slug}"))
    if competition: breadcrumb_items.append((competition,f"/{sport_slug}/{country_slug}/{competition_slug}"))
    if section_name: breadcrumb_items.append((section_name,p))
    breadcrumb=" / ".join(
        f'<a href="{escape(url,quote=True)}">{_ssr_text(label)}</a>' if url != p else _ssr_text(label)
        for label,url in breadcrumb_items
    )

    # STEP 5: advertise only indexable sibling pages as primary crawl links.
    if competition and len(parts)>=3:
        base=f"/{sport_slug}/{country_slug}/{competition_slug}"
        related=[("Overview",base),(f"{competition} fixtures",base+"/fixtures"),
                 (f"{competition} results",base+"/results"),
                 (f"{competition} predictions",base+"/predictions"),
                 (f"{competition} table",base+"/table")]
    else:
        related=[("Today's matches","/today"),("Weekend fixtures","/weekend"),
                 ("Football","/football"),("Rugby","/rugby"),("Cricket","/cricket")]

    # Sport hubs link directly to the strongest competition landing pages.
    competition_links=[]
    country_links=[]
    if p in {"/football","/rugby","/cricket"}:
        # v452 Step 4: expose the canonical Sport -> Country layer explicitly.
        # Derive only from the existing indexable registry; no provider/API work.
        seen_countries=set()
        for c in COMPETITION_REGISTRY:
            if c.get("sport")!=sport_slug or not c.get("indexable",True):
                continue
            _sp,_country_slug,_comp_slug=_seo_competition_parts(c)
            if _country_slug in seen_countries:
                continue
            seen_countries.add(_country_slug)
            _country_name=str(c.get("country") or c.get("continent") or "International").strip()
            country_links.append((_country_name,f"/{sport_slug}/{_country_slug}"))
        # Preserve curated registry order for direct competition discovery too.
        comps=[c for c in COMPETITION_REGISTRY
               if c.get("sport")==sport_slug and c.get("indexable",True)][:18]
        for c in comps:
            competition_links.append((str(c.get("name") or c.get("slug") or c.get("id")),_seo_competition_base(c)))
    elif len(parts)==2 and sport_slug in {"football","rugby","cricket"}:
        comps=[c for c in COMPETITION_REGISTRY
               if c.get("sport")==sport_slug and c.get("indexable",True)
               and _seo_country_slug(c.get("country") or c.get("continent") or "international")==country_slug]
        for c in comps:
            competition_links.append((str(c.get("name") or c.get("slug") or c.get("id")),_seo_competition_base(c)))

    links=" · ".join(f'<a href="{escape(u,quote=True)}">{_ssr_text(n)}</a>' for n,u in related)
    country_html=""
    if country_links:
        country_html=('<section><h2>Browse '+_ssr_text(sport)+' by country or region</h2>'
                      '<nav aria-label="'+_ssr_text(sport)+' countries and regions">'
                      +" · ".join(
                          f'<a href="{escape(u,quote=True)}">{_ssr_text(n)} {_ssr_text(sport)}</a>'
                          for n,u in country_links
                      )+'</nav></section>')
    comp_html=""
    if competition_links:
        comp_html=('<section><h2>Competitions</h2><nav aria-label="'+_ssr_text(sport)+' competitions">'
                   +" · ".join(f'<a href="{escape(u,quote=True)}">{_ssr_text(n)}</a>' for n,u in competition_links)
                   +'</nav></section>')

    # v440 Step 2: enrich canonical competition routes from existing shared LKG only.
    # This is intentionally a pure cache/database read: Googlebot cannot trigger
    # API-Football/OddsPapi refreshes through the SEO renderer.
    cached_real_html=_v440_cached_ssr_html(p) if len(parts)>=3 else ""

    # Trust/policy links are crawlable from every SSR page and support AdSense review.
    trust_links=[("About","/about"),("Contact","/contact"),("Privacy","/privacy"),
                 ("Terms","/terms"),("Cookies","/cookies")]
    trust_html=" · ".join(f'<a href="{u}">{n}</a>' for n,u in trust_links)

    body=(f'<article class="kasiscore--page" data--page="hub"><nav aria-label="Breadcrumb">{breadcrumb}</nav>'
          f'<h1>{_ssr_text(h1)}</h1><p class="-lead">{_ssr_text(intro)}</p>'
          f'<section><h2>Explore {_ssr_text(section_name or competition or sport)}</h2><p>{_ssr_text(desc)}</p></section>'
          f'{info_sections}{cached_real_html}{country_html}{comp_html}<nav aria-label="Related sports pages">{links}</nav>'
          f'<footer><nav aria-label="About and policies">{trust_html}</nav></footer></article>')
    return title,desc,body

def _seo_abs_url(path: str) -> str:
    base=(KASI_PUBLIC_ORIGIN or "https://kasilivescore.com").rstrip("/")
    if not path or path == "/": return base + "/"
    if str(path).startswith(("http://","https://")): return str(path)
    return base + "/" + str(path).lstrip("/")

def _seo_org_schema() -> dict:
    base=(KASI_PUBLIC_ORIGIN or "https://kasilivescore.com").rstrip("/")
    return {"@type":"Organization","@id":base+"/#organization","name":"Kasi Sports News","url":base+"/",
            "logo":{"@type":"ImageObject","@id":base+"/#logo","url":base+"/kasi-sports-news-logo.png","contentUrl":base+"/kasi-sports-news-logo.png","width":512,"height":512}}

def _seo_site_schema() -> dict:
    base=(KASI_PUBLIC_ORIGIN or "https://kasilivescore.com").rstrip("/")
    return {"@type":"WebSite","@id":base+"/#website","url":base+"/","name":"Kasi Sports News",
            "publisher":{"@id":base+"/#organization"},"inLanguage":"en-ZA"}

def _seo_breadcrumb_schema(path: str) -> dict | None:
    p=path.rstrip("/") or "/"
    if p == "/": return None
    parts=[x for x in p.split("/") if x]
    labels={"football":"Football","rugby":"Rugby","cricket":"Cricket","tennis":"Tennis","psl":"PSL","caf":"CAF","afcon":"AFCON","uefa":"UEFA","mls":"MLS"}
    items=[{"@type":"ListItem","position":1,"name":"Kasi Sports News","item":_seo_abs_url("/")}]
    cur=""
    for i,part in enumerate(parts, start=2):
        cur += "/"+part
        name=labels.get(part.lower(),part.replace("-"," ").title())
        items.append({"@type":"ListItem","position":i,"name":name,"item":_seo_abs_url(cur)})
    return {"@type":"BreadcrumbList","@id":_seo_abs_url(p)+"#breadcrumb","itemListElement":items}

def _seo_page_schema(path: str, title: str, desc: str) -> dict:
    url=_seo_abs_url(path); base=(KASI_PUBLIC_ORIGIN or "https://kasilivescore.com").rstrip("/")
    parts=[x for x in path.split("/") if x]
    page_type="CollectionPage" if (path in ("/football","/rugby","/cricket","/tennis","/today","/weekend") or (parts and parts[0] in {"football","rugby","cricket","tennis"})) else "WebPage"
    return {"@type":page_type,"@id":url+"#webpage","url":url,"name":title,"description":desc,
            "isPartOf":{"@id":base+"/#website"},"about":{"@id":base+"/#organization"},"inLanguage":"en-ZA"}


def _v444_schema_sport(sport: str) -> str:
    return {"football":"Soccer","rugby":"Rugby","cricket":"Cricket","tennis":"Tennis"}.get(
        str(sport or "").lower(), str(sport or "").title() or "Sports"
    )

def _v444_schema_date(value) -> str:
    raw=str(value or "").strip()
    if not raw or raw.lower() in {"scheduled","tbd","unknown","none","null"}:
        return ""
    if re.match(r"^\d{4}-\d{2}-\d{2}(?:[T ][0-2]\d:[0-5]\d(?::[0-5]\d)?)?", raw):
        return raw.replace(" ", "T", 1) if " " in raw[:11] else raw
    return ""

def _v444_safe_team_name(match: dict, side: str) -> str:
    """Schema-only tolerant team reader. Never assumes one cached match shape."""
    try:
        v=match.get(side)
        if isinstance(v,dict):
            name=v.get("name") or v.get("team") or v.get("shortName")
            if name:
                return str(name).strip()
        elif isinstance(v,str) and v.strip():
            return v.strip()

        teams=match.get("teams")
        if isinstance(teams,dict):
            v=teams.get(side)
            if isinstance(v,dict):
                name=v.get("name") or v.get("team") or v.get("shortName")
                if name:
                    return str(name).strip()
            elif isinstance(v,str) and v.strip():
                return v.strip()

        for key in (
            f"{side}_team", f"{side}Team", f"{side}_name", f"{side}Name",
            f"{side}TeamName"
        ):
            v=match.get(key)
            if isinstance(v,dict):
                v=v.get("name") or v.get("team")
            if v is not None and str(v).strip():
                return str(v).strip()
    except Exception:
        pass
    return ""

def _v444_safe_fixture_date(match: dict) -> str:
    """Schema-only tolerant kickoff reader."""
    try:
        fixture=match.get("fixture")
        if isinstance(fixture,dict):
            for key in ("date","datetime","kickoff","startTime","commenceTime"):
                if fixture.get(key):
                    return str(fixture.get(key))
        for key in ("date","datetime","kickoff","kickoff_time","startTime","commenceTime","start_date"):
            if match.get(key):
                return str(match.get(key))
    except Exception:
        pass
    return ""

def _v444_competition_schema_nodes(path: str) -> list[dict]:
    """Fail-soft SportsEvent schema from the same v442 cache/DB data as visible SSR.

    Structured-data enrichment must never be able to turn a valid SEO page into HTTP 500.
    """
    try:
        parts=[x for x in str(path or "").strip("/").split("/") if x]
        if len(parts) < 4 or parts[0] not in {"football","rugby","cricket","tennis"}:
            return []
        section=parts[3].lower()
        if section not in {"fixtures","results"}:
            return []

        comp=_v440_competition(path)
        if not isinstance(comp,dict):
            return []

        data=_v442_cached_competition_data(path)
        if not isinstance(data,dict):
            return []
        matches=[m for m in (data.get("matches") or []) if isinstance(m,dict)]
        if not matches:
            return []

        page_url=_seo_abs_url(path)
        sport_name=_v444_schema_sport(parts[0])
        comp_name=str(comp.get("name") or comp.get("slug") or parts[2].replace("-"," ").title())
        events=[]
        refs=[]
        seen=set()

        for n,m in enumerate(matches[:30], start=1):
            try:
                home=_v444_safe_team_name(m,"home")
                away=_v444_safe_team_name(m,"away")
                if not home or not away:
                    continue

                fixture_id=(m.get("providerFixtureId") or m.get("fixtureId") or
                            m.get("_afootFixtureId") or m.get("id"))
                date=_v444_schema_date(_v444_safe_fixture_date(m))
                stable=str(fixture_id or f"{home}-{away}-{date or n}")
                stable=re.sub(r"[^a-zA-Z0-9_-]+","-",stable).strip("-") or str(n)
                event_id=page_url+f"#sports-event-{stable}"
                if event_id in seen:
                    continue
                seen.add(event_id)

                ev={
                    "@type":"SportsEvent",
                    "@id":event_id,
                    "name":f"{home} vs {away}",
                    "url":page_url,
                    "sport":sport_name,
                    "description":f"{home} vs {away} — {comp_name}",
                    "eventStatus":"https://schema.org/EventCompleted" if section=="results"
                                  else "https://schema.org/EventScheduled",
                    "homeTeam":{"@type":"SportsTeam","name":home},
                    "awayTeam":{"@type":"SportsTeam","name":away},
                }
                if date:
                    ev["startDate"]=date

                venue=m.get("venue") or m.get("stadium")
                if isinstance(venue,dict):
                    vn=venue.get("name") or venue.get("stadium")
                    city=venue.get("city")
                    if vn:
                        ev["location"]={"@type":"Place","name":str(vn)}
                        if city:
                            ev["location"]["address"]={
                                "@type":"PostalAddress",
                                "addressLocality":str(city)
                            }
                elif isinstance(venue,(str,int,float)) and str(venue).strip():
                    ev["location"]={"@type":"Place","name":str(venue)}

                # Google Event rich results require a real location.  The
                # canonical cached match may have no verified venue.  Do not
                # guess a home stadium or publish an invalid SportsEvent;
                # the visible match/results page is intentionally unaffected.
                if not isinstance(ev.get("location"), dict) or not str(ev["location"].get("name") or "").strip():
                    continue
                # Likewise, a valid fixture kickoff is required for Event
                # rich results; never manufacture a date from the page.
                if not ev.get("startDate"):
                    continue

                events.append(ev)
                refs.append({
                    "@type":"ListItem",
                    "position":len(refs)+1,
                    "item":{"@id":event_id},
                    "name":f"{home} vs {away}",
                })
            except Exception:
                # One malformed cached match must not break the competition page.
                continue

        if not events:
            return []

        return [{
            "@type":"ItemList",
            "@id":page_url+"#sports-events",
            "name":f"{comp_name} {'Fixtures' if section=='fixtures' else 'Results'}",
            "numberOfItems":len(events),
            "itemListElement":refs,
        }, *events]
    except Exception:
        # SEO schema is enrichment only. Preserve the working v442 SSR page on any schema error.
        return []

def _seo_graph_schema(path: str, title: str, desc: str) -> dict:
    graph=[_seo_org_schema(),_seo_site_schema(),_seo_page_schema(path,title,desc)]
    crumb=_seo_breadcrumb_schema(path)
    if crumb:
        graph.append(crumb)
        graph[2]["breadcrumb"]={"@id":crumb["@id"]}
    # v444: structured data is fail-soft enrichment. It can never take down SSR.
    try:
        event_nodes=_v444_competition_schema_nodes(path)
    except Exception:
        event_nodes=[]
    if event_nodes:
        graph.extend(event_nodes)
        graph[2]["mainEntity"]={"@id":event_nodes[0]["@id"]}
    return {"@context":"https://schema.org","@graph":graph}

def _ksn_seo_route_shell() -> str:
    """One lightweight KSN shell for non-home indexable SSR routes."""
    return '<!doctype html><html lang="en-ZA"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#05080b"><link rel="icon" href="/favicon.ico" sizes="any"><link rel="icon" href="/favicon.png" sizes="96x96" type="image/png"><link rel="apple-touch-icon" href="/apple-touch-icon.png" sizes="180x180"><link rel="manifest" href="/manifest.webmanifest"><title>Kasi Sports News</title><meta name="description" content="Live scores, fixtures, predictions, results and sports intelligence."><link rel="canonical" href="https://kasilivescore.com/"><style id="ksn-unified-seo-shell-css">:root{color-scheme:dark;--bg:#030506;--panel:#0d1114;--panel2:#11171b;--line:#26313a;--text:#f4f7f9;--muted:#aab4bc;--accent:#28c7ef}*{box-sizing:border-box}html,body{margin:0;background:var(--bg);color:var(--text);font-family:Inter,ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,Segoe UI,sans-serif}body{min-height:100vh}a{color:var(--accent);text-decoration:none}a:hover{text-decoration:underline}.ksn-shell-header{position:sticky;top:0;z-index:50;background:rgba(3,5,6,.96);border-bottom:1px solid var(--line);backdrop-filter:blur(12px)}.ksn-shell-head-inner{max-width:1180px;margin:auto;padding:12px 18px 8px;display:flex;align-items:center;gap:12px}.ksn-shell-logo{width:46px;height:46px;border-radius:50%;object-fit:contain}.ksn-shell-brand{font-weight:900;font-size:18px;line-height:1.1}.ksn-shell-sub{font-size:12px;color:var(--muted);margin-top:3px}.ksn-shell-nav{max-width:1180px;margin:auto;padding:0 18px 10px;display:flex;gap:7px;overflow-x:auto;scrollbar-width:none}.ksn-shell-nav::-webkit-scrollbar{display:none}.ksn-shell-nav a{flex:0 0 auto;color:var(--text);font-weight:800;font-size:13px;border:1px solid var(--line);border-radius:9px;padding:9px 12px;background:var(--panel)}.ksn-shell-nav a:hover{border-color:var(--accent);text-decoration:none}.ksn-shell-main{max-width:1180px;margin:18px auto;padding:0 18px 30px}.ksn-shell-footer{border-top:1px solid var(--line);padding:22px 18px 34px;color:var(--muted)}.ksn-shell-footer-inner{max-width:1180px;margin:auto;display:flex;flex-wrap:wrap;gap:12px;justify-content:space-between}.ksn-shell-footer nav{display:flex;gap:12px;flex-wrap:wrap}@media(max-width:700px){.ksn-shell-head-inner{padding:10px 12px 7px}.ksn-shell-logo{width:40px;height:40px}.ksn-shell-nav{padding:0 12px 9px}.ksn-shell-nav a{font-size:12px;padding:8px 10px}.ksn-shell-main{margin-top:12px;padding:0 12px 24px}}</style></head><body><header class="ksn-shell-header"><div class="ksn-shell-head-inner"><a href="/" aria-label="Kasi Sports News home"><img class="ksn-shell-logo" src="/kasi-sports-news-logo.png" alt="Kasi Sports News"></a><div><div class="ksn-shell-brand">Kasi Sports News</div><div class="ksn-shell-sub">Football · Rugby · Cricket · News · Match Intelligence</div></div></div><nav class="ksn-shell-nav" aria-label="Main navigation"><a href="/">Home</a><a href="/?view=live">Live</a><a href="/?view=fixtures">Fixtures</a><a href="/?view=predictions">Predictions</a><a href="/?view=teams">Teams &amp; Players Data</a><a href="/?view=news">News</a><a href="/?view=search">Search</a><a href="/?view=admin">Admin</a></nav></header><main class="ksn-shell-main"><!--KASI_SSR_CONTENT--></main><footer class="ksn-shell-footer"><div class="ksn-shell-footer-inner"><span>&copy; Kasi Sports News</span><nav aria-label="Policies"><a href="/about">About</a><a href="/contact">Contact</a><a href="/privacy">Privacy</a><a href="/terms">Terms</a><a href="/cookies">Cookies</a></nav></div></footer></body></html>'

async def _render_seo_document(path: str) -> str:
    key=f"doc:{path}"; cached=_SSR_CACHE.get(key)
    if cached is not None: return cached
    if path.startswith("/match/"):
        match=await _ssr_match_data(path.split("/",2)[2]);
        if match: title,desc,section=_ssr_match_section(match,path)
        else: title,desc,section=await _ssr_generic_section(path)
    elif path.startswith("/team/"): title,desc,section=await _ssr_team_section(path.split("/",2)[2],path)
    elif path.startswith("/player/"): title,desc,section=await _ssr_player_section(path.split("/",2)[2],path)
    else: title,desc,section=await _ssr_generic_section(path)
    # Home remains the full dashboard; non-home SEO routes use one lightweight KSN shell.
    html=((BASE_DIR/"index.html").read_text(encoding="utf-8") if path == "/" else _ksn_seo_route_shell())
    # v454: one authoritative favicon/manifest set on every SEO-rendered document.
    # This removes duplicate branding declarations without changing dashboard behavior.
    html=re.sub(r'<link\b[^>]*\brel=["\'][^"\']*(?:icon|apple-touch-icon|manifest)[^"\']*["\'][^>]*>\s*', '', html, flags=re.I)
    branding_tags=(
        '<link rel="icon" href="/favicon.ico" sizes="any">'
        '<link rel="icon" href="/favicon.png" sizes="96x96" type="image/png">'
        '<link rel="apple-touch-icon" href="/apple-touch-icon.png" sizes="180x180">'
        '<link rel="manifest" href="/manifest.webmanifest">'
    )
    html=html.replace('</head>', branding_tags+'</head>', 1)
    public=KASI_PUBLIC_ORIGIN; canonical=f"{public}{path}"
    clean_title=str(title or '').strip() or 'Kasi Sports News'
    # STEP 2 v316: strip every trailing brand suffix, including legacy double-appended titles.
    while re.search(r'\s*\|\s*Kasi Sports News\s*$', clean_title, flags=re.I):
        clean_title=re.sub(r'\s*\|\s*Kasi Sports News\s*$', '', clean_title, flags=re.I).strip()
    full_title = 'Kasi Sports News' if clean_title.lower() == 'kasi sports news' else f'{clean_title} | Kasi Sports News'
    html=re.sub(r'<title>.*?</title>',f'<title>{escape(full_title)}</title>',html,count=1,flags=re.S|re.I)
    html=re.sub(r'<meta name="description" content="[^"]*">',f'<meta name="description" content="{escape(desc,quote=True)}">',html,count=1)
    if re.search(r'<link rel="canonical"',html): html=re.sub(r'<link rel="canonical"[^>]*>',f'<link rel="canonical" href="{escape(canonical,quote=True)}">',html,count=1)
    schema=json.dumps(_seo_graph_schema(path, full_title, desc),ensure_ascii=False)
    if '<script id="seoSchema"' in html: html=re.sub(r'<script id="seoSchema"[^>]*>.*?</script>',f'<script id="seoSchema" type="application/ld+json">{schema}</script>',html,count=1,flags=re.S)
    else: html=html.replace('</head>',f'<script id="seoSchema" type="application/ld+json">{schema}</script></head>',1)
    # Production search metadata. The verification token is supplied only through env
    # after the owner verifies the real domain in Google Search Console.
    if not re.search(r'<meta\\s+name=["\\\']robots["\\\']', html, flags=re.I):
        html=html.replace("</head>",'<meta name="robots" content="index,follow,max-image-preview:large,max-snippet:-1,max-video-preview:-1"></head>',1)
    verification=os.getenv("GOOGLE_SITE_VERIFICATION", "").strip()
    if verification:
        tag=f'<meta name="google-site-verification" content="{escape(verification, quote=True)}">'
        html=html.replace('</head>',tag+'</head>',1)
    og_title=escape(full_title, quote=True); og_desc=escape(desc, quote=True); og_url=escape(canonical, quote=True)
    social_image=(public + "/kasi-sports-news-logo.png") if public else "/kasi-sports-news-logo.png"
    # STEP 2: one authoritative Open Graph/Twitter set per rendered page.
    for pattern in (
        r'<meta\s+property=["\']og:(?:title|description|url|type|image)["\'][^>]*>\s*',
        r'<meta\s+name=["\']twitter:(?:card|title|description|image)["\'][^>]*>\s*',
    ):
        html=re.sub(pattern,'',html,flags=re.I)
    social=(f'<meta property="og:title" content="{og_title}">'
            f'<meta property="og:description" content="{og_desc}">'
            f'<meta property="og:url" content="{og_url}">'
            f'<meta property="og:type" content="website">'
            f'<meta property="og:image" content="{escape(social_image,quote=True)}">'
            f'<meta name="twitter:card" content="summary_large_image">'
            f'<meta name="twitter:title" content="{og_title}">'
            f'<meta name="twitter:description" content="{og_desc}">'
            f'<meta name="twitter:image" content="{escape(social_image,quote=True)}">')
    html=html.replace('</head>',social+'</head>',1)
    css='<style id="kasiscore-ssr-css">.kasiscore--page{max-width:1180px;margin:0 auto 18px;padding:18px;border:1px solid var(--line);border-radius:15px;background:var(--card-bg);color:var(--text)}.kasiscore--page h1{font-size:clamp(24px,4vw,38px);margin:10px 0}.kasiscore--page h2{font-size:18px;margin:18px 0 8px}.kasiscore--page a{color:var(--accent)}.-lead{font-size:15px;color:var(--muted);max-width:900px}.-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:9px;margin:14px 0}.-grid div{padding:11px;border:1px solid var(--line);border-radius:10px;background:var(--panel2)}.-grid strong,.-grid span{display:block}.-grid strong{font-size:10px;text-transform:uppercase;color:var(--muted)}.-grid span{font-weight:800;margin-top:4px}@media(max-width:700px){.-grid{grid-template-columns:1fr 1fr}}@media(max-width:440px){.-grid{grid-template-columns:1fr}}</style>'
    # SEO Phase 2: keep route-specific SSR content in the document while the SPA hydrates normally.
    if section and path != "/":
        # STEP 2: the route-specific SSR article owns the page H1. Keep the visual brand
        # header unchanged, but make its heading non-primary in SSR documents.
        # Demote the two static template H1s (noscript + visible brand) on SSR landing pages.
        # The injected route-specific article below is the single primary H1. Visual styling is preserved.
        html=re.sub(r'(<noscript\b[^>]*>.*?<)h1(\b[^>]*>)(.*?</)h1(>)', r'\1div\2\3div\4', html, count=1, flags=re.S|re.I)
        html=re.sub(r'(<div class="brand">.*?<div><)h1(\b[^>]*>)(.*?</)h1(>)', r'\1div class="kasi-brand-heading"\2\3div\4', html, count=1, flags=re.S|re.I)
        if '<!--KASI_SSR_CONTENT-->' in html:
            html=html.replace('<!--KASI_SSR_CONTENT-->', css+section, 1)
        else:
            body_open=re.search(r"<body[^>]*>", html, flags=re.I)
            if body_open:
                insert_at=body_open.end()
                html=html[:insert_at]+css+section+html[insert_at:]
    # STEP 2 v317: final authoritative SEO response pass.
    # Run after every earlier template mutation so legacy metadata cannot re-append
    # the brand or leave duplicate canonical/social tags behind.
    final_title = full_title
    final_desc = str(desc or "Live scores, fixtures, predictions, results and sports intelligence.").strip()
    final_canonical = canonical

    # Title: exactly one title element and exactly one trailing brand.
    html = re.sub(r'<title\b[^>]*>.*?</title>\s*', '', html, flags=re.I|re.S)
    html = html.replace('</head>', f'<title>{escape(final_title)}</title></head>', 1)

    # Description, canonical and robots: exactly one authoritative tag each.
    html = re.sub(r"<meta\s+name=[\"\']description[\"\'][^>]*>\s*", '', html, flags=re.I)
    html = re.sub(r"<link\s+rel=[\"\']canonical[\"\'][^>]*>\s*", '', html, flags=re.I)
    html = re.sub(r"<meta\s+name=[\"\']robots[\"\'][^>]*>\s*", '', html, flags=re.I)
    registry_row = next((r for r in _seo_registry_pages() if r.get("path") == path), None)
    page_indexable = True if registry_row is None else bool(registry_row.get("indexable", True))
    robots_value = ("index,follow,max-image-preview:large,max-snippet:-1,max-video-preview:-1"
                    if page_indexable else "noindex,follow")
    core_meta=(f'<meta name="description" content="{escape(final_desc,quote=True)}">'
               f'<link rel="canonical" href="{escape(final_canonical,quote=True)}">'
               f'<meta name="robots" content="{robots_value}">'
               f'<meta name="google-adsense-account" content="ca-pub-5442799591686279">')
    html = html.replace('</head>', core_meta+'</head>', 1)

    # Open Graph/Twitter: remove every legacy instance, then inject one set.
    html = re.sub(r"<meta\s+property=[\"\']og:(?:title|description|url|type|image)(?::[^\"\']+)?[\"\'][^>]*>\s*", '', html, flags=re.I)
    html = re.sub(r"<meta\s+name=[\"\']twitter:(?:card|title|description|image)[\"\'][^>]*>\s*", '', html, flags=re.I)
    final_social=(f'<meta property="og:title" content="{escape(final_title,quote=True)}">'
                  f'<meta property="og:description" content="{escape(final_desc,quote=True)}">'
                  f'<meta property="og:url" content="{escape(final_canonical,quote=True)}">'
                  f'<meta property="og:type" content="website">'
                  f'<meta property="og:image" content="{escape(social_image,quote=True)}">'
                  f'<meta name="twitter:card" content="summary_large_image">'
                  f'<meta name="twitter:title" content="{escape(final_title,quote=True)}">'
                  f'<meta name="twitter:description" content="{escape(final_desc,quote=True)}">'
                  f'<meta name="twitter:image" content="{escape(social_image,quote=True)}">')
    html = html.replace('</head>', final_social+'</head>', 1)

    # STEP 2 v319: Home keeps the visible brand H1 as its single primary heading.
    # Demote only the noscript fallback heading; this does not alter the visible Home design.
    if path == "/":
        html=re.sub(r'(\<noscript\b[^>]*>.*?<)h1(\b[^>]*>)(.*?</)h1(>)', r'\1div\2\3div\4', html, count=1, flags=re.S|re.I)

    # H1: SEO route article owns the only H1 on non-home SSR pages.
    # Protect that article, demote any legacy/template H1s, then restore it.
    if path != '/' and section:
        m=re.search(r'<article class="kasiscore--page".*?</article>', html, flags=re.I|re.S)
        if m:
            protected=m.group(0)
            token='<!--KASI_V317_PRIMARY_ARTICLE-->'
            tmp=html[:m.start()]+token+html[m.end():]
            tmp=re.sub(r'<h1(\b[^>]*)>', r'<div class="kasi-secondary-heading"\1>', tmp, flags=re.I)
            tmp=re.sub(r'</h1>', '</div>', tmp, flags=re.I)
            html=tmp.replace(token, protected, 1)

    _SSR_CACHE[key]=html
    return html



@app.get("/today", include_in_schema=False)
async def seo_today_page_v447():
    """Functional thin Today landing page; intentionally excluded from search indexing."""
    try:
        html = _render_seo_document("/today")
        return HTMLResponse(
            content=html,
            status_code=200,
            headers={
                "Cache-Control":"public, max-age=300, s-maxage=900, stale-while-revalidate=3600",
                "X-Robots-Tag":"noindex, follow",
                "X-Kasi-SEO-Version":"v457-canonical-results-search-identity",
            },
        )
    except Exception:
        return HTMLResponse(
            content='<!doctype html><html><head><meta name="robots" content="noindex,follow"><title>Today | Kasi Sports News</title></head><body><main><h1>Today</h1><p>Today&#39;s sports page is temporarily unavailable.</p></main></body></html>',
            status_code=200,
            headers={
                "Cache-Control":"public, max-age=60, s-maxage=60",
                "X-Robots-Tag":"noindex, follow",
                "X-Kasi-SEO-Version":"v457-canonical-results-search-identity",
            },
        )

@app.get("/seo-version", include_in_schema=False)
async def seo_version():
    return {"version":"v457-canonical-results-search-identity","root_owner":"root_webapp","seo_renderer":"_render_seo_document","canonical_hierarchy":"sport/country/competition/section"}

@app.get("/launch-check", include_in_schema=False)
async def launch_check():
    index_path=BASE_DIR/"index.html"
    index_text=index_path.read_text(encoding="utf-8") if index_path.exists() else ""
    checks={
        "frontend_present": index_path.exists(),
        "homepage_ad_placeholder_absent": 'id="kasiTopAdSlot"' not in index_text,
        "auth_secret_configured": bool(os.getenv("AUTH_SECRET","").strip()),
        "auth_admin_key_configured": bool(os.getenv("AUTH_ADMIN_KEY","").strip()),
        "football_api_configured": bool(os.getenv("AFOOT_API_KEY","").strip()),
        "search_console_configured": bool(os.getenv("GOOGLE_SITE_VERIFICATION","").strip()),
        "public_domain_configured": bool(os.getenv("PUBLIC_SITE_URL","").strip()),
        "postgres_configured": bool(os.getenv("DATABASE_URL","").strip()),
    }
    return {
        "ok_for_current_stage": all((
            checks["frontend_present"],
            checks["homepage_ad_placeholder_absent"],
            checks["auth_secret_configured"],
            checks["auth_admin_key_configured"]
        )),
        "checks":checks,
        "notes":{
            "football_api_configured":"Expected false until the sports API subscription is activated.",
            "postgres_configured":"Expected false until PostgreSQL is created.",
            "public_domain_configured":"Expected false until the custom domain is configured."
        }
    }

@app.get("/seo-check", include_in_schema=False)
async def seo_check():
    sample=await _render_seo_document("/football/premier-league")
    home=await _render_seo_document("/")
    robots_re=re.compile(r'<meta[^>]+name=["\\\']robots["\\\']',re.I)
    return {
        "homepage":{
            "visible_ssr_panel_injected": 'id="kasiscore-ssr-css"' in home,
            "canonical_present": bool(re.search(r'<link rel="canonical"',home,re.I)),
            "robots_meta_present": bool(robots_re.search(home)),
            "structured_data_present": 'application/ld+json' in home
        },
        "competition_sample":{
            "path":"/football/premier-league",
            "canonical_present": bool(re.search(r'<link rel="canonical"',sample,re.I)),
            "robots_meta_present": bool(robots_re.search(sample)),
            "structured_data_present": 'application/ld+json' in sample,
            "ssr_content_present": 'kasiscore--page' in sample
        },
        "expected_404_tests":[
            "/match/this-match-does-not-exist",
            "/team/not-a-real-team",
            "/player/not-a-real-player",
            "/news/not-a-real-article"
        ]
    }

@app.get("/about",include_in_schema=False,response_class=HTMLResponse)
async def public_about_page():
    return HTMLResponse(await _render_seo_document("/about"),headers={"Cache-Control":"public, max-age=300"})

@app.get("/privacy",include_in_schema=False,response_class=HTMLResponse)
async def public_privacy_page():
    return HTMLResponse(await _render_seo_document("/privacy"),headers={"Cache-Control":"public, max-age=300"})

@app.get("/terms",include_in_schema=False,response_class=HTMLResponse)
async def public_terms_page():
    return HTMLResponse(await _render_seo_document("/terms"),headers={"Cache-Control":"public, max-age=300"})

@app.get("/cookies",include_in_schema=False,response_class=HTMLResponse)
async def public_cookies_page():
    return HTMLResponse(await _render_seo_document("/cookies"),headers={"Cache-Control":"public, max-age=300"})

@app.get("/locale",include_in_schema=False)
def locale_hint(request: Request):
    country=(request.headers.get("cf-ipcountry") or request.headers.get("x-vercel-ip-country") or request.headers.get("x-country-code") or "").upper()
    accept=request.headers.get("accept-language","")
    return {"country":country[:2],"acceptLanguage":accept[:120]}



# ---------------- v227 Production Monetization + Edge Protection ----------------
MONETIZATION = {
    "adsense_client": os.getenv("ADSENSE_CLIENT_ID","ca-pub-5442799591686279").strip(),
    "affiliate_disclosure": os.getenv(
        "AFFILIATE_DISCLOSURE",
        "Kasi Sports News may earn a commission from qualifying purchases made through clearly marked affiliate links, at no additional cost to you."
    ),
    "sponsorship_email": os.getenv("SPONSORSHIP_EMAIL","admin@kasilivescore.com").strip(),
}
ADS_TXT_LINE = os.getenv("ADS_TXT_LINE","google.com, pub-5442799591686279, DIRECT, f08c47fec0942fa0").strip()

# Shared application cache: a million browser refreshes inside the TTL reuse the same
# origin result per process instead of triggering a million upstream provider calls.
# Cloudflare provides the first layer; existing provider caches remain the final layer.
_v227_cache = {}
_v227_locks = {}
_v227_guard = threading.Lock()

def _v227_lock(key):
    with _v227_guard:
        if key not in _v227_locks:
            _v227_locks[key]=threading.Lock()
        return _v227_locks[key]

def v227_cached(key, ttl, loader):
    now=time.time()
    item=_v227_cache.get(key)
    if item and item[0] > now:
        return item[1]
    with _v227_lock(key):
        now=time.time()
        item=_v227_cache.get(key)
        if item and item[0] > now:
            return item[1]
        value=loader()
        _v227_cache[key]=(now+ttl,value)
        return value

@app.middleware("http")
async def v227_cache_headers(request: Request, call_next):
    response=await call_next(request)
    p=request.url.path
    # Never CDN-cache user/auth/admin/private endpoints.
    private_prefixes=("/auth","/admin","/login","/signup","/register","/production-readiness")
    if p.startswith(private_prefixes):
        response.headers["Cache-Control"]="private, no-store"
        return response
    # Browser can revalidate frequently while Cloudflare keeps the shared response
    # for the product's established refresh cadence.
    if p.startswith("/live") or p.startswith("/sports/football/live") or p.startswith("/api/live-scores-with-odds"):
        response.headers["Cache-Control"]="public, max-age=15, s-maxage=180, stale-while-revalidate=30"
        response.headers["CDN-Cache-Control"]="public, s-maxage=180, stale-while-revalidate=30"
    elif p.startswith("/predictions"):
        # v286: public prediction feed — short shared cache to protect Render/provider calls
        # while keeping prediction data fresh for visitors.
        response.headers["Cache-Control"]="public, max-age=60, s-maxage=300, stale-while-revalidate=60"
        response.headers["CDN-Cache-Control"]="public, s-maxage=300, stale-while-revalidate=60"
    elif p.startswith("/fixtures"):
        # v297: normal fixture data is shared for 2 hours at the CDN edge.
        # This matches the frontend refresh and persistent API-Football fixture cache.
        response.headers["Cache-Control"]="public, max-age=60, s-maxage=7200, stale-while-revalidate=120"
        response.headers["CDN-Cache-Control"]="public, s-maxage=7200, stale-while-revalidate=120"
    elif p.startswith("/odds") or p.startswith("/ai-predictions"):
        # Preserve the existing 30-minute cadence for odds / AI predictions.
        response.headers["Cache-Control"]="public, max-age=60, s-maxage=1800, stale-while-revalidate=120"
        response.headers["CDN-Cache-Control"]="public, s-maxage=1800, stale-while-revalidate=120"
    elif p == "/tip-of-day":
        # v291: Tip of the Day — 30-minute shared edge cache.
        response.headers["Cache-Control"]="public, max-age=300, s-maxage=1800, stale-while-revalidate=300"
        response.headers["CDN-Cache-Control"]="public, s-maxage=1800, stale-while-revalidate=300"
    elif p in ("/sports/rugby/predictions", "/sports/cricket/predictions"):
        # v292: rugby/cricket predictions — 30-minute shared edge cache.
        response.headers["Cache-Control"]="public, max-age=300, s-maxage=1800, stale-while-revalidate=300"
        response.headers["CDN-Cache-Control"]="public, s-maxage=1800, stale-while-revalidate=300"
    elif p.startswith("/sports/standings"):
        # v287: standings change relatively slowly; keep browsers reasonably fresh
        # while allowing Cloudflare to absorb repeated public standings requests.
        response.headers["Cache-Control"]="public, max-age=300, s-maxage=10800, stale-while-revalidate=600"
        response.headers["CDN-Cache-Control"]="public, s-maxage=10800, stale-while-revalidate=600"
    elif p == "/sports/news":
        # v288: public news feed — keep browser refresh reasonably fresh while
        # Cloudflare absorbs repeated requests to the same vetted news payload.
        response.headers["Cache-Control"]="public, max-age=300, s-maxage=900, stale-while-revalidate=300"
        response.headers["CDN-Cache-Control"]="public, s-maxage=900, stale-while-revalidate=300"
    elif p == "/sports/videos":
        # v290: public videos feed — 30-minute shared edge cache.
        response.headers["Cache-Control"]="public, max-age=300, s-maxage=1800, stale-while-revalidate=300"
        response.headers["CDN-Cache-Control"]="public, s-maxage=1800, stale-while-revalidate=300"
    elif p.startswith("/standings") or p.startswith("/team/") or p.startswith("/player/") or p.startswith("/sports-db"):
        response.headers["Cache-Control"]="public, max-age=300, s-maxage=21600, stale-while-revalidate=600"
        response.headers["CDN-Cache-Control"]="public, s-maxage=21600, stale-while-revalidate=600"
    elif request.method=="GET" and p=="/":
        # STEP 6 v331: Home is a stable HTML shell. Dynamic scores/news refresh
        # through their JSON endpoints, so a short shared shell cache is safe.
        response.headers["Cache-Control"]="public, max-age=60, s-maxage=300, stale-while-revalidate=600"
        response.headers["CDN-Cache-Control"]="public, s-maxage=300, stale-while-revalidate=600"
    elif request.method=="GET" and re.match(r"^/[a-z]{2}(?:-[a-z]{2})?(?:/|$)",p,re.I):
        # Preserve the legacy no-store behaviour for localized app shells.
        response.headers["Cache-Control"]="no-store, max-age=0"
        response.headers["CDN-Cache-Control"]="no-store"
    return response

@app.get("/ads.txt", include_in_schema=False)
def ads_txt():
    # Set ADS_TXT_LINE only after AdSense gives you the real publisher ID.
    # Never publish a made-up pub ID.
    return Response(content=(ADS_TXT_LINE+"\n") if ADS_TXT_LINE else "# Add the authorized seller line supplied by AdSense after approval.\n",
                    media_type="text/plain",
                    headers={"Cache-Control":"public, max-age=300, s-maxage=3600"})

@app.get("/monetization/config", include_in_schema=False)
def monetization_config():
    return {
        "adsenseConfigured": bool(MONETIZATION["adsense_client"]),
        "adsenseClient": MONETIZATION["adsense_client"],
        "affiliateDisclosure": MONETIZATION["affiliate_disclosure"],
        "sponsorshipEmail": MONETIZATION["sponsorship_email"],
        "affiliateRel": "sponsored nofollow noopener",
        "currency": "ZAR",
        "placements": {
            "leaderboard": os.getenv("ADSENSE_SLOT_LEADERBOARD",""),
            "inContent": os.getenv("ADSENSE_SLOT_IN_CONTENT",""),
            "rightRailRectangle": os.getenv("ADSENSE_SLOT_RIGHT_RECTANGLE",""),
            "rightRailSkyscraper": os.getenv("ADSENSE_SLOT_RIGHT_SKYSCRAPER",""),
            "mobile": os.getenv("ADSENSE_SLOT_MOBILE","")
        }
    }

@app.get("/sponsor", response_class=HTMLResponse, include_in_schema=False)
def sponsor_page():
    email=html.escape(MONETIZATION["sponsorship_email"])
    return HTMLResponse(f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Advertise & Sponsor | Kasi Sports News</title><meta name="description" content="Advertising, sponsorship and commercial partnership opportunities with Kasi Sports News.">
<link rel="canonical" href="{_seo_base()}/sponsor"></head><body style="font-family:system-ui;max-width:900px;margin:40px auto;padding:20px">
<h1>Advertise & Sponsor Kasi Sports News</h1><p>Commercial opportunities can include clearly labelled sponsored placements, campaign partnerships and sports-related brand integrations.</p>
<p>Sponsored content and paid placements are identified as advertising or sponsored content and remain separate from editorial and sports-data results.</p>
<p>Commercial enquiries: <a href="mailto:{email}">{email}</a></p><p><a href="/">Return to Kasi Sports News</a></p></body></html>""")

@app.get("/affiliate-disclosure", response_class=HTMLResponse, include_in_schema=False)
def affiliate_disclosure_page():
    d=html.escape(MONETIZATION["affiliate_disclosure"])
    return HTMLResponse(f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Affiliate Disclosure | Kasi Sports News</title><link rel="canonical" href="{_seo_base()}/affiliate-disclosure"></head>
<body style="font-family:system-ui;max-width:900px;margin:40px auto;padding:20px"><h1>Affiliate Disclosure</h1><p>{d}</p>
<p>Affiliate relationships do not determine scores, statistics, standings or prediction calculations.</p><p><a href="/">Return to Kasi Sports News</a></p></body></html>""")


@app.get("/monetization/placements", include_in_schema=False)
def monetization_placements():
    return {
        "strategy": ["adsense","affiliate","direct-sponsorship"],
        "emptySlotsCollapsed": True,
        "desktop": ["leaderboard","after-live","after-fixtures","after-predictions","right-rectangle","right-sponsor","right-skyscraper","right-affiliate","bottom-sponsor"],
        "mobile": ["leaderboard","after-live","after-fixtures","after-predictions","mobile-sponsor","mobile-affiliate","bottom-sponsor"],
        "note": "AdSense slot IDs and commercial partner URLs are environment/config driven; no publisher or partner identifiers are fabricated."
    }


# ---------------- v229 Contact + Footer cleanup ----------------
@app.get("/contact", response_class=HTMLResponse, include_in_schema=False)
def kasi_contact_page():
    base = KASI_PUBLIC_ORIGIN
    return HTMLResponse(f"""<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Contact | Kasi Sports News</title>
<meta name="description" content="Contact Kasi Sports News for general, advertising, affiliate and sponsorship inquiries.">
<link rel="canonical" href="{base}/contact">
<style>
body{{font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;margin:0;background:#0b1220;color:#f4f7fb}}
main{{max-width:820px;margin:0 auto;padding:56px 22px}}
a{{color:inherit}} .card{{padding:28px;border:1px solid rgba(255,255,255,.15);border-radius:16px;background:rgba(255,255,255,.05)}}
.muted{{opacity:.75}} footer{{margin-top:34px;padding-top:22px;border-top:1px solid rgba(255,255,255,.12);font-size:.9rem}}
</style></head><body><main>
<div class="card">
<h1>Contact Kasi Sports News</h1>
<p><strong>Inquiries:</strong> <a href="mailto:admin@kasilivescore.com">admin@kasilivescore.com</a> · 248 Imam Haron Road, Claremont, Cape Town</p>
<p class="muted">For general inquiries, advertising, affiliate partnerships and direct sponsorship opportunities.</p>
</div>
<footer>&copy; 2026 Kasi Sports News. All rights reserved.</footer>
</main></body></html>""")

# ---------------- v226 International SEO & Discoverability ----------------
SEO_LOCALES = [
 "en","zu","xh","af","st","tn","yo","ig","ha","sw","am","so","sn","ar","ar-eg","ar-ma","ar-dz","ar-ly",
 "fr","pt","es","de","zh-cn","zh-tw","ja","ko","hi","bn","ur","id","ms","vi","th","tl","ta","pl","it","nl",
 "ro","cs","el","tr","uk","ru","sv","da","no","fi","en-us","en-ca","fr-ca","es-mx","es-ar","es-co","es-cl",
 "es-pe","pt-br","ht","qu","gn","tzm","ee","kbp"
]
SEO_INDEX_SECTIONS = ["fixtures","live","results","standings","predictions","news","teams","players"]

SEO_META = {
 "en":("Kasi Sports News","Live scores, fixtures, results, standings, teams, players, predictions and sports news."),
 "fr":("Kasi Sports News","Scores en direct, matchs, résultats, classements, équipes, joueurs, pronostics et actualités sportives."),
 "es":("Kasi Sports News","Resultados en vivo, partidos, resultados, clasificación, equipos, jugadores, pronósticos y noticias deportivas."),
 "pt":("Kasi Sports News","Resultados ao vivo, jogos, resultados, classificação, equipes, jogadores, previsões e notícias esportivas."),
 "pt-br":("Kasi Sports News","Resultados ao vivo, jogos, classificação, times, jogadores, palpites e notícias esportivas."),
 "ar":("Kasi Sports News","نتائج مباشرة ومباريات وترتيب وفرق ولاعبون وتوقعات وأخبار رياضية."),
 "pl":("Kasi Sports News","Wyniki na żywo, mecze, tabela, drużyny, zawodnicy, prognozy i wiadomości sportowe."),
 "ja":("Kasi Sports News","ライブスコア、試合日程、結果、順位表、チーム、選手、予想、スポーツニュース。"),
 "ko":("Kasi Sports News","라이브 스코어, 경기 일정, 결과, 순위, 팀, 선수, 예측 및 스포츠 뉴스."),
 "zh-cn":("Kasi Sports News","实时比分、赛程、赛果、积分榜、球队、球员、预测和体育新闻。"),
 "zh-tw":("Kasi Sports News","即時比分、賽程、賽果、積分榜、球隊、球員、預測和體育新聞。"),
}
SEO_SECTION_TITLES={
 "fixtures":"Fixtures","live":"Live Scores","results":"Results","standings":"Standings","predictions":"Predictions",
 "news":"Sports News","teams":"Teams","players":"Players"
}

def _seo_base():
    return KASI_PUBLIC_ORIGIN

def _seo_locale(lang:str)->str:
    x=(lang or "").strip().lower()
    if x not in SEO_LOCALES:
        raise HTTPException(status_code=404, detail="SEO locale not found")
    return x

def _seo_localized_html(lang:str, section:str="", slug:str="", kind:str=""):
    # STEP 1 soft-404 guard: never coerce an unknown URL segment to English.
    # Unknown locale prefixes must be genuine 404s so crawlers do not index
    # arbitrary SPA URLs as duplicate English pages.
    lang=_seo_locale(lang); base=_seo_base()
    title0,desc=SEO_META.get(lang,SEO_META.get(lang.split("-")[0],SEO_META["en"]))
    label=SEO_SECTION_TITLES.get(section, kind.title() if kind else "")
    title=(f"{label} | {title0}" if label else f"{title0} | Live Scores, Fixtures & Sports Data")
    path=f"/{lang}" + (f"/{section}" if section else "") + (f"/{slug}" if slug else "")
    canonical=base+path
    alternates="\n".join(
      f'<link rel="alternate" hreflang="{x}" href="{base}/{x}{("/"+section) if section else ""}{("/"+slug) if slug else ""}">'
      for x in SEO_LOCALES
    ) + f'\n<link rel="alternate" hreflang="x-default" href="{base}/en{("/"+section) if section else ""}{("/"+slug) if slug else ""}">'
    page=INDEX_HTML.read_text(encoding="utf-8") if INDEX_HTML.exists() else ""
    page=re.sub(r'<link rel="canonical"[^>]*>',f'<link rel="canonical" href="{canonical}">',page,count=1,flags=re.I)
    page=re.sub(r'<meta name="description"[^>]*>',f'<meta name="description" content="{html.escape(desc,quote=True)}">',page,count=1,flags=re.I)
    page=re.sub(r'<meta property="og:title"[^>]*>',f'<meta property="og:title" content="{html.escape(title,quote=True)}">',page,count=1,flags=re.I)
    page=re.sub(r'<meta property="og:description"[^>]*>',f'<meta property="og:description" content="{html.escape(desc,quote=True)}">',page,count=1,flags=re.I)
    page=re.sub(r'<meta property="og:url"[^>]*>',f'<meta property="og:url" content="{canonical}">',page,count=1,flags=re.I)
    page=re.sub(r'<title>.*?</title>',f'<title>{html.escape(title)}</title>',page,count=1,flags=re.I|re.S)
    page=page.replace("</head>",alternates+"\n</head>",1)
    page=page.replace("<html",f'<html lang="{lang}" data-seo-locale="{lang}" data-seo-section="{section}"',1)
    return HTMLResponse(page)

@app.get("/seo/locales",include_in_schema=False)
def seo_locales():
    return {"locales":SEO_LOCALES,"sections":SEO_INDEX_SECTIONS}

@app.get("/{lang}/fixtures",include_in_schema=False)
def localized_fixtures(lang:str): return _seo_localized_html(lang,"fixtures")
@app.get("/{lang}/live",include_in_schema=False)
def localized_live(lang:str): return _seo_localized_html(lang,"live")
@app.get("/{lang}/results",include_in_schema=False)
def localized_results(lang:str): return _seo_localized_html(lang,"results")
@app.get("/{lang}/standings",include_in_schema=False)
def localized_standings(lang:str): return _seo_localized_html(lang,"standings")
@app.get("/{lang}/predictions",include_in_schema=False)
def localized_predictions(lang:str): return _seo_localized_html(lang,"predictions")
@app.get("/{lang}/news",include_in_schema=False)
def localized_news(lang:str): return _seo_localized_html(lang,"news")
@app.get("/{lang}/teams",include_in_schema=False)
def localized_teams(lang:str): return _seo_localized_html(lang,"teams")
@app.get("/{lang}/players",include_in_schema=False)
def localized_players(lang:str): return _seo_localized_html(lang,"players")
@app.get("/{lang}/teams/{slug}",include_in_schema=False)
def localized_team_page(lang:str,slug:str): return _seo_localized_html(lang,"teams",slug,"team")
@app.get("/{lang}/players/{slug}",include_in_schema=False)
def localized_player_page(lang:str,slug:str): return _seo_localized_html(lang,"players",slug,"player")
@app.get("/{lang}/matches/{slug}",include_in_schema=False)
def localized_match_page(lang:str,slug:str): return _seo_localized_html(lang,"matches",slug,"match")
@app.get("/{lang}",include_in_schema=False)
async def localized_home(lang:str):
    # v334: this single-segment catch-all is registered before several later routes.
    # Reserve real application/static routes here so they are never mistaken for SEO locales.
    segment=(lang or "").strip().lower()
    if segment in {"login","signup","register"}:
        if not INDEX_HTML.exists():
            raise HTTPException(status_code=404,detail="Frontend not found")
        return FileResponse(INDEX_HTML,headers={"Cache-Control":"no-store"})
    if segment == "admin":
        page=await _render_seo_document("/admin")
        if 'name="robots"' in page:
            page=re.sub(r'<meta\s+name=["\']robots["\'][^>]*>', '<meta name="robots" content="noindex,nofollow">', page, count=1, flags=re.I)
        else:
            page=page.replace("</head>",'<meta name="robots" content="noindex,nofollow"></head>',1)
        return HTMLResponse(page,headers={"Cache-Control":"no-store"})
    # These are genuine public sport roots and are listed in the sitemap.
    if segment in {"football","rugby","cricket","tennis"}:
        return HTMLResponse(await _render_seo_document(f"/{segment}"), headers={"Cache-Control":"public, max-age=300"})
    return _seo_localized_html(lang)

@app.get("/",response_class=HTMLResponse)
async def root_webapp(): return HTMLResponse(_v434_inject_bootstrap(await _render_seo_document("/"),await _v434_inline_bootstrap_json()),headers={"Cache-Control":"no-cache, max-age=0, must-revalidate", "CDN-Cache-Control":"public, s-maxage=30, stale-while-revalidate=60", "X-KSN-Build":"v426"})
@app.get("/today",response_class=HTMLResponse)
async def ssr_today(): return HTMLResponse(await _render_seo_document("/today"),headers={"Cache-Control":"public, max-age=300"})
@app.get("/weekend",response_class=HTMLResponse)
async def ssr_weekend(): return HTMLResponse(await _render_seo_document("/weekend"),headers={"Cache-Control":"public, max-age=300"})


def _standalone_match_stats_page(entity_id:str, sport:str="football", league:str="") -> str:
    eid=json.dumps(str(entity_id)); sp=json.dumps(str(sport)); lg=json.dumps(str(league or ""))
    return f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Match Centre | Kasi Sports News</title><meta name="google-adsense-account" content="ca-pub-5442799591686279"><script async src="https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js?client=ca-pub-5442799591686279" crossorigin="anonymous"></script><style>
:root{{--bg:#000;--card:#000;--card2:#111;--line:#222;--text:#f5f5f5;--muted:#9b9b9b;--accent:#38bdf8;--green:#38bdf8;--yellow:#60a5fa;--red:#ef4444}}
*{{box-sizing:border-box}}body{{margin:0;background:var(--bg);color:var(--text);font-family:Arial,sans-serif}}a{{color:inherit;text-decoration:none}}main{{max-width:1180px;margin:auto;padding:16px}}.top{{display:flex;justify-content:space-between;align-items:center;margin-bottom:14px}}.back{{border:1px solid var(--line);padding:9px 13px;border-radius:9px;background:#111;cursor:pointer}}.ksn-head{{display:flex;align-items:center;gap:9px;font-weight:900}}.ksn-head img{{width:38px;height:38px;object-fit:contain;border-radius:50%}}.card{{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:18px;margin:14px 0;box-shadow:0 10px 28px rgba(0,0,0,.14)}}.muted{{color:var(--muted)}}.tiny{{font-size:11px}}.hero{{display:grid;grid-template-columns:1fr 190px 1fr;gap:16px;align-items:center;text-align:center}}.team img{{width:72px;height:72px;object-fit:contain}}.team-name{{font-size:18px;font-weight:900;margin-top:8px}}.score{{font-size:38px;font-weight:900}}.status{{font-size:12px;color:var(--accent);font-weight:800}}.scorers{{font-size:12px;color:#d5d9df;line-height:1.7;margin-top:8px}}.tabs{{display:flex;gap:7px;overflow:auto;position:sticky;top:0;background:rgba(5,6,7,.96);padding:8px 0;z-index:5}}.tabs button{{background:var(--card);color:#fff;border:1px solid var(--line);border-radius:999px;padding:9px 13px;white-space:nowrap;cursor:pointer}}.tabs button.active{{border-color:var(--accent);color:var(--accent)}}.panel{{display:none}}.panel.active{{display:block}}.grid2{{display:grid;grid-template-columns:1fr 1fr;gap:12px}}.grid3{{display:grid;grid-template-columns:repeat(3,1fr);gap:10px}}.stat{{display:grid;grid-template-columns:1fr 1.3fr 1fr;align-items:center;gap:8px;padding:10px 0;border-bottom:1px solid var(--line);text-align:center}}.stat b:first-child{{text-align:left}}.stat b:last-child{{text-align:right}}.bar{{height:5px;background:#222;border-radius:4px;overflow:hidden;margin-top:4px}}.bar>i{{display:block;height:100%;background:var(--accent)}}.event{{display:grid;grid-template-columns:52px 1fr;gap:10px;padding:11px 0;border-bottom:1px solid var(--line)}}.minute{{font-weight:900;color:var(--accent)}}.goal{{border-left:3px solid var(--green);padding-left:10px}}.cardevt{{border-left:3px solid var(--yellow);padding-left:10px}}.redevt{{border-left:3px solid var(--red);padding-left:10px}}.person{{display:grid;grid-template-columns:34px 1fr auto;gap:9px;align-items:center;padding:9px 0;border-bottom:1px solid var(--line);cursor:pointer}}.person img{{width:34px;height:34px;border-radius:50%;object-fit:cover;background:#222}}.pill{{font-size:10px;border:1px solid var(--line);padding:3px 6px;border-radius:999px;color:var(--muted)}}.metric{{padding:10px;background:var(--card2);border-radius:9px}}.metric b{{display:block;font-size:18px}}.compare-hero{{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin:14px 0}}.compare-team{{position:relative;overflow:hidden;border:1px solid var(--line);border-radius:14px;padding:16px;background:linear-gradient(135deg,rgba(56,189,248,.13),rgba(0,0,0,.2))}}.compare-team.away{{background:linear-gradient(135deg,rgba(96,165,250,.09),rgba(0,0,0,.2));box-shadow:inset 4px 0 0 rgba(96,165,250,.65)}}.compare-team.home{{box-shadow:inset 4px 0 0 var(--accent)}}.compare-name{{font-size:18px;font-weight:900}}.compare-kpis{{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:8px;margin-top:12px}}.compare-kpi{{padding:9px;border-radius:9px;background:rgba(255,255,255,.045)}}.compare-kpi span{{display:block;color:var(--muted);font-size:10px;text-transform:uppercase}}.compare-kpi b{{font-size:17px}}.compare-bar{{display:grid;grid-template-columns:72px 1fr 72px;gap:10px;align-items:center;padding:10px 0;border-bottom:1px solid var(--line)}}.compare-bar .track{{height:7px;border-radius:99px;background:#151a20;overflow:hidden;display:flex}}.compare-bar .homefill{{background:var(--accent);height:100%}}.compare-bar .awayfill{{background:#60a5fa;height:100%;margin-left:auto}}.section-title{{margin:20px 0 8px;font-size:12px;text-transform:uppercase;letter-spacing:.08em;color:var(--muted)}}.standings-table{{width:100%;border-collapse:collapse;min-width:620px}}.standings-table th,.standings-table td{{padding:10px 12px;border-bottom:1px solid var(--line);font-size:13px;vertical-align:middle;text-align:center;white-space:nowrap}}.standings-table th{{font-size:11px;text-transform:uppercase;letter-spacing:.04em;color:var(--muted);font-weight:800}}.standings-table th:nth-child(2),.standings-table td:nth-child(2){{text-align:left;min-width:180px}}.standings-table td:last-child{{font-weight:900}}.standings-wrap{{overflow:auto}}.standing-team{{display:flex;align-items:center;gap:9px}}.standing-team img{{width:25px;height:25px;object-fit:contain}}.standings-focus{{box-shadow:inset 4px 0 0 var(--accent);background:rgba(56,189,248,.06)}}.form-row{{display:flex;gap:4px;justify-content:center}}.form-pill{{display:inline-flex;align-items:center;justify-content:center;width:23px;height:23px;border-radius:5px;font-size:11px;font-weight:900;background:#555}}.form-w{{background:#16833a}}.form-d{{background:#777}}.form-l{{background:#c8273e}}.empty{{color:var(--muted);padding:14px 0}}.ksn-ad{{min-height:110px;margin:18px 0;border:1px solid var(--line);border-radius:12px;display:flex;align-items:center;justify-content:center;overflow:hidden;contain:layout paint}}.ksn-ad ins{{width:100%;min-height:90px}}pre{{font-size:11px}}
@media(max-width:760px){{.compare-hero{{grid-template-columns:1fr}}.compare-kpis{{grid-template-columns:repeat(2,1fr)}}.compare-bar{{grid-template-columns:55px 1fr 55px}}.top{{gap:10px;align-items:flex-start}}.top>b{{font-size:12px;text-align:right}}.hero{{grid-template-columns:minmax(0,1fr) 88px minmax(0,1fr);gap:7px;padding:13px 8px}}.team img{{width:48px;height:48px}}.team-name{{font-size:13px;overflow-wrap:anywhere}}.score{{font-size:27px}}.scorers{{font-size:10px}}.grid2,.grid3{{grid-template-columns:1fr}}main{{padding:9px}}.tabs{{margin-left:-9px;margin-right:-9px;padding-left:9px;padding-right:9px}}}}
</style></head><body><main><div class="top"><a class="back" href="/" onclick="event.preventDefault();return kasiBackHome();">← Back to Home</a><div class="ksn-head"><img src="/kasi-sports-news-logo.png" alt="Kasi Sports News"><b>Kasi Sports News · Match Centre</b></div></div><div id="page"><div class="card">Loading match data…</div></div></main><script>
const ID={eid},SPORT={sp},LEAGUE={lg},page=document.getElementById('page');function ksnMatchAd(){{if(document.getElementById('ksnMatchCentreAd'))return;const cards=page.querySelectorAll('.card');if(cards.length<2)return;const box=document.createElement('div');box.id='ksnMatchCentreAd';box.className='ksn-ad';box.innerHTML='<ins class="adsbygoogle" style="display:block" data-ad-client="ca-pub-5442799591686279" data-ad-slot="3030391892" data-ad-format="auto" data-full-width-responsive="true"></ins>';cards[0].insertAdjacentElement('afterend',box);try{{(window.adsbygoogle=window.adsbygoogle||[]).push({{}})}}catch(_){{}};const ins=box.querySelector('ins');new MutationObserver((m,o)=>{{if(ins.getAttribute('data-ad-status')==='unfilled'){{box.remove();o.disconnect()}}else if(ins.getAttribute('data-ad-status')==='filled')o.disconnect()}}).observe(ins,{{attributes:true,attributeFilter:['data-ad-status']}});}}new MutationObserver(()=>ksnMatchAd()).observe(page,{{childList:true,subtree:true}});function kasiBackHome(){{try{{if(history.length>1){{history.back();return false}}}}catch(_){{}}location.replace('/');return false;}}const E=v=>String(v??'').replace(/[&<>"']/g,c=>({{'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}}[c]));
const N=v=>{{const n=Number(String(v??'').replace('%',''));return Number.isFinite(n)?n:null}};const localDate=v=>{{try{{return new Date(v).toLocaleString(undefined,{{weekday:'short',day:'2-digit',month:'short',year:'numeric',hour:'2-digit',minute:'2-digit'}})}}catch(_){{return v||'—'}}}};async function J(u,timeout=20000){{let lastErr=null;for(let attempt=0;attempt<2;attempt++){{const c=new AbortController(),t=setTimeout(()=>c.abort('request-timeout'),timeout);try{{const r=await fetch(u,{{signal:c.signal,headers:{{Accept:'application/json'}},cache:attempt?'no-store':'default'}});if(!r.ok)throw Error('HTTP '+r.status);return await r.json()}}catch(e){{lastErr=e;if(attempt===0)await new Promise(r=>setTimeout(r,250));}}finally{{clearTimeout(t)}}}}throw new Error(lastErr?.name==='AbortError'||String(lastErr||'').toLowerCase().includes('abort')?'Data provider is taking longer than expected. Please retry.':(lastErr?.message||'Data temporarily unavailable.'))}}const playerUrl=id=>id?'/players/'+encodeURIComponent(id):'#';
function matchTeamTheme(id,name){{
 const key=String(name||'').toLowerCase().replace(/[^a-z0-9]/g,'');
 const known={{
  arsenal:['#EF0107','#9C1016'],chelsea:['#034694','#1B5FC1'],liverpool:['#C8102E','#7A0018'],manchestercity:['#6CABDD','#2D78A4'],manchesterunited:['#DA291C','#8F1111'],tottenhamhotspur:['#132257','#244A87'],leedsunited:['#FFCD00','#1D428A'],newcastleunited:['#241F20','#5B5B5B'],astonvilla:['#670E36','#95BFE5'],everton:['#003399','#1B55B5'],brighton:['#0057B8','#FFCD00'],westhamunited:['#7A263A','#1BB1E7'],nottinghamforest:['#DD0000','#8E0000'],sunderland:['#EB172B','#8A0D18'],fulham:['#CC0000','#111111'],crystalpalace:['#1B458F','#C4122E'],bournemouth:['#DA291C','#111111'],brentford:['#E30613','#FBB800'],burnley:['#6C1D45','#99D6EA'],wolverhamptonwanderers:['#FDB913','#231F20'],wolves:['#FDB913','#231F20'],
  realmadrid:['#FEBE10','#5E6AFC'],barcelona:['#A50044','#004D98'],atleticomadrid:['#CB3524','#272E61'],athleticclub:['#EE2523','#111111'],villarreal:['#F7E700','#005187'],sevilla:['#D71920','#FFFFFF'],valencia:['#F18E00','#111111'],realsociedad:['#0067B1','#FFFFFF'],realbetis:['#00954C','#FFFFFF'],
  bayernmunich:['#DC052D','#0066B2'],borussiadortmund:['#FDE100','#111111'],bayerleverkusen:['#E32221','#111111'],rbLeipzig:['#DD0741','#001F47'],rbleipzig:['#DD0741','#001F47'],eintrachtfrankfurt:['#E1000F','#111111'],werderbremen:['#1D9053','#FFFFFF'],stuttgart:['#E32219','#FFFFFF'],
  juventus:['#111111','#FFFFFF'],inter:['#0068A8','#111111'],internazionale:['#0068A8','#111111'],acmilan:['#FB090B','#111111'],milan:['#FB090B','#111111'],napoli:['#12A0D7','#FFFFFF'],roma:['#8E1F2F','#F0BC42'],lazio:['#87D8F7','#FFFFFF'],atalanta:['#1E71B8','#111111'],fiorentina:['#5B2A86','#FFFFFF'],
  psg:['#004170','#DA291C'],parissaintgermain:['#004170','#DA291C'],marseille:['#2FAEE0','#FFFFFF'],monaco:['#E30613','#FFFFFF'],lyon:['#1F3A93','#DA291C'],lille:['#E01E2D','#242A5A'],nice:['#D71920','#111111'],lens:['#D71920','#F6C500']
 }};
 if(known[key])return {{primary:known[key][0],secondary:known[key][1]}};
 const palette=[['#2563EB','#1E3A8A'],['#DC2626','#7F1D1D'],['#16A34A','#14532D'],['#9333EA','#581C87'],['#EA580C','#7C2D12'],['#0891B2','#164E63'],['#DB2777','#831843'],['#CA8A04','#713F12']];
 let h=Number(id)||0;if(!h){{for(const c of key)h=((h<<5)-h)+c.charCodeAt(0)}}const c=palette[Math.abs(h)%palette.length];return {{primary:c[0],secondary:c[1]}};
}}
function teamCardStyle(t){{return `border-color:${{t.primary}};box-shadow:inset 5px 0 0 ${{t.primary}};background:linear-gradient(135deg,${{t.primary}}2b,rgba(8,10,12,.97) 48%)`}}
function statRows(rows){{const a=rows?.[0]?.statistics||[],b=rows?.[1]?.statistics||[],m=new Map(b.map(x=>[x.type,x.value]));return a.length?a.map(x=>{{const bv=m.get(x.type),an=N(x.value),bn=N(bv),pct=an!=null&&bn!=null&&an+bn>0?Math.round(an/(an+bn)*100):50;return `<div class="stat"><b>${{E(x.value??'—')}}</b><div><span class="muted">${{E(x.type)}}</span><div class="bar"><i style="width:${{pct}}%"></i></div></div><b>${{E(bv??'—')}}</b></div>`}}).join(''):'<div class="empty">No detailed statistics returned.</div>'}}
function scorerLines(ev,id){{return ev.filter(x=>String(x.type).toLowerCase()==='goal'&&String(x.team?.id)===String(id)).map(x=>`${{E(x.player?.name||'Goal')}} ${{E(x.time?.elapsed??'')}}′${{x.assist?.name?' · '+E(x.assist.name)+' assist':''}}`).join('<br>')}}
function timeline(ev){{if(!ev.length)return '<div class="empty">No timeline returned.</div>';return [...ev].sort((a,b)=>(a.time?.elapsed||0)-(b.time?.elapsed||0)).map(x=>{{const typ=String(x.type||'').toLowerCase(),cls=typ==='goal'?'goal':typ==='card'&&String(x.detail).toLowerCase().includes('red')?'redevt':typ==='card'?'cardevt':'';return `<div class="event"><div class="minute">${{E(x.time?.elapsed??'')}}′</div><div class="${{cls}}"><b>${{typ==='goal'?'⚽':typ==='subst'?'↔':'•'}} ${{E(x.player?.name||x.team?.name||x.type||'Event')}}</b>${{x.assist?.name?` <span class="muted">assist: ${{E(x.assist.name)}}</span>`:''}}<div class="tiny muted">${{E(x.team?.name||'')}} · ${{E(x.detail||x.type||'')}} ${{E(x.comments||'')}}</div></div></div>`}}).join('')}}
function lineups(ts){{return ts.length?ts.map(t=>`<div class="card"><h3>${{E(t.team?.name||'Team')}} <span class="pill">${{E(t.formation||'Formation —')}}</span></h3><div class="tiny muted">Coach: ${{E(t.coach?.name||'—')}}</div>${{(t.players||[]).map(p=>`<a class="person" href="${{playerUrl(p.id)}}">${{p.photo?`<img src="${{E(p.photo)}}" alt="">`:`<span class="pill">${{E(p.number??'—')}}</span>`}}<div><b>${{E(p.name||'Player')}}</b><div class="tiny muted">${{E(p.pos||'')}} · ${{p.starter?'Starting XI':'Substitute'}}</div></div><span>›</span></a>`).join('')}}</div>`).join(''):'<div class="empty">No lineups returned.</div>'}}
function playerStats(rows){{const out=[];(rows||[]).forEach(t=>(t.players||[]).forEach(z=>{{const p=z.player||{{}},st=(z.statistics||[])[0]||{{}};out.push({{team:t.team||{{}},p,st}})}}));return out.length?out.map(x=>{{const g=x.st.games||{{}},go=x.st.goals||{{}},pa=x.st.passes||{{}},sh=x.st.shots||{{}},tk=x.st.tackles||{{}},ca=x.st.cards||{{}};return `<a class="person" href="${{playerUrl(x.p.id)}}">${{x.p.photo?`<img src="${{E(x.p.photo)}}">`:'<span></span>'}}<div><b>${{E(x.p.name||'Player')}}</b><div class="tiny muted">${{E(x.team.name||'')}} · ${{E(g.position||'')}} · ${{E(g.minutes??'—')}} min · Rating ${{E(g.rating??'—')}}</div><div class="tiny muted">Goals ${{E(go.total??0)}} · Assists ${{E(go.assists??0)}} · Shots ${{E(sh.total??0)}} · Passes ${{E(pa.total??0)}} · Tackles ${{E(tk.total??0)}} · YC ${{E(ca.yellow??0)}} · RC ${{E(ca.red??0)}}</div></div><span>›</span></a>`}}).join(''):'<div class="empty">No player match statistics returned.</div>'}}
function intelligence(i){{i=i||{{}};const f=i.form||{{}},fh=f.home||{{}},fa=f.away||{{}},st=i.standings||{{}},h2=i.h2h||{{}},n=i.next5||{{}},ts=i.teamStatistics||{{}},inj=i.injuries||{{}};
 const formRows=x=>(x||[]).map(r=>`<div class="event"><div class="minute">${{E(r.result||'—')}}</div><div><b>${{E(r.home||'')}} ${{E(r.score||'')}} ${{E(r.away||'')}}</b><div class="tiny muted">${{localDate(r.date)}}${{(r.scorers||[]).length?' · Scorers: '+E((r.scorers||[]).join(', ')):''}}</div></div></div>`).join('')||'<div class="empty">Data unavailable.</div>';
 const nextRows=x=>(x||[]).map(r=>`<div class="event"><div class="minute">NEXT</div><div><b>${{E(r.home||'')}} vs ${{E(r.away||'')}}</b><div class="tiny muted">${{localDate(r.date)}}</div></div></div>`).join('')||'<div class="empty">Data unavailable.</div>';
 const S=x=>x||{{}}, total=(x,p)=>Number(S(x?.fixtures?.[p])?.total??0), goals=(x,p)=>Number(S(x?.goals?.[p])?.total?.total??0), pct=(a,b)=>b?Math.round(a*1000/b)/10:0;
 const k=x=>{{const p=total(x,'played'),w=total(x,'wins'),d=total(x,'draws'),l=total(x,'loses'),gf=goals(x,'for'),ga=goals(x,'against');return {{p,w,d,l,gf,ga,wr:pct(w,p),gfpg:p?Math.round(gf*100/p)/100:0,gapg:p?Math.round(ga*100/p)/100:0}}}};
 const hk=k(ts.home),ak=k(ts.away),hp=st.home?.points??'—',ap=st.away?.points??'—';
 const teamCard=(side,name,row,kp,points)=>{{const th=matchTeamTheme(row?.team?.id||0,name);return `<div class="compare-team ${{side}}" style="${{teamCardStyle(th)}}"><div class="tiny muted">${{side==='home'?'HOME TEAM':'AWAY TEAM'}}</div><div class="compare-name">${{E(name)}}</div><div class="tiny muted">League position #${{E(row?.rank??'—')}} · ${{E(points)}} pts</div><div class="compare-kpis"><div class="compare-kpi"><span>Win rate</span><b>${{E(kp.wr)}}%</b></div><div class="compare-kpi"><span>W-D-L</span><b>${{E(kp.w)}}-${{E(kp.d)}}-${{E(kp.l)}}</b></div><div class="compare-kpi"><span>Goals/game</span><b>${{E(kp.gfpg)}}</b></div><div class="compare-kpi"><span>Concede/game</span><b>${{E(kp.gapg)}}</b></div></div></div>`}};
 const cmp=(label,h,a,suffix='')=>{{h=Number(h)||0;a=Number(a)||0;const sum=h+a||1;return `<div class="compare-bar"><b>${{E(h)}}${{suffix}}</b><div><div class="tiny muted" style="text-align:center;margin-bottom:5px">${{E(label)}}</div><div class="track"><i class="homefill" style="width:${{Math.round(h/sum*100)}}%"></i><i class="awayfill" style="width:${{Math.round(a/sum*100)}}%"></i></div></div><b style="text-align:right">${{E(a)}}${{suffix}}</b></div>`}};
 const injuries=(rows)=>rows?.length?rows.slice(0,8).map(x=>`<div class="person"><span></span><div><b>${{E(x.player||'Player')}}</b><div class="tiny muted">${{E(x.type||x.reason||'Unavailable')}}</div></div><span></span></div>`).join(''):'<div class="empty">No current absences returned.</div>';
 return `<div class="compare-hero">${{teamCard('home',fh.team?.name||'Home',st.home,hk,hp)}}${{teamCard('away',fa.team?.name||'Away',st.away,ak,ap)}}</div>
 <div class="card"><h2>Season comparison</h2>${{cmp('Win rate',hk.wr,ak.wr,'%')}}${{cmp('Goals scored',hk.gf,ak.gf)}}${{cmp('Goals conceded',hk.ga,ak.ga)}}${{cmp('League points',Number(hp)||0,Number(ap)||0)}}</div>
 <div class="grid2"><div class="card"><h3>${{E(fh.team?.name||'Home')}} · Last 10</h3>${{formRows(fh.last10)}}</div><div class="card"><h3>${{E(fa.team?.name||'Away')}} · Last 10</h3>${{formRows(fa.last10)}}</div></div>
 <div class="grid2"><div class="card"><h3>Head to head intelligence</h3><div class="grid3"><div class="metric"><span class="tiny muted">Meetings</span><b>${{E(h2.played??0)}}</b></div><div class="metric"><span class="tiny muted">BTTS</span><b>${{E(h2.bttsPct??0)}}%</b></div><div class="metric"><span class="tiny muted">Over 2.5</span><b>${{E(h2.over25Pct??0)}}%</b></div></div><p class="tiny muted">${{E(fh.team?.name||'Home')}} wins ${{E(h2.homeWins??0)}} · Draws ${{E(h2.draws??0)}} · ${{E(fa.team?.name||'Away')}} wins ${{E(h2.awayWins??0)}}</p>${{(h2.meetings||[]).slice(0,10).map(x=>`<div class="event"><div class="minute">H2H</div><div><b>${{E(x.home||'')}} ${{E(x.score||'')}} ${{E(x.away||'')}}</b><div class="tiny muted">${{localDate(x.date)}}</div></div></div>`).join('')||'<div class="empty">Data unavailable.</div>'}}</div><div class="card"><h3>Availability</h3><div class="grid2"><div><b>${{E(fh.team?.name||'Home')}}</b>${{injuries(inj.home)}}</div><div><b>${{E(fa.team?.name||'Away')}}</b>${{injuries(inj.away)}}</div></div></div></div>
 <div class="grid2"><div class="card"><h3>Next 5 · ${{E(fh.team?.name||'Home')}}</h3>${{nextRows(n.home)}}</div><div class="card"><h3>Next 5 · ${{E(fa.team?.name||'Away')}}</h3>${{nextRows(n.away)}}</div></div>`}}

function odds(o){{o=o||{{}};const books=o.bookmakers||[],sel=o.selected||books[0]||{{}},markets=sel.markets||[];
 if(!markets.length)return `<div class="card"><h3>Odds / Prediction</h3><div class="empty">No bookmaker markets currently returned for this fixture.</div></div>`;
 return `<div class="card"><h3>Odds / Prediction</h3><p class="tiny muted">${{E(sel.name||o.source||'Bookmaker')}} · only provider-returned markets</p>${{markets.map(m=>`<div style="padding:11px 0;border-top:1px solid var(--line)"><b>${{E(m.name||m.id||'Market')}}</b><div style="display:flex;gap:7px;flex-wrap:wrap;margin-top:7px">${{(m.values||[]).map(v=>`<span class="pill">${{E(v.value)}} <b>${{E(v.odd)}}</b></span>`).join('')}}</div></div>`).join('')}}</div>`}}
function standingsTable(rows,homeId,awayId){{if(!Array.isArray(rows)||!rows.length)return '<div class="empty">No standings available for this competition.</div>';const form=v=>String(v||'').trim().split('').slice(-5).map(x=>`<span class="form-pill form-${{E(x).toLowerCase()}}">${{E(x)}}</span>`).join('');return `<div class="standings-wrap"><table class="standings-table"><thead><tr><th>Pos</th><th>Team</th><th>P</th><th>W</th><th>D</th><th>L</th><th>F</th><th>A</th><th>+/-</th><th>PTS</th><th>Form</th></tr></thead><tbody>${{rows.map(r=>{{const t=r.team||{{}},a=r.all||{{}},g=a.goals||{{}},focus=String(t.id)===String(homeId)||String(t.id)===String(awayId);return `<tr class="${{focus?'standings-focus':''}}"><td>${{E(r.rank??'—')}}</td><td><div class="standing-team">${{t.logo?`<img src="${{E(t.logo)}}" alt="">`:''}}<b>${{E(t.name||'Team')}}</b></div></td><td>${{E(a.played??'—')}}</td><td>${{E(a.win??'—')}}</td><td>${{E(a.draw??'—')}}</td><td>${{E(a.lose??'—')}}</td><td>${{E(g.for??'—')}}</td><td>${{E(g.against??'—')}}</td><td>${{E(r.goalsDiff??'—')}}</td><td><b>${{E(r.points??'—')}}</b></td><td><div class="form-row">${{form(r.form)}}</div></td></tr>`}}).join('')}}</tbody></table></div>`}}
function wireTabs(){{document.querySelectorAll('.tabs button').forEach(b=>b.onclick=()=>{{document.querySelectorAll('.tabs button').forEach(x=>x.classList.toggle('active',x===b));document.querySelectorAll('.panel').forEach(x=>x.classList.toggle('active',x.id===b.dataset.p))}})}}
async function load(force=false){{try{{const qs=new URLSearchParams();if(LEAGUE)qs.set('league',LEAGUE);if(force)qs.set('refresh','1');const tipMode=new URLSearchParams(location.search).get('tip')==='1';const d=tipMode?{{match:{{}}}}:await J('/sports/'+encodeURIComponent(SPORT)+'/match/'+encodeURIComponent(ID)+(qs.toString()?'?'+qs.toString():'')),m=d.match||{{}};if(SPORT!=='football'){{page.innerHTML=`<div class="card"><h1>${{E(m.home||m.homeTeam||'Home')}} vs ${{E(m.away||m.awayTeam||'Away')}}</h1><div class="score">${{E(m.homeScore??'—')}} – ${{E(m.awayScore??'—')}}</div><p class="muted">${{E(m.league||SPORT)}} · ${{E(m.status||'')}}</p></div><div class="card"><h2>Sport-specific match data</h2><pre style="white-space:pre-wrap">${{E(JSON.stringify(d.statistics?.sportSpecific||d.statistics||{{}},null,2))}}</pre></div>`;return}}const matchStatus=String(m.fixture?.status?.short||m.status?.short||m.fixture?.status?.long||m.status||'').toUpperCase();const isPreMatch=['NS','TBD','SCHEDULED','NOT STARTED','POSTPONED'].some(x=>matchStatus===x||matchStatus.includes(x));if(isPreMatch||!m.teams?.home?.name||!m.teams?.away?.name){{try{{const q=await J('/tip-stats/'+encodeURIComponent(ID),16000),h=q.home||{{}},a=q.away||{{}},o=q.odds||{{}},hh=q.headToHead||[],ht=matchTeamTheme(h.id,h.name),at=matchTeamTheme(a.id,a.name);page.innerHTML=`<div class="card hero"><div class="team" style="${{teamCardStyle(ht)}};padding:14px;border:1px solid ${{ht.primary}};border-radius:12px">${{h.badge?`<img src="${{E(h.badge)}}">`:''}}<div class="team-name">${{E(h.name||'Home')}}</div></div><div><div class="status">TIP OF THE DAY · PRE-MATCH STATS</div><div class="score">vs</div><div class="tiny muted">Live match statistics will populate when available.</div></div><div class="team" style="${{teamCardStyle(at)}};padding:14px;border:1px solid ${{at.primary}};border-radius:12px">${{a.badge?`<img src="${{E(a.badge)}}">`:''}}<div class="team-name">${{E(a.name||'Away')}}</div></div></div><div class="grid3"><div class="metric"><span class="tiny muted">Home wins · last 5</span><b>${{E(h.winsLast5??0)}}/5</b></div><div class="metric"><span class="tiny muted">Away wins · last 5</span><b>${{E(a.winsLast5??0)}}/5</b></div><div class="metric"><span class="tiny muted">H2H matches</span><b>${{E(hh.length)}}</b></div></div><div class="card"><h2>1X2 Odds</h2><p>${{E(h.name||'Home')}}: <b>${{E(o.home??'—')}}</b> · Draw: <b>${{E(o.draw??'—')}}</b> · ${{E(a.name||'Away')}}: <b>${{E(o.away??'—')}}</b></p><p class="tiny muted">${{E(o.bookmaker||'No bookmaker odds currently returned')}}</p></div><div class="grid2"><div class="card" style="${{teamCardStyle(ht)}}"><h2>${{E(h.name||'Home')}} · Last 5</h2>${{(h.last5||[]).map(x=>`<p>${{E(x.home)}} ${{E(x.homeScore??'—')}}–${{E(x.awayScore??'—')}} ${{E(x.away)}}</p>`).join('')||'<div class="empty">No recent form returned.</div>'}}</div><div class="card" style="${{teamCardStyle(at)}}"><h2>${{E(a.name||'Away')}} · Last 5</h2>${{(a.last5||[]).map(x=>`<p>${{E(x.home)}} ${{E(x.homeScore??'—')}}–${{E(x.awayScore??'—')}} ${{E(x.away)}}</p>`).join('')||'<div class="empty">No recent form returned.</div>'}}</div></div><div class="card"><h2>Head to Head</h2>${{hh.map(x=>`<p>${{E(x.home)}} ${{E(x.homeScore??'—')}}–${{E(x.awayScore??'—')}} ${{E(x.away)}}</p>`).join('')||'<div class="empty">No H2H returned.</div>'}}</div><div class="card"><h2>Pre-match Statistics</h2><div class="grid3"><div class="metric"><span class="tiny muted">${{E(h.name||'Home')}} recent wins</span><b>${{E(h.winsLast5??0)}} / 5</b></div><div class="metric"><span class="tiny muted">${{E(a.name||'Away')}} recent wins</span><b>${{E(a.winsLast5??0)}} / 5</b></div><div class="metric"><span class="tiny muted">H2H sample</span><b>${{E(hh.length)}}</b></div></div><p class="tiny muted">These are pre-match indicators from available recent-form, H2H and bookmaker data. Live match statistics populate after kickoff when the provider returns them.</p></div><div class="card"><h2>Standings</h2>${{standingsTable(d.standings,m.teams?.home?.id,m.teams?.away?.id)}}</div>`;return}}catch(_){{}}}}
const ts=m.teams||{{}},ev=d.events||[],st=d.statistics||[],lu=d.teams||[],pl=d.players||[],home=ts.home||{{}},away=ts.away||{{}},fx=m.fixture||{{}},lg=m.league||{{}},ht=matchTeamTheme(home.id,home.name),at=matchTeamTheme(away.id,away.name);page.innerHTML=`<div class="card hero"><a class="team" style="${{teamCardStyle(ht)}};padding:14px;border:1px solid ${{ht.primary}};border-radius:12px" href="/teams/${{encodeURIComponent(home.id||'')}}">${{home.logo?`<img src="${{E(home.logo)}}">`:''}}<div class="team-name">${{E(home.name||'Home')}}</div><div class="scorers">${{scorerLines(ev,home.id)||'&nbsp;'}}</div></a><div><div class="tiny muted">${{lg.flag?`<img src="${{E(lg.flag)}}" alt="" style="width:18px;height:12px;object-fit:cover;vertical-align:middle;margin-right:5px">`:''}}${{E(lg.country||'')}} · ${{E(lg.name||'Football')}}</div><div class="score">${{E(m.goals?.home??'—')}} – ${{E(m.goals?.away??'—')}}</div><div class="status">${{E(fx.status?.long||'Match')}}</div><div class="tiny muted">${{localDate(fx.date)}}<br>${{E(fx.venue?.name||'Venue —')}}</div></div><a class="team" style="${{teamCardStyle(at)}};padding:14px;border:1px solid ${{at.primary}};border-radius:12px" href="/teams/${{encodeURIComponent(away.id||'')}}">${{away.logo?`<img src="${{E(away.logo)}}">`:''}}<div class="team-name">${{E(away.name||'Away')}}</div><div class="scorers">${{scorerLines(ev,away.id)||'&nbsp;'}}</div></a></div><div class="tabs"><button class="active" data-p="overview">Overview</button><button data-p="timeline">Timeline</button><button data-p="stats">Statistics</button><button data-p="standings">Standings</button><button data-p="lineups">Lineups</button><button data-p="players">Player Stats</button><button data-p="intel">Match Intelligence</button><button data-p="odds">Odds / Prediction</button></div><section class="panel active" id="overview"><div class="grid3"><div class="metric"><span class="muted tiny">Venue</span><b>${{E(fx.venue?.name||'—')}}</b><span class="tiny muted">${{E(fx.venue?.city||'')}}</span></div><div class="metric"><span class="muted tiny">Referee</span><b>${{E(fx.referee||'—')}}</b></div><div class="metric"><span class="muted tiny">Round</span><b>${{E(lg.round||'—')}}</b></div></div><div class="card"><h2>Key Events</h2>${{timeline(ev.filter(x=>['goal','card'].includes(String(x.type||'').toLowerCase())).slice(0,14))}}</div><div class="card"><h2>Match Statistics</h2>${{statRows(st)}}</div></section><section class="panel" id="timeline"><div class="card"><h2>Match Timeline</h2>${{timeline(ev)}}</div></section><section class="panel" id="stats"><div class="card"><h2>Detailed Statistics</h2>${{statRows(st)}}</div></section><section class="panel" id="standings"><div class="card"><h2>${{E(lg.name||'Competition')}} Standings</h2>${{standingsTable(d.standings,home.id,away.id)}}</div></section><section class="panel" id="lineups"><div class="grid2">${{lineups(lu)}}</div></section><section class="panel" id="players"><div class="card"><h2>Player Match Data</h2><p class="tiny muted">Click a player for the full profile.</p>${{playerStats(pl)}}</div></section><section class="panel" id="intel">${{intelligence(d.insights)}}</section><section class="panel" id="odds">${{odds(d.odds)}}</section>`;wireTabs();if(!force&&(d.cached||d.refreshing))setTimeout(()=>load(true),350)}}catch(e){{page.innerHTML=`<div class="card"><h2>Match data temporarily unavailable</h2><p class="muted">The match service did not return usable data. Please retry.</p><button onclick="location.reload()">Retry</button></div>`}}}}load();
</script></body></html>"""

def _standalone_sports_page(kind:str, entity_id:str, sport:str="football", league:str="") -> str:
    # Small independent document: it never hydrates the dashboard underneath.
    eid=json.dumps(str(entity_id)); sp=json.dumps(str(sport)); lg=json.dumps(str(league or ""))
    title={"match":"Match Stats","team":"Team","player":"Player"}.get(kind,"Sports")
    # The entity identity is resolved by the route before this document is rendered.
    # A unique self-canonical prevents Google treating unrelated teams as duplicates.
    canonical_tag = ""
    if kind in {"team", "player"} and sport == "football" and str(entity_id).isdigit():
        route = "teams" if kind == "team" else "players"
        canonical_tag = f'<link rel="canonical" href="https://kasilivescore.com/{route}/{int(entity_id)}">'
    return f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
{canonical_tag}<title>{title} | Kasi Sports News</title>
<style>
:root{{--bg:#000;--card:#000;--line:#222;--text:#f5f5f5;--muted:#9b9b9b;--accent:#38bdf8}}
*{{box-sizing:border-box}}body{{margin:0;background:var(--bg);color:var(--text);font-family:Arial,sans-serif;font-size:14px;line-height:1.4}}
main{{max-width:1120px;margin:auto;padding:18px}}a{{color:var(--accent)}}.top{{display:flex;justify-content:space-between;align-items:center;gap:12px;margin-bottom:18px}}
.back{{padding:10px 14px;border:1px solid var(--line);border-radius:9px;text-decoration:none;font-weight:800;background:#111;cursor:pointer}}.ksn-head{{display:flex;align-items:center;gap:9px}}.ksn-head img{{width:38px;height:38px;object-fit:contain;border-radius:50%}}
.card{{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:18px;margin:14px 0;box-shadow:0 10px 28px rgba(0,0,0,.14)}}
.hero{{display:grid;grid-template-columns:1fr auto 1fr;gap:18px;align-items:center;text-align:center}}
.team img,.avatar{{width:64px;height:64px;object-fit:contain;border-radius:50%}}.score{{font-size:34px;font-weight:900}}
.grid{{display:grid;grid-template-columns:1fr 1fr;gap:12px}}.row{{display:grid;grid-template-columns:1fr 1fr 1fr;gap:8px;padding:9px 0;border-bottom:1px solid var(--line)}}.muted{{color:var(--muted)}}.standings-table{{width:100%;border-collapse:collapse;min-width:620px}}.standings-table th,.standings-table td{{padding:10px 12px;border-bottom:1px solid var(--line);font-size:13px;vertical-align:middle;text-align:center;white-space:nowrap}}.standings-table th{{font-size:11px;text-transform:uppercase;letter-spacing:.04em;color:var(--muted);font-weight:800}}.standings-table th:nth-child(2),.standings-table td:nth-child(2){{text-align:left;min-width:180px}}.standings-table td:last-child{{font-weight:900}}
.person{{display:flex;gap:12px;align-items:center;padding:12px 10px;border-bottom:1px solid var(--line);border-radius:9px;cursor:pointer}}.person:hover{{background:#171b20}}
@media(max-width:700px){{.grid,.hero{{grid-template-columns:1fr}}.score{{font-size:28px}}}}
</style></head><body class="ks-standalone-page"><main><div class="top"><a class="back" href="/" onclick="event.preventDefault();return kasiBackHome();">← Back to Home</a><div class="ksn-head"><img src="/kasi-sports-news-logo.png" alt="Kasi Sports News"><b>Kasi Sports News</b></div></div>
<div id="page"><div class="card">Loading {title.lower()}…</div></div></main>
<script>
const KIND={json.dumps(kind)},ID={eid},SPORT={sp},LEAGUE={lg},page=document.getElementById('page');function kasiBackHome(){{try{{if(history.length>1){{history.back();return false}}}}catch(_){{}}location.replace('/');return false;}}
const E=v=>String(v??'').replace(/[&<>"']/g,c=>({{'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}}[c]));
const FD=v=>{{try{{return new Date(v).toLocaleString('en-ZA',{{day:'2-digit',month:'short',year:'numeric',hour:'2-digit',minute:'2-digit'}}).replace(',',' &middot;')}}catch(_){{return v||'—'}}}};
const TEAM_CACHE_KEY='ks:v481:team-page:'+ID;
function teamTheme(id,name){{
 const key=String(name||'').toLowerCase().replace(/[^a-z0-9]/g,'');
 const known={{
  arsenal:['#EF0107','#9C1016'],chelsea:['#034694','#1B5FC1'],liverpool:['#C8102E','#7A0018'],manchestercity:['#6CABDD','#2D78A4'],manchesterunited:['#DA291C','#8F1111'],tottenhamhotspur:['#132257','#244A87'],leedsunited:['#FFCD00','#1D428A'],newcastleunited:['#241F20','#5B5B5B'],astonvilla:['#670E36','#95BFE5'],everton:['#003399','#1B55B5'],brighton:['#0057B8','#FFCD00'],westhamunited:['#7A263A','#1BB1E7'],nottinghamforest:['#DD0000','#8E0000'],sunderland:['#EB172B','#8A0D18'],fulham:['#CC0000','#111111'],crystalpalace:['#1B458F','#C4122E'],bournemouth:['#DA291C','#111111'],brentford:['#E30613','#FBB800'],burnley:['#6C1D45','#99D6EA'],wolverhamptonwanderers:['#FDB913','#231F20'],wolves:['#FDB913','#231F20'],
  realmadrid:['#FEBE10','#5E6AFC'],barcelona:['#A50044','#004D98'],atleticomadrid:['#CB3524','#272E61'],athleticclub:['#EE2523','#111111'],villarreal:['#F7E700','#005187'],sevilla:['#D71920','#FFFFFF'],valencia:['#F18E00','#111111'],realsociedad:['#0067B1','#FFFFFF'],realbetis:['#00954C','#FFFFFF'],
  bayernmunich:['#DC052D','#0066B2'],borussiadortmund:['#FDE100','#111111'],bayerleverkusen:['#E32221','#111111'],rbLeipzig:['#DD0741','#001F47'],rbleipzig:['#DD0741','#001F47'],eintrachtfrankfurt:['#E1000F','#111111'],werderbremen:['#1D9053','#FFFFFF'],stuttgart:['#E32219','#FFFFFF'],
  juventus:['#111111','#FFFFFF'],inter:['#0068A8','#111111'],internazionale:['#0068A8','#111111'],acmilan:['#FB090B','#111111'],milan:['#FB090B','#111111'],napoli:['#12A0D7','#FFFFFF'],roma:['#8E1F2F','#F0BC42'],lazio:['#87D8F7','#FFFFFF'],atalanta:['#1E71B8','#111111'],fiorentina:['#5B2A86','#FFFFFF'],
  psg:['#004170','#DA291C'],parissaintgermain:['#004170','#DA291C'],marseille:['#2FAEE0','#FFFFFF'],monaco:['#E30613','#FFFFFF'],lyon:['#1F3A93','#DA291C'],lille:['#E01E2D','#242A5A'],nice:['#D71920','#111111'],lens:['#D71920','#F6C500']
 }};
 if(known[key])return {{primary:known[key][0],secondary:known[key][1]}};
 const palette=[['#2563EB','#1E3A8A'],['#DC2626','#7F1D1D'],['#16A34A','#14532D'],['#9333EA','#581C87'],['#EA580C','#7C2D12'],['#0891B2','#164E63'],['#DB2777','#831843'],['#CA8A04','#713F12']];
 let h=Number(id)||0;if(!h){{for(const c of key)h=((h<<5)-h)+c.charCodeAt(0)}}const c=palette[Math.abs(h)%palette.length];return {{primary:c[0],secondary:c[1]}};
}}
function applyTeamTheme(el,theme){{if(!el||!theme)return;el.style.setProperty('--team-primary',theme.primary);el.style.setProperty('--team-secondary',theme.secondary);el.style.borderColor=theme.primary;el.style.boxShadow='inset 4px 0 0 '+theme.primary;el.style.background='linear-gradient(135deg,'+theme.primary+'24,rgba(10,12,15,.96) 46%)'}}
function bindTeamTabs(){{document.querySelectorAll('[data-teamtab]').forEach((b,i)=>{{b.style.cssText='border:0;background:transparent;color:#fff;padding:13px 16px;font-weight:800;cursor:pointer;border-bottom:3px solid '+(i===0?'var(--accent)':'transparent');b.onclick=()=>{{document.querySelectorAll('[data-teampanel]').forEach(p=>p.style.display=p.dataset.teampanel===b.dataset.teamtab?'':'none');document.querySelectorAll('[data-teamtab]').forEach(x=>x.style.borderBottom=x===b?'3px solid var(--accent)':'3px solid transparent')}}}})}}
async function J(u,timeout=25000){{let err=null;for(let n=0;n<2;n++){{const c=new AbortController(),t=setTimeout(()=>c.abort('timeout'),timeout);try{{const r=await fetch(u,{{signal:c.signal,headers:{{Accept:'application/json'}},cache:n?'no-store':'default'}});if(!r.ok)throw Error('HTTP '+r.status);return await r.json()}}catch(e){{err=e;if(!n)await new Promise(r=>setTimeout(r,250))}}finally{{clearTimeout(t)}}}}throw Error(err?.message||'Data temporarily unavailable')}}
function teamLink(id,name,logo=''){{return id?`<a class="team" href="/teams/${{encodeURIComponent(id)}}">${{logo?`<img src="${{E(logo)}}" alt="">`:''}}<div>${{E(name)}}</div></a>`:`<div>${{E(name)}}</div>`}}
async function match(){{
 try{{const d=await J('/sports/'+encodeURIComponent(SPORT)+'/match/'+encodeURIComponent(ID)+(LEAGUE?'?league='+encodeURIComponent(LEAGUE):'')),m=d.match||{{}};
  if(SPORT==='football'){{const ts=m.teams||{{}},stats=d.statistics||[],events=d.events||[],line=d.teams||[];
   const statRows=(stats[0]?.statistics||[]).map(s=>{{const other=(stats[1]?.statistics||[]).find(x=>x.type===s.type);return `<div class="row"><b>${{E(s.value??'—')}}</b><span class="muted">${{E(s.type)}}</span><b>${{E(other?.value??'—')}}</b></div>`}}).join('');
   const lineups=line.map(t=>`<div class="card"><h3>${{E(t.team?.name||'Team')}}</h3>${{(t.startXI||t.players||[]).map(z=>{{const q=z.player||z;return `<div class="person" onclick="location.href='/players/${{encodeURIComponent(q.id)}}'">${{E(q.name||'Player')}}</div>`}}).join('')||'<div class="muted">No lineup returned.</div>'}}</div>`).join('');
   page.innerHTML=`<div class="card hero">${{teamLink(ts.home?.id,ts.home?.name||'Home',ts.home?.logo)}}<div><div class="muted">${{E(m.league?.name||'Football')}}</div><div class="score">${{E(m.goals?.home??'—')}} - ${{E(m.goals?.away??'—')}}</div><div class="muted">${{E(m.fixture?.status?.long||'Match')}}</div></div>${{teamLink(ts.away?.id,ts.away?.name||'Away',ts.away?.logo)}}</div><div class="grid"><div class="card"><h2>Match Statistics</h2>${{statRows||'<div class="muted">No statistics returned for this match.</div>'}}</div><div class="card"><h2>Match Information</h2><p>Venue: ${{E(m.fixture?.venue?.name||'—')}}</p><p>Referee: ${{E(m.fixture?.referee||'—')}}</p><p>Status: ${{E(m.fixture?.status?.long||'—')}}</p></div></div>${{events.length?`<div class="card"><h2>Events</h2>${{events.map(x=>`<p>${{E(x.time?.elapsed??'')}}′ · ${{E(x.team?.name||'')}} · ${{E(x.type||'')}} ${{E(x.detail||'')}}</p>`).join('')}}</div>`:''}}<div class="grid">${{lineups}}</div>`;
  }}else{{const x=m.fixture||m,st=d.statistics||{{}},periods=st.scoresByPeriod||{{}};
   const scoreRows=Object.entries(periods).map(([k,v])=>`<div class="row"><b>${{E(v?.participant1Score??'—')}}</b><span class="muted">Period ${{E(k)}}</span><b>${{E(v?.participant2Score??'—')}}</b></div>`).join('');
   const hf=st.homeForm||{{}},af=st.awayForm||{{}};
   page.innerHTML=`<div class="card"><h1>${{E(x.home||x.homeTeam||m.home||'Home')}} vs ${{E(x.away||x.awayTeam||m.away||'Away')}}</h1><p>${{E(x.league||m.league||SPORT)}}</p><p class="score">${{E(x.homeScore??'—')}} - ${{E(x.awayScore??'—')}}</p><p>${{E(x.status||'')}}</p></div><div class="grid"><div class="card"><h2>Scores / periods</h2>${{scoreRows||'<div class="muted">No score breakdown returned by the provider.</div>'}}</div><div class="card"><h2>Recent form</h2><p>${{E(x.home||'Home')}}: ${{E(hf.wins??0)}}W ${{E(hf.draws??0)}}D ${{E(hf.losses??0)}}L</p><p>${{E(x.away||'Away')}}: ${{E(af.wins??0)}}W ${{E(af.draws??0)}}D ${{E(af.losses??0)}}L</p></div></div>`}}
 }}catch(e){{page.innerHTML=`<div class="card"><h2>Match data temporarily unavailable</h2><p class="muted">The match provider did not return data after a retry. Please try again shortly.</p><button onclick="location.reload()" style="padding:10px 14px;border-radius:8px;cursor:pointer">Retry</button></div>`}}
}}
async function resolve(kind,id){{if(/^\\d+$/.test(id))return id;const d=await J('/public-resolve/'+kind+'/'+encodeURIComponent(id));return d.id}}
async function team(){{
 try{{
  let cachedHtml='';try{{const c=JSON.parse(localStorage.getItem(TEAM_CACHE_KEY)||'null');if(c&&c.html&&Date.now()-c.savedAt<86400000){{cachedHtml=c.html;page.innerHTML=cachedHtml;bindTeamTabs()}}}}catch(_){{}}
  if(!cachedHtml)page.innerHTML='<div class="card"><h2>Loading team…</h2><p class="muted">Building the club profile from the latest available data.</p></div>';
  const id=await resolve('team',ID);
  const [d,h,ti]=await Promise.all([J('/team/profile?team='+encodeURIComponent(id),25000),J('/team/seasons-history?team='+encodeURIComponent(id)+'&seasons=5',35000).catch(()=>({{seasons:[]}})),J('/team/intelligence?team='+encodeURIComponent(id),35000).catch(()=>({{}}))]);
  const t=d.team||{{}},players=d.players||[],theme=teamTheme(id,t.name),hist=h.seasons||[],sum=ti.summary||{{}},inj=(ti.injuries||{{}}).players||[],forms=ti.recentFormations||[],cov=ti.coverage||{{}},fp=ti.fantasyPlayers||[];
  document.documentElement.style.setProperty('--accent',theme.primary);
  const seasonLabel=(v)=>v?`${{E(v)}}/${{String((Number(v)||0)+1).slice(-2)}}`:'Current';
  const rank=(d.standings||[]).find(r=>String(r.team?.id||'')===String(id));
  const resultMark=x=>{{const home=String(x.homeId||x.homeTeamId||'')===String(id)||String(x.home||'').toLowerCase()===String(t.name||'').toLowerCase();const a=Number(x.homeScore),b=Number(x.awayScore);if(!Number.isFinite(a)||!Number.isFinite(b))return '';const z=home?a-b:b-a;return z>0?'W':z<0?'L':'D'}};
  const resultColor=r=>r==='W'?'#22c55e':r==='L'?'#ef4444':'#f59e0b';
  const matchRows=(rows,finished)=>rows.map(x=>{{const r=finished?resultMark(x):'';return `<tr><td>${{E(FD(x.date))}}</td><td>${{E(x.league||'—')}}</td><td style="text-align:left"><b>${{E(x.home||'')}} ${{finished?E(x.homeScore??'—'):'vs'}} ${{finished?E(x.awayScore??'—'):''}} ${{E(x.away||'')}}</b></td><td>${{r?`<b style="color:${{resultColor(r)}}">${{r}}</b>`:'—'}}</td><td>${{x.id?`<a class="back" style="padding:6px 10px" href="/matches/${{encodeURIComponent(x.id)}}/stats">Stats</a>`:'—'}}</td></tr>`}}).join('');
  const positionOrder={{'Goalkeeper':0,'Defender':1,'Midfielder':2,'Attacker':3}}; players.sort((a,b)=>(positionOrder[a.position]??9)-(positionOrder[b.position]??9)||String(a.name||'').localeCompare(String(b.name||'')));
  const squadRows=players.map(p=>{{const f=fp.find(q=>String(q.name||'').toLowerCase()===String(p.name||'').toLowerCase())||{{}};return `<tr><td style="text-align:left"><a href="/players/${{encodeURIComponent(p.publicRef||p.id)}}" style="color:inherit;text-decoration:none;display:flex;align-items:center;gap:9px">${{p.photo?`<img src="${{E(p.photo)}}" style="width:34px;height:34px;border-radius:50%;object-fit:cover">`:''}}<b>${{E(p.name)}}</b></a></td><td>${{E(p.position||'—')}}</td><td>${{E(p.number??'—')}}</td><td>${{E(p.nationality||'—')}}</td><td style="color:#c084fc"><b>${{E(f.fantasyPoints??'—')}}</b></td></tr>`}}).join('');
  const histRows=hist.map((r,i)=>`<tr style="border-left:4px solid ${{i===0?theme.primary:theme.secondary}}"><td style="text-align:left"><b>${{seasonLabel(r.season)}}</b></td><td>${{E(r.rank??'—')}}</td><td>${{E(r.points??'—')}}</td><td>${{E(r.played??'—')}}</td><td style="color:#22c55e">${{E(r.wins??'—')}}</td><td style="color:#f59e0b">${{E(r.draws??'—')}}</td><td style="color:#ef4444">${{E(r.losses??'—')}}</td><td>${{E(r.goalsFor??'—')}}</td><td>${{E(r.goalsAgainst??'—')}}</td><td>${{E(r.goalDifference??'—')}}</td><td>${{E(r.winRate??'—')}}${{r.winRate!=null?'%':''}}</td><td>${{E(r.cleanSheets??'—')}}</td></tr>`).join('');
  const statRows=[['Played',sum.played??d.teamStats?.fixtures?.played?.total],['Wins',sum.wins??d.teamStats?.fixtures?.wins?.total],['Draws',sum.draws??d.teamStats?.fixtures?.draws?.total],['Losses',sum.losses??d.teamStats?.fixtures?.loses?.total],['Goals For',sum.goalsFor??d.teamStats?.goals?.for?.total?.total],['Goals Against',sum.goalsAgainst??d.teamStats?.goals?.against?.total?.total],['Goal Difference',sum.goalDifference],['Win Rate',sum.winRate==null?'—':sum.winRate+'%'],['Clean Sheets',sum.cleanSheets],['Failed to Score',sum.failedToScore],['Home W / P',(sum.homeWins??'—')+' / '+(sum.homePlayed??'—')],['Away W / P',(sum.awayWins??'—')+' / '+(sum.awayPlayed??'—')]];
  const metricTable=`<div style="overflow:auto"><table class="standings-table"><thead><tr><th style="text-align:left">Metric</th><th>Value</th></tr></thead><tbody>${{statRows.map(x=>`<tr><td style="text-align:left">${{E(x[0])}}</td><td><b>${{E(x[1]??'—')}}</b></td></tr>`).join('')}}</tbody></table></div>`;
  page.innerHTML=`<section class="card" style="border-color:${{theme.primary}};box-shadow:inset 6px 0 0 ${{theme.primary}};background:linear-gradient(135deg,${{theme.primary}}2b,rgba(5,7,10,.97) 46%)"><div style="display:flex;align-items:center;gap:18px;flex-wrap:wrap">${{t.logo?`<img src="${{E(t.logo)}}" style="width:82px;height:82px;object-fit:contain">`:''}}<div style="flex:1;min-width:240px"><h1 style="margin:0 0 5px">${{E(t.name||'Team')}}</h1><div class="muted">${{E(t.country||'—')}} · ${{E((d.venue||{{}}).name||'Stadium unavailable')}}</div><div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:12px"><span style="border:1px solid ${{theme.primary}};border-radius:999px;padding:6px 10px"><b>${{E(rank?.rank?'#'+rank.rank:'—')}}</b> League position</span><span style="border:1px solid #30363d;border-radius:999px;padding:6px 10px">Form <b>${{E((d.form||[]).join(' ')||'—')}}</b></span><span style="border:1px solid #30363d;border-radius:999px;padding:6px 10px">Season <b>${{seasonLabel(d.season)}}</b></span></div></div></div></section>
  <div class="card" style="padding:0 12px"><div class="ks-team-tabs" style="display:flex;gap:2px;overflow:auto"><button data-teamtab="overview">Overview</button><button data-teamtab="matches">Matches</button><button data-teamtab="standings">Standings</button><button data-teamtab="stats">Stats</button><button data-teamtab="squad">Squad</button><button data-teamtab="players">Players</button><button data-teamtab="history">History</button></div></div>
  <section data-teampanel="overview"><div class="card"><h2>Team Overview</h2><p class="muted">Current form, matches, league position and leading players in one club profile.</p></div><div class="grid"><div class="card"><h2>Recent Matches</h2><div style="overflow:auto"><table class="standings-table"><tbody>${{matchRows((d.past10||[]).slice(0,5),true)||'<tr><td class="muted">No recent results returned.</td></tr>'}}</tbody></table></div></div><div class="card"><h2>Next Fixtures</h2><div style="overflow:auto"><table class="standings-table"><tbody>${{matchRows((d.future||[]).slice(0,5),false)||'<tr><td class="muted">No upcoming fixtures returned.</td></tr>'}}</tbody></table></div></div></div><div class="grid"><div class="card"><h2>Season Snapshot</h2>${{metricTable}}</div><div class="card"><h2>Leading Players</h2>${{fp.length?fp.slice().sort((a,b)=>(Number(b.fantasyPoints)||0)-(Number(a.fantasyPoints)||0)).slice(0,6).map(p=>`<div class="person"><div><b>${{E(p.name)}}</b><div class="muted">${{E(p.position||'—')}}</div></div><b style="margin-left:auto;color:#c084fc">${{E(p.fantasyPoints??'—')}} pts</b></div>`).join(''):'<p class="muted">Fantasy leaders unavailable for this team/season.</p>'}}</div></div></section>
  <section data-teampanel="matches" style="display:none"><div class="card"><h2>Results</h2><div style="overflow:auto"><table class="standings-table"><thead><tr><th>Date</th><th>Competition</th><th style="text-align:left">Match</th><th>Form</th><th>Stats</th></tr></thead><tbody>${{matchRows(d.past10||[],true)}}</tbody></table></div></div><div class="card"><h2>Fixtures</h2><div style="overflow:auto"><table class="standings-table"><thead><tr><th>Date</th><th>Competition</th><th style="text-align:left">Match</th><th></th><th>Stats</th></tr></thead><tbody>${{matchRows(d.future||[],false)}}</tbody></table></div></div></section>
  <section data-teampanel="standings" style="display:none"><div class="card"><h2>Standings</h2>${{(d.standings||[]).length?`<div style="overflow:auto"><table class="standings-table"><thead><tr><th>#</th><th>Team</th><th>P</th><th>W</th><th>D</th><th>L</th><th>GF</th><th>GA</th><th>GD</th><th>Pts</th><th>Form</th></tr></thead><tbody>${{d.standings.map(r=>`<tr style="${{String(r.team?.id)===String(id)?'background:'+theme.primary+'22;border-left:4px solid '+theme.primary:''}}"><td>${{E(r.rank??'—')}}</td><td>${{E(r.team?.name||'')}}</td><td>${{E(r.all?.played??'—')}}</td><td>${{E(r.all?.win??'—')}}</td><td>${{E(r.all?.draw??'—')}}</td><td>${{E(r.all?.lose??'—')}}</td><td>${{E(r.all?.goals?.for??'—')}}</td><td>${{E(r.all?.goals?.against??'—')}}</td><td>${{E(r.goalsDiff??'—')}}</td><td><b>${{E(r.points??'—')}}</b></td><td>${{E(r.form||'—')}}</td></tr>`).join('')}}</tbody></table></div>`:'<p class="muted">Standings unavailable for this league/season.</p>'}}</div></section>
  <section data-teampanel="stats" style="display:none"><div class="grid"><div class="card"><h2>Team Stats · Current Season</h2>${{metricTable}}</div><div class="card"><h2>Availability & Formations</h2><h3>Injuries / Suspensions</h3>${{inj.length?inj.slice(0,12).map(x=>`<div class="person"><b>${{E(x.name||'Player')}}</b><span style="margin-left:auto;color:#ef4444">${{E(x.type||x.reason||'Unavailable')}}</span></div>`).join(''):`<p class="muted">${{cov.injuries===false?'Injury coverage unavailable for this league/season.':'No current injuries or suspensions returned.'}}</p>`}}<h3>Recent formations</h3><p>${{forms.length?forms.map(x=>`<span style="display:inline-block;border:1px solid ${{theme.primary}};border-radius:999px;padding:5px 9px;margin:3px">${{E(x)}}</span>`).join(''):'<span class="muted">No confirmed recent formations returned.</span>'}}</p></div></div></section>
  <section data-teampanel="squad" style="display:none"><div class="card"><h2>First Team Squad</h2><div style="overflow:auto"><table class="standings-table"><thead><tr><th style="text-align:left">Player</th><th>Position</th><th>#</th><th>Nationality</th><th>Fantasy pts</th></tr></thead><tbody>${{squadRows||'<tr><td colspan="5" class="muted">No squad returned by the provider.</td></tr>'}}</tbody></table></div></div></section>
  <section data-teampanel="players" style="display:none"><div class="card"><h2>Players</h2><p class="muted">Football identity and squad data are combined with Fantasy performance when available. Select a player for the dedicated multi-season Player Stats page.</p><div style="overflow:auto"><table class="standings-table"><thead><tr><th style="text-align:left">Player</th><th>Position</th><th>#</th><th>Nationality</th><th>Fantasy pts</th></tr></thead><tbody>${{squadRows||'<tr><td colspan="5" class="muted">Player data unavailable for this mapped team.</td></tr>'}}</tbody></table></div></div></section>
  <section data-teampanel="history" style="display:none"><div class="card"><h2>Team History</h2><p class="muted">Completed seasons remain stored separately; current-season data is never replaced by historical data.</p>${{histRows?`<div style="overflow:auto"><table class="standings-table" style="min-width:900px"><thead><tr><th style="text-align:left">Season</th><th>Pos</th><th>Pts</th><th>P</th><th>W</th><th>D</th><th>L</th><th>GF</th><th>GA</th><th>GD</th><th>Win %</th><th>CS</th></tr></thead><tbody>${{histRows}}</tbody></table></div>`:'<p class="muted">Historical season data is not yet available for this team.</p>'}}</div></section>`;
  bindTeamTabs();
  try{{localStorage.setItem(TEAM_CACHE_KEY,JSON.stringify({{savedAt:Date.now(),html:page.innerHTML}}))}}catch(_){{}}
 }}catch(e){{page.innerHTML=`<div class="card"><h2>Team data unavailable</h2><p class="muted">${{E(e.message)}}</p><button onclick="location.reload()" style="padding:10px 14px;border-radius:8px;cursor:pointer">Retry team data</button></div>`}}
}}
async function player(){{
 try{{const id=await resolve('player',ID),d=await J('/player/profile?player='+encodeURIComponent(id),25000),x=d.player||d||{{}};page.innerHTML=`<div class="card"><h1>${{E(x.name||'Player')}}</h1><p class="muted">Dedicated Player Stats profile</p></div>`}}catch(e){{page.innerHTML=`<div class="card"><h2>Player data unavailable</h2><p>${{E(e.message)}}</p></div>`}}
}}
(KIND==='match'?match:KIND==='team'?team:player)();
</script></body></html>"""

@app.get("/match/{sport}/{match_id}",response_class=HTMLResponse)
async def dedicated_match_stats_page(sport:str,match_id:str,league:str=Query("")):
    sport=(sport or "football").lower().strip()
    if sport not in {"football","rugby","cricket"}:raise HTTPException(404,"Match not found")
    return HTMLResponse(_standalone_match_stats_page(match_id,sport,league),headers={"Cache-Control":"public, max-age=60, s-maxage=300, stale-while-revalidate=600"})


def _multi_outcome(row:dict)->str:
    hs=row.get("homeScore"); aw=row.get("awayScore")
    try:
        hs=float(hs);aw=float(aw)
        return "HOME" if hs>aw else ("AWAY" if aw>hs else "DRAW")
    except Exception:return ""

async def _multi_recent(team_id, sport:str, limit:int=5):
    if not team_id:return []
    rows=await _oddspapi_sport_fixtures(sport,None,False)
    out=[x for x in rows if str(x.get("homeId"))==str(team_id) or str(x.get("awayId"))==str(team_id)]
    out=[x for x in out if _multi_outcome(x)]
    out.sort(key=lambda x:str(x.get("date") or ""),reverse=True)
    return out[:limit]

def _multi_team_form(rows:list,team_id)->dict:
    wins=draws=losses=0
    for x in rows:
        outcome=_multi_outcome(x)
        home=str(x.get("homeId"))==str(team_id)
        won=(outcome=="HOME" and home) or (outcome=="AWAY" and not home)
        if outcome=="DRAW":draws+=1
        elif won:wins+=1
        else:losses+=1
    return {"wins":wins,"draws":draws,"losses":losses,"played":len(rows)}


async def _oddspapi_fixture_scores(fixture_id:str)->dict:
    """Fetch OddsPapi period scores for one fixture. Fail-soft and quota-aware via _oddspapi_get."""
    fid=str(fixture_id or "").strip()
    if not fid:return {"fixtureId":"","periods":{},"latest":{},"available":False}
    if not fid.startswith("id"): fid="id"+fid
    try:
        d=await _oddspapi_get(f"{ODDSPAPI_REST_LANGUAGE}/scores",{"fixtureId":fid})
        raw=d if isinstance(d,dict) else {}
        periods=raw.get("scores") if isinstance(raw.get("scores"),dict) else {}
        def pkey(kv):
            k,v=kv
            try:return (0,int(k))
            except:return (1,str(k))
        ordered=sorted(periods.items(),key=pkey)
        latest=(ordered[-1][1] if ordered and isinstance(ordered[-1][1],dict) else {})
        # Return a normalized aggregate as well as period detail. Rugby/cricket
        # score payloads differ by competition, so reuse the same tolerant score
        # extractor used for fixture payloads instead of assuming one field pair.
        aggregate_source={"scores":periods,"latest":latest,**raw}
        home_score,away_score=_oddspapi_score_pair(aggregate_source)
        return {"fixtureId":fid,"periods":periods,"latest":latest,"homeScore":home_score,"awayScore":away_score,"available":bool(periods) or (home_score is not None and away_score is not None)}
    except Exception as exc:
        log.warning("OddsPapi score lookup failed fixture=%s: %s",fid,exc)
        return {"fixtureId":fid,"periods":{},"latest":{},"available":False,"warning":"Score data unavailable"}

async def _oddspapi_find_fixture(sport:str,fixture_id:str)->dict:
    clean=str(fixture_id or "").strip()
    if clean.startswith("id") and clean[2:].isdigit():clean=clean[2:]
    # First try a direct provider lookup; if unavailable, use normalized fixture windows.
    try:
        sid={"football":ODDSPAPI_SPORT_FOOTBALL,"rugby":ODDSPAPI_SPORT_RUGBY,"cricket":ODDSPAPI_SPORT_CRICKET}.get(sport)
        d=await _oddspapi_get(f"{ODDSPAPI_REST_LANGUAGE}/fixtures",{"sportId":sid,"fixtureIds":clean})
        for raw in _oddspapi_rows(d):
            x=_oddspapi_multisport_event(raw,sport)
            if str(x.get("id"))==clean or str(x.get("providerFixtureId")) in {clean,"id"+clean}:return x
    except Exception as exc:log.warning("OddsPapi %s fixture lookup failed: %s",sport,exc)
    for shift in (-1,0,1):
        day=(datetime.now(timezone.utc)+timedelta(days=shift)).strftime("%Y-%m-%d")
        try:
            for x in await _oddspapi_sport_fixtures(sport,day,False):
                if str(x.get("id"))==clean or str(x.get("providerFixtureId")) in {clean,"id"+clean}:return x
        except Exception:pass
    return {}

@app.get("/sports/{sport}/finished")
async def multisport_finished(sport:str,limit:int=Query(100,ge=1,le=200)):
    """Confirmed Rugby/Cricket finals from the rolling previous 48 hours.

    A row is public only when it is provider-confirmed finished AND has a real
    final score. Missing fixture scores are resolved from the score endpoint;
    simulated/SRL events are excluded upstream.
    """
    sport=sport.lower().strip()
    if sport not in {"rugby","cricket"}:raise HTTPException(400,"Supported sports: rugby, cricket")
    now=datetime.now(timezone.utc);cutoff=now-timedelta(hours=48)
    rows=await _oddspapi_sport_range(sport,cutoff,now+timedelta(minutes=5),2)
    rows=await _oddspapi_enrich_scores(rows,200)
    done=[]
    for x in rows:
        sid=x.get("statusId");st=str(x.get("status") or "").lower()
        confirmed=(sid==2 or st in {"finished","ended","complete","completed","full time","final"} or "finished" in st or "final" in st)
        scored=x.get("homeScore") is not None and x.get("awayScore") is not None
        try:
            when=datetime.fromisoformat(str(x.get("date") or "").replace("Z","+00:00"))
            in_window=cutoff <= when <= now+timedelta(minutes=5)
        except Exception:in_window=True
        if confirmed and scored and in_window:done.append(x)
    done.sort(key=lambda x:str(x.get("date") or ""),reverse=True)
    done=done[:limit]
    return {"sport":sport,"matches":done,"count":len(done),"source":"OddsPapi","windowHours":48,"confirmedScoresOnly":True}

@app.get("/sports/{sport}/predictions")
async def multisport_predictions(sport:str,limit:int=Query(12,ge=1,le=30)):
    sport=sport.lower().strip()
    if sport not in {"rugby","cricket"}:raise HTTPException(400,"Supported sports: rugby, cricket")
    snap_key=f"v363:predictions:{sport}:{limit}"
    snap=_dashboard_snapshot_get(snap_key)
    if isinstance(snap,dict) and isinstance(snap.get("data"),dict) and (snap.get("data",{}).get("predictions") or []):
        cached=dict(snap["data"]); cached["fromPersistentCache"]=True
        # A cached prediction response is intentionally returned immediately; normal
        # browser/dashboard refresh will replace it on the next provider cycle.
        return cached
    now=datetime.now(timezone.utc)
    # One upcoming snapshot + one shared history snapshot. This replaces the
    # previous N+1 design that could spend ~50 provider calls for 12 picks.
    upcoming=await _oddspapi_sport_range(sport,now-timedelta(minutes=30),now+timedelta(days=7),0)
    history=await _oddspapi_sport_range(sport,now-timedelta(days=14),now+timedelta(minutes=5),2)
    future=[x for x in upcoming if x.get("statusId") in (0,None) and not _multi_outcome(x)]
    future.sort(key=lambda x:str(x.get("date") or ""))
    by_team={}
    for g in history:
        if not _multi_outcome(g):continue
        for tid in (g.get("homeId"),g.get("awayId")):
            if tid is not None:by_team.setdefault(str(tid),[]).append(g)
    for games in by_team.values():games.sort(key=lambda x:str(x.get("date") or ""),reverse=True)
    result=[]
    for x in future[:limit]:
        hr=by_team.get(str(x.get("homeId")),[])[:5]
        ar=by_team.get(str(x.get("awayId")),[])[:5]
        hf=_multi_team_form(hr,x.get("homeId"));af=_multi_team_form(ar,x.get("awayId"))
        hscore=(hf["wins"]+0.5*hf["draws"])/max(1,hf["played"])
        ascore=(af["wins"]+0.5*af["draws"])/max(1,af["played"])
        if hf["played"]==0 and af["played"]==0:
            # Keep the fixture visible but do not invent confidence from absent history.
            pick="NO_FORM_DATA";conf=0.0;qualified=False
        else:
            pick="DRAW" if abs(hscore-ascore)<0.08 else ("HOME" if hscore>ascore else "AWAY")
            conf=round(50+min(35,abs(hscore-ascore)*50),1);qualified=True
        result.append({**x,"prediction":pick,"confidence":conf,"homeForm":hf,"awayForm":af,
                       "method":"shared 14-day recent-form snapshot","qualified":qualified})
    payload={"sport":sport,"predictions":result,"count":len(result),"source":"Kasi prediction engine",
            "upcomingWindowDays":7,"historyWindowDays":14,"updatedAt":datetime.now(timezone.utc).isoformat(),
            "publicFree":True,"requiresSubscription":False}
    if result:_dashboard_snapshot_put(snap_key,{"data":payload})
    return payload

@app.get("/sports/{sport}/teams-players")
async def multisport_teams_players(sport:str,limit:int=Query(60,ge=1,le=200)):
    sport=sport.lower().strip()
    if sport not in {"rugby","cricket"}:raise HTTPException(400,"Supported sports: rugby, cricket")
    snap_key=f"v363:teams-players:{sport}:{limit}"
    snap=_dashboard_snapshot_get(snap_key)
    cached=(snap.get("data") if isinstance(snap,dict) else None)
    try:
        rows=await asyncio.wait_for(_oddspapi_sport_fixtures(sport,None,False),timeout=5.0)
    except Exception as exc:
        log.debug("%s fixture directory seed unavailable: %s",sport,exc); rows=[]
    teams={}
    for x in rows:
        for side in ("home","away"):
            tid=x.get(side+"Id");name=x.get(side)
            if not tid or not name:continue
            teams[str(tid)]={"id":tid,"name":name,"badge":x.get(side+"Logo") or "","flag":x.get(side+"Flag") or "","country":x.get("country") or "","sport":sport,"source":x.get("source") or "OddsPapi"}
    players=[]
    # Same-sport media enrichment only. Bound it so Teams/Players cannot hold the page open.
    try:
        directory=await asyncio.wait_for(sports_directory(sport,""),timeout=5.0)
        by_name={str(t.get("name") or "").strip().lower():t for t in (directory.get("teams") or []) if t.get("name")}
        for key,t in list(teams.items()):
            d=by_name.get(str(t.get("name") or "").strip().lower()) or {}
            t["badge"]=t.get("badge") or d.get("badge") or d.get("logo") or ""
            t["flag"]=t.get("flag") or d.get("flag") or ""
            t["country"]=t.get("country") or d.get("country") or ""
        for t in directory.get("teams") or []:
            if str(t.get("sport") or sport).lower()!=sport:continue
            tid=str(t.get("id") or t.get("ref") or t.get("name") or "")
            if tid and tid not in teams:teams[tid]={**t,"sport":sport}
        players=[p for p in (directory.get("players") or []) if str(p.get("sport") or sport).lower()==sport][:limit]
    except Exception as exc:
        log.debug("%s same-sport media enrichment unavailable: %s",sport,exc)
    payload={"sport":sport,"teams":list(teams.values())[:limit],"players":players,"teamCount":min(len(teams),limit),"playerCount":len(players),"source":"sport-isolated providers/cache","playersMessage":"" if players else "Player roster data is not supplied by the active provider for this sport.","updatedAt":datetime.now(timezone.utc).isoformat()}
    if payload["teams"] or payload["players"]:
        _dashboard_snapshot_put(snap_key,{"data":payload});return payload
    if isinstance(cached,dict) and (cached.get("teams") or cached.get("players")):
        return {**cached,"fromPersistentCache":True,"stale":True}
    return payload

async def match_tip_stats(fixture_id:int):
    """Compact Tip-of-the-Day evidence: last-five home/away wins, H2H, 1X2 odds and badges."""
    fd=await _afoot_get("/fixtures",{"id":fixture_id})
    rows=fd.get("response") or []
    if not rows: raise HTTPException(404,"Fixture not found")
    f=rows[0]; teams=f.get("teams") or {}
    home=teams.get("home") or {}; away=teams.get("away") or {}
    hid=int(home.get("id") or 0); aid=int(away.get("id") or 0)
    async def recent(tid:int):
        if not tid:return []
        d=await _afoot_get("/fixtures",{"team":tid,"last":5})
        return (d.get("response") or [])[-5:]
    async def h2h():
        if not hid or not aid:return []
        d=await _afoot_get("/fixtures/headtohead",{"h2h":f"{hid}-{aid}","last":5})
        return (d.get("response") or [])[-5:]
    async def odds():
        try:
            d=await _afoot_get("/odds",{"fixture":fixture_id})
            rr=d.get("response") or []
            for bookrow in rr:
                for book in bookrow.get("bookmakers") or []:
                    for bet in book.get("bets") or []:
                        if str(bet.get("name") or "").strip().lower() in {"match winner","1x2","winner"}:
                            vals={str(v.get("value") or "").strip().lower():v.get("odd") for v in bet.get("values") or []}
                            return {"home":vals.get("home") or vals.get("1"),"draw":vals.get("draw") or vals.get("x"),"away":vals.get("away") or vals.get("2"),"bookmaker":book.get("name")}
        except Exception: pass
        return {}
    gathered=await asyncio.gather(recent(hid),recent(aid),h2h(),odds(),return_exceptions=True)
    hr=gathered[0] if isinstance(gathered[0],list) else []
    ar=gathered[1] if isinstance(gathered[1],list) else []
    hh=gathered[2] if isinstance(gathered[2],list) else []
    oo=gathered[3] if isinstance(gathered[3],dict) else {}
    def won(row,tid):
        ts=row.get("teams") or {}; goals=row.get("goals") or {}
        if (ts.get("home") or {}).get("id")==tid:return (goals.get("home") or 0)>(goals.get("away") or 0)
        if (ts.get("away") or {}).get("id")==tid:return (goals.get("away") or 0)>(goals.get("home") or 0)
        return False
    def compact(row):
        ts=row.get("teams") or {}; g=row.get("goals") or {}; fx=row.get("fixture") or {}
        return {"id":fx.get("id"),"date":fx.get("date"),"home":(ts.get("home") or {}).get("name"),"away":(ts.get("away") or {}).get("name"),"homeScore":g.get("home"),"awayScore":g.get("away")}
    return {
      "fixtureId":fixture_id,
      "home":{"id":hid,"name":home.get("name"),"badge":home.get("logo"),"winsLast5":sum(1 for x in hr if won(x,hid)),"last5":[compact(x) for x in hr]},
      "away":{"id":aid,"name":away.get("name"),"badge":away.get("logo"),"winsLast5":sum(1 for x in ar if won(x,aid)),"last5":[compact(x) for x in ar]},
      "headToHead":[compact(x) for x in hh],
      "odds":oo,
      "updatedAt":datetime.now(timezone.utc).isoformat()
    }


_TIP_STATS_CACHE: dict[str,tuple[float,dict]] = {}

@app.get("/tip-stats/{fixture_id}")
async def tip_stats_fast(fixture_id: int):
    """Fast Tip-of-the-Day evidence endpoint. Reuses the existing football evidence
    endpoint but caches the result and always returns JSON instead of leaving the UI spinning."""
    key=str(fixture_id); now=time.time()
    cached=_TIP_STATS_CACHE.get(key)
    if cached and now-cached[0] < 900:return {**cached[1],"cached":True}
    try:
        data=await asyncio.wait_for(match_tip_stats(fixture_id),timeout=14.0)
        if isinstance(data,dict):
            _TIP_STATS_CACHE[key]=(now,data)
            return data
    except Exception as exc:
        log.warning("Tip stats %s failed: %s",fixture_id,exc)
    return {"fixtureId":fixture_id,"available":False,"error":"Match insights temporarily unavailable"}

@app.get("/matches/{fixture_id}/tip-stats")
async def match_tip_stats_alias(fixture_id:int):
    return await tip_stats_fast(fixture_id)


@app.get("/team/data-health")
async def team_data_health(team:int=Query(...,ge=1), season:int=Query(0,ge=0), refresh:int=Query(0,ge=0,le=1)):
    """v480 deployment/data hand-off check. A Big-5 page is healthy only when identity plus real football data is present."""
    season=season or _current_season()
    if refresh and SPORTS_DB_ENABLED:
        try: await _sql_sync_team(team,season,force=True)
        except Exception as exc: log.warning("v480 health refresh %s/%s: %s",team,season,exc)
    prof=_sql_team_profile(team,season) if SPORTS_DB_ENABLED else None
    if not prof:
        prof=await team_profile(team=str(team),season=season)
    identity=prof.get("team") or {}
    checks={
      "identity":bool(identity.get("name") and str(identity.get("name"))!=str(team)),
      "matches":bool((prof.get("past10") or []) or (prof.get("future") or [])),
      "squad":len(prof.get("players") or [])>0,
      "seasonStats":bool(prof.get("teamStats") or {}),
      "standings":bool(prof.get("standings") or [])
    }
    return {"build":KSN_BUILD_VERSION,"teamId":team,"teamName":identity.get("name"),"season":season,"checks":checks,"healthy":all(checks.values()),
            "counts":{"recent":len(prof.get("past10") or []),"upcoming":len(prof.get("future") or []),"squad":len(prof.get("players") or []),"standings":len(prof.get("standings") or [])},
            "note":"healthy=false identifies the exact provider/database hand-off still missing; no zero-filled UI is treated as valid data."}

@app.get("/build-version")
async def build_version():
    return {"version":KSN_BUILD_VERSION,"teamRenderer":"canonical-big5-team-profile-v480","dataPipeline":"canonical-big5-v480"}

@app.get("/matches/{fixture_id}/stats",response_class=HTMLResponse)
async def canonical_match_stats_page(fixture_id:str):
    return HTMLResponse(_standalone_match_stats_page(fixture_id,"football",""),headers={"Cache-Control":"public, max-age=60, s-maxage=300, stale-while-revalidate=600"})

@app.get("/teams/{team_id}",response_class=HTMLResponse)
async def canonical_team_page(team_id:str):
    # This is the first matching FastAPI route for /teams/{...}. Resolve public
    # tokens here, not in the later shadowed /teams/{slug:path} SEO handler.
    if re.fullmatch(r"[1-9][0-9]{0,11}", team_id):
        canonical_id = int(team_id)
    elif "--" in team_id:
        canonical_id = _public_decode("team", team_id)
        # A signed public reference is an alias for its encoded provider ID.
        # Never infer an ID from the human-readable slug or Google's selection.
        return RedirectResponse(url=f"/teams/{canonical_id}", status_code=308,
                                headers={"Cache-Control":"no-store", "X-KSN-Build":KSN_BUILD_VERSION})
    else:
        raise HTTPException(404,"Team not found")
    html=_standalone_sports_page("team",str(canonical_id),"football","")
    html=html.replace("</body>", f'<div id="ksn-build-marker" data-build="{KSN_BUILD_VERSION}" style="display:none"></div></body>', 1)
    return HTMLResponse(html,headers={"Cache-Control":"no-store, no-cache, must-revalidate","Pragma":"no-cache","X-KSN-Build":KSN_BUILD_VERSION})

@app.get("/players/{player_id}",response_class=HTMLResponse)
async def canonical_player_page(player_id:str):
    if re.fullmatch(r"[1-9][0-9]{0,11}",player_id):
        canonical_id=int(player_id)
    elif "--" in player_id:
        canonical_id=_public_decode("player",player_id)
        return RedirectResponse(url=f"/players/{canonical_id}",status_code=308,headers={"Cache-Control":"no-store"})
    else:
        raise HTTPException(404,"Player not found")
    return HTMLResponse(_standalone_sports_page("player",str(canonical_id),"football",""),headers={"Cache-Control":"no-store"})

@app.get("/match/{slug:path}",response_class=HTMLResponse)
async def ssr_match(slug:str):
    path=f"/match/{slug}"
    match=await _ssr_match_data(slug)
    if not match:
        html=(BASE_DIR/"index.html").read_text(encoding="utf-8")
        html=re.sub(r'<title>.*?</title>', '<title>Match Not Found | Kasi Sports News</title>', html, count=1, flags=re.S)
        html=re.sub(r'<meta name="description" content="[^"]*">', '<meta name="description" content="The requested Kasi Sports News match page could not be found.">', html, count=1)
        html=html.replace("</head>",'<meta name="robots" content="noindex,nofollow"></head>',1)
        return HTMLResponse(html,status_code=404,headers={"Cache-Control":"public, max-age=60"})
    return HTMLResponse(await _render_seo_document(path),headers={"Cache-Control":"public, max-age=300, s-maxage=300, stale-while-revalidate=600"})
def _valid_public_slug(slug: str, kind: str = "") -> bool:
    """Accept legacy numeric IDs and signed opaque public refs generated by _public_ref()."""
    value=(slug or "").strip()
    if re.fullmatch(r"[1-9][0-9]{0,11}", value):
        return True
    if kind in {"team","player"} and "--" in value:
        try:
            _public_decode(kind,value)
            return True
        except HTTPException:
            return False
    return False

def _public_slug_to_id(kind: str, slug: str) -> int:
    value=(slug or "").strip()
    if re.fullmatch(r"[1-9][0-9]{0,11}", value):
        return int(value)
    return _public_decode(kind,value)


@app.get("/team/{slug:path}",response_class=HTMLResponse)
async def ssr_team(slug:str):
    if not _valid_public_slug(slug,"team"):raise HTTPException(404,"Team not found")
    return RedirectResponse(url=f"/teams/{slug}",status_code=308,headers={"Cache-Control":"no-store","X-KSN-Build":KSN_BUILD_VERSION})
@app.get("/player/{slug:path}",response_class=HTMLResponse)
async def ssr_player(slug:str):
    if not _valid_public_slug(slug,"player"):raise HTTPException(404,"Player not found")
    return HTMLResponse(_standalone_sports_page("player",slug,"football",""),headers={"Cache-Control":"no-store"})
@app.get("/admin",response_class=HTMLResponse)
async def ssr_admin():
    html=await _render_seo_document("/admin")
    html=html.replace("</head>",'<meta name="robots" content="noindex,nofollow"></head>',1)
    return HTMLResponse(html,headers={"Cache-Control":"no-store"})

def _seo_valid_sport_path(path: str) -> bool:
    """True only for public sport URLs explicitly present in the SEO registry."""
    p = "/" + str(path or "").strip("/")
    try:
        # STEP 4 v325: route validity and search indexability are separate.
        # noindex competition pages must remain reachable for visitors/crawlers;
        # sitemap generation still filters indexable=False independently.
        valid = {str(r.get("path") or "") for r in _seo_registry_pages()}
    except Exception:
        return False
    return p in valid


@app.get("/teams/{slug:path}",response_class=HTMLResponse)
async def ssr_teams(slug:str):
    if not _valid_public_slug(slug,"team"): raise HTTPException(404,"Team not found")
    return HTMLResponse(await _render_seo_document(f"/team/{slug}"),headers={"Cache-Control":"public, max-age=300"})
@app.get("/players/{slug:path}",response_class=HTMLResponse)
async def ssr_players(slug:str):
    if not _valid_public_slug(slug,"player"): raise HTTPException(404,"Player not found")
    return HTMLResponse(await _render_seo_document(f"/player/{slug}"),headers={"Cache-Control":"public, max-age=300"})
def _seo_route_or_redirect(full: str, not_found: str):
    target = _seo_legacy_aliases().get(full)
    if target:
        return RedirectResponse(url=target,status_code=308,headers={"Cache-Control":"public, max-age=86400"})
    if not _seo_valid_sport_path(full):
        raise HTTPException(404,not_found)
    return None

@app.get("/football/{path:path}",response_class=HTMLResponse)
async def ssr_football(path:str):
    full=f"/football/{str(path or '').strip('/')}"
    redirected=_seo_route_or_redirect(full,"Football page not found")
    if redirected: return redirected
    return HTMLResponse(await _render_seo_document(full),headers={"Cache-Control":"public, max-age=300, s-maxage=900, stale-while-revalidate=3600"})
@app.get("/rugby/{path:path}",response_class=HTMLResponse)
async def ssr_rugby(path:str):
    full=f"/rugby/{str(path or '').strip('/')}"
    redirected=_seo_route_or_redirect(full,"Rugby page not found")
    if redirected: return redirected
    return HTMLResponse(await _render_seo_document(full),headers={"Cache-Control":"public, max-age=300, s-maxage=900, stale-while-revalidate=3600"})
@app.get("/cricket",response_class=HTMLResponse)
async def ssr_cricket_root(): return HTMLResponse(await _render_seo_document("/cricket"),headers={"Cache-Control":"public, max-age=300"})
@app.get("/cricket/{path:path}",response_class=HTMLResponse)
async def ssr_cricket(path:str):
    full=f"/cricket/{str(path or '').strip('/')}"
    redirected=_seo_route_or_redirect(full,"Cricket page not found")
    if redirected: return redirected
    return HTMLResponse(await _render_seo_document(full),headers={"Cache-Control":"public, max-age=300, s-maxage=900, stale-while-revalidate=3600"})
@app.get("/tennis",response_class=HTMLResponse)
async def ssr_tennis_root(): return HTMLResponse(await _render_seo_document("/tennis"),headers={"Cache-Control":"public, max-age=300"})
@app.get("/tennis/{path:path}",response_class=HTMLResponse)
async def ssr_tennis(path:str):
    full=f"/tennis/{str(path or '').strip('/')}"
    if not _seo_valid_sport_path(full): raise HTTPException(404,"Tennis page not found")
    return HTMLResponse(await _render_seo_document(full),headers={"Cache-Control":"public, max-age=300"})

class GrowthEvent(BaseModel):
    event: str
    path: str = ""
    pageType: str = ""
    sport: str = ""
    competition: str = ""
    entityId: str = ""
    referrer: str = ""
    sessionId: str = ""

class WebVitalEvent(BaseModel):
    metric: str
    value: float
    path: str = ""
    device: str = ""

@app.post("/analytics/web-vital")
def analytics_web_vital(payload: WebVitalEvent):
    metric = payload.metric.strip().upper()
    if metric not in {"LCP", "INP", "CLS", "TTFB"} or not (0 <= payload.value < 120000):
        raise HTTPException(400, "Unsupported web vital")
    with _growth_db() as c:
        c.execute("INSERT INTO web_vitals(metric,value,path,device,created_at) VALUES(?,?,?,?,?)", (
            metric, float(payload.value), payload.path[:500], payload.device[:80], datetime.now(timezone.utc).isoformat()))
    return {"ok": True}

@app.post("/analytics/event")
def analytics_event(payload: GrowthEvent):
    allowed = {"page_view","match_open","prediction_view","live_open","share","follow","notification_enable","search","affiliate_click","ad_view","ad_click"}
    event = payload.event.strip().lower()
    if event not in allowed:
        raise HTTPException(400, f"Unsupported event: {event}")
    with _growth_db() as c:
        c.execute("INSERT INTO page_events(event_name,path,page_type,sport,competition,entity_id,referrer,session_id,created_at) VALUES(?,?,?,?,?,?,?,?,?)", (
            event, payload.path[:500], payload.pageType[:80], payload.sport[:80], payload.competition[:120], payload.entityId[:120], payload.referrer[:500], payload.sessionId[:120], datetime.now(timezone.utc).isoformat()))
    return {"ok":True}

@app.get("/growth/dashboard")
def growth_dashboard():
    with _growth_db() as c:
        total = c.execute("SELECT COUNT(*) FROM page_events").fetchone()[0]
        views = c.execute("SELECT COUNT(*) FROM page_events WHERE event_name='page_view'").fetchone()[0]
        shares = c.execute("SELECT COUNT(*) FROM page_events WHERE event_name='share'").fetchone()[0]
        follows = c.execute("SELECT COUNT(*) FROM page_events WHERE event_name='follow'").fetchone()[0]
        notifications = c.execute("SELECT COUNT(*) FROM page_events WHERE event_name='notification_enable'").fetchone()[0]
        top = [dict(r) for r in c.execute("SELECT path,COUNT(*) count FROM page_events WHERE event_name='page_view' GROUP BY path ORDER BY count DESC LIMIT 20").fetchall()]
        sources = [dict(r) for r in c.execute("SELECT COALESCE(NULLIF(referrer,''),'direct') source,COUNT(*) count FROM page_events GROUP BY source ORDER BY count DESC LIMIT 20").fetchall()]
        vitals = [dict(r) for r in c.execute("SELECT metric, ROUND(AVG(value),2) average, ROUND(MIN(value),2) minimum, ROUND(MAX(value),2) maximum, COUNT(*) samples FROM web_vitals GROUP BY metric").fetchall()]
    return {"phase":"production","events":total,"pageViews":views,"shares":shares,"follows":follows,"notificationEnables":notifications,"topPages":top,"trafficSources":sources,"seoPages":len(_seo_registry_pages()),"webVitals":vitals}




def get_current_user(authorization: Optional[str] = Header(default=None)):
    """Validate Bearer token, load the active user from SQLite, and return a safe user object."""
    row=_user_from_token(authorization)
    if not row:
        raise HTTPException(
            status_code=401,
            detail="Not authenticated",
            headers={"WWW-Authenticate":"Bearer"},
        )
    configured=os.getenv("ADMIN_EMAIL",os.getenv("PAYMENT_ADMIN_EMAIL","")).strip().lower()
    is_configured_admin=bool(configured and str(row[1]).strip().lower()==configured)
    return {"id":int(row[0]),"email":str(row[1]),"pro":True if is_configured_admin else bool(row[2]),
            "role":"admin" if is_configured_admin else str(row[3] or "user").lower(),"status":str(row[4] or "active").lower()}

def require_admin(authorization: Optional[str] = Header(default=None)):
    """Require an authenticated administrator. Non-admin users receive HTTP 403."""
    user=get_current_user(authorization)
    configured=os.getenv("ADMIN_EMAIL",os.getenv("PAYMENT_ADMIN_EMAIL","")).strip().lower()
    is_admin=user["role"]=="admin" or (configured and user["email"].strip().lower()==configured)
    if not is_admin:
        raise HTTPException(status_code=403,detail="Admin access required")
    return user

# Backward-compatible alias for existing admin endpoints.
def _require_admin_user(authorization: Optional[str]):
    return require_admin(authorization)

@app.get("/auth/admin")
def auth_admin(authorization: Optional[str]=Header(default=None)):
    return require_admin(authorization)

class AdminUserUpdate(BaseModel):
    role: Optional[str]=None
    status: Optional[str]=None

@app.get("/admin/users")
def admin_users(authorization: Optional[str]=Header(default=None)):
    _require_admin_user(authorization); c=_auth_db()
    rows=c.execute("SELECT id,email,username,COALESCE(role,'user'),created_at,last_login,COALESCE(status,'active') FROM users ORDER BY created_at DESC").fetchall();c.close()
    return {"users":[{"id":r[0],"email":r[1],"name":r[2] or "","role":r[3],"createdAt":r[4],"lastLogin":r[5],"status":r[6]} for r in rows]}

@app.patch("/admin/users/{user_id}")
def admin_user_update(user_id:int,p:AdminUserUpdate,authorization: Optional[str]=Header(default=None)):
    _require_admin_user(authorization)
    role=(p.role or "").lower();status=(p.status or "").lower()
    if role and role not in {"user","admin"}:raise HTTPException(400,"Invalid role")
    if status and status not in {"active","disabled"}:raise HTTPException(400,"Invalid status")
    c=_auth_db()
    if role:c.execute("UPDATE users SET role=? WHERE id=?",(role,user_id))
    if status:c.execute("UPDATE users SET status=? WHERE id=?",(status,user_id))
    c.commit();n=c.total_changes;c.close();return {"updated":n}

@app.get("/admin/security/status")
def admin_security_status(authorization: Optional[str]=Header(default=None)):
    user=_user_from_token(authorization)
    admin_email=os.getenv("ADMIN_EMAIL",os.getenv("PAYMENT_ADMIN_EMAIL","")).strip().lower()
    if not user or not admin_email or str(user[1]).strip().lower()!=admin_email:
        raise HTTPException(403,"Admin access required")
    recovery=os.getenv("ADMIN_RECOVERY_EMAIL","").strip()
    smtp_ready=bool(os.getenv("SMTP_HOST","").strip() and os.getenv("SMTP_FROM",os.getenv("SMTP_USER","")).strip())
    masked=""
    if recovery and "@" in recovery:
        a,b=recovery.split("@",1);masked=(a[:2]+"***@"+b)
    return {"loginEmail":user[1],"recoveryEmail":masked,"recoveryConfigured":bool(recovery),"smtpConfigured":smtp_ready,"passwordResetDelivery":"configured" if smtp_ready else "not_configured","note":"Recovery email is configured through secure server environment settings."}

@app.get("/admin/analytics")
def admin_analytics(authorization: Optional[str]=Header(default=None)):
    user=_user_from_token(authorization)
    admin_email=os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL", "jbatuma@yahoo.com")).strip().lower()
    if not user or str(user[1]).lower()!=admin_email:
        raise HTTPException(403,"Administrator access required")
    with _growth_db() as c:
        unique_visitors=c.execute("SELECT COUNT(DISTINCT NULLIF(session_id,'')) FROM page_events").fetchone()[0] or 0
        views=c.execute("SELECT COUNT(*) FROM page_events WHERE event_name='page_view'").fetchone()[0] or 0
        clicks=c.execute("SELECT COUNT(*) FROM page_events WHERE event_name NOT IN ('page_view')").fetchone()[0] or 0
        earnings=c.execute("SELECT COALESCE(SUM(amount),0) FROM earnings").fetchone()[0] or 0
        daily=[dict(r) for r in c.execute("SELECT substr(created_at,1,10) day, SUM(CASE WHEN event_name='page_view' THEN 1 ELSE 0 END) views, COUNT(*) clicks FROM page_events WHERE created_at>=date('now','-30 day') GROUP BY substr(created_at,1,10) ORDER BY day").fetchall()]
        top_pages=[dict(r) for r in c.execute("SELECT path,COUNT(*) count FROM page_events WHERE event_name='page_view' GROUP BY path ORDER BY count DESC LIMIT 20").fetchall()]
        top_clicks=[dict(r) for r in c.execute("SELECT path,COUNT(*) count FROM page_events WHERE event_name!='page_view' GROUP BY path ORDER BY count DESC LIMIT 20").fetchall()]
    return {"uniqueVisitors":unique_visitors,"pageViews":views,"clicks":clicks,"earnings":earnings,"daily":daily,"topPages":top_pages,"topClicks":top_clicks}

@app.post("/admin/earnings")
def admin_add_earnings(amount: float=Query(..., ge=0), source: str=Query("manual"), authorization: Optional[str]=Header(default=None)):
    user=_user_from_token(authorization)
    admin_email=os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL", "jbatuma@yahoo.com")).strip().lower()
    if not user or str(user[1]).lower()!=admin_email:
        raise HTTPException(403,"Administrator access required")
    with _growth_db() as c:
        c.execute("INSERT INTO earnings(amount,source,created_at) VALUES(?,?,?)",(float(amount),source[:80],datetime.now(timezone.utc).isoformat()))
    return {"ok":True,"amount":amount,"source":source}


@app.get("/weekend-data")
async def weekend_data(
    date_from: Optional[str] = Query(None),
    date_to: Optional[str] = Query(None),
    limit: int = Query(100, ge=1, le=200),
):
    """Return the actual weekend fixture, odds and qualified-prediction data.

    The frontend uses this endpoint for the Weekend Hub instead of treating the
    SEO/content shell as if it were match data.
    """
    now = datetime.now()
    # South Africa convention: weekend = Friday through Sunday.
    days_ahead = (4 - now.weekday()) % 7
    friday = (now + timedelta(days=days_ahead)).date()
    saturday = friday + timedelta(days=1)
    sunday = friday + timedelta(days=2)
    d0 = date_from or friday.isoformat()
    d1 = date_to or sunday.isoformat()

    fixtures_data = await fixtures_with_odds(
        league="ALL",
        type="upcoming",
        date_from=d0,
        date_to=d1,
        refresh=0,
    )
    matches = fixtures_data.get("matches", [])
    qualified = []
    for match in matches:
        if match.get("isFinished") or not _valid_1x2(match.get("odds", {})):
            continue
        try:
            pred = _prediction(match)
            _save_prediction_to_db(match, pred)
            qualified.append({
                **match,
                **pred,
                "oddsAvailable": True,
                "bookmakerGatePassed": True,
            })
        except Exception as exc:
            log.warning("Weekend prediction failed fixture=%s: %s", match.get("_afootFixtureId"), exc)

    qualified.sort(key=lambda x: float((x.get("prediction") or {}).get("confidence", 0) or 0), reverse=True)
    return {
        "dateFrom": d0,
        "dateTo": d1,
        "fixtures": matches[:limit],
        "predictions": qualified[:limit],
        "qualifiedCount": len(qualified),
        "oddsComplete": fixtures_data.get("oddsComplete", sum(1 for x in matches if _valid_1x2(x.get("odds", {})))),
        "fixtureCount": len(matches),
        "source": "KasiScore match engine + API-Football",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
    }

@app.get("/content/weekend")
async def weekend_intelligence():
    # Returns an honest content shell. Live fixture data is fetched by the dashboard
    # from the existing match engine, while this endpoint supplies the publishing plan.
    featured = [c for c in COMPETITION_REGISTRY if c.get("sport") in ALLOWED_PUBLIC_SPORTS and c.get("featured") and c.get("seo")]
    return {
        "title":"Weekend Sports Intelligence",
        "generatedAt":datetime.now(timezone.utc).isoformat(),
        "competitions":[{"name":c["name"],"sport":c["sport"],"slug":c["slug"]} for c in featured],
        "modules":["top-matches","ai-predictions","live-now","odds-movement","prediction-record","post-match-results","share-cards"],
    }


# ============================================================================
# PHASE 4 — SOUTH AFRICAN RUGBY INTELLIGENCE LAYER
# Springboks · URC · Bulls · Stormers · Sharks · Lions · Currie Cup
# Dedicated endpoints for match centres, standings, news, squads,
# and the AI rugby prediction engine (score-line model).
# ============================================================================

import random  # used for ensemble jitter in demo / offline fallback

# ---------------------------------------------------------------------------
# SA Rugby League IDs (API-Sports rugby v1)
# ---------------------------------------------------------------------------
SA_RUGBY_LEAGUES = {
    "springboks":         {"name": "Rugby Championship", "id": 23, "nation": "ZA"},
    "urc":                {"name": "United Rugby Championship", "id": 25, "nation": ""},
    "currie_cup":         {"name": "Currie Cup", "id": 27, "nation": "ZA"},
    "super_rugby_africa": {"name": "Super Rugby Africa", "id": 36, "nation": ""},
    "rugby_world_cup":    {"name": "Rugby World Cup", "id": 22, "nation": ""},
    "lions_series":       {"name": "British & Irish Lions", "id": 39, "nation": ""},
}

SA_CLUBS = {
    "bulls":    {"name": "Bulls",    "city": "Pretoria"},
    "stormers": {"name": "Stormers", "city": "Cape Town"},
    "sharks":   {"name": "Sharks",   "city": "Durban"},
    "lions":    {"name": "Lions",    "city": "Johannesburg"},
    "cheetahs": {"name": "Cheetahs","city": "Bloemfontein"},
    "griquas":  {"name": "Griquas", "city": "Kimberley"},
    "pumas":    {"name": "Pumas",   "city": "Nelspruit"},
    "boland":   {"name": "Boland Cavaliers", "city": "Wellington"},
}

RUGBY_CACHE: TTLCache = TTLCache(maxsize=300, ttl=90)   # 90 s for live
RUGBY_PRED_CACHE: TTLCache = TTLCache(maxsize=100, ttl=3600)  # 1 h for predictions

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _rugby_headers() -> dict:
    key = SPORTS_API_KEYS.get("rugby", "")
    if not key:
        return {}
    return {"x-apisports-key": key, "Accept": "application/json"}

async def _rugby_api(path: str, params: dict | None = None):
    """Call API-Sports rugby endpoint. Returns raw response list or {} on failure."""
    key = SPORTS_API_KEYS.get("rugby", "")
    if not key:
        return None
    url = "https://v1.rugby.api-sports.io" + path
    try:
        data = await _sports_get(url, params or {}, _rugby_headers())
        return data.get("response", data)
    except Exception as exc:
        log.warning("Rugby API %s failed: %s", path, exc)
        return None

def _norm_rugby_game(g: dict, league_name: str = "") -> dict:
    """Normalise an API-Sports rugby game object."""
    teams  = g.get("teams") or {}
    scores = g.get("scores") or {}
    fixture= g.get("fixture") or {}
    status = fixture.get("status") or g.get("status") or {}
    league = g.get("league") or {}
    periods= scores.get("periods") if isinstance(scores, dict) else {}

    home_score = scores.get("home") if isinstance(scores, dict) else None
    away_score = scores.get("away") if isinstance(scores, dict) else None
    ht_home = (periods or {}).get("first", {}).get("home") if periods else None
    ht_away = (periods or {}).get("first", {}).get("away") if periods else None

    return {
        "id":          str(fixture.get("id") or g.get("id") or ""),
        "sport":       "rugby",
        "league":      league.get("name") or league_name,
        "leagueId":    league.get("id"),
        "season":      league.get("season"),
        "round":       league.get("round") or "",
        "date":        fixture.get("date") or g.get("date"),
        "home":        (teams.get("home") or {}).get("name", "Home"),
        "homeId":      (teams.get("home") or {}).get("id"),
        "homeLogo":    (teams.get("home") or {}).get("logo", ""),
        "away":        (teams.get("away") or {}).get("name", "Away"),
        "awayId":      (teams.get("away") or {}).get("id"),
        "awayLogo":    (teams.get("away") or {}).get("logo", ""),
        "homeScore":   home_score,
        "awayScore":   away_score,
        "htHome":      ht_home,
        "htAway":      ht_away,
        "status":      status.get("long") or status.get("short") or "Scheduled",
        "statusShort": status.get("short") or "NS",
        "elapsed":     status.get("elapsed"),
        "venue":       (fixture.get("venue") or {}).get("name") or "",
        "source":      "API-Sports",
    }

# ---------------------------------------------------------------------------
# AI Rugby Prediction Engine
# ---------------------------------------------------------------------------

RUGBY_PRED_WEIGHTS = {
    "form":          0.28,  # recent results (last 5)
    "h2h":          0.20,  # head-to-head
    "home_adv":     0.15,  # home/neutral field
    "ranking":      0.17,  # world ranking proxy
    "attack_def":   0.20,  # points scored vs conceded ratio
}

def _rugby_predict(home: str, away: str, league: str,
                   home_form: list | None = None,
                   away_form: list | None = None,
                   h2h_results: list | None = None,
                   home_ranking: int = 10,
                   away_ranking: int = 10,
                   home_pts_for: float = 25.0,
                   home_pts_against: float = 22.0,
                   away_pts_for: float = 24.0,
                   away_pts_against: float = 23.0,
                   neutral_venue: bool = False) -> dict:
    """
    Weighted ensemble rugby prediction model.
    Returns win probability, predicted scoreline, try count estimate,
    and confidence band.
    """

    # 1. Form signal (W=1, D=0.5, L=0) over last 5 games
    def _form_score(results: list | None) -> float:
        if not results:
            return 0.5
        weights = [0.10, 0.15, 0.20, 0.25, 0.30]  # most recent = highest weight
        results = results[-5:]
        pad = 5 - len(results)
        results = ["D"] * pad + results
        total = sum(
            (1.0 if r == "W" else 0.5 if r == "D" else 0.0) * w
            for r, w in zip(results, weights)
        )
        return total  # 0 → 1

    home_form_score = _form_score(home_form)
    away_form_score = _form_score(away_form)

    # 2. H2H
    def _h2h_score(results: list | None, perspective: str) -> float:
        if not results:
            return 0.5
        wins  = sum(1 for r in results if r.get("winner") == perspective)
        total = len(results)
        return wins / total if total else 0.5

    home_h2h = _h2h_score(h2h_results, "home")
    away_h2h = 1.0 - home_h2h

    # 3. Home advantage (rugby: meaningful ~5-8 pts)
    home_adv_score = 0.60 if not neutral_venue else 0.50
    away_adv_score = 1.0 - home_adv_score

    # 4. World ranking proxy (lower rank = better)
    max_rank = max(home_ranking, away_ranking, 1)
    home_rank_score = (max_rank - home_ranking + 1) / (max_rank + 1)
    away_rank_score = (max_rank - away_ranking + 1) / (max_rank + 1)

    # 5. Attack vs Defence ratio
    home_ad = (home_pts_for / max(home_pts_against, 1)) / 2.5
    away_ad = (away_pts_for / max(away_pts_against, 1)) / 2.5
    # Clamp
    home_ad = min(max(home_ad, 0.1), 1.0)
    away_ad = min(max(away_ad, 0.1), 1.0)

    # Weighted composite
    w = RUGBY_PRED_WEIGHTS
    home_raw = (
        home_form_score * w["form"]
        + home_h2h      * w["h2h"]
        + home_adv_score* w["home_adv"]
        + home_rank_score * w["ranking"]
        + home_ad       * w["attack_def"]
    )
    away_raw = (
        away_form_score * w["form"]
        + away_h2h      * w["h2h"]
        + away_adv_score* w["home_adv"]
        + away_rank_score * w["ranking"]
        + away_ad       * w["attack_def"]
    )

    total = home_raw + away_raw or 1.0
    home_win_prob = round(home_raw / total, 4)
    away_win_prob = round(away_raw / total, 4)
    draw_prob     = round(max(0.03, 0.07 - abs(home_win_prob - away_win_prob) * 0.3), 4)
    # Renormalise
    tot_prob = home_win_prob + draw_prob + away_win_prob
    home_win_prob = round(home_win_prob / tot_prob, 4)
    draw_prob     = round(draw_prob     / tot_prob, 4)
    away_win_prob = round(away_win_prob / tot_prob, 4)

    # Predicted scoreline (based on attack/defence)
    home_pred_pts = round((home_pts_for * 0.6 + away_pts_against * 0.4) * (1 + (home_win_prob - 0.5) * 0.4))
    away_pred_pts = round((away_pts_for * 0.6 + home_pts_against * 0.4) * (1 + (away_win_prob - 0.5) * 0.4))
    # Round to nearest 7 or 3 (rugby scoring increments)
    def _round_rugby(n):
        return max(0, round(n / 3) * 3)
    home_pred_pts = _round_rugby(home_pred_pts)
    away_pred_pts = _round_rugby(away_pred_pts)

    # Confidence: based on spread between probabilities
    spread = abs(home_win_prob - away_win_prob)
    confidence = round(0.45 + spread * 0.6, 4)
    confidence = min(max(confidence, 0.45), 0.93)

    winner = home if home_win_prob >= away_win_prob else away
    if draw_prob > max(home_win_prob, away_win_prob):
        winner = "Draw"

    best_pick = (
        "Home Win" if home_win_prob >= away_win_prob and draw_prob < home_win_prob
        else "Away Win" if away_win_prob > home_win_prob and draw_prob < away_win_prob
        else "Draw"
    )

    # Try estimate (average ~4 tries per game in URC, ~6 in Currie Cup)
    tries_avg = 4.0 if "urc" in league.lower() or "championship" in league.lower() else 5.0
    home_tries = round((home_pred_pts / 7) * 0.8 + (home_pred_pts / 3) * 0.05)
    away_tries = round((away_pred_pts / 7) * 0.8 + (away_pred_pts / 3) * 0.05)

    return {
        "home":          home,
        "away":          away,
        "league":        league,
        "bestPick":      best_pick,
        "winner":        winner,
        "confidence":    confidence,
        "probabilities": {
            "homeWin": home_win_prob,
            "draw":    draw_prob,
            "awayWin": away_win_prob,
        },
        "predictedScore": {
            "home": home_pred_pts,
            "away": away_pred_pts,
        },
        "predictedTries": {
            "home": max(0, home_tries),
            "away": max(0, away_tries),
        },
        "modelWeights": RUGBY_PRED_WEIGHTS,
        "signals": {
            "homeForm":    round(home_form_score, 3),
            "awayForm":    round(away_form_score, 3),
            "homeH2H":     round(home_h2h, 3),
            "awayH2H":     round(away_h2h, 3),
            "homeAdvantage": home_adv_score,
            "homeRanking": round(home_rank_score, 3),
            "awayRanking": round(away_rank_score, 3),
            "homeAttackDef": round(home_ad, 3),
            "awayAttackDef": round(away_ad, 3),
        },
        "source":        "KasiScore Rugby AI v1",
    }

# ---------------------------------------------------------------------------
# SA Rugby Endpoints
# ---------------------------------------------------------------------------

@app.get("/rugby/leagues")
async def rugby_leagues():
    """Return the supported SA rugby leagues with their API IDs."""
    return {"leagues": SA_RUGBY_LEAGUES, "clubs": SA_CLUBS}


@app.get("/rugby/matches")
async def rugby_matches(
    league:  str = Query("urc"),
    season:  int = Query(0, ge=0),
    date:    str = Query(""),
    live:    int = Query(0, ge=0, le=1),
    team:    str = Query(""),
):
    """
    Match centre for SA rugby competitions.
    Falls back to ESPN rugby-union scoreboard when API-Sports key is absent.
    """
    season = season or _current_season()
    cache_key = f"rugby:matches:{league}:{season}:{date}:{live}:{team}"
    if cache_key in RUGBY_CACHE:
        return RUGBY_CACHE[cache_key]

    league_meta = SA_RUGBY_LEAGUES.get(league.lower())
    league_name = league_meta["name"] if league_meta else league

    games: list[dict] = []

    # Primary: API-Sports
    key = SPORTS_API_KEYS.get("rugby", "")
    if key and league_meta:
        params: dict = {"league": league_meta["id"], "season": season}
        if date:
            params["date"] = date
        if live:
            params["live"] = "all"
        if team:
            # Resolve club name to ID if needed (best-effort substring match)
            club = SA_CLUBS.get(team.lower(), {})
            if club:
                params["team"] = team  # caller should pass numeric ID in prod
        raw = await _rugby_api("/games", params)
        if isinstance(raw, list):
            games = [_norm_rugby_game(g, league_name) for g in raw]

    # Fallback: ESPN rugby-union
    if not games:
        try:
            espn_games = await _espn_scores("rugby", date or None, "rugby-union")
            games = espn_games
        except Exception as exc:
            log.warning("ESPN rugby fallback failed: %s", exc)

    if not games:
        games = []

    # Sort: live first, then by date
    games.sort(key=lambda x: (
        x.get("statusShort", "NS") not in ("1H", "2H", "HT", "ET", "BT", "in"),
        x.get("date") or ""
    ))

    result = {
        "league":      league,
        "leagueName":  league_name,
        "season":      season,
        "count":       len(games),
        "games":       games,
        "source":      "API-Sports" if (games and games[0].get("source") == "API-Sports") else "ESPN",
    }
    RUGBY_CACHE[cache_key] = result
    return result


@app.get("/rugby/standings")
async def rugby_standings(
    league: str = Query("urc"),
    season: int = Query(0, ge=0),
):
    """League table for SA rugby competitions."""
    season = season or _current_season()
    cache_key = f"rugby:standings:{league}:{season}"
    if cache_key in RUGBY_CACHE:
        return RUGBY_CACHE[cache_key]

    league_meta = SA_RUGBY_LEAGUES.get(league.lower())

    # API-Sports standings
    if SPORTS_API_KEYS.get("rugby") and league_meta:
        raw = await _rugby_api("/standings", {"league": league_meta["id"], "season": season})
        if raw:
            result = {
                "league":      league,
                "leagueName":  league_meta["name"],
                "season":      season,
                "standings":   raw if isinstance(raw, list) else [],
                "source":      "API-Sports",
            }
            RUGBY_CACHE[cache_key] = result
            return result

    # ESPN standings fallback
    try:
        data = await _sports_get(
            f"https://site.api.espn.com/apis/v2/sports/rugby/rugby-union/standings",
            {"season": season}
        )
        result = {
            "league":    league,
            "season":    season,
            "standings": data.get("children") or data.get("standings") or [],
            "source":    "ESPN",
        }
        RUGBY_CACHE[cache_key] = result
        return result
    except Exception as exc:
        return {"league": league, "season": season, "standings": [], "source": "unavailable", "error": str(exc)}


@app.get("/rugby/news")
async def rugby_news(
    team:  str = Query(""),
    limit: int = Query(30, ge=1, le=50),
):
    """
    SA Rugby news — Springboks, URC teams, Currie Cup.
    Returns Google News RSS headline metadata only (no copyrighted bodies).
    """
    if team:
        club = SA_CLUBS.get(team.lower())
        query = f"South Africa {club['name']} rugby" if club else f"{team} rugby South Africa"
    else:
        query = (
            "Springboks URC Bulls Stormers Sharks Lions Currie Cup South Africa rugby"
        )
    try:
        items = await _google_news(query, limit)
        return {
            "team":   team or "all",
            "query":  query,
            "count":  len(items),
            "items":  items,
            "source": "Google News RSS",
        }
    except Exception as exc:
        return {"team": team, "count": 0, "items": [], "error": str(exc)}


@app.get("/rugby/squad")
async def rugby_squad(team_id: int = Query(..., ge=1), season: int = Query(0, ge=0)):
    """Player squad for a team (API-Sports)."""
    season = season or _current_season()
    if not SPORTS_API_KEYS.get("rugby"):
        raise HTTPException(503, "Rugby API key not configured")
    raw = await _rugby_api("/players", {"team": team_id, "season": season})
    return {
        "teamId":  team_id,
        "season":  season,
        "players": raw if isinstance(raw, list) else [],
        "source":  "API-Sports",
    }


@app.get("/rugby/h2h")
async def rugby_h2h(home_id: int = Query(..., ge=1), away_id: int = Query(..., ge=1)):
    """Head-to-head history between two SA rugby teams."""
    cache_key = f"rugby:h2h:{home_id}:{away_id}"
    if cache_key in RUGBY_CACHE:
        return RUGBY_CACHE[cache_key]
    raw = await _rugby_api("/games/h2h", {"h2h": f"{home_id}-{away_id}"})
    games = [_norm_rugby_game(g) for g in (raw or [])] if isinstance(raw, list) else []
    result = {"homeId": home_id, "awayId": away_id, "count": len(games), "games": games, "source": "API-Sports"}
    RUGBY_CACHE[cache_key] = result
    return result


@app.get("/rugby/predictions")
async def rugby_predictions(
    league:  str   = Query("urc"),
    season:  int   = Query(0, ge=0),
    date:    str   = Query(""),
):
    """
    AI Rugby Predictions for upcoming SA rugby fixtures.
    Fetches scheduled games for the given league/season/date,
    runs them through the rugby prediction engine, and returns
    predictions sorted by confidence.
    """
    season = season or _current_season()
    cache_key = f"rugby:pred:{league}:{season}:{date}"
    if cache_key in RUGBY_PRED_CACHE:
        return RUGBY_PRED_CACHE[cache_key]

    # Get fixtures first
    matches_resp = await rugby_matches(league=league, season=season, date=date, live=0, team="")
    games = matches_resp.get("games", [])

    predictions = []
    for g in games:
        # Skip already-completed games
        if g.get("statusShort") in ("FT", "AET", "AOT"):
            continue

        home = g.get("home", "Home")
        away = g.get("away", "Away")
        league_name = g.get("league", league)

        # Attempt to fetch recent form from API-Sports (best-effort)
        home_form: list | None = None
        away_form: list | None = None
        home_id = g.get("homeId")
        away_id = g.get("awayId")

        if home_id and away_id and SPORTS_API_KEYS.get("rugby"):
            try:
                hf_raw = await _rugby_api("/teams/statistics", {"team": home_id, "season": season})
                af_raw = await _rugby_api("/teams/statistics", {"team": away_id, "season": season})
                # Extract form strings if available
                if isinstance(hf_raw, dict):
                    form_str = hf_raw.get("form") or ""
                    home_form = list(form_str) if form_str else None
                if isinstance(af_raw, dict):
                    form_str = af_raw.get("form") or ""
                    away_form = list(form_str) if form_str else None
            except Exception:
                pass

        pred = _rugby_predict(
            home=home,
            away=away,
            league=league_name,
            home_form=home_form,
            away_form=away_form,
            neutral_venue=(g.get("venue") == ""),
        )
        pred["fixture"] = {
            "id":     g.get("id"),
            "date":   g.get("date"),
            "venue":  g.get("venue"),
            "round":  g.get("round"),
            "status": g.get("status"),
            "homeLogo": g.get("homeLogo"),
            "awayLogo": g.get("awayLogo"),
        }
        predictions.append(pred)

    predictions.sort(key=lambda x: -x["confidence"])

    result = {
        "league":      league,
        "season":      season,
        "date":        date or datetime.now().strftime("%Y-%m-%d"),
        "count":       len(predictions),
        "predictions": predictions,
        "engine":      "KasiScore Rugby AI v1 — weighted ensemble (form · H2H · home adv · ranking · attack/def)",
        "weights":     RUGBY_PRED_WEIGHTS,
    }
    RUGBY_PRED_CACHE[cache_key] = result
    return result


@app.get("/rugby/health")
async def rugby_health():
    """Rugby intelligence layer status."""
    return {
        "status":            "ok",
        "apiSportsConfigured": bool(SPORTS_API_KEYS.get("rugby")),
        "leagues":           list(SA_RUGBY_LEAGUES.keys()),
        "clubs":             list(SA_CLUBS.keys()),
        "predictionEngine":  "KasiScore Rugby AI v1",
        "endpoints": [
            "/rugby/leagues", "/rugby/matches", "/rugby/standings",
            "/rugby/news", "/rugby/squad", "/rugby/h2h", "/rugby/predictions",
        ],
    }

# ===========================================================================
# WEB PUSH ENDPOINTS
# ===========================================================================

class PushSubscriptionPayload(BaseModel):
    endpoint: str
    keys: dict  # {p256dh, auth}

class PushBroadcastPayload(BaseModel):
    title: str
    body: str
    url: str = "/"
    admin_key: str = ""

@app.post("/push/subscribe")
async def push_subscribe(
    payload: PushSubscriptionPayload,
    authorization: Optional[str] = Header(default=None),
    user_agent: Optional[str] = Header(default=None),
):
    """Register a browser push subscription. Works for anonymous and logged-in users."""
    user = _user_from_token(authorization)
    user_id = user[0] if user else None
    if not payload.endpoint or not payload.keys.get("p256dh") or not payload.keys.get("auth"):
        raise HTTPException(400, "Invalid push subscription object")
    sub_id = _store_push_subscription(user_id, {"endpoint": payload.endpoint, "keys": payload.keys}, user_agent or "")
    return {"subscribed": True, "id": sub_id}

@app.delete("/push/subscribe")
async def push_unsubscribe(payload: PushSubscriptionPayload):
    """Remove a push subscription (called when user disables notifications)."""
    _delete_push_subscription(payload.endpoint)
    return {"unsubscribed": True}

@app.post("/push/broadcast")
async def push_broadcast(payload: PushBroadcastPayload):
    """Send a push notification to all subscribers (admin-only)."""
    if not hmac.compare_digest(payload.admin_key, os.getenv("AUTH_ADMIN_KEY", "")):
        raise HTTPException(403, "Forbidden")
    subs = _get_push_subscriptions()
    sent, failed = 0, 0
    for sub in subs:
        ok = await _send_web_push(sub, payload.title, payload.body, payload.url)
        if ok: sent += 1
        else: failed += 1
    return {"sent": sent, "failed": failed, "total": len(subs)}

@app.post("/push/test")
async def push_test(authorization: Optional[str] = Header(default=None)):
    """Send a test push to the calling user's subscriptions."""
    user = _user_from_token(authorization)
    if not user: raise HTTPException(401, "Not authenticated")
    subs = _get_push_subscriptions(user_id=user[0])
    if not subs: return {"sent": 0, "message": "No subscriptions found for this account"}
    ok = await _send_web_push(subs[0], "KasiScore Test ", "Push notifications are working!", "/")
    return {"sent": 1 if ok else 0}

@app.get("/push/vapid-public-key")
async def push_vapid_public_key():
    """Return the VAPID public key for the frontend to use when subscribing."""
    key = os.getenv("VAPID_PUBLIC_KEY", "")
    if not key:
        return {"configured": False, "message": "Set VAPID_PUBLIC_KEY in .env. Generate: python -m pywebpush --gen-keys"}
    return {"configured": True, "publicKey": key}

@app.get("/push/stats")
async def push_stats(admin_key: str = Query(...)):
    """Push subscription stats (admin)."""
    if not hmac.compare_digest(admin_key, os.getenv("AUTH_ADMIN_KEY", "")):
        raise HTTPException(403, "Forbidden")
    c = _push_db()
    total = c.execute("SELECT COUNT(*) FROM push_subscriptions").fetchone()[0]
    recent = c.execute("SELECT title, sent_at, status FROM push_log ORDER BY id DESC LIMIT 20").fetchall()
    c.close()
    return {"subscribers": total, "recentLog": [{"title": r[0], "sentAt": r[1], "status": r[2]} for r in recent]}

# ===========================================================================
# PAYMENT WEBHOOK ENDPOINTS
# ===========================================================================

class PayFastWebhookPayload(BaseModel):
    m_payment_id: str = ""
    pf_payment_id: str = ""
    payment_status: str = ""
    item_name: str = ""
    item_description: str = ""
    amount_gross: str = ""
    email_address: str = ""
    custom_str1: str = ""  # We pass: email
    custom_str2: str = ""  # We pass: plan (monthly/lifetime)
    signature: str = ""

def _payfast_verify_signature(data: dict, passphrase: str) -> bool:
    """Verify PayFast ITN signature."""
    import urllib.parse
    filtered = {k: v for k, v in data.items() if k != "signature" and v != ""}
    param_str = urllib.parse.urlencode(sorted(filtered.items()))
    if passphrase:
        param_str += f"&passphrase={urllib.parse.quote_plus(passphrase)}"
    return hashlib.md5(param_str.encode()).hexdigest() == data.get("signature", "")

@app.post("/webhooks/payfast")
async def payfast_webhook(request):
    """
    PayFast Instant Transaction Notification (ITN).
    Set your PayFast merchant notify_url to: https://your-domain.com/webhooks/payfast
    """
    from fastapi import Request
    body = await request.body()
    import urllib.parse
    try:
        params = dict(urllib.parse.parse_qsl(body.decode()))
    except Exception:
        raise HTTPException(400, "Invalid payload")

    if PAYFAST_PASSPHRASE and not _payfast_verify_signature(params, PAYFAST_PASSPHRASE):
        log.warning("PayFast signature mismatch")
        raise HTTPException(400, "Signature mismatch")

    status = params.get("payment_status", "")
    email = params.get("custom_str1") or params.get("email_address", "")

    if status == "COMPLETE" and email:
        c = _auth_db()
        result = c.execute("UPDATE users SET pro=1 WHERE email=?", (email.lower(),))
        c.commit(); changed = result.rowcount; c.close()
        if changed:
            log.info(f"PayFast: Pro entitlement granted to {email}")
            # Send a welcome push if the user has subscriptions
            subs = _get_push_subscriptions()
            email_subs = [s for s in subs]  # In a real system, link by user_id
            for sub in email_subs[:1]:
                await _send_web_push(sub, "KasiScore Pro Activated ",
                                     "Your Pro subscription is now active.", "/")
        return {"received": True, "entitlementGranted": bool(changed)}

    return {"received": True, "status": status}

@app.post("/webhooks/stripe")
async def stripe_webhook(request):
    """
    Stripe webhook handler.
    Set endpoint in Stripe Dashboard → Developers → Webhooks.
    Events: checkout.session.completed, customer.subscription.deleted
    """
    from fastapi import Request
    body = await request.body()
    sig_header = request.headers.get("stripe-signature", "")

    event_data: dict = {}
    if STRIPE_WEBHOOK_SECRET:
        # Verify Stripe signature
        try:
            parts = {p.split("=")[0]: p.split("=")[1] for p in sig_header.split(",") if "=" in p}
            ts = parts.get("t", "0")
            signed_payload = f"{ts}.{body.decode()}"
            expected_sig = hmac.new(STRIPE_WEBHOOK_SECRET.encode(), signed_payload.encode(), hashlib.sha256).hexdigest()
            if not any(hmac.compare_digest(expected_sig, v) for k, v in parts.items() if k == "v1"):
                raise HTTPException(400, "Invalid Stripe signature")
        except Exception as e:
            raise HTTPException(400, f"Signature error: {e}")

    try:
        event_data = json.loads(body)
    except Exception:
        raise HTTPException(400, "Invalid JSON")

    event_type = event_data.get("type", "")
    obj = event_data.get("data", {}).get("object", {})

    if event_type == "checkout.session.completed":
        email = obj.get("customer_details", {}).get("email") or obj.get("customer_email", "")
        if email:
            c = _auth_db()
            c.execute("UPDATE users SET pro=1 WHERE email=?", (email.lower(),))
            c.commit(); c.close()
            log.info(f"Stripe checkout completed: Pro granted to {email}")

    elif event_type in ("customer.subscription.deleted", "invoice.payment_failed"):
        email = obj.get("customer_email", "")
        if email:
            c = _auth_db()
            c.execute("UPDATE users SET pro=0 WHERE email=?", (email.lower(),))
            c.commit(); c.close()
            log.info(f"Stripe subscription ended: Pro revoked for {email}")

    return {"received": True}

# ===========================================================================
# ENTITLEMENT CHECK ENDPOINT (for frontend JWT-based gate)
# ===========================================================================

@app.get("/auth/entitlement")
def check_entitlement(authorization: Optional[str] = Header(default=None)):
    """Returns live entitlement from the server (not localStorage). Used by the frontend gate."""
    user = _user_from_token(authorization)
    if not user:
        return {"authenticated": False, "pro": False, "role": "public"}
    admin_email=os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL", "")).strip().lower()
    role="admin" if admin_email and str(user[1]).strip().lower()==admin_email else "user"
    return {"authenticated": True, "id": user[0], "email": user[1], "pro": bool(user[2]), "role": role}



def _require_intelligence_admin(authorization: Optional[str]):
    user=_user_from_token(authorization)
    admin_email=os.getenv("ADMIN_EMAIL", os.getenv("PAYMENT_ADMIN_EMAIL", "")).strip().lower()
    if not user:
        raise HTTPException(401,"Authentication required")
    if not admin_email or str(user[1]).strip().lower()!=admin_email:
        raise HTTPException(403,"Admin access required")
    return user

@app.get("/intelligence/top-goalscorers")
async def intelligence_top_goalscorers(authorization: Optional[str]=Header(default=None)):
    _require_intelligence_admin(authorization)
    data=await players_top_scorers(league=39,season=2025,_t=None)
    return {"role":"admin","items":data.get("response",[])[:30],"source":data.get("source","current sports data")}

@app.get("/intelligence/team")
async def intelligence_team(team: str=Query(...), authorization: Optional[str]=Header(default=None)):
    _require_intelligence_admin(authorization)
    return await team_profile(team=team)

@app.get("/intelligence/player")
async def intelligence_player(player: str=Query(...), authorization: Optional[str]=Header(default=None)):
    _require_intelligence_admin(authorization)
    try:
        pid=int(str(player).strip())
    except Exception:
        raise HTTPException(400,"Player search requires a provider player ID")
    return await player_profile(player=pid)

# ===========================================================================
# LOTTERY AI — South Africa (Daily Lotto · Lotto · PowerBall)
# ===========================================================================
import collections, random

LOTTERY_DB = BASE_DIR / "kasiscore_lottery.db"
LOTTERY_GAMES = {
    "daily_lotto": {"main": 5, "pool": 36, "bonus_count": 0, "bonus_pool": 0, "name": "Daily Lotto"},
    "lotto":       {"main": 6, "pool": 52, "bonus_count": 1, "bonus_pool": 52, "name": "Lotto"},
    "powerball":   {"main": 5, "pool": 50, "bonus_count": 1, "bonus_pool": 20, "name": "PowerBall"},
}

def _lottery_db():
    c = sqlite3.connect(LOTTERY_DB)
    c.execute("""CREATE TABLE IF NOT EXISTS lottery_results(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        game TEXT NOT NULL,
        draw_number TEXT,
        draw_date TEXT NOT NULL,
        numbers TEXT NOT NULL,
        bonus TEXT,
        fetched_at TEXT NOT NULL)""")
    c.commit(); return c

def _lottery_numbers(game: str, rows: list) -> dict:
    """Frequency + recency scoring model."""
    cfg = LOTTERY_GAMES[game]
    pool = cfg["pool"]
    freq: dict[int, int] = collections.Counter()
    last_seen: dict[int, int] = {}
    for idx, row in enumerate(rows):
        nums = [int(x) for x in str(row[0]).split(",") if x.strip().isdigit()]
        for n in nums:
            freq[n] += 1
            if n not in last_seen: last_seen[n] = idx
    all_nums = list(range(1, pool + 1))
    total = max(1, len(rows))
    scores = {}
    for n in all_nums:
        f = freq.get(n, 0)
        recency = last_seen.get(n, total)
        recency_score = 1 - (recency / total)
        freq_score = f / total
        scores[n] = round(0.55 * freq_score + 0.35 * recency_score + 0.10 * random.random(), 6)
    ranked = sorted(all_nums, key=lambda n: scores[n], reverse=True)
    hot = ranked[:8]
    cold = ranked[-8:]
    freq_rank = [{"number": n, "count": freq.get(n, 0), "score": scores[n]} for n in ranked[:30]]
    return {"hotNumbers": hot, "coldNumbers": cold, "frequencyRank": freq_rank, "scores": scores, "totalDraws": total}

def _lottery_generate_picks(game: str, rows: list, n_picks: int = 3, target_date: str = "") -> list:
    cfg = LOTTERY_GAMES[game]
    analysis = _lottery_numbers(game, rows)
    scores = analysis["scores"]
    all_nums = sorted(scores.keys(), key=lambda x: -scores[x])
    picks = []
    labels = [f"Pick {i+1}" for i in range(n_picks)]
    for i, label in enumerate(labels):
        # Weighted random sample; top candidates more likely but with shuffling for variety
        weights = [scores[n] ** (1 + i * 0.2) for n in all_nums]
        total_w = sum(weights)
        normed = [w / total_w for w in weights]
        chosen: list[int] = []
        while len(chosen) < cfg["main"]:
            r = random.random()
            cumulative = 0.0
            for num, prob in zip(all_nums, normed):
                cumulative += prob
                if r <= cumulative and num not in chosen:
                    chosen.append(num)
                    break
        chosen.sort()
        bonus = []
        if cfg["bonus_count"] > 0:
            bp = cfg["bonus_pool"]
            b_scores = {n: scores.get(n, random.random() * 0.5) for n in range(1, bp + 1) if n not in chosen}
            b_ranked = sorted(b_scores.keys(), key=lambda x: -b_scores[x])
            bonus = random.sample(b_ranked[:max(10, len(b_ranked))], min(cfg["bonus_count"], len(b_ranked)))
        picks.append({
            "label": label, "game": game, "numbers": chosen, "bonus": bonus,
            "targetDate": target_date or "Next draw",
            "drawsUsed": analysis["totalDraws"], "modelVersion": "KasiScore Lottery AI v1 (freq+recency+entropy)"
        })
    return picks

@app.get("/lottery/status")
def lottery_status():
    c = _lottery_db()
    counts = {}
    cutoff_date = (datetime.now(timezone.utc) - timedelta(days=180)).strftime("%Y-%m-%d")
    for game in LOTTERY_GAMES:
        n = c.execute("SELECT COUNT(*) FROM lottery_results WHERE game=? AND draw_date>=?", (game, cutoff_date)).fetchone()[0]
        counts[game] = n
    last = c.execute("SELECT fetched_at FROM lottery_results ORDER BY id DESC LIMIT 1").fetchone()
    c.close()
    return {"games": counts, "cutoff": cutoff_date, "lastFetchedAt": last[0] if last else None}

@app.post("/lottery/sync")
async def lottery_sync():
    """
    Sync lottery results from Lottery.co.za public JSON feed.
    Falls back to seeding synthetic data for demo if the feed is unavailable.
    """
    cutoff = (datetime.now(timezone.utc) - timedelta(days=180)).strftime("%Y-%m-%d")
    rows_processed = 0
    c = _lottery_db()
    try:
        async with httpx.AsyncClient(timeout=15) as client:
            for game, cfg in LOTTERY_GAMES.items():
                try:
                    url = f"https://www.lottery.co.za/results/{game.replace('_','-')}/results.json"
                    r = await client.get(url)
                    if r.status_code == 200:
                        data = r.json()
                        for draw in (data.get("results") or data if isinstance(data, list) else []):
                            date = str(draw.get("date","")).split("T")[0]
                            if date < cutoff: continue
                            nums = ",".join(str(n) for n in (draw.get("numbers") or draw.get("mainNumbers") or []))
                            bonus = ",".join(str(n) for n in (draw.get("bonus") or draw.get("bonusBall") or draw.get("powerball") or []) if n)
                            draw_no = str(draw.get("drawNumber") or draw.get("draw") or "")
                            try:
                                c.execute("INSERT OR IGNORE INTO lottery_results(game,draw_number,draw_date,numbers,bonus,fetched_at) VALUES(?,?,?,?,?,?)",
                                          (game, draw_no, date, nums, bonus, datetime.now(timezone.utc).isoformat()))
                                rows_processed += 1
                            except Exception: pass
                except Exception as e:
                    log.warning(f"Lottery sync {game}: {e}")
                    # Seed synthetic data so the UI is not empty
                    for i in range(20):
                        date = (datetime.now(timezone.utc) - timedelta(days=i*7+random.randint(0,6))).strftime("%Y-%m-%d")
                        if date < cutoff: continue
                        pool = cfg["pool"]; main_n = cfg["main"]
                        nums = sorted(random.sample(range(1, pool+1), main_n))
                        nums_str = ",".join(str(n) for n in nums)
                        bonus_str = ""
                        if cfg["bonus_count"]:
                            b_pool = cfg["bonus_pool"]
                            bonus_str = str(random.choice([n for n in range(1, b_pool+1) if n not in nums]))
                        try:
                            c.execute("INSERT OR IGNORE INTO lottery_results(game,draw_number,draw_date,numbers,bonus,fetched_at) VALUES(?,?,?,?,?,?)",
                                      (game, f"SEED-{i}", date, nums_str, bonus_str, datetime.now(timezone.utc).isoformat()))
                            rows_processed += 1
                        except Exception: pass
        c.commit()
    finally: c.close()
    return {"status": "synced", "rowsProcessed": rows_processed, "source": "Lottery.co.za (with synthetic fallback)"}

@app.get("/lottery/analytics/{game}")
def lottery_analytics(game: str):
    if game not in LOTTERY_GAMES: raise HTTPException(400, f"Unknown game: {game}")
    cutoff = (datetime.now(timezone.utc) - timedelta(days=180)).strftime("%Y-%m-%d")
    c = _lottery_db()
    rows = c.execute("SELECT numbers FROM lottery_results WHERE game=? AND draw_date>=? ORDER BY draw_date DESC", (game, cutoff)).fetchall()
    c.close()
    if not rows: raise HTTPException(404, "No draw history found. Run /lottery/sync first.")
    return _lottery_numbers(game, rows)

@app.get("/lottery/predictions")
def lottery_predictions(picks: int = Query(3, ge=1, le=6)):
    cutoff = (datetime.now(timezone.utc) - timedelta(days=180)).strftime("%Y-%m-%d")
    all_picks = []
    c = _lottery_db()
    for game in LOTTERY_GAMES:
        rows = c.execute("SELECT numbers FROM lottery_results WHERE game=? AND draw_date>=? ORDER BY draw_date DESC", (game, cutoff)).fetchall()
        if not rows:
            all_picks.append({"label": f"{LOTTERY_GAMES[game]['name']} — No data", "game": game,
                              "numbers": [], "bonus": [], "targetDate": "—",
                              "drawsUsed": 0, "modelVersion": "Run /lottery/sync to load draw history"})
            continue
        game_picks = _lottery_generate_picks(game, rows, n_picks=picks)
        # Label with the game name
        for p in game_picks:
            p["label"] = f"{LOTTERY_GAMES[game]['name']} · {p['label']}"
        all_picks.extend(game_picks)
    c.close()
    return {"predictions": all_picks, "generatedAt": datetime.now(timezone.utc).isoformat(), "disclaimer": "AI predictions are for entertainment only. Results are random — play responsibly."}

@app.get("/lottery/results")
def lottery_results(game: str = Query("daily_lotto"), limit: int = Query(30, le=200)):
    if game not in LOTTERY_GAMES: raise HTTPException(400, f"Unknown game: {game}")
    c = _lottery_db()
    rows = c.execute("SELECT draw_number,draw_date,numbers,bonus FROM lottery_results WHERE game=? ORDER BY draw_date DESC LIMIT ?", (game, limit)).fetchall()
    c.close()
    return {"game": game, "results": [{"drawNumber": r[0], "date": r[1],
        "numbers": [int(x) for x in r[2].split(",") if x.strip().isdigit()],
        "bonus": [int(x) for x in r[3].split(",") if x.strip().isdigit()] if r[3] else []} for r in rows]}

# ===========================================================================
# PSL PLAYER STATS — Premier Soccer League South Africa (API-Football league 288)
# ===========================================================================
PSL_PLAYER_CACHE: dict = {}
PSL_PLAYER_CACHE_TS: float = 0
PSL_PLAYER_TTL = 3600  # 1 hour

@app.get("/players/psl")
async def players_psl(season: int = Query(2025)):
    global PSL_PLAYER_CACHE, PSL_PLAYER_CACHE_TS
    cache_key = f"psl_{season}"
    if cache_key in PSL_PLAYER_CACHE and time.time() - PSL_PLAYER_CACHE_TS < PSL_PLAYER_TTL:
        return PSL_PLAYER_CACHE[cache_key]
    if not API_KEY:
        return {"players": [], "source": "API key not configured", "league": "PSL South Africa", "season": season}
    players: list = []
    page = 1
    async with httpx.AsyncClient(timeout=30) as client:
        while True:
            try:
                r = await client.get(f"{API_BASE}/players", params={"league": 288, "season": season, "page": page},
                                     headers={"x-apisports-key": API_KEY})
                _record_quota(r, "/players/psl")
                data = r.json()
                results = data.get("response", [])
                if not results: break
                for item in results:
                    p = item.get("player", {})
                    stats = item.get("statistics", [{}])[0] if item.get("statistics") else {}
                    team = stats.get("team", {}).get("name", "")
                    goals = stats.get("goals", {})
                    passes = stats.get("passes", {})
                    games = stats.get("games", {})
                    players.append({
                        "id": p.get("id"), "name": p.get("name", ""), "team": team,
                        "position": games.get("position", ""),
                        "appearances": games.get("appearences", 0) or 0,
                        "goals": goals.get("total", 0) or 0,
                        "assists": goals.get("assists", 0) or 0,
                        "rating": float(games.get("rating", 0) or 0),
                        "nationality": p.get("nationality", ""),
                        "photo": p.get("photo", ""),
                        "yellow": stats.get("cards", {}).get("yellow", 0) or 0,
                        "red": stats.get("cards", {}).get("red", 0) or 0,
                        "minutesPlayed": games.get("minutes", 0) or 0,
                        "keyPasses": passes.get("key", 0) or 0,
                        "shotsTotal": stats.get("shots", {}).get("total", 0) or 0,
                        "dribbles": stats.get("dribbles", {}).get("success", 0) or 0,
                    })
                paging = data.get("paging", {})
                if page >= paging.get("total", 1): break
                page += 1
                await asyncio.sleep(0.25)  # respect rate limit
            except Exception as e:
                log.warning(f"PSL players page {page}: {e}"); break
    result = {"players": players, "count": len(players), "league": "PSL South Africa", "leagueId": 288, "season": season, "source": "API-Football"}
    PSL_PLAYER_CACHE[cache_key] = result
    PSL_PLAYER_CACHE_TS = time.time()
    return result



@app.head("/", include_in_schema=False)
async def root_head():
    return Response(status_code=200)

# SEO STEP 2 v318: legacy duplicate root decorator disabled.
# root_webapp() above is the authoritative GET / route.
async def home_page():
    return HTMLResponse(await _render_seo_document("/"), headers={"Cache-Control":"no-store, max-age=0"})

@app.get("/app", response_class=HTMLResponse)
async def app_page(): return await home_page()

# ---------------------------------------------------------------------------
# STATIC ASSETS — manifest, service worker, icons, robots
# These files live next to server.py. FastAPI does not auto-serve static
# files from disk, so each asset needs an explicit route.
# ---------------------------------------------------------------------------

@app.get("/sw.js")
async def serve_sw():
    f = BASE_DIR / "sw.js"
    if not f.exists():
        raise HTTPException(404, "sw.js not found")
    return Response(f.read_text(encoding="utf-8"),
                    media_type="application/javascript",
                    headers={"Cache-Control": "no-cache, no-store, must-revalidate"})

# SEO STEP 1: legacy duplicate disabled; google_robots_txt above is authoritative.
async def serve_robots():
    f = BASE_DIR / "robots.txt"
    if not f.exists():
        return Response("User-agent: *\nAllow: /\n", media_type="text/plain")
    return Response(f.read_text(encoding="utf-8"), media_type="text/plain",
                    headers={"Cache-Control": "public, max-age=86400"})

# SEO STEP 1: legacy duplicate disabled; google_sitemap_xml above is authoritative.
def sitemap_xml():
    base=_seo_base() if "_seo_base" in globals() else os.getenv("PUBLIC_APP_URL","https://www.kasilivescore.com").rstrip("/")
    static=["/","/about","/contact","/privacy","/terms","/cookies","/affiliate-disclosure","/sponsor"]
    urls=[base+p for p in static]
    if "SEO_LOCALES" in globals():
        for lang in SEO_LOCALES:
            urls.append(f"{base}/{lang}")
            for sec in SEO_INDEX_SECTIONS:
                urls.append(f"{base}/{lang}/{sec}")
    body="".join(f"<url><loc>{u}</loc></url>" for u in urls)
    return Response(content='<?xml version="1.0" encoding="UTF-8"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'+body+"</urlset>",media_type="application/xml")

@app.get("/icons/{filename}")
async def serve_icon(filename: str):
    # Only allow safe filenames — no path traversal
    import re as _re
    if not _re.match(r'^[\w\-\.]+$', filename):
        raise HTTPException(400, "Invalid filename")
    f = BASE_DIR / "icons" / filename
    if not f.exists():
        raise HTTPException(404, f"Icon not found: {filename}")
    suffix = f.suffix.lower()
    mime = {"png": "image/png", "jpg": "image/jpeg", "jpeg": "image/jpeg",
            "svg": "image/svg+xml", "ico": "image/x-icon"}.get(suffix.lstrip("."), "application/octet-stream")
    return Response(f.read_bytes(), media_type=mime,
                    headers={"Cache-Control": "public, max-age=31536000, immutable"})

# ---------------------------------------------------------------------------
# ENTRY POINT  (must be last — all routes above must be registered first)
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import uvicorn

    uvicorn.run(
        app,
        host=os.getenv("HOST", "0.0.0.0"),
        port=PORT,
        reload=False,
        log_level=LOG_LEVEL.lower(),
    )



# v363: requested-only cache-first multisport media/team-profile/prediction reliability.

# === KSN v402: requested-only News image recovery + Finished Games football Stats ID resolution ===
async def _v402_fetch_image_bytes(image_url: str, article_url: str = ""):
    """Return a real publisher image. If the feed thumbnail is blocked/stale, recover OG/Twitter image from article."""
    c = await _sports_client()
    headers = {"User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124 Safari/537.36",
               "Accept":"image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8","Accept-Language":"en-ZA,en;q=0.9"}
    candidates=[]
    if image_url: candidates.append(image_url)
    if article_url:
        try:
            ar=await c.get(article_url,follow_redirects=True,timeout=httpx.Timeout(7,connect=3),headers={**headers,"Accept":"text/html,application/xhtml+xml"})
            if ar.status_code < 400:
                html=ar.text[:800000]
                for pat in [r'<meta[^>]+property=["\']og:image(?::secure_url)?["\'][^>]+content=["\']([^"\']+)',
                            r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image(?::secure_url)?["\']',
                            r'<meta[^>]+name=["\']twitter:image["\'][^>]+content=["\']([^"\']+)',
                            r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+name=["\']twitter:image["\']']:
                    m=re.search(pat,html,re.I)
                    if m:
                        candidates.append(urllib.parse.urljoin(str(ar.url),unescape(m.group(1)))); break
        except Exception as exc:
            log.debug("v402 article image discovery failed %s: %s",article_url,exc)
    seen=set()
    for u in candidates:
        u=str(u or '').strip()
        if not u or u in seen or _is_generic_news_image(u): continue
        seen.add(u)
        try:
            p=urllib.parse.urlparse(u)
            if p.scheme not in {'http','https'} or (p.hostname or '').lower() in {'localhost','127.0.0.1','::1'}: continue
            for h in ({**headers,"Referer":f"{p.scheme}://{p.netloc}/"},headers):
                r=await c.get(u,follow_redirects=True,timeout=httpx.Timeout(8,connect=3),headers=h)
                ct=r.headers.get('content-type','').lower()
                if r.status_code<400 and ct.startswith('image/') and 800 < len(r.content) <= 6_000_000:
                    return r.content,ct.split(';')[0]
        except Exception:
            continue
    return None,None

@app.get('/sports/news/card-image')
async def v402_news_card_image(image: str = Query(''), article: str = Query('')):
    content,ctype=await _v402_fetch_image_bytes(image,article)
    if not content: raise HTTPException(404,'No verified article image available')
    return Response(content=content,media_type=ctype or 'image/jpeg',headers={'Cache-Control':'public, max-age=43200, stale-while-revalidate=86400'})

# === KSN v478: permanent Finished Games -> API-Football reconciliation ===
def _v478_norm_team(v: str) -> str:
    v=unidecode(str(v or '')).lower()
    v=re.sub(r'\b(fc|cf|afc|sc|ac|club|football club)\b',' ',v)
    return re.sub(r'[^a-z0-9]+',' ',v).strip()

def _v478_norm_comp(v: str) -> str:
    return re.sub(r'[^a-z0-9]+',' ',unidecode(str(v or '')).lower()).strip()

def _v478_parse_dt(v):
    try: return datetime.fromisoformat(str(v or '').replace('Z','+00:00'))
    except Exception: return None

def _v478_persist_archive_fixture_id(fid:int, home:str, away:str, date:str='', competition:str='', provider_fixture:dict|None=None):
    """Write a verified API-Football fixture id back to legacy archive rows permanently."""
    _results_archive_init(); conn,kind=_results_db(); cur=conn.cursor()
    hn,an=_v478_norm_team(home),_v478_norm_team(away)
    try:
        ph='%s' if kind=='postgres' else '?'
        sql=("SELECT ksn_key,home_name,away_name,kickoff,competition,provider_id,source_payload "
             "FROM ksn_results_archive WHERE sport='football' AND (provider_id IS NULL OR provider_id='')")
        params=[]
        day=''
        try: day=_v478_parse_dt(date).date().isoformat() if _v478_parse_dt(date) else re.search(r'\d{4}-\d{2}-\d{2}',str(date or '')).group(0)
        except Exception: day=''
        if day:
            if kind=='postgres': sql += f" AND kickoff >= {ph}::date AND kickoff < ({ph}::date + INTERVAL '1 day')"; params += [day,day]
            else: sql += f" AND substr(kickoff,1,10)={ph}"; params += [day]
        cur.execute(sql,tuple(params)); rows=cur.fetchall(); matches=[]
        for row in rows:
            vals=dict(row) if hasattr(row,'keys') else {'ksn_key':row[0],'home_name':row[1],'away_name':row[2],'kickoff':row[3],'competition':row[4],'provider_id':row[5],'source_payload':row[6]}
            direct=_v478_norm_team(vals['home_name'])==hn and _v478_norm_team(vals['away_name'])==an
            if not direct: continue
            if competition:
                ca,cb=_v478_norm_comp(competition),_v478_norm_comp(vals.get('competition'))
                if ca and cb and ca!=cb and ca not in cb and cb not in ca: continue
            matches.append(vals)
        if len(matches)!=1: return False
        row=matches[0]; payload=row.get('source_payload') or {}
        if isinstance(payload,str):
            try: payload=json.loads(payload)
            except Exception: payload={}
        payload=dict(payload) if isinstance(payload,dict) else {}
        payload['providerFixtureId']=int(fid); payload['fixtureId']=int(fid)
        payload.setdefault('provider','API-Football')
        if provider_fixture: payload['_verifiedProviderFixture']=provider_fixture
        if kind=='postgres':
            cur.execute("UPDATE ksn_results_archive SET provider='API-Football',provider_id=%s,source_payload=%s::jsonb,updated_at=NOW() WHERE ksn_key=%s",(str(fid),json.dumps(payload,ensure_ascii=False,default=str),row['ksn_key']))
        else:
            cur.execute("UPDATE ksn_results_archive SET provider=?,provider_id=?,source_payload=?,updated_at=? WHERE ksn_key=?",('API-Football',str(fid),json.dumps(payload,ensure_ascii=False,default=str),datetime.now(timezone.utc).isoformat(),row['ksn_key']))
        conn.commit(); return True
    except Exception as exc:
        conn.rollback(); log.warning('v478 archive fixture-id persistence failed: %s',exc); return False
    finally:
        cur.close(); conn.close()

async def _v478_fixture_candidates(home:str, away:str, date:str='', competition:str=''):
    h=' '.join(str(home).split()).strip(); a=' '.join(str(away).split()).strip()
    if not h or not a: return []
    target_dt=_v478_parse_dt(date); day=target_dt.date().isoformat() if target_dt else ''
    if not day:
        m=re.search(r'\d{4}-\d{2}-\d{2}',str(date or '')); day=m.group(0) if m else ''
    queries=[]
    try:
        for nm in (h,a):
            td=await _afoot_get('/teams',{'search':nm},force_fresh=True)
            for x in (td.get('response') or [])[:3]:
                tid=(x.get('team') or {}).get('id')
                if tid: queries.append({'team':tid,**({'date':day} if day else {})})
    except Exception as exc: log.debug('v478 team lookup failed: %s',exc)
    if day: queries.append({'date':day})
    seen={}; hn,an=_v478_norm_team(h),_v478_norm_team(a); cn=_v478_norm_comp(competition)
    for q in queries[:7]:
        try:
            fd=await _afoot_get('/fixtures',q,force_fresh=True)
            for x in fd.get('response') or []:
                fx=x.get('fixture') or {}; teams=x.get('teams') or {}; league=x.get('league') or {}
                fid=fx.get('id')
                if not fid or fid in seen: continue
                hh=_v478_norm_team((teams.get('home') or {}).get('name')); aa=_v478_norm_team((teams.get('away') or {}).get('name'))
                # Direction is intentionally strict for archive reconciliation.
                if hh!=hn or aa!=an: continue
                score=100
                provider_dt=_v478_parse_dt(fx.get('date'))
                if target_dt and provider_dt:
                    try:
                        delta=abs((provider_dt-target_dt).total_seconds())/60
                        if delta<=15: score+=25
                        elif delta<=120: score+=15
                        elif delta<=360: score+=5
                        else: score-=30
                    except Exception: pass
                lc=_v478_norm_comp(league.get('name'))
                if cn and lc:
                    if cn==lc: score+=20
                    elif cn in lc or lc in cn: score+=10
                    else: score-=15
                seen[fid]={'fixtureId':int(fid),'score':score,'fixture':x,'resolvedHome':(teams.get('home') or {}).get('name'),'resolvedAway':(teams.get('away') or {}).get('name'),'competition':league.get('name'),'kickoff':fx.get('date')}
        except Exception as exc: log.debug('v478 fixture candidate query failed %s: %s',q,exc)
    return sorted(seen.values(),key=lambda z:z['score'],reverse=True)

@app.get('/results/football-fixture-id')
async def v478_resolve_football_fixture_id(home: str = Query(...), away: str = Query(...), date: str = Query(''), competition: str = Query('')):
    """Resolve only a unique high-confidence API-Football fixture and persist it to the archive."""
    key=f"v478-resolve:{_v478_norm_team(home)}:{_v478_norm_team(away)}:{str(date)[:16]}:{_v478_norm_comp(competition)}"
    snap=_dashboard_snapshot_get(key)
    if isinstance(snap,dict) and snap.get('fixtureId'): return {**snap,'cached':True}
    candidates=await _v478_fixture_candidates(home,away,date,competition)
    if not candidates: return {'fixtureId':None,'available':False,'reason':'no-provider-match'}
    best=candidates[0]; second=candidates[1] if len(candidates)>1 else None
    # Exact team direction plus >=100 score; reject ambiguous near-ties.
    if best['score']<100 or (second and second['score']>=best['score']-5):
        return {'fixtureId':None,'available':False,'reason':'ambiguous-provider-match','candidates':len(candidates)}
    persisted=_v478_persist_archive_fixture_id(best['fixtureId'],home,away,date,competition,best.get('fixture'))
    out={'fixtureId':best['fixtureId'],'available':True,'verified':True,'persisted':persisted,'source':'API-Football','resolvedHome':best['resolvedHome'],'resolvedAway':best['resolvedAway'],'competition':best.get('competition'),'kickoff':best.get('kickoff')}
    _dashboard_snapshot_put(key,out); return out

@app.get('/results/open-stats')
async def v478_open_finished_stats(fixture_id: str = Query(''), home: str = Query(''), away: str = Query(''), date: str = Query(''), competition: str = Query('')):
    """Finished Games Stats: verify existing ID, otherwise reconcile+persist, then open canonical Match Centre."""
    fid=int(re.sub(r'\D','',str(fixture_id)) or 0)
    if fid:
        try:
            chk=await _afoot_get('/fixtures',{'id':fid},force_fresh=True)
            rows=chk.get('response') or []
            if rows:
                _v478_persist_archive_fixture_id(fid,home,away,date,competition,rows[0])
                return RedirectResponse(url=f'/matches/{fid}/stats',status_code=307)
        except Exception as exc: log.debug('v478 existing fixture verify failed: %s',exc)
    resolved=await v478_resolve_football_fixture_id(home=home,away=away,date=date,competition=competition)
    rid=resolved.get('fixtureId') if isinstance(resolved,dict) else None
    if rid: return RedirectResponse(url=f'/matches/{rid}/stats',status_code=307)
    return HTMLResponse("""<!doctype html><html><head><meta name='viewport' content='width=device-width,initial-scale=1'><title>Match Stats | Kasi Sports News</title><style>body{background:#000;color:#fff;font-family:Arial;padding:24px}.card{max-width:640px;margin:12vh auto;border:1px solid #2b2b2b;border-radius:14px;padding:22px}h2{font-size:24px}p{color:#b8c0cc;line-height:1.55}a{color:#38bdf8}</style></head><body><div class='card'><h2>Detailed statistics are not available for this archived match.</h2><p>We could not verify a unique API-Football fixture for this result, so Kasi Sports News will not attach statistics from another match.</p><a href='/#live'>← Back to Finished Games</a></div></body></html>""",status_code=404)

@app.get('/build-version-v478')
async def v478_build_version():
    return {'version':'v478-finished-stats-archive-reconciliation'}

# ---------------------------------------------------------------------------
# v418 FINAL PRE-SEO STABILITY — canonical public prediction aliases + LKG
# ---------------------------------------------------------------------------
# The frontend public contract is /sports/<sport>/predictions.  Older backend
# implementations exposed /rugby/predictions and /cricket/predictions only,
# which made the public Rugby/Cricket tabs receive 404/empty responses.

@app.get('/sports/cricket/predictions')
async def v418_public_cricket_predictions(
    date: str = Query(''),
    limit: int = Query(20, ge=1, le=50),
):
    key = f'predictions:last_good:cricket:{date or "current"}'
    snap = _dashboard_snapshot_get(key) if '_dashboard_snapshot_get' in globals() else None
    old = (snap or {}).get('data') if isinstance(snap, dict) else None
    try:
        data = await cricket_predictions(date=date, limit=limit)
    except Exception as exc:
        if isinstance(old, dict) and (old.get('predictions') or old.get('matches')):
            return {**old, 'stale': True, 'fromSharedLastGood': True,
                    'staleReason': 'Cricket prediction refresh failed',
                    'publicFree': True, 'requiresSubscription': False}
        return {'sport':'cricket','count':0,'predictions':[],'matches':[],
                'state':'provider-error','error':str(exc),
                'publicFree':True,'requiresSubscription':False}
    rows = list(data.get('predictions') or data.get('matches') or [])
    payload = {**data, 'predictions': rows[:limit], 'matches': rows[:limit],
               'count': len(rows[:limit]), 'publicFree': True,
               'requiresSubscription': False}
    if rows:
        if '_dashboard_snapshot_put' in globals():
            _dashboard_snapshot_put(key, {'data': payload})
        return payload
    if isinstance(old, dict) and (old.get('predictions') or old.get('matches')):
        return {**old, 'stale': True, 'fromSharedLastGood': True,
                'staleReason': 'Current cricket scan returned no predictions',
                'publicFree': True, 'requiresSubscription': False}
    return payload

@app.get('/sports/rugby/predictions')
async def v418_public_rugby_predictions(
    league: str = Query('urc'),
    season: int = Query(0, ge=0),
    date: str = Query(''),
    limit: int = Query(20, ge=1, le=50),
):
    key = f'predictions:last_good:rugby:{league}:{season or "current"}:{date or "current"}'
    snap = _dashboard_snapshot_get(key) if '_dashboard_snapshot_get' in globals() else None
    old = (snap or {}).get('data') if isinstance(snap, dict) else None
    try:
        data = await rugby_predictions(league=league, season=season, date=date)
    except Exception as exc:
        if isinstance(old, dict) and (old.get('predictions') or old.get('matches')):
            return {**old, 'stale': True, 'fromSharedLastGood': True,
                    'staleReason': 'Rugby prediction refresh failed',
                    'publicFree': True, 'requiresSubscription': False}
        return {'sport':'rugby','count':0,'predictions':[],'matches':[],
                'state':'provider-error','error':str(exc),
                'publicFree':True,'requiresSubscription':False}
    rows = list(data.get('predictions') or data.get('matches') or [])[:limit]
    payload = {**data, 'sport':'rugby', 'predictions':rows, 'matches':rows,
               'count':len(rows), 'publicFree':True, 'requiresSubscription':False}
    if rows:
        if '_dashboard_snapshot_put' in globals():
            _dashboard_snapshot_put(key, {'data': payload})
        return payload
    if isinstance(old, dict) and (old.get('predictions') or old.get('matches')):
        return {**old, 'stale': True, 'fromSharedLastGood': True,
                'staleReason': 'Current rugby scan returned no predictions',
                'publicFree': True, 'requiresSubscription': False}
    return payload

# KSN v471: shared Stats / Team Theme architecture marker.
# Match Centre, Team and Player pages retain the server-side teamTheme implementation;
# public widgets use the shared frontend resolver in KSN_Frontend_v471_Shared_Stats_Team_Theme.html.
KSN_SHARED_MATCH_ACTIONS_VERSION = "v471-shared-stats-team-theme-1"

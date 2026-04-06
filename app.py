# app.py - Free Fire Bot Web Application (with Music Player)
import os
import sys
import json
import time
import socket
import threading
import queue
import urllib3
from datetime import datetime
from flask import Flask, request, jsonify, session, render_template_string
from flask_socketio import SocketIO
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
import jwt
import requests
import eventlet
eventlet.monkey_patch()


urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

from masry import (
    EnC_AEs, EnC_PacKeT, DEc_PacKeT, DeCode_PackEt, DecodE_HeX,
    CrEaTe_ProTo, GeneRaTePk, xMsGFixinG, generate_random_color,
    JoinSq, ExitSq, OpenCh, MsqSq, GeTSQDaTa
)
import Xr

# ==================== LOGGING ====================
import logging
from logging.handlers import RotatingFileHandler

LOG_LEVEL = os.environ.get('LOG_LEVEL', 'INFO').upper()
LOG_MAX_BYTES = 3 * 1024 * 1024
LOG_BACKUP_COUNT = 1

LOG_DIR = "logs"
if not os.path.exists(LOG_DIR):
    os.makedirs(LOG_DIR)

logger = logging.getLogger("FF_WEB")
logger.setLevel(getattr(logging, LOG_LEVEL))

console_handler = logging.StreamHandler(sys.stdout)
console_handler.setLevel(logging.INFO)
console_formatter = logging.Formatter('%(asctime)s [%(levelname)s] %(message)s', '%H:%M:%S')
console_handler.setFormatter(console_formatter)

file_handler = RotatingFileHandler(
    os.path.join(LOG_DIR, "app.log"),
    maxBytes=LOG_MAX_BYTES,
    backupCount=LOG_BACKUP_COUNT
)
file_handler.setLevel(logging.DEBUG)
file_formatter = logging.Formatter('%(asctime)s [%(levelname)s] %(name)s:%(lineno)d - %(message)s')
file_handler.setFormatter(file_formatter)

logger.addHandler(console_handler)
logger.addHandler(file_handler)

def info(msg): logger.info(msg)
def err(msg): logger.error(msg)
def dbg(msg): logger.debug(msg)
def warn(msg): logger.warning(msg)

# ==================== FLASK APP ====================
app = Flask(__name__)
app.config['SECRET_KEY'] = os.environ.get('SECRET_KEY', 'freefire-bot-secret-key')
socketio = SocketIO(app, cors_allowed_origins="*", logger=False, engineio_logger=False)

# ==================== CONFIGURATION ====================
freefire_version = "OB52"
client_secret = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"

connected_clients = {}
connected_clients_lock = threading.Lock()

WEB_PASSWORD = os.environ.get('WEB_PASSWORD', 'admin123')

SPAM_ACCOUNTS = [
    {'id': '4692213103', 'password': 'Senzu_999MK2QL'},
]

# URL nhạc từ GitHub
MUSIC_URL = "https://raw.githubusercontent.com/DevHuy2000/tinhve/main/tinh-ve-remix-nhac-trung-japandee-remix.mp3"

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

# ==================== xCLF CLASS ====================
class xCLF:
    def __init__(self, id, password):
        self.id = id
        self.password = password
        self.CliEnts = None
        self.CliEnts2 = None
        self.key = None
        self.iv = None
        self.is_ready = False
        self.max_retries = 3
        self.retry_count = 0
        self._squad_queue = queue.Queue()
        self._squad_active = False
        
        with connected_clients_lock:
            connected_clients[self.id] = self
        
        info(f"[xCLF] Init account {self.id}")
        threading.Thread(target=self._init_login, daemon=True).start()
    
    def _init_login(self):
        try:
            self.GeNToKeNLogin()
        except Exception as e:
            err(f"[{self.id}] Login error: {e}")
            time.sleep(10)
            self._init_login()
    
    def mark_ready(self):
        self.is_ready = True
        info(f"[{self.id}] ✅ Ready!")
    
    def wait_ready(self, timeout=60):
        start = time.time()
        while not self.is_ready and time.time() - start < timeout:
            time.sleep(0.5)
        return self.is_ready
    
    def GeTinFoSqMsG(self, teamcode):
        info(f"[SQUAD:{self.id}] Getting squad {teamcode}")
        
        if not self.wait_ready(timeout=30):
            return {"success": False, "reason": "Client not ready"}
        
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
            
            pkt = JoinSq(teamcode, self.key, self.iv)
            self.CliEnts2.send(pkt)
            info(f"[SQUAD:{self.id}] JoinSq sent")
            
            buf = b""
            buf_offset = 0
            start_time = time.time()
            
            while time.time() - start_time < 20:
                try:
                    chunk = self._squad_queue.get(timeout=1.0)
                    if chunk:
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
                            
                            if dT:
                                OwNer, SQuAD, ChaT = GeTSQDaTa(dT)
                                if OwNer and ChaT:
                                    info(f"[SQUAD:{self.id}] ✅ Found! Owner={OwNer}")
                                    try:
                                        self.CliEnts2.send(ExitSq('000000', self.key, self.iv))
                                    except:
                                        pass
                                    return {"success": True, "OwNer_UiD": OwNer,
                                            "SQuAD_CoDe": SQuAD, "ChaT_CoDe": ChaT}
                        except:
                            i += 1
                            continue
                    
                    buf_offset = i
                except queue.Empty:
                    continue
                except Exception as e:
                    err(f"[SQUAD:{self.id}] Error: {e}")
                    break
            
            return {"success": False, "reason": "Timeout"}
        except Exception as e:
            err(f"[SQUAD:{self.id}] Exception: {e}")
            return {"success": False, "reason": str(e)}
        finally:
            self._squad_active = False
    
    def SeNd_SpaM_MsG(self, owner_uid, chat_code, message, count=50):
        info(f"[SPAM] Spamming {count} messages")
        
        if not self.wait_ready(timeout=30):
            return False
        
        try:
            ready_clients = []
            with connected_clients_lock:
                for c in connected_clients.values():
                    if c.is_ready and c.CliEnts and c.CliEnts2:
                        ready_clients.append(c)
            
            if not ready_clients:
                warn("[SPAM] No ready clients")
                return False
            
            for client in ready_clients[:3]:
                chat_thread = threading.Thread(
                    target=self._spam_chat,
                    args=(client, owner_uid, chat_code, message, count),
                    daemon=True
                )
                room_thread = threading.Thread(
                    target=self._spam_room,
                    args=(client, owner_uid, count),
                    daemon=True
                )
                chat_thread.start()
                room_thread.start()
            
            return True
        except Exception as e:
            err(f"[SPAM] Error: {e}")
            return False
    
    def _spam_chat(self, client, owner_uid, chat_code, message, count):
        try:
            if client.CliEnts:
                client.CliEnts.send(OpenCh(owner_uid, chat_code, client.key, client.iv))
                time.sleep(0.5)
                for i in range(count):
                    client.CliEnts.send(
                        MsqSq(f'[b][c]{generate_random_color()}{message}', 
                              owner_uid, client.key, client.iv)
                    )
                    time.sleep(0.2)
                info(f"[CHAT:{client.id}] Sent {count} chat messages")
        except Exception as e:
            err(f"[CHAT:{client.id}] Error: {e}")
    
    def _spam_room(self, client, owner_uid, count):
        try:
            if client.CliEnts2:
                k = client.key if isinstance(client.key, bytes) else bytes.fromhex(client.key)
                iv = client.iv if isinstance(client.iv, bytes) else bytes.fromhex(client.iv)
                room_pkt = _openRoom(k, iv)
                spm_pkt = _spmRoom(k, iv, owner_uid)
                
                client.CliEnts2.send(room_pkt)
                time.sleep(0.5)
                for i in range(count):
                    client.CliEnts2.send(spm_pkt)
                    time.sleep(0.1)
                info(f"[ROOM:{client.id}] Sent {count} room invites")
        except Exception as e:
            err(f"[ROOM:{client.id}] Error: {e}")
    
    def ConnEcT_SerVer_OnLiNe(self, Token, tok, host, port, key, iv, host2, port2):
        self.key = key
        self.iv = iv
        
        while True:
            try:
                info(f"[SOCK2:{self.id}] Connecting {host2}:{port2}")
                self.CliEnts2 = socket.create_connection((host2, int(port2)), timeout=10)
                self.CliEnts2.send(bytes.fromhex(tok))
                
                while True:
                    try:
                        self.CliEnts2.settimeout(1.0)
                        data = self.CliEnts2.recv(65535)
                        if not data:
                            break
                        if self._squad_active:
                            self._squad_queue.put(data)
                    except socket.timeout:
                        continue
                    except:
                        break
            except Exception as e:
                err(f"[SOCK2:{self.id}] Error: {e}")
                time.sleep(3)
                continue
    
    def ConnEcT_SerVer(self, Token, tok, host, port, key, iv, host2, port2):
        self.key = key
        self.iv = iv
        
        retry_count = 0
        while retry_count < 5:
            try:
                info(f"[SOCK1:{self.id}] Connecting {host}:{port}")
                self.CliEnts = socket.create_connection((host, int(port)), timeout=10)
                self.CliEnts.send(bytes.fromhex(tok))
                self.CliEnts.recv(1024)
                info(f"[SOCK1:{self.id}] Connected")
                break
            except Exception as e:
                retry_count += 1
                err(f"[SOCK1:{self.id}] Failed ({retry_count}/5): {e}")
                time.sleep(2)
                if retry_count >= 5:
                    threading.Timer(30, lambda: self.ConnEcT_SerVer(Token, tok, host, port, key, iv, host2, port2)).start()
                    return
        
        threading.Thread(
            target=self.ConnEcT_SerVer_OnLiNe,
            args=(Token, tok, host, port, key, iv, host2, port2),
            daemon=True
        ).start()
        
        self.mark_ready()
        
        while True:
            try:
                self.CliEnts.settimeout(5.0)
                data = self.CliEnts.recv(4096)
                if len(data) == 0:
                    break
                self.retry_count = 0
            except socket.timeout:
                continue
            except Exception as e:
                err(f"[SOCK1:{self.id}] Error: {e}")
                self.retry_count += 1
                if self.retry_count >= self.max_retries:
                    break
                time.sleep(2)
        
        self.is_ready = False
        try:
            if self.CliEnts:
                self.CliEnts.close()
            if self.CliEnts2:
                self.CliEnts2.close()
        except:
            pass
        
        self.ConnEcT_SerVer(Token, tok, host, port, key, iv, host2, port2)
    
    def GeT_Key_Iv(self, serialized_data):
        try:
            from google.protobuf.timestamp_pb2 import Timestamp
            msg = Xr.MyMessage()
            msg.ParseFromString(serialized_data)
            ts_obj = Timestamp()
            ts_obj.FromNanoseconds(msg.field21)
            combined_ts = ts_obj.seconds * 1_000_000_000 + ts_obj.nanos
            return combined_ts, msg.field22, msg.field23
        except Exception as e:
            err(f"GeT_Key_Iv error: {e}")
            return None, None, None
    
    def GuestLogin(self, uid, password):
        info(f"[LOGIN:{uid}] GuestLogin...")
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
                verify=False,
                timeout=30
            ).json()
            
            self.Access_ToKen = resp['access_token']
            self.Access_Uid = resp['open_id']
            info(f"[LOGIN:{uid}] GuestLogin OK")
            time.sleep(0.2)
            return self.MajorLogin(self.Access_ToKen, self.Access_Uid)
        except Exception as e:
            err(f"[LOGIN:{uid}] GuestLogin error: {e}")
            raise
    
    def DataLogin(self, JwT_ToKen, PayLoad):
        info(f"[LOGIN:{self.id}] DataLogin...")
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
                data=PayLoad,
                verify=False,
                timeout=30
            )
            
            d = json.loads(DeCode_PackEt(resp.content.hex()))
            addr = d['32']['data']
            addr2 = d['14']['data']
            ip = addr[:len(addr)-6]
            port = addr[len(addr)-5:]
            ip2 = addr2[:len(addr2)-6]
            port2 = addr2[len(addr2)-5:]
            info(f"[LOGIN:{self.id}] DataLogin OK")
            return ip, port, ip2, port2
        except Exception as e:
            err(f"[LOGIN:{self.id}] DataLogin error: {e}")
            raise
    
    def MajorLogin(self, Access_ToKen, Access_Uid):
        info(f"[LOGIN:{self.id}] MajorLogin...")
        
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
                data=self.PaYload,
                verify=False,
                timeout=30
            )
            
            if resp.status_code != 200 or len(resp.text) < 10:
                raise Exception(f"MajorLogin failed: {resp.status_code}")
            
            decoded = DeCode_PackEt(resp.content.hex())
            d = json.loads(decoded)
            self.JwT_ToKen = d['8']['data']
            
            combined_ts, self.key, self.iv = self.GeT_Key_Iv(resp.content)
            if not self.key:
                raise Exception("No key/iv")
            
            info(f"[LOGIN:{self.id}] MajorLogin OK")
            
            ip, port, ip2, port2 = self.DataLogin(self.JwT_ToKen, self.PaYload)
            if not ip:
                raise Exception("No server IP")
            
            return self.JwT_ToKen, self.key, self.iv, combined_ts, ip, port, ip2, port2
        except Exception as e:
            err(f"[LOGIN:{self.id}] MajorLogin error: {e}")
            raise
    
    def GeNToKeNLogin(self):
        info(f"[LOGIN:{self.id}] Starting login...")
        try:
            token, key, iv, Ts, ip, port, ip2, port2 = self.GuestLogin(self.id, self.password)
            self.JwT_ToKen = token
            
            dec = jwt.decode(token, options={"verify_signature": False})
            encoded_acc = hex(dec['account_id'])[2:]
            time_hex = DecodE_HeX(Ts)
            jwt_hex = token.encode().hex()
            head_len = hex(len(EnC_PacKeT(jwt_hex, key, iv)) // 2)[2:]
            zeros = {7: '000000000', 8: '00000000', 9: '0000000', 10: '000000'}.get(len(encoded_acc), '00000000')
            final_token = f'0115{zeros}{encoded_acc}{time_hex}00000{head_len}' + EnC_PacKeT(jwt_hex, key, iv)
            
            info(f"[LOGIN:{self.id}] Connecting to server...")
            self.ConnEcT_SerVer(token, final_token, ip, port, key, iv, ip2, port2)
        except Exception as e:
            err(f"[LOGIN:{self.id}] Login error: {e}")
            time.sleep(15)
            self.GeNToKeNLogin()

# ==================== START ACCOUNTS ====================
def _start_spam_account(account):
    try:
        client = xCLF(account['id'], account['password'])
        client.wait_ready(timeout=60)
    except Exception as e:
        err(f"Start account error: {e}")
        time.sleep(10)
        _start_spam_account(account)

def start_spam_server():
    info(f"[SERVER] Starting {len(SPAM_ACCOUNTS)} accounts")
    for acc in SPAM_ACCOUNTS:
        threading.Thread(target=_start_spam_account, args=(acc,), daemon=True).start()
        time.sleep(5)

# ==================== HTML TEMPLATE ====================
HTML_TEMPLATE = '''
<!DOCTYPE html>
<html lang="vi">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=yes">
    <title>FF Bot | Spam Tool</title>
    <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&display=swap" rel="stylesheet">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        
        body {
            font-family: 'Inter', sans-serif;
            min-height: 100vh;
            color: #fff;
            position: relative;
            background: #1a1a2e;
        }
        
        /* Fullscreen Background Image */
        body::before {
            content: '';
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background-image: url('https://i.postimg.cc/xqM0PNLP/4k-anime-cherry-blossom-wallpaper.jpg');
            background-size: cover;
            background-position: center;
            background-repeat: no-repeat;
            background-attachment: fixed;
            filter: brightness(0.6);
            z-index: -2;
        }
        
        /* Overlay */
        body::after {
            content: '';
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: linear-gradient(135deg, rgba(0,0,0,0.5) 0%, rgba(0,0,0,0.3) 100%);
            z-index: -1;
        }
        
        .container {
            position: relative;
            z-index: 1;
            max-width: 500px;
            margin: 0 auto;
            padding: 20px;
            min-height: 100vh;
            display: flex;
            flex-direction: column;
        }
        
        /* Music Player Button */
        .music-btn {
            position: fixed;
            bottom: 20px;
            right: 20px;
            width: 50px;
            height: 50px;
            background: linear-gradient(135deg, #ff6b6b, #ffb347);
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            cursor: pointer;
            z-index: 100;
            box-shadow: 0 4px 15px rgba(0,0,0,0.3);
            transition: all 0.3s ease;
            border: none;
            color: white;
            font-size: 24px;
        }
        
        .music-btn:hover {
            transform: scale(1.1);
        }
        
        .music-btn.playing {
            animation: musicPulse 1s infinite;
        }
        
        @keyframes musicPulse {
            0%, 100% { box-shadow: 0 0 0 0 rgba(255, 107, 107, 0.4); }
            50% { box-shadow: 0 0 0 15px rgba(255, 107, 107, 0); }
        }
        
        .header {
            text-align: center;
            padding: 30px 0 20px;
            animation: slideDown 0.6s ease;
        }
        
        @keyframes slideDown {
            from { opacity: 0; transform: translateY(-30px); }
            to { opacity: 1; transform: translateY(0); }
        }
        
        .logo {
            width: 80px;
            height: 80px;
            background: linear-gradient(135deg, #ff6b6b, #ffb347);
            border-radius: 25px;
            display: flex;
            align-items: center;
            justify-content: center;
            margin: 0 auto 15px;
            animation: pulse 2s infinite;
        }
        
        @keyframes pulse {
            0%, 100% { box-shadow: 0 0 0 0 rgba(255, 107, 107, 0.4); }
            50% { box-shadow: 0 0 0 20px rgba(255, 107, 107, 0); }
        }
        
        .logo i { font-size: 38px; color: #fff; }
        
        h1 {
            font-size: 28px;
            font-weight: 800;
            background: linear-gradient(135deg, #ffb347, #ff6b6b);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
        }
        
        .subtitle {
            color: rgba(255,255,255,0.8);
            font-size: 14px;
            margin-top: 5px;
        }
        
        .status-card {
            background: rgba(255, 255, 255, 0.15);
            backdrop-filter: blur(10px);
            border-radius: 20px;
            padding: 15px 20px;
            margin-bottom: 20px;
            display: flex;
            justify-content: space-between;
            align-items: center;
            animation: fadeInUp 0.5s ease 0.1s both;
            border: 1px solid rgba(255, 255, 255, 0.2);
        }
        
        @keyframes fadeInUp {
            from { opacity: 0; transform: translateY(20px); }
            to { opacity: 1; transform: translateY(0); }
        }
        
        .status-info {
            display: flex;
            align-items: center;
            gap: 10px;
        }
        
        .status-dot {
            width: 10px;
            height: 10px;
            border-radius: 50%;
            background: #00ff88;
            animation: blink 1.5s infinite;
        }
        
        @keyframes blink {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.3; }
        }
        
        .status-dot.offline { background: #ff4444; animation: none; }
        
        .form-card {
            background: rgba(255, 255, 255, 0.15);
            backdrop-filter: blur(10px);
            border-radius: 25px;
            padding: 25px;
            margin-bottom: 20px;
            animation: fadeInUp 0.5s ease 0.2s both;
            border: 1px solid rgba(255, 255, 255, 0.2);
        }
        
        .form-group {
            margin-bottom: 20px;
        }
        
        label {
            display: block;
            margin-bottom: 8px;
            font-size: 14px;
            font-weight: 500;
            color: rgba(255,255,255,0.9);
        }
        
        input, textarea {
            width: 100%;
            padding: 14px 16px;
            background: rgba(0, 0, 0, 0.5);
            border: 1px solid rgba(255, 255, 255, 0.2);
            border-radius: 12px;
            color: #fff;
            font-size: 16px;
            transition: all 0.3s ease;
        }
        
        input:focus, textarea:focus {
            outline: none;
            border-color: #ffb347;
            box-shadow: 0 0 15px rgba(255, 179, 71, 0.3);
        }
        
        textarea {
            resize: vertical;
            min-height: 80px;
        }
        
        .btn {
            width: 100%;
            padding: 14px;
            background: linear-gradient(135deg, #ff6b6b, #ffb347);
            border: none;
            border-radius: 12px;
            color: #fff;
            font-size: 16px;
            font-weight: 600;
            cursor: pointer;
            transition: all 0.3s ease;
        }
        
        .btn:hover {
            transform: translateY(-2px);
            box-shadow: 0 10px 25px rgba(255, 107, 107, 0.4);
        }
        
        .btn:disabled {
            opacity: 0.6;
            cursor: not-allowed;
        }
        
        .btn-loading {
            pointer-events: none;
            position: relative;
        }
        
        .btn-loading::after {
            content: '';
            position: absolute;
            width: 20px;
            height: 20px;
            top: 50%;
            left: 50%;
            margin-left: -10px;
            margin-top: -10px;
            border: 2px solid #fff;
            border-top-color: transparent;
            border-radius: 50%;
            animation: spin 0.8s linear infinite;
        }
        
        @keyframes spin {
            to { transform: rotate(360deg); }
        }
        
        .result-card {
            background: rgba(0, 0, 0, 0.6);
            backdrop-filter: blur(10px);
            border-radius: 20px;
            padding: 20px;
            margin-bottom: 20px;
            display: none;
            border: 1px solid rgba(255, 179, 71, 0.3);
        }
        
        .result-card.show {
            display: block;
            animation: slideUp 0.4s ease;
        }
        
        @keyframes slideUp {
            from { opacity: 0; transform: translateY(20px); }
            to { opacity: 1; transform: translateY(0); }
        }
        
        .result-title {
            font-size: 14px;
            color: #ffb347;
            margin-bottom: 12px;
            display: flex;
            align-items: center;
            gap: 8px;
        }
        
        .result-content {
            font-size: 13px;
            color: rgba(255,255,255,0.8);
        }
        
        .result-item {
            margin-bottom: 8px;
            display: flex;
            gap: 10px;
            flex-wrap: wrap;
        }
        
        .result-label {
            font-weight: 600;
            color: #ffb347;
            min-width: 90px;
        }
        
        .modal {
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0, 0, 0, 0.8);
            backdrop-filter: blur(10px);
            z-index: 1000;
            display: flex;
            align-items: center;
            justify-content: center;
        }
        
        .modal.hide {
            display: none;
        }
        
        .modal-card {
            background: rgba(30, 30, 50, 0.95);
            backdrop-filter: blur(15px);
            border-radius: 30px;
            padding: 35px 25px;
            width: 85%;
            max-width: 350px;
            text-align: center;
            animation: modalIn 0.4s ease;
            border: 1px solid rgba(255, 179, 71, 0.3);
        }
        
        @keyframes modalIn {
            from { opacity: 0; transform: scale(0.9); }
            to { opacity: 1; transform: scale(1); }
        }
        
        .modal-icon {
            width: 70px;
            height: 70px;
            background: linear-gradient(135deg, #ff6b6b, #ffb347);
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            margin: 0 auto 20px;
        }
        
        .modal-icon i { font-size: 30px; }
        
        .modal h3 { margin-bottom: 10px; }
        .modal p { color: rgba(255,255,255,0.6); font-size: 14px; margin-bottom: 25px; }
        
        .error-msg {
            background: rgba(255, 68, 68, 0.2);
            border: 1px solid #ff4444;
            border-radius: 10px;
            padding: 10px;
            margin-top: 15px;
            font-size: 13px;
            color: #ff8888;
            display: none;
        }
        
        .error-msg.show { display: block; }
        
        .toast {
            position: fixed;
            bottom: 30px;
            left: 50%;
            transform: translateX(-50%) translateY(100px);
            background: rgba(0, 0, 0, 0.9);
            backdrop-filter: blur(10px);
            padding: 12px 24px;
            border-radius: 50px;
            font-size: 14px;
            z-index: 1001;
            transition: all 0.3s ease;
            white-space: nowrap;
        }
        
        .toast.show {
            transform: translateX(-50%) translateY(0);
        }
        
        .toast.success { border-left: 3px solid #00ff88; }
        .toast.error { border-left: 3px solid #ff4444; }
        
        .footer {
            text-align: center;
            padding: 20px;
            font-size: 12px;
            color: rgba(255,255,255,0.5);
            margin-top: auto;
        }
        
        ::-webkit-scrollbar {
            width: 5px;
        }
        
        ::-webkit-scrollbar-track {
            background: rgba(255, 255, 255, 0.05);
        }
        
        ::-webkit-scrollbar-thumb {
            background: #ffb347;
            border-radius: 5px;
        }
    </style>
</head>
<body>
    <!-- Music Button -->
    <button class="music-btn" id="musicBtn" onclick="toggleMusic()">
        <i class="fas fa-music"></i>
    </button>
    
    <!-- Audio Element -->
    <audio id="bgMusic" loop preload="auto">
        <source src="{{ music_url }}" type="audio/mpeg">
    </audio>
    
    <div class="container">
        <div class="header">
            <div class="logo">
                <i class="fas fa-fire"></i>
            </div>
            <h1>FF SPAM</h1>
            <p class="subtitle"> Free Fire Spam Tool | OB52 </p>
        </div>
        
        <div class="status-card">
            <div class="status-info">
                <div class="status-dot" id="statusDot"></div>
                <span id="statusText">Đang kết nối...</span>
            </div>
            <div>
                <i class="fas fa-server"></i>
                <span id="clientCount">0</span> clients
            </div>
        </div>
        
        <div class="form-card">
            <div class="form-group">
                <label><i class="fas fa-hashtag"></i> Teamcode</label>
                <input type="text" id="teamcode" placeholder="Nhập mã team...">
            </div>
            <div class="form-group">
                <label><i class="fas fa-comment"></i> Nội dung spam</label>
                <textarea id="message" placeholder="Nhập nội dung cần spam..."></textarea>
            </div>
            <div class="form-group">
                <label><i class="fas fa-chart-line"></i> Số lượng (Max 50)</label>
                <input type="number" id="count" value="30" min="1" max="50">
            </div>
            <button class="btn" id="spamBtn" onclick="startSpam()">
                <i class="fas fa-paper-plane"></i> GỬI SPAM
            </button>
        </div>
        
        <div class="result-card" id="resultCard">
            <div class="result-title">
                <i class="fas fa-check-circle"></i>
                <span> KẾT QUẢ SPAM </span>
            </div>
            <div class="result-content">
                <div class="result-item">
                    <span class="result-label">Owner UID:</span>
                    <span id="resultOwner">-</span>
                </div>
                <div class="result-item">
                    <span class="result-label">Chat Code:</span>
                    <span id="resultChat">-</span>
                </div>
                <div class="result-item">
                    <span class="result-label">Số lượng:</span>
                    <span id="resultCount">-</span>
                </div>
                <div class="result-item">
                    <span class="result-label">Nội dung:</span>
                    <span id="resultMsg">-</span>
                </div>
            </div>
        </div>
        
        <div class="footer">
            <i class="fas fa-bolt"></i> Free Fire Bot | OB52 | <i class="fas fa-cherry-blossom"></i> @S_ZU_01
        </div>
    </div>
    
    <div class="modal" id="loginModal">
        <div class="modal-card">
            <div class="modal-icon">
                <i class="fas fa-lock"></i>
            </div>
            <h3> Đăng nhập </h3>
            <p>Nhập mật khẩu để sử dụng bot</p>
            <div class="form-group">
                <input type="password" id="loginPassword" placeholder="Mật khẩu">
            </div>
            <button class="btn" onclick="login()">Đăng nhập</button>
            <div class="error-msg" id="loginError"></div>
        </div>
    </div>
    
    <div class="toast" id="toast"></div>
    
    <script>
        let isAuthenticated = false;
        let isMusicPlaying = false;
        const audio = document.getElementById('bgMusic');
        const musicBtn = document.getElementById('musicBtn');
        
        // Load saved music state from localStorage
        const savedMusicState = localStorage.getItem('musicPlaying');
        if (savedMusicState === 'true') {
            isMusicPlaying = true;
            audio.play().catch(e => console.log('Auto-play blocked'));
            musicBtn.classList.add('playing');
            musicBtn.innerHTML = '<i class="fas fa-stop"></i>';
        }
        
        function toggleMusic() {
            if (isMusicPlaying) {
                audio.pause();
                musicBtn.classList.remove('playing');
                musicBtn.innerHTML = '<i class="fas fa-music"></i>';
                isMusicPlaying = false;
                localStorage.setItem('musicPlaying', 'false');
            } else {
                audio.play().catch(e => {
                    console.log('Play failed:', e);
                    showToast('⚠️ Trình duyệt chặn tự động phát nhạc. Hãy bấm play lại!', 'error');
                });
                musicBtn.classList.add('playing');
                musicBtn.innerHTML = '<i class="fas fa-stop"></i>';
                isMusicPlaying = true;
                localStorage.setItem('musicPlaying', 'true');
            }
        }
        
        function showToast(message, type = 'success') {
            const toast = document.getElementById('toast');
            toast.textContent = message;
            toast.className = `toast ${type} show`;
            setTimeout(() => {
                toast.classList.remove('show');
            }, 3000);
        }
        
        async function checkStatus() {
            try {
                const resp = await fetch('/api/status');
                const data = await resp.json();
                const dot = document.getElementById('statusDot');
                const text = document.getElementById('statusText');
                const clientSpan = document.getElementById('clientCount');
                
                if (data.connected_clients > 0) {
                    dot.classList.remove('offline');
                    text.textContent = ' Đã kết nối';
                } else {
                    dot.classList.add('offline');
                    text.textContent = 'Reconnection...';
                }
                clientSpan.textContent = data.connected_clients;
            } catch(e) {
                console.error(e);
            }
        }
        
        async function login() {
            const password = document.getElementById('loginPassword').value;
            const errorDiv = document.getElementById('loginError');
            
            if (!password) {
                errorDiv.textContent = 'Vui lòng nhập mật khẩu';
                errorDiv.classList.add('show');
                return;
            }
            
            errorDiv.classList.remove('show');
            
            try {
                const resp = await fetch('/api/login', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ password })
                });
                const data = await resp.json();
                
                if (data.success) {
                    isAuthenticated = true;
                    document.getElementById('loginModal').classList.add('hide');
                    showToast('🌸 Đăng nhập thành công!', 'success');
                    checkStatus();
                    setInterval(checkStatus, 30000);
                } else {
                    errorDiv.textContent = data.error || 'Sai mật khẩu';
                    errorDiv.classList.add('show');
                }
            } catch(e) {
                errorDiv.textContent = 'Lỗi kết nối';
                errorDiv.classList.add('show');
            }
        }
        
        async function startSpam() {
            if (!isAuthenticated) {
                showToast('🌸 Vui lòng đăng nhập trước', 'error');
                return;
            }
            
            const teamcode = document.getElementById('teamcode').value.trim();
            const message = document.getElementById('message').value.trim();
            const count = parseInt(document.getElementById('count').value);
            
            if (!teamcode) {
                showToast('🌸 Vui lòng nhập Teamcode', 'error');
                return;
            }
            if (!message) {
                showToast('🌸 Vui lòng nhập nội dung spam', 'error');
                return;
            }
            if (count < 1 || count > 50) {
                showToast('🌸 Số lượng phải từ 1-50', 'error');
                return;
            }
            
            const btn = document.getElementById('spamBtn');
            btn.disabled = true;
            btn.classList.add('btn-loading');
            btn.innerHTML = '';
            
            try {
                const resp = await fetch('/api/spam', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ teamcode, message, count })
                });
                const data = await resp.json();
                
                if (data.success) {
                    const resultCard = document.getElementById('resultCard');
                    document.getElementById('resultOwner').textContent = data.data.owner_uid;
                    document.getElementById('resultChat').textContent = data.data.chat_code;
                    document.getElementById('resultCount').textContent = data.data.count;
                    document.getElementById('resultMsg').textContent = data.data.message.substring(0, 50);
                    resultCard.classList.add('show');
                    showToast(`🌸 Đã gửi ${count} tin nhắn thành công!`, 'success');
                } else {
                    showToast(data.error || 'Gửi thất bại', 'error');
                }
            } catch(e) {
                showToast('🌸 Lỗi kết nối đến server', 'error');
            } finally {
                btn.disabled = false;
                btn.classList.remove('btn-loading');
                btn.innerHTML = '<i class="fas fa-paper-plane"></i> GỬI SPAM';
            }
        }
        
        setInterval(checkStatus, 30000);
        checkStatus();
    </script>
</body>
</html>
'''

# ==================== FLASK ROUTES ====================
@app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE, music_url=MUSIC_URL)

@app.route('/api/login', methods=['POST'])
def api_login():
    data = request.json
    password = data.get('password', '')
    
    if password == WEB_PASSWORD:
        session['authenticated'] = True
        return jsonify({'success': True})
    return jsonify({'success': False, 'error': 'Sai mật khẩu'})

@app.route('/api/logout', methods=['POST'])
def api_logout():
    session.clear()
    return jsonify({'success': True})

@app.route('/api/status', methods=['GET'])
def api_status():
    with connected_clients_lock:
        ready_count = sum(1 for c in connected_clients.values() if c.is_ready)
    return jsonify({
        'connected_clients': ready_count,
        'version': freefire_version,
        'status': 'active' if ready_count > 0 else 'idle'
    })

@app.route('/api/spam', methods=['POST'])
def api_spam():
    if not session.get('authenticated'):
        return jsonify({'success': False, 'error': 'Not authenticated'}), 401
    
    data = request.json
    teamcode = data.get('teamcode', '').strip()
    message = data.get('message', '').strip()
    count = min(int(data.get('count', 30)), 50)
    
    if not teamcode or not teamcode.isdigit():
        return jsonify({'success': False, 'error': 'Teamcode không hợp lệ'})
    if not message:
        return jsonify({'success': False, 'error': 'Nội dung không được để trống'})
    
    with connected_clients_lock:
        ready_clients = [c for c in connected_clients.values() if c.is_ready]
        if not ready_clients:
            return jsonify({'success': False, 'error': 'Client chưa sẵn sàng, vui lòng đợi 30 giây'})
        first_client = ready_clients[0]
    
    team_data = first_client.GeTinFoSqMsG(teamcode)
    
    if not team_data["success"]:
        return jsonify({'success': False, 'error': team_data.get('reason', 'Không lấy được thông tin squad')})
    
    def spam_task():
        first_client.SeNd_SpaM_MsG(
            team_data["OwNer_UiD"],
            team_data["ChaT_CoDe"],
            message,
            count=count
        )
    
    threading.Thread(target=spam_task, daemon=True).start()
    
    return jsonify({
        'success': True,
        'data': {
            'owner_uid': team_data["OwNer_UiD"],
            'chat_code': team_data["ChaT_CoDe"],
            'squad_code': team_data.get("SQuAD_CoDe", ""),
            'count': count,
            'message': message
        }
    })

# ==================== MAIN ====================
if __name__ == "__main__":
    info("=" * 50)
    info("🌸 Free Fire Bot Web Server starting...")
    info(f"📁 Log directory: {LOG_DIR}")
    info(f"🎵 Music URL: {MUSIC_URL}")
    info("=" * 50)
    
    threading.Thread(target=start_spam_server, daemon=True).start()
    
    port = int(os.environ.get('PORT', 8080))
    socketio.run(app, host='0.0.0.0', port=port, debug=False)
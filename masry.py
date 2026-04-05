import requests , json , binascii , time , urllib3 , base64 , datetime , re ,socket , threading , random , os
from protobuf_decoder.protobuf_decoder import Parser
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad , unpad
from datetime import datetime
from google.protobuf.timestamp_pb2 import Timestamp

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

Key , Iv = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56]) , bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
    
def EnC_AEs(HeX):
    cipher = AES.new(Key , AES.MODE_CBC , Iv)
    return cipher.encrypt(pad(bytes.fromhex(HeX), AES.block_size)).hex()
    
def DEc_AEs(HeX):
    cipher = AES.new(Key , AES.MODE_CBC , Iv)
    return unpad(cipher.decrypt(bytes.fromhex(HeX)), AES.block_size).hex()
    
def EnC_PacKeT(HeX , K , V): 
    return AES.new(K , AES.MODE_CBC , V).encrypt(pad(bytes.fromhex(HeX) ,16)).hex()
    
def DEc_PacKeT(HeX , K , V):
    return unpad(AES.new(K , AES.MODE_CBC , V).decrypt(bytes.fromhex(HeX)) , 16).hex()  

def EnC_Uid(H , Tp):
    e , H = [] , int(H)
    while H:
        e.append((H & 0x7F) | (0x80 if H > 0x7F else 0)) ; H >>= 7
    return bytes(e).hex() if Tp == 'Uid' else None

def EnC_Vr(N):
    if N < 0: ''
    H = []
    while True:
        BesTo = N & 0x7F ; N >>= 7
        if N: BesTo |= 0x80
        H.append(BesTo)
        if not N: break
    return bytes(H)
    
def DEc_Uid(H):
    n = s = 0
    for b in bytes.fromhex(H):
        n |= (b & 0x7F) << s
        if not b & 0x80: break
        s += 7
    return n
    
def CrEaTe_VarianT(field_number, value):
    field_header = (field_number << 3) | 0
    return EnC_Vr(field_header) + EnC_Vr(value)

def CrEaTe_LenGTh(field_number, value):
    field_header = (field_number << 3) | 2
    encoded_value = value.encode() if isinstance(value, str) else value
    return EnC_Vr(field_header) + EnC_Vr(len(encoded_value)) + encoded_value

def CrEaTe_ProTo(fields):
    packet = bytearray()    
    for field, value in fields.items():
        if isinstance(value, dict):
            nested_packet = CrEaTe_ProTo(value)
            packet.extend(CrEaTe_LenGTh(field, nested_packet))
        elif isinstance(value, int):
            packet.extend(CrEaTe_VarianT(field, value))           
        elif isinstance(value, str) or isinstance(value, bytes):
            packet.extend(CrEaTe_LenGTh(field, value))           
    return packet    
    
def DecodE_HeX(H):
    R = hex(H) 
    F = str(R)[2:]
    if len(F) == 1: F = "0" + F ; return F
    else: return F

def Fix_PackEt(parsed_results):
    result_dict = {}
    for result in parsed_results:
        field_data = {}
        field_data['wire_type'] = result.wire_type
        if result.wire_type == "varint":
            field_data['data'] = result.data
        if result.wire_type == "string":
            field_data['data'] = result.data
        if result.wire_type == "bytes":
            field_data['data'] = result.data
        elif result.wire_type == 'length_delimited':
            field_data["data"] = Fix_PackEt(result.data.results)
        result_dict[result.field] = field_data
    return result_dict

def DeCode_PackEt(input_text):
    try:
        parsed_results = Parser().parse(input_text)
        parsed_results_objects = parsed_results
        parsed_results_dict = Fix_PackEt(parsed_results_objects)
        json_data = json.dumps(parsed_results_dict)
        return json_data
    except Exception as e:
        print(f"error {e}")
        return None
    
def xMsGFixinG(n):
    return '🗿'.join(str(n)[i:i + 3] for i in range(0 , len(str(n)) , 3))

def _V(b, i):
    r = s = 0
    while True:
        c = b[i]; i += 1
        r |= (c & 0x7F) << s
        if c < 0x80: break
        s += 7
    return r, i

def PrOtO(hx):
    b, i, R = bytes.fromhex(hx), 0, {}
    while i < len(b):
        H, i = _V(b, i)
        F, T = H >> 3, H & 7
        if T == 0:
            R[F], i = _V(b, i)
        elif T == 2:
            L, i = _V(b, i)
            S = b[i:i+L]; i += L
            try: R[F] = S.decode()
            except:
                try: R[F] = PrOtO(S.hex())
                except: R[F] = S
        elif T == 5:
            R[F] = int.from_bytes(b[i:i+4], 'little'); i += 4
        else:
            raise ValueError(f'Unknown wire type: {T}')
    return R
    
def GeT_KEy(obj , target):
    values = []
    def collect(o):
        if isinstance(o, dict):
            for k, v in o.items():
                if k == target:
                    values.append(v)
                collect(v)
        elif isinstance(o, list):
            for v in o:
                collect(v)
    collect(obj)
    return values[-1] if values else None
 
def GeneRaTePk(Pk , N , K , V):
    PkEnc = EnC_PacKeT(Pk , K , V)
    _ = DecodE_HeX(int(len(PkEnc) // 2))
    if len(_) == 2: HeadEr = N + "000000"
    elif len(_) == 3: HeadEr = N + "00000"
    elif len(_) == 4: HeadEr = N + "0000"
    elif len(_) == 5: HeadEr = N + "000"
    return bytes.fromhex(HeadEr + _ + PkEnc)
    
def GuiLd_AccEss(Tg , Nm , Uid , BLk , OwN , AprV):
    return Tg in Nm and Uid not in BLk and Uid in (OwN | AprV)
            
def ChEck_Commande(id):
    return "<" not in id and ">" not in id and "[" not in id and "]" not in id

def ResTarT_BoT():
    print('\nError In Src! ')
    p = psutil.Process(os.getpid())
    open_files = p.open_files()
    connections = p.net_connections()
    for handler in open_files:
        try:
            os.close(handler.fd)
        except Exception:
            pass           
    for conn in connections:
        try:
            conn.close()
        except Exception:
            pass
    sys.path.append(os.path.dirname(os.path.abspath(sys.argv[0])))
    python = sys.executable
    os.execl(python, python, *sys.argv)

def GeT_Time(timestamp):
    last_login = datetime.fromtimestamp(timestamp)
    now = datetime.now()
    diff = now - last_login   
    d = diff.days
    h, rem = divmod(diff.seconds, 3600)
    m, s = divmod(rem, 60)    
    return d, h, m, s
    
def Device():
    versions = [
        '4.0.18P6', '4.0.19P7', '4.0.20P1', '4.1.0P3', '4.1.5P2', '4.2.1P8',
        '4.2.3P1', '5.0.1B2', '5.0.2P4', '5.1.0P1', '5.2.0B1', '5.2.5P3',
        '5.3.0B1', '5.3.2P2', '5.4.0P1', '5.4.3B2', '5.5.0P1', '5.5.2P3'
    ]
    models = [
        'SM-A125F', 'SM-A225F', 'SM-A325M', 'SM-A515F', 'SM-A725F', 'SM-M215F', 'SM-M325FV',
        'Redmi 9A', 'Redmi 9C', 'POCO M3', 'POCO M4 Pro', 'RMX2185', 'RMX3085',
        'moto g(9) play', 'CPH2239', 'V2027', 'OnePlus Nord', 'ASUS_Z01QD',
    ]
    android_versions = ['9', '10', '11', '12', '13', '14']
    languages = ['en-US', 'es-MX', 'pt-BR', 'id-ID', 'ru-RU', 'hi-IN']
    countries = ['USA', 'MEX', 'BRA', 'IDN', 'RUS', 'IND']
    version = random.choice(versions)
    model = random.choice(models)
    android = random.choice(android_versions)
    lang = random.choice(languages)
    country = random.choice(countries)    
    
def generate_random_color():
    color_list = [
        "[00FF00][b][c]", "[FFDD00][b][c]", "[3813F3][b][c]", "[FF0000][b][c]", 
        "[0000FF][b][c]", "[FFA500][b][c]", "[DF07F8][b][c]", "[11EAFD][b][c]",
        "[DCE775][b][c]", "[A8E6CF][b][c]", "[7CB342][b][c]", "[FF0000][b][c]",
        "[FFB300][b][c]", "[90EE90][b][c]", "[FF4500][b][c]", "[FFD700][b][c]",
        "[32CD32][b][c]", "[87CEEB][b][c]", "[9370DB][b][c]", "[FF69B4][b][c]",
        "[8A2BE2][b][c]", "[00BFFF][b][c]", "[1E90FF][b][c]", "[20B2AA][b][c]",
        "[00FA9A][b][c]", "[008000][b][c]", "[FFFF00][b][c]", "[FF8C00][b][c]",
        "[DC143C][b][c]", "[FF6347][b][c]", "[FFA07A][b][c]", "[FFDAB9][b][c]",
        "[CD853F][b][c]", "[D2691E][b][c]", "[BC8F8F][b][c]", "[F0E68C][b][c]",
        "[556B2F][b][c]", "[808000][b][c]", "[4682B4][b][c]", "[6A5ACD][b][c]",
        "[7B68EE][b][c]", "[8B4513][b][c]", "[C71585][b][c]", "[4B0082][b][c]",
        "[B22222][b][c]", "[228B22][b][c]", "[8B008B][b][c]", "[483D8B][b][c]",
        "[556B2F][b][c]", "[800000][b][c]", "[008080][b][c]", "[000080][b][c]",
        "[800080][b][c]", "[808080][b][c]", "[A9A9A9][b][c]", "[D3D3D3][b][c]", "[F0F0F0][b][c]"
    ]
    return random.choice(color_list)   
    
def xBunnEr():
    bN = [902000306 , 902000305 , 902000017 , 902000011 , 902000091 , 902000207 , 902050001 , 902050002 , 902050003 , 902050004 , 902050005 , 902050006]
    return random.choice(bN)

# ======== دوال مضافة من xC4.py ========

def GeTSQDaTa(dT):
    try:
        # طباعة هيكل البيانات للتحقق
        print(f"DEBUG GeTSQDaTa: Keys in dT: {list(dT.keys())}")
        
        if '5' in dT and 'data' in dT['5']:
            data_field = dT['5']['data']
            print(f"DEBUG GeTSQDaTa: Keys in data_field: {list(data_field.keys())}")
            
            # استخراج البيانات
            OwNer_UiD = data_field.get('1', {}).get('data') if '1' in data_field else None
            SQuAD_CoDe = data_field.get('31', {}).get('data') if '31' in data_field else None
            ChaT_CoDe = data_field.get('17', {}).get('data') if '17' in data_field else None
            
            # إذا كان الحقل 17 غير موجود، جرب الحقل 14 (سيكر كود)
            if not ChaT_CoDe and '14' in data_field:
                ChaT_CoDe = data_field['14'].get('data')
            
            print(f"DEBUG GeTSQDaTa extracted:")
            print(f"  Owner UID from field 1: {OwNer_UiD}")
            print(f"  Squad Code from field 31: {SQuAD_CoDe}")
            print(f"  Chat Code from field 17: {ChaT_CoDe}")
            
            return OwNer_UiD, SQuAD_CoDe, ChaT_CoDe
        
        return None, None, None
        
    except Exception as e:
        print(f"Error extracting squad data: {e}")
        import traceback
        traceback.print_exc()
        return None, None, None

def OpenCh(idT, code, K, V):
    fields = {
  1: 3,
  2: {
    1: idT,
    3: "en",
    4: str(code)
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()) , '1215' , K , V)
   
def ExitSq(id , K , V):
    fields = {
        1: 7,
        2: {
            1: int(11037044965)
        }
        }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()) , '0515' , K , V)      
    
def ArA_CoLor():
    Tp = [   
        "FF9999",  
        "99FF99",  
        "99CCFF", 
        "FFD700", 
        "FFB6C1", 
        "FFA07A",  
        "98FB98", 
        "E6E6FA",  
        "AFEEEE",  
        "F0E68C",  
        "FFE4B5",  
        "D8BFD8", 
        "FFFACD",  
        "87CEFA",  
        "FFDEAD",  
        "B0E0E6",  
        "FFDAB9",  
        "E0FFFF",  
        "F5DEB3",  
        "FFC0CB",  
        "FFF0F5",  
        "ADD8E6"]
    return random.choice(Tp)
    
def MsqSq(Msg , id , K , V):
    fields = {1: id , 2: id , 4: Msg , 5: 1756580149, 7: 2, 8: 901048018, 9: {1: "MeRoBoT", 2: xBunnEr(), 4: 330, 5: 827001005, 8: "MeRoBoT", 10: 1, 11: 1, 13: {1: 2}, 14: {1: 1158053040, 2: 8, 3: "\u0010\u0015\b\n\u000b\u0015\f\u000f\u0011\u0004\u0007\u0002\u0003\r\u000e\u0012\u0001\u0005\u0006"}}, 10: "en", 13: {2: 2, 3: 1}}
    Pk = (CrEaTe_ProTo(fields)).hex()
    Pk = "080112" + EnC_Uid(len(Pk) // 2, Tp='Uid') + Pk
    return GeneRaTePk(Pk, '1215', K, V)    
    
def JoinSq(code, key, iv):
    fields = {}
    fields[1] = 4
    fields[2] = {}
    fields[2][4] = bytes.fromhex("01090a0b121920")
    fields[2][5] = str(code)
    fields[2][6] = 6
    fields[2][8] = 1
    fields[2][9] = {}
    fields[2][9][2] = 800
    fields[2][9][6] = 11
    fields[2][9][8] = "1.111.1"
    fields[2][9][9] = 5
    fields[2][9][10] = 1
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0515', key, iv)

# ======== دوال جديدة من xC4.py ========

def AuthClan(CLan_Uid, AuTh, K, V):
    fields = {1: 3, 2: {1: int(CLan_Uid), 2: 1, 4: str(AuTh)}}
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '1201', K, V)

def AutH_GlobAl(K, V):
    fields = {
        1: 3,
        2: {
            2: 5,
            3: "en"
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '1215', K, V)

def xSEndMsg(Msg, Tp, Tp2, id, K, V):
    fields = {1: id, 2: Tp2, 3: Tp, 4: Msg, 5: 1735129800, 7: 2, 9: {1: "AlliFF_BOT", 2: int(xBunnEr()), 3: 901048018, 4: 330, 5: 909034009, 8: "AlliFF_BOT", 10: 1, 11: 1, 13: {1: 2}, 14: {1: 12484827014, 2: 8, 3: "\u0010\u0015\b\n\u000b\u0013\f\u000f\u0011\u0004\u0007\u0002\u0003\r\u000e\u0012\u0001\u0005\u0006"}, 12: 0}, 10: "en", 13: {3: 1}}
    Pk = (CrEaTe_ProTo(fields)).hex()
    Pk = "080112" + EnC_Uid(len(Pk) // 2, Tp='Uid') + Pk
    return GeneRaTePk(Pk, '1201', K, V)

def xSEndMsgsQ(Msg, id, K, V):
    fields = {1: id, 2: id, 4: Msg, 5: 1756580149, 7: 2, 8: 904990072, 9: {1: "AlliFF_BOT", 2: xBunnEr(), 4: 330, 5: 827001005, 8: "AlliFF_BOT", 10: 1, 11: 1, 13: {1: 2}, 14: {1: 1158053040, 2: 8, 3: "\u0010\u0015\b\n\u000b\u0015\f\u000f\u0011\u0004\u0007\u0002\u0003\r\u000e\u0012\u0001\u0005\u0006"}}, 10: "en", 13: {2: 2, 3: 1}}
    Pk = (CrEaTe_ProTo(fields)).hex()
    Pk = "080112" + EnC_Uid(len(Pk) // 2, Tp='Uid') + Pk
    return GeneRaTePk(Pk, '1201', K, V)

def SPam_Room(Uid, Rm, Nm, K, V):
    fields = {1: 78, 2: {1: int(Rm), 2: f"[{ArA_CoLor()}]{Nm}", 3: {2: 1, 3: 1}, 4: 330, 5: 1, 6: 201, 10: xBunnEr(), 11: int(Uid), 12: 1}}
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0e15', K, V)

def FS(K, V):
    fields = {
        1: 9,
        2: {
            1: 13256361202
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0515', K, V)

def send_emote_packet(TarGeT, idT, K, V, region):
    fields = {
        1: 21,
        2: {
            1: int(TarGeT),
            2: int(idT),
            3: 1,
            4: 1,
            5: {
                1: int(TarGeT),
                2: int(idT),
                3: 1,
            }
        }
    }
    if region.lower() == "ind":
        packet = '0514'
    elif region.lower() == "bd":
        packet = "0519"
    else:
        packet = "0515"
    
    print(f"🎭 DEBUG EMOTE: Target: {TarGeT}, Emote: {idT}, Region: {region}")
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), packet, K, V)

def OpEnSq(K, V, region):
    fields = {1: 1, 2: {2: "\u0001", 3: 1, 4: 1, 5: "en", 9: 1, 11: 1, 13: 1, 14: {2: 5756, 6: 11, 8: "1.111.5", 9: 2, 10: 4}}}
    if region.lower() == "ind":
        packet = '0514'
    elif region.lower() == "bd":
        packet = "0519"
    else:
        packet = "0515"
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), packet, K, V)

def cHSq(Nu, Uid, K, V, region):
    fields = {1: 17, 2: {1: int(Uid), 2: 1, 3: int(Nu - 1), 4: 62, 5: "\u001a", 8: 5, 13: 329}}
    if region.lower() == "ind":
        packet = '0514'
    elif region.lower() == "bd":
        packet = "0519"
    else:
        packet = "0515"
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), packet, K, V)

def SEnd_InV(Nu, Uid, K, V, region):
    fields = {1: 2, 2: {1: int(Uid), 2: region, 4: int(Nu)}}
    if region.lower() == "ind":
        packet = '0514'
    elif region.lower() == "bd":
        packet = "0519"
    else:
        packet = "0515"
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), packet, K, V)

def ExiT(idT, K, V):
    fields = {
        1: 7,
        2: {
            1: int(idT) if idT else 11037044965,
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0515', K, V)

def AutH_Chat(T, uid, code, K, V):
    fields = {
        1: T,
        2: {
            1: int(uid),
            3: "en",
            4: str(code)
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '1215', K, V)

def ghost_pakcet(player_id, secret_code, K, V):
    fields = {
        1: 61,
        2: {
            1: int(player_id),
            2: {
                1: int(player_id),
                2: int(time.time()),
                3: "AlliFF_Ghost",
                5: 12,
                6: 9999999,
                7: 1,
                8: {
                    2: 1,
                    3: 1,
                },
                9: 3,
            },
            3: secret_code, }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0515', K, V)

def GenJoinGlobaL(owner, code, K, V):
    fields = {
        1: 4,
        2: {
            1: int(owner),
            6: 1,
            8: 1,
            13: "en",
            15: code,
            16: "OR",
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0515', K, V)

def LagSquad(K, V):
    fields = {
        1: 15,
        2: {
            1: 1124759936,
            2: 1
        }
    }
    return GeneRaTePk(str(CrEaTe_ProTo(fields).hex()), '0515', K, V)

def GeT_Status(PLayer_Uid, K, V):
    PLayer_Uid_hex = EnC_Uid(int(PLayer_Uid), Tp='Uid')
    if len(PLayer_Uid_hex) == 8:
        Pk = f'080112080a04{PLayer_Uid_hex}1005'
    elif len(PLayer_Uid_hex) == 10:
        Pk = f"080112090a05{PLayer_Uid_hex}1005"
    return GeneRaTePk(Pk, '0f15', K, V)
#!/usr/bin/env python3
"""
Training Room Camera Capture Pipeline (Pure Python, Zero Dependencies)
=====================================================================
Captures images from training room cameras via HikIoT Open Platform,
generates a web gallery, and prepares for deployment.

NO external packages required - uses only Python standard library.

Supports env vars (for GitHub Actions / CI):
  HIK_APP_KEY, HIK_APP_SECRET, HIK_USER_NAME, HIK_PASSWORD, HIK_NVR_SERIAL

Usage:
  python3 hik_pipeline.py                    # capture + generate gallery
  python3 hik_pipeline.py --output /custom/dir
  python3 hik_pipeline.py --gallery-only     # just regenerate gallery HTML
"""
import argparse
import base64
import json
import os
import sys
import time
import urllib.parse
import urllib.request
from datetime import datetime, timezone, timedelta
from pathlib import Path


# Beijing timezone (UTC+8)
BEIJING_TZ = timezone(timedelta(hours=8))


def beijing_now():
    """Return current datetime in Beijing timezone (UTC+8)."""
    return datetime.now(BEIJING_TZ)


# ==================== Configuration ====================
APP_KEY = os.environ.get("HIK_APP_KEY", "2081247314391167027")
APP_SECRET = os.environ.get("HIK_APP_SECRET", "MIICdgIBADANBgkqhkiG9w0BAQEFAASCAmAwggJcAgEAAoGBAMFioLiTE0FIqwVGr5+WUpPPTl6fNE9k5WRrm00xFEL/TDOurjnRA7y+0r+lM70TBZsih5LHoW9/Qjh2HJkdrLU3AtR8Sqw7Y19Ec1hSOoLcNDzJdLgrATg2WXY7Hd9cAvFmBNwOMM5G9DrBDOX7xoeQ1s9v71sgi2qW6QAj+Es/AgMBAAECgYAPzq0OiU8gnf0EwGNoqxPy6xYf2+mdt8ScccNPCvz6AP5MlzG8nh4tFngJnEpfYSerJ6ZnVBQZFhDmppjt1yQfw4EKuYqSUSndSfWjvnSoBMmtPe6W0mQpwqcrqBROWsK8mEtob9PuuHCxDTl2ZEtH6XIW0Qd3wXWhoMymWi5xIQJBAOukXRvhMcBGTAHIRc2m56kOPk6Lm9nzBreHRvnWqbcgruh+SbW/6wUsGd2A9VYKyWN4S96UvwWa/gTdlFVOf+8CQQDSF65yv5ldVUCSYcehLrQHPvAdWZFBMMjZPTb8FUAbQAzrJqyR3UrX6WnE/E7NIFOfiNduEqbD8lTY2mIphJmxAkAac9gT8iLAn+OWa6ISZQMqgjPSY2+6dsKxRZldIJDqwtt/s/WYVpQOf5XjvL9NymYzKWTy9qW+/lg3uZwWO3q3AkAn3Oxxw18DMZDd9YWeVLE+CrgeqYcBGpORfKb5L8MJKJ8K4zytNJLl4tj50nHVRAP56koODaXs2gc1WkJz5EARAkEA6SR5dB2H3gsuDCjTrTGuCv1rbW+Src+14uz+0H4xnfThj/XEvzlRmyFRjeVWI7rnfe0qDVpF/oAV+qYDmEqtWQ==")
USER_NAME = os.environ.get("HIK_USER_NAME", "18601632466")
PASSWORD = os.environ.get("HIK_PASSWORD", "Bill/0523")
REDIRECT_URL = "https://www.baidu.com"

NVR_SERIAL = os.environ.get("HIK_NVR_SERIAL", "F60238772")
CAMERAS = [
    {"name": "Camera_01", "channelNo": 1},
    {"name": "Camera_02", "channelNo": 2},
]

# Gallery shows ONLY the latest capture (live monitor view, no history)
SHOW_LATEST_ONLY = True
# Auto-cleanup: keep only the last few captures on disk as a safety buffer,
# delete everything older. Keeps disk tiny even with frequent captures.
KEEP_LAST_CAPTURES = 3

API_BASE = "https://open-api.hikiot.com"

# File paths
SCRIPT_DIR = Path(__file__).parent.resolve()
TOKEN_CACHE = SCRIPT_DIR / "tokens.json"
DEFAULT_OUTPUT = SCRIPT_DIR / "captures"
GALLERY_DIR = SCRIPT_DIR / "gallery"

# ==================== RSA: ASN.1 DER Parser ====================
def _der_read_length(data, offset):
    """Read a DER length field. Returns (length, new_offset)."""
    first = data[offset]
    offset += 1
    if first & 0x80:
        num_len_bytes = first & 0x7F
        length = int.from_bytes(data[offset:offset + num_len_bytes], "big")
        offset += num_len_bytes
    else:
        length = first
    return length, offset


def _der_read_integer(data, offset):
    """Read a DER INTEGER. Returns (value, new_offset)."""
    assert data[offset] == 0x02, f"Expected INTEGER tag 0x02, got {hex(data[offset])}"
    offset += 1
    length, offset = _der_read_length(data, offset)
    value = int.from_bytes(data[offset:offset + length], "big")
    offset += length
    return value, offset


def parse_rsa_private_key(base64_key):
    """Parse PKCS#8 DER-encoded RSA private key (base64-encoded).
    Returns (n, e, d) where n=modulus, e=public exponent, d=private exponent.
    Pure Python, no external crypto libraries."""
    der = base64.b64decode(base64_key)
    pos = 0

    # Outer SEQUENCE (PrivateKeyInfo)
    assert der[pos] == 0x30, "Expected outer SEQUENCE"
    pos += 1
    _, pos = _der_read_length(der, pos)

    # version INTEGER (0)
    _, pos = _der_read_integer(der, pos)

    # AlgorithmIdentifier SEQUENCE { OID, NULL }
    assert der[pos] == 0x30, "Expected AlgorithmIdentifier SEQUENCE"
    pos += 1
    alg_len, pos = _der_read_length(der, pos)
    pos += alg_len  # skip OID + NULL

    # OCTET STRING containing RSAPrivateKey
    assert der[pos] == 0x04, "Expected OCTET STRING"
    pos += 1
    _, pos = _der_read_length(der, pos)

    # RSAPrivateKey SEQUENCE
    assert der[pos] == 0x30, "Expected RSAPrivateKey SEQUENCE"
    pos += 1
    _, pos = _der_read_length(der, pos)

    # version INTEGER (0)
    _, pos = _der_read_integer(der, pos)
    # n (modulus)
    n, pos = _der_read_integer(der, pos)
    # e (public exponent)
    e, pos = _der_read_integer(der, pos)
    # d (private exponent)
    d, pos = _der_read_integer(der, pos)

    return n, e, d


# ==================== RSA: Encrypt / Decrypt ====================
def rsa_encrypt_private(data_str, n, d):
    """Encrypt data with RSA private key using PKCS#1 v1.5 Type 1 padding.
    This is signature-style encryption (0x00 0x01 0xFF... 0x00 data).
    Supports multi-block for data longer than key_size - 11 bytes.
    Returns base64-encoded ciphertext."""
    data_bytes = data_str.encode("utf-8")
    key_size = (n.bit_length() + 7) // 8
    max_block = key_size - 11  # PKCS#1 v1.5 overhead
    result = b""

    for i in range(0, len(data_bytes), max_block):
        block = data_bytes[i:i + max_block]
        pad_len = key_size - len(block) - 3
        # Type 1 padding: 0x00 0x01 0xFF...0xFF 0x00 data
        padded = b"\x00\x01" + b"\xff" * pad_len + b"\x00" + block
        m = int.from_bytes(padded, "big")
        # Private key operation: c = m^d mod n
        c = pow(m, d, n)
        result += c.to_bytes(key_size, "big")

    return base64.b64encode(result).decode("utf-8")


def rsa_decrypt_private(data_b64, n, d):
    """Decrypt data with RSA private key (standard PKCS#1 v1.5).
    Handles both Type 1 (0x00 0x01 0xFF...) and Type 2 (0x00 0x02 random) padding.
    Supports multi-block. Returns decoded string."""
    ciphertext = base64.b64decode(data_b64)
    key_size = (n.bit_length() + 7) // 8
    result = b""

    for i in range(0, len(ciphertext), key_size):
        block = ciphertext[i:i + key_size]
        c = int.from_bytes(block, "big")
        m = pow(c, d, n)
        decrypted = m.to_bytes(key_size, "big")

        # Remove PKCS#1 v1.5 padding
        plaintext = b""
        if len(decrypted) >= 2:
            if decrypted[0] == 0x00 and decrypted[1] == 0x01:
                # Type 1: 0x00 0x01 0xFF... 0x00 [data]
                sep_idx = decrypted.find(b"\x00", 2)
                if sep_idx >= 0:
                    plaintext = decrypted[sep_idx + 1:]
            elif decrypted[0] == 0x00 and decrypted[1] == 0x02:
                # Type 2: 0x00 0x02 [random non-zero] 0x00 [data]
                sep_idx = decrypted.find(b"\x00", 2)
                if sep_idx >= 0:
                    plaintext = decrypted[sep_idx + 1:]
            elif decrypted[0] == 0x01:
                # No leading 0x00, Type 1
                sep_idx = decrypted.find(b"\x00", 1)
                if sep_idx >= 0:
                    plaintext = decrypted[sep_idx + 1:]
            elif decrypted[0] == 0x02:
                # No leading 0x00, Type 2
                sep_idx = decrypted.find(b"\x00", 1)
                if sep_idx >= 0:
                    plaintext = decrypted[sep_idx + 1:]
            else:
                # Fallback: strip leading zeros
                plaintext = decrypted.lstrip(b"\x00")
        else:
            plaintext = decrypted

        result += plaintext

    text = result.decode("utf-8", errors="replace").rstrip("\x00")
    # HikIoT URL-encodes the decrypted JSON
    if text.startswith("%"):
        text = urllib.parse.unquote(text)
    return text


# ==================== HTTP Helpers ====================
def _http_request(method, url, headers=None, data=None, timeout=30):
    """Make an HTTP request and return parsed JSON response."""
    req = urllib.request.Request(url, data=data, method=method)
    if headers:
        for k, v in headers.items():
            req.add_header(k, v)
    if data is not None and "Content-Type" not in (headers or {}):
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw)
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8")
        try:
            return json.loads(body)
        except json.JSONDecodeError:
            return {"code": -1, "msg": f"HTTP {e.code}: {body}"}
    except Exception as e:
        return {"code": -1, "msg": str(e)}


# ==================== HikIoT API Client ====================
class HikIoTClient:
    """HikIoT Open Platform API client with RSA encryption (pure Python)."""

    def __init__(self, app_key, app_secret):
        self.app_key = app_key
        self.app_secret = app_secret
        self.n, self.e, self.d = parse_rsa_private_key(app_secret)
        self.key_size = (self.n.bit_length() + 7) // 8

    def _encrypt(self, data_str):
        """Encrypt a string with RSA private key, return base64."""
        return rsa_encrypt_private(data_str, self.n, self.d)

    def _decrypt(self, data_b64):
        """Decrypt base64-encoded RSA ciphertext, return string."""
        return rsa_decrypt_private(data_b64, self.n, self.d)

    def _api_call(self, endpoint, method="POST", body=None, headers=None,
                  encrypt_body=True, decrypt_response=True):
        """Call HikIoT API with automatic RSA encryption/decryption."""
        url = f"{API_BASE}{endpoint}"
        data = None

        if body is not None:
            if method == "POST":
                if encrypt_body:
                    encrypted = self._encrypt(json.dumps(body))
                    data = json.dumps({"bodySecret": encrypted}).encode("utf-8")
                else:
                    data = json.dumps(body).encode("utf-8")
            elif method == "GET":
                if encrypt_body:
                    query = urllib.parse.urlencode(body)
                    encrypted = self._encrypt(query)
                    url = f"{url}?querySecret={urllib.parse.quote(encrypted, safe='')}"
                else:
                    query = urllib.parse.urlencode(body)
                    url = f"{url}?{query}"

        result = _http_request(method, url, headers=headers, data=data)

        if (decrypt_response and result.get("code") == 0
                and isinstance(result.get("data"), str)):
            decrypted = self._decrypt(result["data"])
            result["data"] = json.loads(decrypted)

        return result

    def get_app_token(self):
        """Step 1: Exchange appKey + appSecret for App-Access-Token."""
        r = self._api_call(
            "/auth/exchangeAppToken", "POST",
            {"appKey": self.app_key, "appSecret": self.app_secret},
            encrypt_body=False, decrypt_response=False,
        )
        if r.get("code") != 0:
            raise RuntimeError(f"exchangeAppToken failed: {r}")
        return r["data"]["appAccessToken"]

    def get_user_token(self):
        """Steps 2-3: Server-side OAuth -> authCode -> User-Access-Token.
        Returns (userAccessToken, refreshUserToken)."""
        app_token = self.get_app_token()

        # Step 2: Apply for authCode (server-side, no browser redirect)
        r = self._api_call(
            "/auth/third/applyAuthCode", "POST",
            {"appKey": self.app_key, "userName": USER_NAME,
             "password": PASSWORD, "redirectUrl": REDIRECT_URL},
            headers={"App-Access-Token": app_token},
            encrypt_body=False, decrypt_response=False,
        )
        if r.get("code") != 0:
            raise RuntimeError(f"applyAuthCode failed: {r}")
        auth_code = r["data"]["authCode"]

        # Step 3: Exchange authCode for user token (RSA encrypted)
        r = self._api_call(
            "/auth/third/code2Token", "GET", {"authCode": auth_code},
            headers={"App-Access-Token": app_token},
            encrypt_body=True, decrypt_response=True,
        )
        if r.get("code") != 0:
            raise RuntimeError(f"code2Token failed: {r}")
        return r["data"]["userAccessToken"], r["data"]["refreshUserToken"]

    def refresh_user_token(self, refresh_token):
        """Refresh User-Access-Token using refreshUserToken."""
        app_token = self.get_app_token()
        r = self._api_call(
            "/auth/third/refreshUserToken", "GET",
            {"refreshUserToken": refresh_token},
            headers={"App-Access-Token": app_token},
            encrypt_body=True, decrypt_response=True,
        )
        if r.get("code") != 0:
            raise RuntimeError(f"refreshUserToken failed: {r}")
        return r["data"]["userAccessToken"]

    def capture_image(self, user_token, device_serial, channel_no):
        """Capture image from camera. Returns image URL (valid 2 hours)."""
        app_token = self.get_app_token()
        r = self._api_call(
            "/device/direct/v1/captureImage/captureImage", "POST",
            {"deviceSerial": device_serial, "payload": {"channelNo": channel_no}},
            headers={"App-Access-Token": app_token, "User-Access-Token": user_token},
            encrypt_body=True, decrypt_response=True,
        )
        if r.get("code") != 0:
            raise RuntimeError(f"captureImage failed: {r}")
        return r["data"]["captureUrl"]


# ==================== Token Cache ====================
def load_cached_tokens():
    """Load cached tokens from disk."""
    if TOKEN_CACHE.exists():
        try:
            with open(TOKEN_CACHE) as f:
                return json.load(f)
        except Exception:
            pass
    return None


def save_cached_tokens(user_token, refresh_token):
    """Save tokens to disk for reuse across runs."""
    TOKEN_CACHE.parent.mkdir(parents=True, exist_ok=True)
    with open(TOKEN_CACHE, "w") as f:
        json.dump({
            "userAccessToken": user_token,
            "refreshUserToken": refresh_token,
            "cached_at": beijing_now().isoformat(),
        }, f, indent=2)


# ==================== Image Download ====================
def download_image(url, dest_path):
    """Download image from URL to local file."""
    req = urllib.request.Request(url)
    req.add_header("User-Agent", "HikIoT-Capture/1.0")
    with urllib.request.urlopen(req, timeout=30) as resp:
        data = resp.read()
    with open(dest_path, "wb") as f:
        f.write(data)
    return len(data)


# ==================== Gallery Generation ====================
def _group_captures(captures_dir):
    """Scan captured images and group by timestamp.
    Returns dict {timestamp: {camera_name: path}}, sorted newest first."""
    all_images = sorted(captures_dir.glob("*.jpg"), reverse=True)
    groups = {}
    for img in all_images:
        # Filename: 20260726_140050_Camera_01.jpg
        parts = img.stem.split("_")
        if len(parts) >= 3:
            ts = "_".join(parts[:2])  # 20260726_140050
            cam = "_".join(parts[2:])  # Camera_01
            if ts not in groups:
                groups[ts] = {}
            groups[ts][cam] = img
    return groups


def generate_gallery(captures_dir, gallery_dir):
    """Generate a LIVE MONITOR gallery that shows ONLY the latest capture.
    No history is kept on the page -- people see the freshest snapshot, that's it.
    Also prunes the gallery image dir so only the current images live there."""
    import shutil
    gallery_dir.mkdir(parents=True, exist_ok=True)

    groups = _group_captures(captures_dir)
    sorted_ts = sorted(groups.keys(), reverse=True)

    if not sorted_ts:
        # No captures -- show a waiting state but keep page live
        html = """<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<meta http-equiv="refresh" content="120">
<title>训练室监控</title>
<style>
* { margin:0; padding:0; box-sizing:border-box; }
body { font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
       background:#0f172a; color:#e2e8f0; min-height:100vh;
       display:flex; align-items:center; justify-content:center; }
.box { text-align:center; }
.dot { width:14px; height:14px; border-radius:50%; background:#f59e0b;
       display:inline-block; animation:pulse 1.5s infinite; margin-bottom:18px; }
@keyframes pulse { 0%,100%{opacity:1} 50%{opacity:0.3} }
h1 { font-size:1.4rem; font-weight:600; margin-bottom:8px; }
p { color:#94a3b8; font-size:0.95rem; }
</style>
</head>
<body>
<div class="box">
<div class="dot"></div>
<h1>等待首次抓拍</h1>
<p>下一次自动抓拍将更新画面</p>
</div>
</body>
</html>"""
        (gallery_dir / "index.html").write_text(html, encoding="utf-8")
        # Clear stale gallery images
        for old in gallery_dir.glob("*.jpg"):
            try:
                old.unlink()
            except Exception:
                pass
        return 0

    latest_ts = sorted_ts[0]
    cams = groups[latest_ts]

    # Wipe gallery image dir, then copy ONLY the latest images in
    for old in gallery_dir.glob("*.jpg"):
        try:
            old.unlink()
        except Exception:
            pass
    for cam, img_path in cams.items():
        shutil.copy2(str(img_path), str(gallery_dir / img_path.name))

    # Format timestamp for display: 20260726_140050 -> 2026-07-26 14:00:50
    display_ts = (f"{latest_ts[:4]}-{latest_ts[4:6]}-{latest_ts[6:8]} "
                  f"{latest_ts[9:11]}:{latest_ts[11:13]}:{latest_ts[13:15]}")

    # Build camera cards — always show all configured cameras, with
    # placeholder for any that failed to capture
    cache_bust = latest_ts
    cards_html = ""
    # Always iterate over the configured camera list so all slots appear
    for configured_cam in CAMERAS:
        cam_name = configured_cam["name"]
        label = cam_name.replace("_", " ")
        if cam_name in cams:
            img = cams[cam_name]
            cards_html += f"""
        <div class="cam">
            <div class="cam-label">{label}</div>
            <img src="{img.name}?t={cache_bust}" alt="{label}" onclick="this.classList.toggle('zoom')">
        </div>"""
        else:
            # No capture for this camera — show "offline" placeholder
            cards_html += f"""
        <div class="cam offline">
            <div class="cam-label">{label}</div>
            <div class="offline-icon">📷</div>
            <div class="offline-msg">抓拍失败<br><span>等待下次更新</span></div>
        </div>"""

    now = beijing_now().strftime("%Y-%m-%d %H:%M")

    html = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<meta http-equiv="refresh" content="120">
<title>训练室监控</title>
<style>
* {{ margin:0; padding:0; box-sizing:border-box; }}
body {{
    font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
    background:#0f172a; color:#e2e8f0; min-height:100vh;
}}
header {{
    background:#1e293b; padding:14px 24px;
    box-shadow:0 2px 12px rgba(0,0,0,0.4);
    position:sticky; top:0; z-index:100;
    display:flex; justify-content:space-between; align-items:center;
    flex-wrap:wrap; gap:8px;
}}
header h1 {{ font-size:1.25rem; font-weight:600; }}
.live {{
    font-size:0.82rem; color:#94a3b8;
    display:flex; align-items:center; gap:6px;
}}
.live::before {{
    content:''; width:8px; height:8px; border-radius:50%;
    background:#22c55e; display:inline-block; animation:pulse 2s infinite;
}}
@keyframes pulse {{ 0%,100%{{opacity:1}} 50%{{opacity:0.4}} }}
.ts-bar {{
    background:#1e293b; margin:0; padding:10px 24px;
    display:flex; justify-content:space-between; align-items:center;
    border-bottom:1px solid #334155; font-size:0.9rem;
}}
.ts-bar .when {{ font-weight:600; color:#f1f5f9; }}
.ts-bar .updated {{ color:#64748b; font-size:0.8rem; }}
.cams {{
    display:flex; gap:3px; padding:3px; min-height:calc(100vh - 110px);
}}
.cam {{ flex:1; position:relative; background:#000; overflow:hidden; }}
.cam-label {{
    position:absolute; top:10px; left:10px;
    background:rgba(0,0,0,0.65); color:#fff;
    padding:3px 12px; border-radius:5px; font-size:0.78rem;
    z-index:2; backdrop-filter:blur(4px);
}}
.cam img {{
    width:100%; height:100%; object-fit:cover; display:block;
    cursor:zoom-in; transition:transform 0.25s;
}}
.cam img.zoom {{
    position:fixed; top:50%; left:50%;
    transform:translate(-50%,-50%) scale(2);
    z-index:9999; max-width:96vw; max-height:96vh;
    object-fit:contain; cursor:zoom-out;
}}
.cam.offline {{
    display:flex; flex-direction:column; align-items:center; justify-content:center;
    background:#1e293b;
}}
.offline-icon {{
    font-size:2.5rem; margin-bottom:6px; opacity:0.4;
}}
.offline-msg {{
    color:#64748b; font-size:0.9rem; text-align:center; line-height:1.5;
}}
.offline-msg span {{
    font-size:0.75rem; color:#475569;
}}
@media (max-width:720px) {{
    .cams {{ flex-direction:column; }}
    header h1 {{ font-size:1.05rem; }}
    .ts-bar {{ padding:8px 12px; flex-direction:column; align-items:flex-start; gap:2px; }}
}}
</style>
</head>
<body>
<header>
    <h1>训练室监控</h1>
    <div class="live">每 15 分钟更新</div>
</header>
<div class="ts-bar">
    <span class="when">拍摄时间 {display_ts}</span>
    <span class="updated">页面生成 {now}</span>
</div>
<div class="cams">{cards_html}
</div>
</body>
</html>"""

    index_path = gallery_dir / "index.html"
    with open(index_path, "w", encoding="utf-8") as f:
        f.write(html)

    return 1  # always exactly 1 (latest) on the page


# ==================== Disk Cleanup ====================
def cleanup_old_captures(captures_dir, keep_last=KEEP_LAST_CAPTURES):
    """Keep only the last `keep_last` capture groups on disk; delete the rest.
    Keeps disk tiny even with frequent captures. Reports files removed."""
    if not captures_dir.exists():
        return 0
    groups = _group_captures(captures_dir)
    sorted_ts = sorted(groups.keys(), reverse=True)
    # Timestamps to KEEP (newest N)
    keep_ts = set(sorted_ts[:keep_last])
    removed = 0
    for ts, cams in groups.items():
        if ts in keep_ts:
            continue
        for img in cams.values():
            try:
                img.unlink()
                removed += 1
            except Exception:
                pass
    return removed


# ==================== Main Pipeline ====================
def run_capture(output_dir):
    """Capture images from all cameras and save to output_dir."""
    output_dir.mkdir(parents=True, exist_ok=True)
    client = HikIoTClient(APP_KEY, APP_SECRET)

    # Try cached token first
    user_token = None
    refresh_token = None
    cached = load_cached_tokens()
    if cached:
        print("[Token] Trying cached User-Access-Token...")
        try:
            app_token = client.get_app_token()
            test_r = client._api_call(
                "/device/direct/v1/captureImage/captureImage", "POST",
                {"deviceSerial": NVR_SERIAL, "payload": {"channelNo": 1}},
                headers={"App-Access-Token": app_token,
                         "User-Access-Token": cached["userAccessToken"]},
                encrypt_body=True, decrypt_response=True,
            )
            if test_r.get("code") == 0:
                user_token = cached["userAccessToken"]
                refresh_token = cached.get("refreshUserToken")
                print("[Token] Cached token works!")
            else:
                raise Exception(f"API error: {test_r}")
        except Exception as e:
            print(f"[Token] Cached token invalid: {e}")
            # Try refresh
            if cached.get("refreshUserToken"):
                try:
                    print("[Token] Trying refresh token...")
                    user_token = client.refresh_user_token(
                        cached["refreshUserToken"])
                    refresh_token = cached["refreshUserToken"]
                    print("[Token] Refresh succeeded!")
                except Exception as e2:
                    print(f"[Token] Refresh also failed: {e2}")

    # If still no token, do full OAuth
    if not user_token:
        print("[Token] Running full OAuth flow...")
        user_token, refresh_token = client.get_user_token()
        save_cached_tokens(user_token, refresh_token)
        print(f"[Token] Tokens cached to {TOKEN_CACHE}")

    # Capture from all cameras
    timestamp = beijing_now().strftime("%Y%m%d_%H%M%S")
    results = []
    for cam in CAMERAS:
        print(f"[Capture] {cam['name']} (channel={cam['channelNo']})...")
        # Retry up to 3 times on failure (API is occasionally flaky)
        last_error = None
        for attempt in range(1, 4):
            try:
                capture_url = client.capture_image(
                    user_token, NVR_SERIAL, cam["channelNo"])
                fname = f"{timestamp}_{cam['name']}.jpg"
                dest = output_dir / fname
                size = download_image(capture_url, str(dest))
                print(f"[Capture] Saved: {dest} ({size:,} bytes)")
                results.append({"name": cam["name"], "path": str(dest), "size": size})
                last_error = None
                break
            except Exception as e:
                last_error = e
                if attempt < 3:
                    print(f"[Capture] Retry {attempt}/3 {cam['name']}: {e}")
                    time.sleep(3)  # Wait a bit before retry
                else:
                    print(f"[Capture] ERROR (all 3 retries exhausted) {cam['name']}: {e}")
                    results.append({"name": cam["name"], "path": None, "error": str(e)})
        time.sleep(2)  # API rate limit between cameras

    return timestamp, results


def main():
    parser = argparse.ArgumentParser(
        description="Training room camera capture pipeline")
    parser.add_argument("--output", "-o", type=Path,
                        default=DEFAULT_OUTPUT,
                        help="Output directory for captured images")
    parser.add_argument("--gallery-only", action="store_true",
                        help="Only regenerate gallery HTML (no capture)")
    args = parser.parse_args()

    if not args.gallery_only:
        print("=" * 50)
        print(f"Training Room Camera Capture")
        print(f"Time: {beijing_now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 50)
        timestamp, results = run_capture(args.output)
        success = sum(1 for r in results if r.get("path"))
        print(f"\n{'=' * 50}")
        print(f"Captured {success}/{len(results)} images")
        for r in results:
            status = "OK" if r.get("path") else "FAIL"
            print(f"  [{status}] {r['name']}: {r.get('path', r.get('error', '?'))}")
        if success == 0:
            print("\nAll captures failed. Check credentials/network.")
            return 1

    # Clean up old captures to keep disk from filling
    removed = cleanup_old_captures(args.output)
    if removed:
        print(f"[Cleanup] Removed {removed} old image(s), kept latest {KEEP_LAST_CAPTURES} capture(s)")

    # Generate gallery
    print(f"\n[Gallery] Generating from {args.output}...")
    count = generate_gallery(args.output, GALLERY_DIR)
    print(f"[Gallery] {count} capture(s) indexed at {GALLERY_DIR}/index.html")
    print(f"[Gallery] Images dir: {GALLERY_DIR}")

    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:
        print(f"[FATAL] Unhandled exception: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)

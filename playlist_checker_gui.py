#!/usr/bin/env python3
"""
TV & Radio Playlist Checker  (GUI)
==================================
Open IPTV / internet-radio playlists (M3U, M3U8, PLS, XSPF) from files, folders
or a web address, and:

  * check every stream: online / offline
      - HTTP / HTTPS streams, HLS (.m3u8, checks the real video segment),
        Icecast / Shoutcast radio, RTMP / RTSP / MMS (server port check)
      - honours per-channel User-Agent / Referer (#EXTVLCOPT, url|User-Agent=...)
  * find duplicate channels (same stream URL, optionally same channel name)
  * manage groups (group-title): include/exclude, rename, merge, reorder
  * rename channels, move them between groups, delete them, play them in VLC
  * save a NEW clean playlist - tvg-id, tvg-logo, EPG url (url-tvg) and
    #EXTVLCOPT options are kept - or one playlist per group
  * export a CSV report of the check
  * Settings menu: hide hidden files/folders, add the date to saved file names,
    right-to-left text fix (Hebrew / Arabic on Linux), add the app (with its icon)
    to the Linux application menu or desktop

Requires Python 3.9+ only (tkinter is included in the normal Windows / macOS
Python installers; on Linux install the "python3-tk" package).

Run:   python playlist_checker_gui.py            (or double-click it on Windows)
       python playlist_checker_gui.py tv.m3u radio.pls
"""
from __future__ import annotations

import base64
import csv
import http.client
import json
import locale
import os
import queue
import re
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import date
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path

import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog, ttk

APP_TITLE = "TV & Radio Playlist Checker"
APP_VERSION = "1.3.3"
PROJECT_URL = "https://github.com/antoxa78/PyPlaylist-Checker"
DEFAULT_UA = "VLC/3.0.20 LibVLC/3.0.20"
# Settings -> User-Agent. Some IPTV providers only answer certain players/apps.
# (section title, [(name, User-Agent string), ...])
USER_AGENTS = [
    ("Media players", [
        ("VLC", DEFAULT_UA),
        ("FFmpeg / ffplay", "Lavf/61.7.100"),
        ("mpv", "libmpv"),
        ("Kodi", "Kodi/21.1 (X11; Linux x86_64) App_Bitness/64 Version/21.1-(21.1.0)-Git:20240831-0bd4c4fe7c"),
        ("GStreamer (Totem, Rhythmbox)", "GStreamer souphttpsrc 1.24.2 libsoup/3.4.4"),
    ]),
    ("Android", [
        ("ExoPlayer", "ExoPlayerLib/2.19.1"),
        ("Media3 ExoPlayer (new Android apps)", "androidx.media3.exoplayer/1.4.1"),
        ("Android MediaPlayer", "stagefright/1.2 (Linux;Android 13)"),
        ("TiviMate", "TiviMate/5.1.6 (Android 12)"),
        ("IPTV Smarters", "IPTVSmartersPlayer"),
        ("OTT Navigator", "OTT Navigator/1.7.1.4 (Linux;Android 12) ExoPlayerLib/2.19.1"),
    ]),
    ("Smart TV and receivers", [
        ("Samsung Smart TV (Tizen)", "Mozilla/5.0 (SMART-TV; LINUX; Tizen 7.0) AppleWebKit/537.36 "
                                     "(KHTML, like Gecko) 94.0.4606.31/7.0 TV Safari/537.36"),
        ("LG Smart TV (webOS)", "Mozilla/5.0 (Web0S; Linux/SmartTV) AppleWebKit/537.36 (KHTML, like Gecko) "
                                "Chrome/87.0.4280.88 Safari/537.36 WebAppManager"),
        ("Enigma2 receiver", "Enigma2 HbbTV/1.1.1 (+PVR+RTSP+DL;OpenATV;;;)"),
        ("Apple TV / iPhone (AVPlayer)", "AppleCoreMedia/1.0.0.21G93 (iPhone; U; CPU OS 17_6 like Mac OS X; en_us)"),
    ]),
    ("Web browsers", [
        ("Chrome (Windows)", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                             "Chrome/130.0.0.0 Safari/537.36"),
        ("Firefox (Linux)", "Mozilla/5.0 (X11; Linux x86_64; rv:131.0) Gecko/20100101 Firefox/131.0"),
    ]),
]


def user_agent_name(ua: str) -> str:
    for _, items in USER_AGENTS:
        for name, value in items:
            if value == ua:
                return name
    return "custom"
CONFIG_DIR = Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config") / "playlist-checker"
SETTINGS_FILE = CONFIG_DIR / "settings.json"
OLD_SETTINGS_FILE = Path.home() / ".playlist_checker_gui.json"  # used by earlier versions
# installed as a system package (deb) -> the menu entry already exists
INSTALLED = str(Path(__file__).resolve()).startswith(("/usr/", "/opt/"))
LEGACY_ENCODINGS = [("auto", "Auto-detect"), ("cp1255", "Hebrew (Windows-1255)"),
                    ("cp1251", "Cyrillic (Windows-1251)"), ("cp1256", "Arabic (Windows-1256)"),
                    ("cp1252", "Western European (Windows-1252)")]
PLAYLIST_EXT = (".m3u", ".m3u8", ".pls", ".xspf")
NO_GROUP = "(no group)"
LAUNCHER_ID = "playlist-checker"
# physical key codes of A, C, V, X: Ctrl+C/V/X/A must also work while a Hebrew or
# Russian keyboard layout is active (Tk on Linux sees "hebrew_bet", not "c")
KEYCODE_LETTERS = {"x11": {38: "a", 54: "c", 55: "v", 53: "x"},
                   "win32": {65: "a", 67: "c", 86: "v", 88: "x"}}
TEXT_FIELD_CLASSES = ("Entry", "TEntry", "TCombobox", "Spinbox", "TSpinbox")
STREAM_URL_RE = re.compile(r"^\s*(?:https?|rtmpe?|rtmps|rtmpt|rtsps?|mmsh?|mmst|udp|rtp|srt)://\S+", re.I)

ONLINE, OFFLINE, UNCHECKED, CHECKING = "online", "offline", "unchecked", "checking"
STATUS_TEXT = {ONLINE: "● Online", OFFLINE: "✖ Offline", UNCHECKED: "○ Not checked", CHECKING: "… Checking"}
STATUS_RANK = {ONLINE: 0, UNCHECKED: 1, CHECKING: 1, OFFLINE: 2}

TCP_PORTS = {"rtmp": 1935, "rtmpe": 1935, "rtmpt": 80, "rtmps": 443, "rtsp": 554, "rtsps": 322,
             "mms": 1755, "mmst": 1755, "mmsh": 80}
NOT_CHECKABLE = {"udp", "rtp", "igmp", "srt", "acestream", "magnet", "p2p", "sop"}

SHOW_OPTIONS = ["All", "Online", "Offline", "Not checked", "Duplicates",
                "Problems (offline + duplicates)", "Good (online, unique)",
                "Included (will be saved)", "Excluded (unticked)"]

ATTR_RE = re.compile(r'([A-Za-z0-9_\-:.]+)\s*=\s*(?:"([^"]*)"|\'([^\']*)\'|([^\s"\',]+))')
QUALITY_RE = re.compile(r"\b(?:uhd|fhd|hd|sd|hq|lq|4k|8k|hevc|h\.?26[45]|\d{3,4}p|\d{2}\s?fps|backup|orig(?:inal)?)\b", re.I)
BAD_FILENAME_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')


# =============================================================================
#  Data model and playlist reading
# =============================================================================

@dataclass
class Channel:
    name: str
    url: str
    group: str = ""
    duration: str = "-1"
    attrs: dict = field(default_factory=dict)    # tvg-id, tvg-logo, group-title ...
    extra: list = field(default_factory=list)    # #EXTVLCOPT / #KODIPROP lines
    source: str = ""                             # playlist file or URL it came from
    base_dir: str = ""                           # for relative local paths
    uid: int = 0
    status: str = UNCHECKED
    info: str = ""
    latency: int | None = None
    dup_of: int | None = None
    dup_reason: str = ""

    def http_options(self) -> tuple[str | None, str | None]:
        """User-Agent and Referer the playlist asks for, if any."""
        ua = ref = None
        for line in self.extra:
            low = line.lower()
            if low.startswith("#extvlcopt:http-user-agent="):
                ua = line.split("=", 1)[1].strip()
            elif low.startswith(("#extvlcopt:http-referrer=", "#extvlcopt:http-referer=")):
                ref = line.split("=", 1)[1].strip()
        ua = ua or self.attrs.get("user-agent") or self.attrs.get("http-user-agent")
        ref = ref or self.attrs.get("http-referrer") or self.attrs.get("http-referer") or self.attrs.get("referer")
        return ua, ref

    def export_url(self) -> str:
        """URL for saving; relative local paths become absolute so the new playlist works anywhere."""
        u = self.url
        if is_local(u) and not os.path.isabs(u) and self.base_dir:
            return os.path.normpath(os.path.join(self.base_dir, u))
        return u


def is_local(url: str) -> bool:
    if re.match(r"^[a-zA-Z]:[\\/]", url) or url.startswith(("\\\\", "/", "~")):
        return True
    return "://" not in url and not url.lower().startswith("file:")


def guess_legacy_encoding(data: bytes) -> str:
    """Old (non-UTF-8) playlists: tell Hebrew, Cyrillic and Western Windows code pages apart."""
    high = [b for b in data if b >= 0x80]
    if not high:
        return "cp1252"
    n = len(high)
    hebrew_letters = sum(0xE0 <= b <= 0xFA for b in high)
    cyr_upper = sum(0xC0 <= b <= 0xDF for b in high)
    cyr_only = sum(b >= 0xFB for b in high)            # ы ь э ю я - unused in Hebrew
    letters_in_runs = len(re.findall(rb"[\xc0-\xff]{3,}", data))  # whole words of non-Latin letters
    if letters_in_runs and hebrew_letters / n > 0.85 and cyr_upper / n < 0.05 and not cyr_only:
        return "cp1255"
    if letters_in_runs and sum(b >= 0xC0 for b in high) / n > 0.85:
        return "cp1251"
    return "cp1252"


def decode_bytes(data: bytes, legacy: str = "auto") -> str:
    """UTF-8 first (the normal case); otherwise the chosen or detected Windows code page."""
    try:
        return data.decode("utf-8-sig")
    except UnicodeDecodeError:
        pass
    candidates = []
    if legacy and legacy != "auto":
        candidates.append(legacy)
    sys_enc = (locale.getpreferredencoding(False) or "").lower()
    if sys_enc and "utf" not in sys_enc:
        candidates.append(sys_enc)            # e.g. Windows set to Hebrew -> cp1255
    candidates += [guess_legacy_encoding(data), "cp1252", "latin-1"]
    for enc in candidates:
        try:
            return data.decode(enc).lstrip("\ufeff")
        except (UnicodeDecodeError, LookupError):
            continue
    return data.decode("utf-8", "replace")


def parse_attrs(text: str) -> dict:
    out = {}
    for m in ATTR_RE.finditer(text):
        val = next((g for g in m.groups()[1:] if g is not None), "")
        out[m.group(1)] = val
    return out


def split_extinf(body: str) -> tuple[str, str]:
    """Split '#EXTINF:' body into (duration+attributes, channel name) - commas inside quotes are ignored."""
    in_quotes = False
    for i, ch in enumerate(body):
        if ch == '"':
            in_quotes = not in_quotes
        elif ch == "," and not in_quotes:
            return body[:i], body[i + 1:].strip()
    return body, ""


def name_from_url(url: str) -> str:
    p = urllib.parse.urlparse(url.split("|", 1)[0])
    stem = Path(urllib.parse.unquote(p.path)).stem
    return stem or p.netloc or url


def parse_m3u(text: str, source: str, base_dir: str) -> tuple[dict, list[Channel]]:
    header: dict = {}
    channels: list[Channel] = []
    pending = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        upper = line.upper()
        if upper.startswith("#EXTM3U"):
            for k, v in parse_attrs(line[7:]).items():
                header.setdefault(k, v)
            continue
        if line.startswith("#"):
            if pending is None:
                pending = {"name": "", "duration": "-1", "attrs": {}, "group": "", "extra": []}
            if upper.startswith("#EXTINF"):
                head, name = split_extinf(line.partition(":")[2])
                m = re.match(r"\s*(-?\d+(?:\.\d+)?)", head)
                pending["duration"] = m.group(1) if m else "-1"
                pending["attrs"] = parse_attrs(head)
                pending["name"] = name
                if pending["attrs"].get("group-title", "").strip():
                    pending["group"] = pending["attrs"]["group-title"].strip()
            elif upper.startswith("#EXTGRP:"):
                if not pending["group"]:
                    pending["group"] = line[8:].strip()
            elif upper.startswith(("#EXTVLCOPT", "#KODIPROP", "#EXTHTTP")):
                pending["extra"].append(line)
            continue
        p = pending or {"name": "", "duration": "-1", "attrs": {}, "group": "", "extra": []}
        channels.append(Channel(name=p["name"] or name_from_url(line), url=line, group=p["group"],
                                duration=p["duration"], attrs=p["attrs"], extra=p["extra"],
                                source=source, base_dir=base_dir))
        pending = None
    return header, channels


def parse_pls(text: str, source: str, base_dir: str) -> list[Channel]:
    entries: dict[int, dict] = defaultdict(dict)
    for raw in text.splitlines():
        m = re.match(r"\s*(File|Title|Length)(\d+)\s*=\s*(.*)", raw, re.I)
        if m:
            entries[int(m.group(2))][m.group(1).lower()] = m.group(3).strip()
    out = []
    for idx in sorted(entries):
        e = entries[idx]
        if e.get("file"):
            out.append(Channel(name=e.get("title") or name_from_url(e["file"]), url=e["file"],
                               source=source, base_dir=base_dir))
    return out


def parse_xspf(text: str, source: str, base_dir: str) -> list[Channel]:
    text = re.sub(r"^\s*<\?xml[^>]*\?>", "", text.lstrip("\ufeff"))
    root = ET.fromstring(text)
    local = lambda tag: tag.rsplit("}", 1)[-1]
    out = []
    for el in root.iter():
        if local(el.tag) != "track":
            continue
        info = {local(c.tag): (c.text or "").strip() for c in el}
        loc = info.get("location")
        if not loc:
            continue
        if loc.lower().startswith("file:"):
            loc = urllib.request.url2pathname(urllib.parse.urlparse(loc).path)
        name = info.get("title") or name_from_url(loc)
        if info.get("title") and info.get("creator"):
            name = f"{info['creator']} - {info['title']}"
        out.append(Channel(name=name, url=loc, source=source, base_dir=base_dir))
    return out


def parse_playlist(text: str, source: str, base_dir: str = "") -> tuple[dict, list[Channel]]:
    start = text.lstrip("\ufeff \t\r\n")[:300].lower()
    if start.startswith("[playlist]") or source.lower().endswith(".pls"):
        return {}, parse_pls(text, source, base_dir)
    if start.startswith("<?xml") or start.startswith("<playlist") or source.lower().endswith(".xspf"):
        return {}, parse_xspf(text, source, base_dir)
    return parse_m3u(text, source, base_dir)


# =============================================================================
#  Right-to-left text (Hebrew / Arabic)
# =============================================================================
# Tk on Linux draws text strictly left-to-right, so Hebrew comes out backwards.
# bidi_visual() reorders a string into "visual" order (a compact version of the
# Unicode Bidirectional Algorithm) - used ONLY for what is shown on screen;
# the playlist data and saved files always keep the normal (logical) text.

RTL_RE = re.compile("[\u0590-\u08ff\ufb1d-\ufdff\ufe70-\ufeff]")
MIRROR = str.maketrans("()[]{}<>«»", ")(][}{><»«")
BIDI = {"enabled": False}


def bidi_visual(text: str) -> str:
    if not text or not RTL_RE.search(text):
        return text
    if "\n" in text:
        return "\n".join(bidi_visual(line) for line in text.split("\n"))
    types = [unicodedata.bidirectional(ch) for ch in text]
    n = len(text)
    base = next((0 if t == "L" else 1 for t in types if t in ("L", "R", "AL")), 0)

    cls = []  # L, R, '#' (number) or N (neutral)
    for i, t in enumerate(types):
        if t in ("R", "AL"):
            cls.append("R")
        elif t == "L":
            cls.append("L")
        elif t in ("EN", "AN"):
            cls.append("#")
        elif t == "NSM" and i:
            cls.append(cls[-1])
        else:
            cls.append("N")
    for i in range(1, n - 1):  # 1,000 / 103.5 / 10-12 stay one number
        if cls[i] == "N" and types[i] in ("CS", "ES") and cls[i - 1] == "#" and cls[i + 1] == "#":
            cls[i] = "#"
    for i in range(n):  # $5, 50%
        if types[i] == "ET" and ((i and cls[i - 1] == "#") or (i + 1 < n and cls[i + 1] == "#")):
            cls[i] = "#"
    last_strong = "L" if base == 0 else "R"
    for i in range(n):  # numbers after Latin text are Latin
        if cls[i] in ("L", "R"):
            last_strong = cls[i]
        elif cls[i] == "#" and last_strong == "L":
            cls[i] = "L"
    i = 0
    while i < n:  # neutrals take the direction around them, else the paragraph direction
        if cls[i] != "N":
            i += 1
            continue
        j = i
        while j < n and cls[j] == "N":
            j += 1
        left = ("R" if cls[i - 1] == "#" else cls[i - 1]) if i else ("L" if base == 0 else "R")
        right = ("R" if cls[j] == "#" else cls[j]) if j < n else ("L" if base == 0 else "R")
        fill = left if left == right else ("L" if base == 0 else "R")
        for k in range(i, j):
            cls[k] = fill
        i = j

    if base == 0:
        levels = [0 if c == "L" else 1 if c == "R" else 2 for c in cls]
    else:
        levels = [1 if c == "R" else 2 for c in cls]
    chars = [ch.translate(MIRROR) if lv % 2 else ch for ch, lv in zip(text, levels)]
    for lvl in range(max(levels), 0, -1):
        i = 0
        while i < n:
            if levels[i] >= lvl:
                j = i
                while j < n and levels[j] >= lvl:
                    j += 1
                chars[i:j] = chars[i:j][::-1]
                levels[i:j] = levels[i:j][::-1]
                i = j
            else:
                i += 1
    return "".join(chars)


def vis(text) -> str:
    """Text for display: reordered for right-to-left scripts when the fix is on."""
    text = "" if text is None else str(text)
    return bidi_visual(text) if BIDI["enabled"] else text


def _wrap_messagebox():
    """Message boxes are drawn by Tk on Linux too - show their text in visual order."""
    for name in ("showinfo", "showwarning", "showerror", "askyesno", "askokcancel"):
        orig = getattr(messagebox, name)

        def wrapped(title=None, message=None, _orig=orig, **kw):
            return _orig(title, vis(message) if message else message, **kw)
        setattr(messagebox, name, wrapped)


_wrap_messagebox()


# =============================================================================
#  Stream checking
# =============================================================================

def split_url_headers(url: str) -> tuple[str, dict]:
    """Kodi style 'http://host/stream|User-Agent=abc&Referer=xyz'."""
    if "|" not in url:
        return url, {}
    base, _, rest = url.partition("|")
    headers = {}
    for part in rest.split("&"):
        k, _, v = part.partition("=")
        if k.strip():
            headers[urllib.parse.unquote(k.strip())] = urllib.parse.unquote(v.strip())
    return base, headers


def short_error(err) -> str:
    text = str(getattr(err, "reason", err) or err.__class__.__name__)
    text = re.sub(r"^\[Errno -?\d+\]\s*", "", text)
    text = re.sub(r"^<urlopen error (.*)>$", r"\1", text)
    low = text.lower()
    if "name or service not known" in low or "getaddrinfo failed" in low or "nodename nor servname" in low:
        return "server not found (DNS)"
    if "refused" in low:
        return "connection refused"
    if "timed out" in low:
        return "timeout"
    return text[:80]


def read_some(resp, limit: int, deadline: float) -> bytes:
    """Read up to `limit` bytes, but stop at `deadline` - a server that sends data
    very slowly can't hold one channel's check for minutes."""
    buf = b""
    read = getattr(resp, "read1", resp.read)
    try:
        while len(buf) < limit and time.monotonic() < deadline:
            chunk = read(min(65536, limit - len(buf)))
            if not chunk:
                break
            buf += chunk
    except (socket.timeout, TimeoutError, OSError, http.client.HTTPException):
        if not buf:
            raise
    return buf


# ---------------------------------------------------------------- playlist downloads / URL lists
DOWNLOAD_PARALLEL = 4
URL_IN_LINE_RE = re.compile(r"([a-z][a-z0-9+.\-]*://[^\s\"'<>]+)", re.I)


def looks_like_playlist_text(text: str) -> bool:
    head = text.lstrip("\ufeff \t\r\n")[:2000].upper()
    return head.startswith("#EXTM3U") or "#EXTINF" in head or head.startswith("[PLAYLIST]")


def parse_url_list(text: str, base_dir: Path) -> tuple[list[str], list[str], list[Path]]:
    """A .txt list: one address per line; empty lines and lines starting with # ; // are ignored.
    Returns (web addresses to download, direct stream links, local playlist files)."""
    web, streams, local, seen = [], [], [], set()
    for raw in text.splitlines():
        line = raw.strip().lstrip("\ufeff")
        if not line or line.startswith(("#", ";", "//")):
            continue
        m = URL_IN_LINE_RE.search(line)
        if m:
            url = m.group(1).rstrip(".,;)")
            if url in seen:
                continue
            seen.add(url)
            if url.lower().startswith(("http://", "https://")):
                web.append(url)
            elif STREAM_URL_RE.match(url):
                streams.append(url)
            continue
        p = Path(os.path.expanduser(line))
        if not p.is_absolute():
            p = base_dir / p
        if p.suffix.lower() in PLAYLIST_EXT and p.is_file() and str(p) not in seen:
            seen.add(str(p))
            local.append(p)
    return web, streams, local


def classify_download(head: bytes, ctype: str) -> str:
    """What a web address returned: 'playlist', 'stream' (one TV/radio channel) or 'page'."""
    h = head.lstrip(b"\xef\xbb\xbf \t\r\n")
    low = h[:300].lower()
    if h.startswith(b"#EXTM3U") or h.startswith(b"#EXTINF"):
        # an HLS stream (one channel) also starts with #EXTM3U, but uses #EXT-X- tags
        if re.search(rb"#EXT-X-(TARGETDURATION|STREAM-INF|MEDIA-SEQUENCE|VERSION|KEY|MAP)", head):
            return "stream"
        return "playlist"
    if low.startswith(b"[playlist]") or low.startswith(b"<playlist") or (low.startswith(b"<?xml") and b"<playlist" in low):
        return "playlist"
    if low.startswith((b"<!doctype html", b"<html")) or ctype.startswith("text/html"):
        return "page"
    if ctype.startswith(("audio/", "video/")) and not any(t in ctype for t in ("mpegurl", "scpls", "xspf")):
        return "stream"
    if b"\x00" in head:
        return "stream"  # binary data: a stream, not a text playlist
    return "playlist"    # plain text, e.g. a simple list of stream links


def fetch_playlist(url: str, ua: str, ignore_ssl: bool, legacy: str, timeout: float = 40,
                   max_seconds: float = 300, max_bytes: int = 100 * 1024 * 1024) -> tuple[str, str]:
    """Download a playlist. Returns (kind, text): kind 'playlist' with its text, 'stream' or 'page'.
    A live stream is recognised from its first bytes and not downloaded."""
    ctx = ssl.create_default_context()
    if ignore_ssl:
        ctx.check_hostname, ctx.verify_mode = False, ssl.CERT_NONE
    opener = urllib.request.build_opener(urllib.request.HTTPSHandler(context=ctx))
    req = urllib.request.Request(url, headers={"User-Agent": ua or DEFAULT_UA, "Accept": "*/*"})
    with opener.open(req, timeout=timeout) as r:
        ctype = (r.headers.get("Content-Type") or "").split(";")[0].strip().lower()
        start = time.monotonic()
        head = read_some(r, 4096, start + timeout)
        kind = classify_download(head, ctype)
        if kind != "playlist":
            return kind, ""
        data = head + read_some(r, max_bytes, start + max_seconds)
    return "playlist", decode_bytes(data, legacy)


class StreamChecker:
    def __init__(self, timeout: float, user_agent: str, deep_hls: bool, ignore_ssl: bool):
        self.timeout = timeout
        self.ua = user_agent or DEFAULT_UA
        self.deep = deep_hls
        self.ctx = ssl.create_default_context()
        if ignore_ssl:
            self.ctx.check_hostname = False
            self.ctx.verify_mode = ssl.CERT_NONE

    def check(self, url: str, base_dir: str = "", ua: str | None = None, referer: str | None = None):
        """Returns (status, info, milliseconds)."""
        t0 = time.monotonic()
        try:
            status, info = self._check(url.strip(), base_dir, ua, referer)
        except Exception as e:  # never let one channel stop the whole check
            status, info = OFFLINE, f"error: {short_error(e)}"
        return status, info, int((time.monotonic() - t0) * 1000)

    def _check(self, url, base_dir, ua, referer):
        if is_local(url):
            return self._local(url, base_dir)
        url, extra_headers = split_url_headers(url)
        p = urllib.parse.urlparse(url)
        scheme = p.scheme.lower()
        if scheme == "file":
            return self._local(urllib.request.url2pathname(p.path), base_dir)
        if scheme in ("http", "https"):
            headers = {"User-Agent": ua or self.ua, "Accept": "*/*", "Icy-MetaData": "1"}
            if referer:
                headers["Referer"] = referer
            headers.update(extra_headers)
            return self._http(url, headers, 0)
        if scheme in TCP_PORTS:
            return self._tcp(p, scheme)
        if scheme in NOT_CHECKABLE:
            return UNCHECKED, f"{scheme}:// links can't be checked from here"
        return UNCHECKED, f"unsupported link type ({scheme or '?'})"

    def _local(self, path, base_dir):
        p = os.path.expanduser(path)
        if not os.path.isabs(p) and base_dir:
            p = os.path.join(base_dir, p)
        return (ONLINE, "local file found") if os.path.isfile(p) else (OFFLINE, "local file not found")

    def _tcp(self, p, scheme):
        port = p.port or TCP_PORTS[scheme]
        try:
            with socket.create_connection((p.hostname, port), timeout=self.timeout):
                return ONLINE, f"{scheme.upper()} server answers (port {port})"
        except socket.gaierror:
            return OFFLINE, "server not found (DNS)"
        except (socket.timeout, TimeoutError):
            return OFFLINE, "timeout"
        except OSError as e:
            return OFFLINE, short_error(e)

    def _http(self, url, headers, depth):
        opener = urllib.request.build_opener(urllib.request.HTTPSHandler(context=self.ctx))
        req = urllib.request.Request(url, headers=headers)
        try:
            with opener.open(req, timeout=self.timeout) as r:
                code = r.status
                ctype = (r.headers.get("Content-Type") or "").split(";")[0].strip().lower()
                final_url = r.geturl()
                deadline = time.monotonic() + self.timeout
                data = read_some(r, 2048, deadline)
                is_hls = data.lstrip(b"\xef\xbb\xbf \t\r\n").startswith(b"#EXTM3U")
                if is_hls:
                    data += read_some(r, 1024 * 1024, deadline)  # rest of the HLS playlist
        except urllib.error.HTTPError as e:
            return OFFLINE, f"HTTP {e.code} {e.reason}".strip()
        except http.client.BadStatusLine as e:
            line = str(getattr(e, "line", e)).strip()
            if line.upper().startswith("ICY 200"):
                return ONLINE, "ICY 200 (Shoutcast radio)"
            if isinstance(e, http.client.RemoteDisconnected):
                return OFFLINE, "server closed the connection"
            return OFFLINE, f"bad answer: {line[:40]}"
        except urllib.error.URLError as e:
            if isinstance(e.reason, (socket.timeout, TimeoutError)):
                return OFFLINE, "timeout"
            if isinstance(e.reason, ssl.SSLError):
                return OFFLINE, "SSL error (try 'Ignore SSL errors')"
            return OFFLINE, short_error(e)
        except (socket.timeout, TimeoutError):
            return OFFLINE, "timeout (no data)"
        except (OSError, http.client.HTTPException) as e:
            return OFFLINE, short_error(e)

        if is_hls:
            text = data.decode("utf-8", "ignore")
            uris = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.strip().startswith("#")]
            if not uris:
                return OFFLINE, f"HTTP {code} · HLS playlist is empty"
            if not self.deep or depth >= 3:
                return ONLINE, f"HTTP {code} · HLS playlist"
            # master playlist -> first quality variant; media playlist -> newest segment
            nxt = uris[0] if "#EXT-X-STREAM-INF" in text else uris[-1]
            status, info = self._http(urllib.parse.urljoin(final_url, nxt), headers, depth + 1)
            if info.startswith("HLS"):
                return status, info
            return status, ("HLS · " if status == ONLINE else "HLS segment: ") + info

        if not data:
            return OFFLINE, f"HTTP {code} · empty answer"
        if ctype.startswith("text/html") or data.lstrip()[:20].lower().startswith((b"<!doctype html", b"<html")):
            return OFFLINE, f"HTTP {code} · web page, not a stream"
        return ONLINE, f"HTTP {code}" + (f" · {ctype}" if ctype else "")


# =============================================================================
#  Duplicates, sorting, saving
# =============================================================================

def norm_url(url: str) -> str:
    u = url.strip().split("|", 1)[0]
    p = urllib.parse.urlsplit(u)
    if p.scheme and p.netloc:
        u = urllib.parse.urlunsplit((p.scheme.lower(), p.netloc.lower(), p.path, p.query, ""))
    return u.rstrip("/")


def norm_name(name: str, ignore_quality: bool) -> str:
    s = name.casefold()
    if ignore_quality:
        s = QUALITY_RE.sub(" ", s)
        s = re.sub(r"[\(\[\{]\s*[\)\]\}]", " ", s)
    return re.sub(r"[\W_]+", " ", s).strip()


def find_duplicates(channels: list[Channel], by_url: bool, by_name: bool,
                    ignore_quality: bool) -> dict[int, tuple[int, str]]:
    """{uid of duplicate: (uid of the copy that is kept, reason)}.
    The copy that is kept: online first, then the one that appears first."""
    dups: dict[int, tuple[int, str]] = {}

    def run(keyfunc, reason):
        buckets = defaultdict(list)
        for idx, c in enumerate(channels):
            if c.uid not in dups:
                k = keyfunc(c)
                if k:
                    buckets[k].append((STATUS_RANK.get(c.status, 1), idx, c))
        for items in buckets.values():
            if len(items) > 1:
                items.sort(key=lambda x: (x[0], x[1]))
                keep = items[0][2]
                for _, _, c in items[1:]:
                    dups[c.uid] = (keep.uid, reason)

    if by_url:
        run(lambda c: norm_url(c.url), "same URL")
    if by_name:
        run(lambda c: norm_name(c.name, ignore_quality), "same name")
    return dups


def mark_duplicates(channels: list[Channel], by_url: bool, by_name: bool, ignore_quality: bool) -> None:
    dups = find_duplicates(channels, by_url, by_name, ignore_quality)
    for c in channels:
        c.dup_of, c.dup_reason = dups.get(c.uid, (None, ""))


def natural_key(s: str):
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s.casefold())]


def attrs_to_str(attrs: dict) -> str:
    return "".join(f' {k}="{str(v).replace(chr(34), chr(39))}"' for k, v in attrs.items())


def write_m3u(path: str, items: list[Channel], header: dict) -> None:
    lines = ["#EXTM3U" + attrs_to_str(header)]
    for c in items:
        attrs = dict(c.attrs)
        if c.group:
            attrs["group-title"] = c.group
        else:
            attrs.pop("group-title", None)
        lines.append(f"#EXTINF:{c.duration}{attrs_to_str(attrs)},{c.name}")
        lines.extend(c.extra)
        lines.append(c.export_url())
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_pls(path: str, items: list[Channel]) -> None:
    lines = ["[playlist]"]
    for i, c in enumerate(items, 1):
        lines += [f"File{i}={c.export_url()}", f"Title{i}={c.name}", f"Length{i}=-1"]
    lines += [f"NumberOfEntries={len(items)}", "Version=2"]
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")


FILE_PREFIX = "Playlist Checker"


def dated_name(base: str, ext: str, with_date: bool, with_prefix: bool = False, suffix: str = "") -> str:
    """'tv' -> 'Playlist Checker_tv_2026-10-23.m3u8'.
    A date and prefix already in the name (a file saved by this program earlier) are replaced,
    so they never pile up."""
    base = re.sub(r"[ _-]*\d{4}-\d{2}-\d{2}$", "", base)
    base = re.sub(r"^\s*playlist[ _-]?checker(?=$|[ _-])[ _-]*", "", base, flags=re.I)
    base = base.strip(" _-")
    if not base and not with_prefix:
        base = "playlist"
    parts = ([FILE_PREFIX] if with_prefix else []) + ([base] if base else []) + ([suffix] if suffix else [])
    if with_date:
        parts.append(date.today().isoformat())
    return "_".join(parts) + f".{ext}"


# one color per playlist: (strong color for the square, light tint for the row)
PLAYLIST_COLORS = [("#1f77b4", "#e4eef8"), ("#ff7f0e", "#fdeedd"), ("#2ca02c", "#e2f2e2"), ("#d62728", "#f9e2e2"),
                   ("#9467bd", "#eee7f6"), ("#8c564b", "#f1e8e5"), ("#e377c2", "#fbe8f4"), ("#17becf", "#ddf4f7"),
                   ("#bcbd22", "#f4f4d8"), ("#393b79", "#e3e4f1"), ("#7f7f7f", "#ededed"), ("#637939", "#eaefe0")]


def playlist_labels(sources) -> dict:
    """Short, unique display names for playlist sources (file names; host added when two are alike)."""
    def short(src):
        if src == "clipboard":
            return "Pasted from clipboard"
        return short_source(src) or src
    base = {s: short(s) for s in sources}
    counts = defaultdict(int)
    for b in base.values():
        counts[b] += 1
    out = {}
    for s, b in base.items():
        if counts[b] > 1:
            where = urllib.parse.urlparse(s).netloc if "://" in s else Path(s).parent.name
            b = f"{b} ({where})"
        out[s] = b
    return out


def safe_filename(name: str) -> str:
    name = BAD_FILENAME_CHARS.sub("_", name).strip(" .")
    return (name or "No group")[:100]


def short_source(src: str) -> str:
    if "://" in src:
        p = urllib.parse.urlparse(src)
        return (Path(p.path).name or p.netloc)[:40]
    return Path(src).name


def find_player() -> str | None:
    cands = [shutil.which("vlc"), shutil.which("mpv")]
    if sys.platform.startswith("win"):
        for base in (os.environ.get("ProgramFiles", r"C:\Program Files"),
                     os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")):
            cands.append(os.path.join(base, "VideoLAN", "VLC", "vlc.exe"))
    elif sys.platform == "darwin":
        cands.append("/Applications/VLC.app/Contents/MacOS/VLC")
    return next((c for c in cands if c and os.path.isfile(c)), None)


def is_hidden(path: Path) -> bool:
    """Dot-files on Linux/macOS, plus files with the 'hidden' attribute on Windows."""
    if path.name.startswith("."):
        return True
    if sys.platform.startswith("win"):
        try:
            return bool(os.stat(path).st_file_attributes & 2)  # FILE_ATTRIBUTE_HIDDEN
        except (OSError, AttributeError):
            return False
    return False


def find_playlists(folder: Path, skip_hidden: bool) -> list[Path]:
    found = []
    for root, dirs, files in os.walk(folder):
        if skip_hidden:
            dirs[:] = [d for d in dirs if not is_hidden(Path(root) / d)]
        dirs.sort(key=str.casefold)
        for name in sorted(files, key=str.casefold):
            p = Path(root) / name
            if p.suffix.lower() in PLAYLIST_EXT and not (skip_hidden and is_hidden(p)):
                found.append(p)
    return found


def desktop_quote(arg: str) -> str:
    """Quote one argument for the Exec= line of a .desktop file."""
    if arg and not re.search(r'[\s"`$\\\'<>~|&;*?#()]', arg):
        return arg
    return '"' + re.sub(r'(["`$\\])', r'\\\1', arg) + '"'


def load_settings() -> dict:
    for f in (SETTINGS_FILE, OLD_SETTINGS_FILE):
        try:
            data = json.loads(f.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
        except Exception:
            continue
    return {}


# =============================================================================
#  Dialogs
# =============================================================================

class ComboDialog(simpledialog.Dialog):
    """Ask for a value with a drop-down of existing values (groups)."""

    def __init__(self, parent, title, prompt, values, initial=""):
        self.prompt, self.values, self.initial, self.result = prompt, values, initial, None
        super().__init__(parent, title)

    def body(self, master):
        ttk.Label(master, text=vis(self.prompt)).pack(anchor="w", padx=6, pady=(6, 2))
        self.var = tk.StringVar(value=self.initial)
        self.to_logical = {vis(v): v for v in self.values}
        if vis(self.initial) != self.initial:
            self.var.set(vis(self.initial))
        cb = ttk.Combobox(master, textvariable=self.var, values=list(self.to_logical), width=45)
        cb.pack(fill="x", padx=6, pady=(2, 6))
        return cb

    def apply(self):
        value = self.var.get().strip()
        self.result = self.to_logical.get(value, value)


class ExportDialog(simpledialog.Dialog):
    OPTIONS = [
        ("drop_offline", "Remove offline channels", True),
        ("drop_dups", "Remove duplicates", True),
        ("drop_unchecked", "Remove channels that were not checked", False),
        ("only_enabled_groups", "Only groups and playlists ticked ☑ on the left", True),
        ("sort_groups", "Sort groups A-Z  (otherwise: order of the group list)", False),
        ("sort_channels", "Sort channels A-Z inside each group  (otherwise: original order)", False),
        ("split", "Save one playlist file per group (into a folder)", False),
    ]

    def __init__(self, parent, summary, saved):
        self.summary, self.saved, self.result = summary, saved or {}, None
        super().__init__(parent, "Save new playlist")

    def body(self, master):
        bold = tkfont.nametofont("TkDefaultFont").copy()
        bold.configure(weight="bold")
        self._bold = bold
        ttk.Label(master, text=self.summary, font=bold).grid(
            row=0, column=0, sticky="w", padx=8, pady=(8, 6))
        self.vars = {}
        for r, (key, text, default) in enumerate(self.OPTIONS, 1):
            self.vars[key] = tk.BooleanVar(value=self.saved.get(key, default))
            ttk.Checkbutton(master, text=text, variable=self.vars[key]).grid(row=r, column=0, sticky="w", padx=8, pady=2)
        fmt = ttk.LabelFrame(master, text="Format", padding=6)
        fmt.grid(row=len(self.OPTIONS) + 1, column=0, sticky="we", padx=8, pady=8)
        self.fmt = tk.StringVar(value=self.saved.get("format", "m3u8"))
        ttk.Radiobutton(fmt, text="M3U8 – TV & radio, keeps logos, EPG, groups", value="m3u8",
                        variable=self.fmt).pack(anchor="w")
        ttk.Radiobutton(fmt, text="M3U – same, older extension", value="m3u", variable=self.fmt).pack(anchor="w")
        ttk.Radiobutton(fmt, text="PLS – simple radio players (no groups/logos)", value="pls",
                        variable=self.fmt).pack(anchor="w")
        return None

    def apply(self):
        self.result = {k: v.get() for k, v in self.vars.items()}
        self.result["format"] = self.fmt.get()


# =============================================================================
#  Main window
# =============================================================================

class App(tk.Tk):
    def __init__(self, files=()):
        super().__init__(className="PlaylistChecker")
        self.title(APP_TITLE)
        self._set_app_icon()
        self.geometry("1320x800")
        self.minsize(980, 560)
        self.settings = load_settings()

        self.channels: list[Channel] = []
        self.by_uid: dict[int, Channel] = {}
        self.header: dict = {}
        self.group_enabled: dict[str, bool] = {}
        self.group_order: list[str] = []
        self.uid_counter = 0

        self.q: queue.Queue = queue.Queue()
        self.stop_event = threading.Event()
        self.checking = False
        self.check_total = self.check_done = 0
        self.current_group: str | None = None
        self.sort_col, self.sort_rev = "num", False
        self._search_job = None
        self._last_group_refresh = 0.0
        self._suppress_group_select = False
        self._source_labels: dict[str, str] = {}
        self._recheck: set[int] | None = None
        self._pending_check = False   # playlists added while a check was running
        self.downloading = False
        self._dl_stop = threading.Event()
        self._dl_gen = 0           # changes on "Clear list", so late downloads are ignored
        self._dl: dict = {}
        self._dl_last_refresh = 0.0
        self._previous: dict[int, tuple] = {}

        self.v_hide_hidden = tk.BooleanVar(value=self.settings.get("hide_hidden", True))
        self.v_date_names = tk.BooleanVar(value=self.settings.get("date_names", True))
        self.v_prefix_names = tk.BooleanVar(value=self.settings.get("prefix_names", True))
        self.v_encoding = tk.StringVar(value=self.settings.get("encoding", "auto"))
        self.v_ua = tk.StringVar(value=self.settings.get("user_agent", DEFAULT_UA))
        self.v_confirm_exit = tk.BooleanVar(value=self.settings.get("confirm_exit", True))
        self.v_auto_check = tk.BooleanVar(value=self.settings.get("auto_check", False))
        self.v_tint = tk.BooleanVar(value=self.settings.get("tint_rows", True))
        self.v_hide_excluded = tk.BooleanVar(value=self.settings.get("hide_excluded", True))
        self.source_color: dict[str, int] = {}     # playlist -> color number
        self.source_enabled: dict[str, bool] = {}  # playlist ticked for saving
        self.current_source: str | None = None
        self._swatch_images: dict[int, tk.PhotoImage] = {}
        is_x11 = self.tk.call("tk", "windowingsystem") == "x11"  # Windows / macOS draw RTL text themselves
        self.v_bidi = tk.BooleanVar(value=self.settings.get("bidi_fix", is_x11))
        BIDI["enabled"] = self.v_bidi.get()
        self._setup_style()
        self._build_menu()
        self._build_toolbar()
        self._build_settings()
        self._build_statusbar()
        self._build_main()
        self._bind_keys()
        self._install_text_field_menus()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(120, self._poll)
        self.after(300, self._replace_old_launchers)

        urls = [f for f in files if re.match(r"^https?://", f, re.I)]
        for u in urls:
            self._start_download(u)
        files = [f for f in files if f not in urls]
        lists = [f for f in files if Path(f).suffix.lower() in (".txt", ".list")]
        files = [f for f in files if f not in lists]
        for f in lists:
            self.after(200, lambda f=f: self.load_url_list(Path(f)))
        added = sum(self.load_path(Path(f)) for f in files)
        if files:
            self.after_load(added)
        else:
            self.refresh_all()

    # ------------------------------------------------------------------ UI build
    def _setup_style(self):
        st = ttk.Style(self)
        if sys.platform.startswith("linux") and "clam" in st.theme_names():
            st.theme_use("clam")
        line = tkfont.nametofont("TkDefaultFont").metrics("linespace")
        st.configure("Treeview", rowheight=line + 6)
        st.configure("Big.TButton", padding=(10, 4))

    def _build_menu(self):
        mb = tk.Menu(self)
        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Open playlist files…", accelerator="Ctrl+O", command=self.open_files)
        m.add_command(label="Open folder with playlists…", command=self.open_folder)
        m.add_command(label="Add playlist from URL…", accelerator="Ctrl+U", command=self.open_url)
        m.add_command(label="Open list of playlist URLs (.txt)…", accelerator="Ctrl+L", command=self.open_url_list)
        m.add_separator()
        m.add_command(label="Save new playlist…", accelerator="Ctrl+S", command=self.export_dialog)
        m.add_command(label="Export check report (CSV)…", command=self.export_report)
        m.add_separator()
        m.add_command(label="Clear list", command=self.clear_all)
        m.add_command(label="Exit", accelerator="Ctrl+Q", command=self.on_close)
        mb.add_cascade(label="File", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Copy stream URLs", accelerator="Ctrl+C", command=self.copy_url)
        m.add_command(label="Paste stream links / playlist", accelerator="Ctrl+V", command=self.paste_channels)
        m.add_separator()
        m.add_command(label="Select all shown", accelerator="Ctrl+A", command=self.select_all)
        m.add_command(label="Rename channel…", accelerator="F2", command=self.rename_channel)
        m.add_command(label="Move selected to group…", accelerator="Ctrl+G", command=self.move_to_group)
        m.add_command(label="Delete selected", accelerator="Del", command=self.delete_selected)
        m.add_separator()
        m.add_command(label="Remove all offline channels from list", command=self.remove_offline)
        m.add_command(label="Remove all duplicates from list", command=self.remove_duplicates)
        mb.add_cascade(label="Edit", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Check all channels", accelerator="F5", command=self.check_all)
        m.add_command(label="Check shown channels", command=self.check_visible)
        m.add_command(label="Check selected channels", command=self.check_selected)
        m.add_separator()
        m.add_command(label="Recheck offline / broken channels", accelerator="Shift+F5", command=self.recheck_offline)
        m.add_command(label="Stop", accelerator="Esc", command=self.stop_check)
        mb.add_cascade(label="Check", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_checkbutton(label="Hide hidden files and folders", variable=self.v_hide_hidden,
                          command=self.on_hidden_option)
        m.add_checkbutton(label=f"Add “{FILE_PREFIX}” to saved file names", variable=self.v_prefix_names,
                          command=self.save_settings)
        m.add_checkbutton(label="Add date to saved file names", variable=self.v_date_names,
                          command=self.save_settings)
        m.add_checkbutton(label="Fix right-to-left text (Hebrew / Arabic)", variable=self.v_bidi,
                          command=self.on_bidi_option)
        m.add_checkbutton(label="Confirm before exit", variable=self.v_confirm_exit, command=self.save_settings)
        m.add_checkbutton(label="Check new channels automatically after loading", variable=self.v_auto_check,
                          command=self.save_settings)
        m.add_checkbutton(label="Hide unticked groups and playlists in the channel list",
                          variable=self.v_hide_excluded,
                          command=lambda: (self.save_settings(), self.refresh_channels()))
        m.add_checkbutton(label="Tint rows with the playlist color", variable=self.v_tint,
                          command=lambda: (self.save_settings(), self.refresh_channels()))
        m.add_separator()
        enc = tk.Menu(m, tearoff=0)
        for value, label in LEGACY_ENCODINGS:
            enc.add_radiobutton(label=label, value=value, variable=self.v_encoding, command=self.save_settings)
        m.add_cascade(label="Encoding of old (non-UTF-8) playlists", menu=enc)
        uam = tk.Menu(m, tearoff=0)
        for i, (section, items) in enumerate(USER_AGENTS):
            if i:
                uam.add_separator()
            uam.add_command(label=section, state="disabled")
            for name, value in items:
                uam.add_radiobutton(label="   " + name, value=value, variable=self.v_ua,
                                    command=lambda n=name: self.on_user_agent(n))
        uam.add_separator()
        uam.add_command(label="Custom…", command=self.custom_user_agent)
        m.add_cascade(label="User-Agent (identify as player / app)", menu=uam)
        m.add_separator()
        linux = sys.platform.startswith("linux")
        state = "normal" if linux else "disabled"
        suffix = "" if linux else "  (Linux only)"
        if INSTALLED:  # the package already added it to the applications menu
            m.add_command(label="Already in the applications menu (installed package)", state="disabled")
        else:
            m.add_command(label="Add to applications menu" + suffix, command=self.add_to_app_menu, state=state)
        m.add_command(label="Create desktop shortcut" + suffix, command=self.create_desktop_shortcut, state=state)
        m.add_command(label=("Remove desktop shortcut" if INSTALLED else "Remove from applications menu and desktop")
                      + suffix, command=self.remove_launchers,
                      state=state)
        mb.add_cascade(label="Settings", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="How to use", command=self.show_help)
        m.add_command(label="Project page on GitHub", command=lambda: self.open_link(PROJECT_URL))
        m.add_command(label="Report a problem…", command=lambda: self.open_link(PROJECT_URL + "/issues"))
        m.add_separator()
        m.add_command(label="About", command=self.show_about)
        mb.add_cascade(label="Help", menu=m)
        self.config(menu=mb)

    def _build_toolbar(self):
        tb = ttk.Frame(self, padding=(8, 8, 8, 4))
        tb.pack(fill="x")

        def btn(text, cmd, style="TButton"):
            b = ttk.Button(tb, text=text, command=cmd, style=style)
            b.pack(side="left", padx=2)
            return b

        def sep():
            ttk.Separator(tb, orient="vertical").pack(side="left", fill="y", padx=8)

        btn("Open files…", self.open_files)
        btn("Open folder…", self.open_folder)
        btn("Add from URL…", self.open_url)
        sep()
        self.btn_check = btn("▶  Check streams", self.check_all, "Big.TButton")
        self.btn_recheck = btn("↻  Recheck offline", self.recheck_offline)
        self.btn_stop = btn("■  Stop", self.stop_check)
        self.btn_stop.state(["disabled"])
        sep()
        btn("💾  Save new playlist…", self.export_dialog, "Big.TButton")
        btn("Export report…", self.export_report)
        sep()
        btn("Clear", self.clear_all)

    def _build_settings(self):
        s = self.settings
        row1 = ttk.Frame(self, padding=(10, 0, 10, 2))
        row1.pack(fill="x")
        self.v_timeout = tk.StringVar(value=str(s.get("timeout", 8)))
        self.v_threads = tk.StringVar(value=str(s.get("threads", 20)))
        self.v_deep = tk.BooleanVar(value=s.get("deep_hls", True))
        self.v_ssl = tk.BooleanVar(value=s.get("ignore_ssl", True))
        self.v_dup_url = tk.BooleanVar(value=s.get("dup_url", True))
        self.v_dup_name = tk.BooleanVar(value=s.get("dup_name", False))
        self.v_dup_quality = tk.BooleanVar(value=s.get("dup_quality", True))

        ttk.Label(row1, text="Check:  timeout (s)").pack(side="left")
        ttk.Spinbox(row1, from_=2, to=60, width=4, textvariable=self.v_timeout).pack(side="left", padx=(4, 12))
        ttk.Label(row1, text="parallel checks").pack(side="left")
        ttk.Spinbox(row1, from_=1, to=100, width=4, textvariable=self.v_threads).pack(side="left", padx=(4, 12))
        ttk.Label(row1, text="User-Agent").pack(side="left")
        ttk.Entry(row1, textvariable=self.v_ua, width=26).pack(side="left", padx=(4, 12))
        ttk.Checkbutton(row1, text="Deep HLS check (test the video itself)", variable=self.v_deep).pack(side="left", padx=4)
        ttk.Checkbutton(row1, text="Ignore SSL certificate errors", variable=self.v_ssl).pack(side="left", padx=4)

        row2 = ttk.Frame(self, padding=(10, 0, 10, 4))
        row2.pack(fill="x")
        ttk.Label(row2, text="Duplicates:").pack(side="left")
        for text, var in (("same stream URL", self.v_dup_url), ("same channel name", self.v_dup_name),
                          ("ignore HD / FHD / 4K / 1080p in names", self.v_dup_quality)):
            ttk.Checkbutton(row2, text=text, variable=var, command=self.on_dup_options).pack(side="left", padx=6)

    def _build_statusbar(self):
        sb = ttk.Frame(self, padding=(10, 3, 10, 6))
        sb.pack(fill="x", side="bottom")
        self.progress = ttk.Progressbar(sb, length=240, mode="determinate")
        self.progress.pack(side="left")
        self.lbl_status = ttk.Label(sb, text="")
        self.lbl_status.pack(side="left", padx=10)

    def _build_main(self):
        pw = ttk.Panedwindow(self, orient="horizontal")
        pw.pack(fill="both", expand=True, padx=10, pady=4)
        left, right = ttk.Frame(pw), ttk.Frame(pw)
        pw.add(left, weight=0)
        pw.add(right, weight=1)

        # ---- groups
        ttk.Label(left, text="Groups   (click ☑ to include / exclude)").pack(anchor="w", pady=(0, 3))
        gf = ttk.Frame(left)
        gf.pack(fill="both", expand=True)
        self.gtree = ttk.Treeview(gf, columns=("inc", "name", "total", "online"), show="headings", selectmode="browse")
        for col, text, w, anchor, stretch in (("inc", "✓", 30, "center", False), ("name", "Group", 200, "w", True),
                                              ("total", "Ch.", 48, "e", False), ("online", "Online", 60, "e", False)):
            self.gtree.heading(col, text=text)
            self.gtree.column(col, width=w, anchor=anchor, stretch=stretch)
        gsb = ttk.Scrollbar(gf, orient="vertical", command=self.gtree.yview)
        self.gtree.configure(yscrollcommand=gsb.set)
        self.gtree.pack(side="left", fill="both", expand=True)
        gsb.pack(side="right", fill="y")
        self.gtree.bind("<<TreeviewSelect>>", self.on_group_select)
        self.gtree.bind("<Button-1>", self.on_group_click)
        self.gtree.bind("<space>", lambda e: self.toggle_selected_group())
        self.gtree.bind("<F2>", lambda e: self.rename_group())

        gb = ttk.Frame(left)
        gb.pack(fill="x", pady=(4, 0))
        for text, cmd, w in (("All ☑", lambda: self.set_all_groups(True), 6), ("None ☐", lambda: self.set_all_groups(False), 7),
                             ("▲", lambda: self.move_group(-1), 2), ("▼", lambda: self.move_group(1), 2),
                             ("Rename…", self.rename_group, 8)):
            ttk.Button(gb, text=text, width=w, command=cmd).pack(side="left", padx=1)

        # ---- playlists (color legend, filter, include / exclude)
        ttk.Label(left, text="Playlists   (click a name to show only it)").pack(anchor="w", pady=(10, 3))
        pf = ttk.Frame(left)
        pf.pack(fill="x")
        self.ptree = ttk.Treeview(pf, columns=("inc", "name", "total", "online"), show="tree headings",
                                  selectmode="browse", height=5)
        self.ptree.column("#0", width=30, minwidth=30, stretch=False, anchor="center")
        for col, text, w, anchor, stretch in (("inc", "✓", 30, "center", False), ("name", "Playlist", 170, "w", True),
                                              ("total", "Ch.", 48, "e", False), ("online", "Online", 60, "e", False)):
            self.ptree.heading(col, text=text)
            self.ptree.column(col, width=w, anchor=anchor, stretch=stretch)
        psb = ttk.Scrollbar(pf, orient="vertical", command=self.ptree.yview)
        self.ptree.configure(yscrollcommand=psb.set)
        self.ptree.pack(side="left", fill="x", expand=True)
        psb.pack(side="right", fill="y")
        self.ptree.bind("<<TreeviewSelect>>", self.on_source_select)
        self.ptree.bind("<Button-1>", self.on_source_click)
        self._suppress_source_select = False

        # ---- filter bar
        fb = ttk.Frame(right)
        fb.pack(fill="x")
        ttk.Label(fb, text="Search:").pack(side="left")
        self.v_search = tk.StringVar()
        ttk.Entry(fb, textvariable=self.v_search, width=32).pack(side="left", padx=(4, 14))
        self.v_search.trace_add("write", lambda *a: self._debounced_refresh())
        ttk.Label(fb, text="Show:").pack(side="left")
        self.v_show = tk.StringVar(value="All")
        cb = ttk.Combobox(fb, textvariable=self.v_show, values=SHOW_OPTIONS, state="readonly", width=28)
        cb.pack(side="left", padx=4)
        cb.bind("<<ComboboxSelected>>", lambda e: self.refresh_channels())
        self.lbl_shown = ttk.Label(fb, text="")
        self.lbl_shown.pack(side="right")

        # ---- channel table
        tf = ttk.Frame(right)
        tf.pack(fill="both", expand=True, pady=(4, 0))
        self.cols = ("num", "status", "name", "group", "info", "dup", "url", "source")
        self.col_titles = {"num": "#", "status": "Status", "name": "Channel", "group": "Group",
                           "info": "Check result", "dup": "Duplicate", "url": "Stream URL", "source": "Playlist"}
        widths = {"num": 50, "status": 125, "name": 210, "group": 130, "info": 230, "dup": 120, "url": 330, "source": 110}
        self.tree = ttk.Treeview(tf, columns=self.cols, show="tree headings", selectmode="extended")
        self.tree.column("#0", width=30, minwidth=30, stretch=False, anchor="center")  # playlist color
        for c in self.cols:
            self.tree.heading(c, text=self.col_titles[c], command=lambda c=c: self.sort_by(c))
            self.tree.column(c, width=widths[c], anchor="e" if c == "num" else "w",
                             stretch=c in ("name", "url", "info"))
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(tf, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        tf.rowconfigure(0, weight=1)
        tf.columnconfigure(0, weight=1)
        self.tree.tag_configure("excluded", foreground="#a0a0a0")
        self.tree.tag_configure(ONLINE, foreground="#1b7a34")
        self.tree.tag_configure(OFFLINE, foreground="#c62828")
        self.tree.tag_configure(CHECKING, foreground="#1565c0")
        self.tree.tag_configure(UNCHECKED, foreground="#555555")
        self.tree.tag_configure("dup", background="#fff1c4")

        self.cmenu = tk.Menu(self, tearoff=0)
        self.cmenu.add_command(label="▶ Play (VLC)", command=self.play_selected)
        self.cmenu.add_command(label="Copy URL", accelerator="Ctrl+C", command=self.copy_url)
        self.cmenu.add_command(label="Paste stream links / playlist", accelerator="Ctrl+V", command=self.paste_channels)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="Check selected", command=self.check_selected)
        self.cmenu.add_command(label="Recheck all offline / broken", command=self.recheck_offline)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="Rename channel…", command=self.rename_channel)
        self.cmenu.add_command(label="Move to group…", command=self.move_to_group)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="Delete from list", command=self.delete_selected)
        self.tree.bind("<Button-3>", self.on_right_click)
        self.tree.bind("<Button-2>", self.on_right_click)  # macOS
        self.tree.bind("<Control-KeyPress>", self._tree_ctrl_key)
        self.tree.bind("<Double-1>", lambda e: self.play_selected())
        self.tree.bind("<Return>", lambda e: self.play_selected())

    def _bind_keys(self):
        def main_window_only(fn):
            # not while a dialog (rename, save, file dialog...) is open, and only for the main window
            def handler(e):
                try:
                    if str(self.tk.call("grab", "current")):
                        return None
                    if str(self.tk.call("winfo", "toplevel", str(e.widget))) != ".":
                        return None
                except tk.TclError:
                    return None
                fn()
                return "break"
            return handler

        for keys, fn in ((("<Control-o>", "<Control-O>"), self.open_files),
                         (("<Control-u>", "<Control-U>"), self.open_url),
                         (("<Control-l>", "<Control-L>"), self.open_url_list),
                         (("<Control-s>", "<Control-S>"), self.export_dialog),
                         (("<Control-q>", "<Control-Q>"), self.on_close),
                         (("<F5>",), self.check_all),
                         (("<Shift-F5>",), self.recheck_offline),
                         (("<Escape>",), self.stop_check)):
            for k in keys:
                self.bind_all(k, main_window_only(fn))
        self.tree.bind("<Control-a>", lambda e: (self.select_all(), "break")[1])
        self.tree.bind("<Delete>", lambda e: self.delete_selected())
        self.tree.bind("<F2>", lambda e: self.rename_channel())
        self.tree.bind("<Control-g>", lambda e: self.move_to_group())

    # ------------------------------------------------------------------ loading
    def open_files(self):
        paths = self._fd().askopenfilenames(
            parent=self, title="Open playlists", initialdir=self.settings.get("last_dir") or str(Path.home()),
            filetypes=[("Playlists", "*.m3u *.m3u8 *.pls *.xspf"), ("Lists of playlist URLs", "*.txt *.list"),
                       ("All files", "*.*")])
        if not paths:
            return
        self.settings["last_dir"] = str(Path(paths[0]).parent)
        lists = [Path(p) for p in paths if Path(p).suffix.lower() in (".txt", ".list")]
        files = [Path(p) for p in paths if Path(p) not in lists]
        if files:
            self.after_load(sum(self.load_path(p) for p in files))
        for p in lists:
            self.load_url_list(p)

    def open_folder(self):
        d = self._fd().askdirectory(parent=self, title="Folder with playlists",
                                    initialdir=self.settings.get("last_dir") or str(Path.home()))
        if not d:
            return
        self.settings["last_dir"] = d
        files = find_playlists(Path(d), self.v_hide_hidden.get())
        if not files:
            messagebox.showinfo(APP_TITLE, "No playlist files (.m3u .m3u8 .pls .xspf) in this folder.", parent=self)
            return
        self.after_load(sum(self.load_path(f) for f in files))

    def open_url(self):
        url = simpledialog.askstring(APP_TITLE, "Playlist web address (http://… or https://…):", parent=self)
        if not url or not url.strip():
            return
        self._start_download(url.strip())

    def _start_download(self, url: str):
        self.set_status(f"Downloading playlist {url} …")
        self.progress.configure(mode="indeterminate")
        self.progress.start(12)
        threading.Thread(target=self._fetch_playlist, args=(url, self.v_ua.get().strip() or DEFAULT_UA,
                                                            self.v_ssl.get(), self.v_encoding.get()),
                         daemon=True).start()

    def _fetch_playlist(self, url, ua, ignore_ssl, legacy):
        try:
            kind, text = fetch_playlist(url, ua, ignore_ssl, legacy)
            if kind == "playlist":
                self.q.put(("loaded", text, url))
            elif kind == "stream":
                self.q.put(("stream", url))
            else:
                self.q.put(("error", f"This address returns a web page, not a playlist:\n{url}\n\n"
                                     "Check the address, or whether the provider needs a login or another "
                                     "User-Agent (Settings → User-Agent)."))
        except Exception as e:
            self.q.put(("error", f"Could not download the playlist:\n{url}\n\n{short_error(e)}"))

    # ------------------------------------------------------------------ list of playlist URLs (.txt)
    def open_url_list(self):
        path = self._fd().askopenfilename(
            parent=self, title="Open a list of playlist addresses",
            initialdir=self.settings.get("last_dir") or str(Path.home()),
            filetypes=[("Text files", "*.txt *.list"), ("All files", "*.*")])
        if path:
            self.settings["last_dir"] = str(Path(path).parent)
            self.load_url_list(Path(path))

    def load_url_list(self, path: Path):
        """Text file with one playlist address per line -> download every playlist."""
        try:
            data = path.read_bytes()
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not open {path}:\n{e}", parent=self)
            return
        text = decode_bytes(data, self.v_encoding.get())
        if looks_like_playlist_text(text):  # it is a playlist saved as .txt
            self.after_load(self.add_playlist_text(text, str(path), str(path.parent.resolve())))
            return
        web, streams, local = parse_url_list(text, path.parent.resolve())
        if not (web or streams or local):
            messagebox.showinfo(APP_TITLE, f"{path.name} contains no playlist addresses.\n\n"
                                "Write one address per line, for example:\n"
                                "http://provider.example/get.php?username=…&type=m3u_plus\n"
                                "https://example.com/radio.m3u\n\n"
                                "Lines starting with # are ignored.", parent=self)
            return
        added = self.add_stream_urls(streams, str(path)) if streams else 0
        added += sum(self.load_path(p) for p in local)
        if added:
            self.after_load(added)
        if web:
            self._download_many(web, path.name, added, source=str(path))

    def add_stream_urls(self, urls: list[str], source: str, group: str = "") -> int:
        g_attr = f' group-title="{group.replace(chr(34), chr(39))}"' if group else ""
        playlist = "#EXTM3U\n" + "".join(f"#EXTINF:-1{g_attr},{name_from_url(u)}\n{u}\n" for u in urls)
        return self.add_playlist_text(playlist, source, "")

    def _download_many(self, urls: list[str], label: str, already_added: int = 0, source: str = ""):
        if self.downloading:
            messagebox.showinfo(APP_TITLE, "Playlists are still being downloaded – wait or press Stop.", parent=self)
            return
        self.downloading = True
        self._dl_stop.clear()
        for u in urls:  # colors follow the order of the list, not the order the downloads finish
            self._source_index(u)
        self._dl = {"label": label, "source": source, "total": len(urls), "done": 0, "ok": 0, "streams": 0,
                    "channels": already_added, "failed": [], "gen": self._dl_gen}
        self.progress.stop()
        self.progress.configure(mode="determinate", maximum=len(urls), value=0)
        self.btn_stop.state(["!disabled"])
        self.set_status(f"Downloading {len(urls)} playlists from {label} …")
        args = (urls, self.v_ua.get().strip() or DEFAULT_UA, self.v_ssl.get(), self.v_encoding.get(), self._dl_gen)
        threading.Thread(target=self._download_worker, args=args, daemon=True).start()

    def _download_worker(self, urls, ua, ignore_ssl, legacy, gen):
        stop = self._dl_stop

        def task(url):
            if stop.is_set():
                return url, "skipped", ""
            try:
                return (url,) + fetch_playlist(url, ua, ignore_ssl, legacy)
            except urllib.error.HTTPError as e:
                return url, "error", f"HTTP {e.code} {e.reason}".strip()
            except Exception as e:
                return url, "error", short_error(e)

        ex = ThreadPoolExecutor(max_workers=DOWNLOAD_PARALLEL)
        try:
            pending = {ex.submit(task, u) for u in urls}
            while pending and not stop.is_set():
                done, pending = wait(pending, timeout=0.25, return_when=FIRST_COMPLETED)
                for f in done:
                    self.q.put(("dl_item", gen) + f.result())
        finally:
            ex.shutdown(wait=False, cancel_futures=True)
            self.q.put(("dl_done", gen, stop.is_set()))

    def _download_item(self, gen, url, kind, text):
        if gen != self._dl_gen:
            return
        d = self._dl
        d["done"] += 1
        if kind == "playlist":
            n = self.add_playlist_text(text, url, "", quiet=True)
            if n < 0:
                d["failed"].append((url, "not a readable playlist"))
            elif n == 0:
                d["failed"].append((url, "the playlist is empty"))
            else:
                d["ok"] += 1
                d["channels"] += n
        elif kind == "stream":
            d["streams"] += 1
            d["channels"] += self.add_stream_urls([url], d.get("source") or url)
        elif kind == "page":
            d["failed"].append((url, "web page instead of a playlist (wrong address or login needed)"))
        elif kind != "skipped":
            d["failed"].append((url, text or "download failed"))
        self.progress["value"] = d["done"]
        self.set_status(f"Downloading playlists from {d['label']}: {d['done']} / {d['total']} · "
                        f"{d['channels']} channels so far")
        now = time.monotonic()
        if now - self._dl_last_refresh > 1.5:  # keep the window responsive with big lists
            self._dl_last_refresh = now
            self.refresh_all()

    def _download_finished(self, gen, stopped):
        if gen != self._dl_gen:
            self.downloading = False
            return
        d = self._dl
        self.downloading = False
        if not self.checking:
            self.btn_stop.state(["disabled"])
        self.after_load(d["channels"])
        parts = [f"{d['ok']} of {d['total']} playlists loaded"]
        if d["streams"]:
            parts.append(f"{d['streams']} direct stream link(s)")
        parts.append(f"{d['channels']} channels added")
        if d["failed"]:
            parts.append(f"{len(d['failed'])} failed")
        self.set_status(("Stopped. " if stopped else "") + f"{d['label']}: " + " · ".join(parts) + ".")
        if d["failed"]:
            lines = [f"• {u}\n   {why}" for u, why in d["failed"][:12]]
            more = f"\n…and {len(d['failed']) - 12} more" if len(d["failed"]) > 12 else ""
            messagebox.showwarning(APP_TITLE, f"{len(d['failed'])} of {d['total']} addresses could not be loaded:\n\n"
                                   + "\n".join(lines) + more, parent=self)

    def load_path(self, path: Path) -> int:
        try:
            data = path.read_bytes()
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not open {path}:\n{e}", parent=self)
            return 0
        if b"\x00" in data[:4096]:
            messagebox.showerror(APP_TITLE, f"{path.name} is not a text playlist.", parent=self)
            return 0
        text = decode_bytes(data, self.v_encoding.get())
        return self.add_playlist_text(text, str(path), str(path.parent.resolve()))

    def add_playlist_text(self, text: str, source: str, base_dir: str = "", quiet: bool = False) -> int:
        """Add the channels of a playlist; returns how many (or -1 if quiet and it can't be read)."""
        try:
            header, chans = parse_playlist(text, source, base_dir)
        except Exception as e:
            if quiet:
                return -1
            messagebox.showerror(APP_TITLE, f"Could not read {source}:\n{e}", parent=self)
            return 0
        for k, v in header.items():
            self.header.setdefault(k, v)
        remote = re.match(r"^https?://", source, re.I) is not None
        for c in chans:
            if remote and is_local(c.url) and not re.match(r"^[a-zA-Z]:[\\/]", c.url):
                c.url = urllib.parse.urljoin(source, c.url)  # link relative to the playlist's web address
            self.uid_counter += 1
            c.uid = self.uid_counter
            self.channels.append(c)
            self.by_uid[c.uid] = c
            self._source_index(c.source)
            if c.group not in self.group_enabled:
                self.group_enabled[c.group] = True
                self.group_order.append(c.group)
        return len(chans)

    def after_load(self, added: int):
        reset = added > 0 and self._reset_view_filters()
        self.recompute_duplicates()
        self.refresh_all()
        if added > 0 and self.checking:
            self._pending_check = True       # checked as soon as the running check ends
        elif added > 0 and self.v_auto_check.get() and not self.downloading:
            self.after(300, self._auto_check)
        dups = sum(1 for c in self.channels if c.dup_of)
        playlists = len({c.source for c in self.channels})
        text = (f"Added {added} channels · now {playlists} playlist{'s' if playlists != 1 else ''}, "
                f"{len(self.channels)} channels · {dups} duplicates.")
        if added > 0 and self.checking:
            text += " They will be checked when the running check ends."
        else:
            text += " Press “Check streams” to test them."
        if reset:
            text += " (Filters were reset so the new channels are visible.)"
        self.set_status(text)

    def _reset_view_filters(self) -> bool:
        """New channels must be visible: go back to all groups, all playlists, Show: All, no search."""
        changed = (self.current_group is not None or self.current_source is not None
                   or self.v_show.get() != "All" or bool(self.v_search.get().strip()))
        self.current_group = None
        self.current_source = None
        self.v_show.set("All")
        if self.v_search.get():
            self.v_search.set("")
        self._suppress_group_select = self._suppress_source_select = True
        try:
            if self.gtree.exists("*"):
                self.gtree.selection_set("*")
            if self.ptree.exists("*"):
                self.ptree.selection_set("*")
            self.update_idletasks()
        finally:
            self._suppress_group_select = self._suppress_source_select = False
        return changed

    def _auto_check(self):
        if self.checking or self.downloading:
            return
        new = [c for c in self.channels if c.status == UNCHECKED and self._included(c)]
        if new:
            self.start_check(new)

    # ------------------------------------------------------------------ checking
    def check_all(self):
        targets = [c for c in self.channels if self._included(c)]
        if self.channels and not targets:
            messagebox.showinfo(APP_TITLE, "All groups or playlists are unticked (☐), so there is nothing to "
                                           "check.\nTick the ones you want to check on the left.", parent=self)
            return
        self.start_check(targets)

    def recheck_offline(self):
        """Check again only the channels marked offline (dead links, broken HLS, timeouts...).
        Uses double the timeout, so slow servers get a second, fairer chance."""
        if self.checking:
            return
        targets = [c for c in self.channels if c.status == OFFLINE and self._included(c)]
        if not targets:
            messagebox.showinfo(APP_TITLE, "There are no offline channels to recheck.\n"
                                           "Run “Check streams” first.", parent=self)
            return
        self.start_check(targets, recheck=True)

    def check_visible(self):
        self.start_check([self.by_uid[int(i)] for i in self.tree.get_children()])

    def check_selected(self):
        self.start_check([self.by_uid[int(i)] for i in self.tree.selection()])

    def start_check(self, targets: list[Channel], recheck: bool = False):
        if self.checking:
            return
        if not targets:
            messagebox.showinfo(APP_TITLE, "There are no channels to check.", parent=self)
            return
        self.save_settings()
        timeout = min(max(self._int(self.v_timeout, 8), 1), 120) * (2 if recheck else 1)
        threads = min(max(self._int(self.v_threads, 20), 1), 200)
        checker = StreamChecker(timeout, self.v_ua.get().strip(), self.v_deep.get(), self.v_ssl.get())
        jobs = []
        self._recheck = {c.uid for c in targets} if recheck else None
        self._previous = {c.uid: (c.status, c.info, c.latency) for c in targets}  # restored if stopped
        for c in targets:
            c.status, c.info, c.latency = CHECKING, "", None
            ua, ref = c.http_options()
            jobs.append((c.uid, c.url, c.base_dir, ua, ref))
        self.stop_event.clear()
        self.checking = True
        self.check_total, self.check_done = len(jobs), 0
        self.progress.stop()
        self.progress.configure(mode="determinate", maximum=len(jobs), value=0)
        self.btn_check.state(["disabled"])
        self.btn_recheck.state(["disabled"])
        self.btn_stop.state(["!disabled"])
        self.refresh_channels()
        self.set_status(self._progress_text())
        threading.Thread(target=self._check_worker, args=(checker, jobs, threads), daemon=True).start()

    def _check_worker(self, checker: StreamChecker, jobs, threads):
        stop = self.stop_event

        def task(job):
            uid, url, base, ua, ref = job
            if stop.is_set():
                return uid, None
            return uid, checker.check(url, base, ua, ref)

        ex = ThreadPoolExecutor(max_workers=threads)
        try:
            pending = {ex.submit(task, j) for j in jobs}
            while pending and not stop.is_set():  # short waits so "Stop" reacts at once
                done, pending = wait(pending, timeout=0.25, return_when=FIRST_COMPLETED)
                for f in done:
                    try:
                        uid, res = f.result()
                    except Exception:
                        continue
                    self.q.put(("result", uid, res))
        finally:
            ex.shutdown(wait=False, cancel_futures=True)
            self.q.put(("done", stop.is_set()))

    def stop_check(self):
        if self.downloading:
            self._dl_stop.set()
            self.set_status("Stopping the downloads…")
        if self.checking:
            self.stop_event.set()
            self.set_status("Stopping…")

    def _check_finished(self, stopped: bool):
        for c in self.channels:
            if c.status == CHECKING:  # stopped before this one was checked: keep its old result
                c.status, c.info, c.latency = self._previous.get(c.uid, (UNCHECKED, "", None))
        self.checking = False
        self.btn_check.state(["!disabled"])
        self.btn_recheck.state(["!disabled"])
        if not self.downloading:
            self.btn_stop.state(["disabled"])
        self.progress["value"] = self.check_done
        self.recompute_duplicates()
        self.refresh_all()
        on = sum(c.status == ONLINE for c in self.channels)
        off = sum(c.status == OFFLINE for c in self.channels)
        dups = sum(1 for c in self.channels if c.dup_of)
        text = (f"{'Stopped' if stopped else 'Check finished'}: {on} online · {off} offline · "
                f"{dups} duplicates · {len(self.channels)} channels total.")
        skipped = sum(1 for c in self.channels if not self._included(c))
        if skipped:
            text += f" {skipped} in unticked groups / playlists were not checked."
        if self._recheck:
            back = sum(1 for uid in self._recheck if uid in self.by_uid and self.by_uid[uid].status == ONLINE)
            text = (f"Recheck {'stopped' if stopped else 'finished'}: {back} of {len(self._recheck)} offline "
                    f"channels are back online · still offline: {off}.")
            self._recheck = None
        self.set_status(text)
        if self._pending_check and not stopped:
            self._pending_check = False
            if any(c.status == UNCHECKED and self._included(c) for c in self.channels):
                self.after(400, self._check_added)
                return
        self._pending_check = False
        if not stopped:
            self.bell()

    def _check_added(self):
        """Continue with the playlists that were opened while the previous check was running."""
        targets = [c for c in self.channels if c.status == UNCHECKED and self._included(c)]
        if targets and not self.checking:
            self.start_check(targets)
            self.set_status(f"Checking {len(targets)} channels added during the previous check …")

    def _progress_text(self) -> str:
        skipped = sum(1 for c in self.channels if not self._included(c))
        note = f"   ·   {skipped} unticked skipped" if skipped else ""
        return self._progress_core() + note

    def _progress_core(self) -> str:
        on = sum(c.status == ONLINE for c in self.channels)
        off = sum(c.status == OFFLINE for c in self.channels)
        return f"Checking {self.check_done} / {self.check_total}   ·   online {on}   ·   offline {off}"

    def _poll(self):
        updated = False
        try:
            for _ in range(2000):
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "result":
                    c = self.by_uid.get(msg[1])
                    if c is not None and msg[2] is not None:
                        c.status, c.info, c.latency = msg[2]
                        self._update_row(c)
                    self.check_done += 1
                    updated = True
                elif kind == "done":
                    self._check_finished(msg[1])
                elif kind == "loaded":
                    self.progress.stop()
                    self.progress.configure(mode="determinate", value=0)
                    self.after_load(self.add_playlist_text(msg[1], msg[2], ""))
                elif kind == "stream":
                    self.progress.stop()
                    self.progress.configure(mode="determinate", value=0)
                    self.after_load(self.add_stream_urls([msg[1]], msg[1]))
                    self.set_status("That address is a single TV/radio stream, not a playlist – "
                                    "it was added as one channel.")
                elif kind == "dl_item":
                    self._download_item(*msg[1:])
                elif kind == "dl_done":
                    self._download_finished(msg[1], msg[2])
                elif kind == "error":
                    self.progress.stop()
                    self.progress.configure(mode="determinate", value=0)
                    self.set_status("Download failed.")
                    messagebox.showerror(APP_TITLE, msg[1], parent=self)
        except queue.Empty:
            pass
        if updated and self.checking:
            self.progress["value"] = self.check_done
            self.set_status(self._progress_text())
            now = time.monotonic()
            if now - self._last_group_refresh > 1.0:
                self._last_group_refresh = now
                self.refresh_groups()
        self.after(120, self._poll)

    # ------------------------------------------------------------------ view
    def refresh_all(self):
        self.refresh_groups()
        self.refresh_channels()

    def _debounced_refresh(self):
        if self._search_job:
            self.after_cancel(self._search_job)
        self._search_job = self.after(250, self.refresh_channels)

    def _row_values(self, c: Channel):
        info = c.info
        if c.status == ONLINE and c.latency is not None:
            info += f" · {c.latency} ms"
        dup = f"{c.dup_reason} as #{c.dup_of}" if c.dup_of else ""
        return (c.uid, STATUS_TEXT[c.status], vis(c.name), vis(c.group or NO_GROUP), vis(info), dup,
                vis(c.url), vis(self._source_labels.get(c.source, short_source(c.source))))

    def _included(self, c: Channel) -> bool:
        """In a ticked group and a ticked playlist = will be saved."""
        return self.group_enabled.get(c.group, True) and self.source_enabled.get(c.source, True)

    def _row_tags(self, c: Channel):
        tags = [c.status]
        if not self._included(c):
            tags.append("excluded")
        if c.dup_of:
            tags.append("dup")                # created first, so its yellow wins over the playlist tint
        if self.v_tint.get():
            tags.append(self._source_tag(c.source))
        return tuple(tags)

    # ------------------------------------------------------------------ playlist colors
    def _source_index(self, src: str) -> int:
        if src not in self.source_color:
            self.source_color[src] = len(self.source_color)
            self.source_enabled.setdefault(src, True)
        return self.source_color[src] % len(PLAYLIST_COLORS)

    def _source_tag(self, src: str) -> str:
        i = self._source_index(src)
        tag = f"src{i}"
        if tag not in self._swatch_images.get("_tags", ()):  # configure each tint once (after "dup")
            self.tree.tag_configure(tag, background=PLAYLIST_COLORS[i][1])
            self._swatch_images.setdefault("_tags", set()).add(tag)
        return tag

    def _swatch(self, src: str) -> tk.PhotoImage:
        i = self._source_index(src)
        if i not in self._swatch_images:
            img = tk.PhotoImage(master=self, width=16, height=14)
            img.put(PLAYLIST_COLORS[i][0], to=(2, 1, 15, 13))
            self._swatch_images[i] = img
        return self._swatch_images[i]

    def _update_row(self, c: Channel):
        iid = str(c.uid)
        if self.tree.exists(iid):
            self.tree.item(iid, values=self._row_values(c), tags=self._row_tags(c), image=self._swatch(c.source))

    def _matches(self, c: Channel, q: str, show: str) -> bool:
        if self.current_group is not None and c.group != self.current_group:
            return False
        if self.current_source is not None and c.source != self.current_source:
            return False
        if (self.v_hide_excluded.get() and not self._included(c) and not show.startswith("Excluded")
                and self.current_group is None and self.current_source is None):
            return False  # unticked: hidden, but shown when its own group / playlist is clicked
        if show == "Online" and c.status != ONLINE:
            return False
        if show == "Offline" and c.status != OFFLINE:
            return False
        if show == "Not checked" and c.status not in (UNCHECKED, CHECKING):
            return False
        if show == "Duplicates" and not c.dup_of:
            return False
        if show.startswith("Problems") and not (c.status == OFFLINE or c.dup_of):
            return False
        if show.startswith("Good") and not (c.status == ONLINE and not c.dup_of):
            return False
        if show.startswith("Included") and not self._included(c):
            return False
        if show.startswith("Excluded") and self._included(c):
            return False
        if q and q not in c.name.casefold() and q not in c.url.casefold() and q not in c.group.casefold():
            return False
        return True

    def _sort_key(self, col):
        return {
            "num": lambda c: c.uid,
            "status": lambda c: (STATUS_RANK[c.status], c.uid),
            "name": lambda c: natural_key(c.name),
            "group": lambda c: (natural_key(c.group), c.uid),
            "info": lambda c: (c.latency if c.status == ONLINE and c.latency is not None else 10 ** 9, c.info),
            "dup": lambda c: (c.dup_of is None, c.dup_of or 0, c.uid),
            "url": lambda c: c.url.casefold(),
            "source": lambda c: (short_source(c.source).casefold(), c.uid),
        }[col]

    def sort_by(self, col):
        if self.sort_col == col:
            self.sort_rev = not self.sort_rev
        else:
            self.sort_col, self.sort_rev = col, False
        for c in self.cols:
            arrow = (" ▼" if self.sort_rev else " ▲") if c == self.sort_col and c != "num" else ""
            self.tree.heading(c, text=self.col_titles[c] + arrow)
        self.refresh_channels()

    def refresh_channels(self):
        self._search_job = None
        q = self.v_search.get().strip().casefold()
        show = self.v_show.get()
        rows = [c for c in self.channels if self._matches(c, q, show)]
        rows.sort(key=self._sort_key(self.sort_col), reverse=self.sort_rev)
        selected = set(self.tree.selection())
        self.tree.delete(*self.tree.get_children())
        for c in rows:
            self.tree.insert("", "end", iid=str(c.uid), values=self._row_values(c), tags=self._row_tags(c),
                             image=self._swatch(c.source))
        keep = [i for i in selected if self.tree.exists(i)]
        if keep:
            self.tree.selection_set(keep)
        self._update_shown_label(len(rows))
        if not self.channels:
            self.set_status("Open a playlist to start:  File → Open, Open folder, or Add from URL.")

    def _update_shown_label(self, shown: int | None = None):
        if shown is None:
            shown = len(self.tree.get_children())
        total = len(self.channels)
        included = sum(1 for c in self.channels if self._included(c))
        text = f"Shown: {shown}   ·   Included: {included} of {total}" if included != total else f"Shown: {shown} of {total}"
        self.lbl_shown.configure(text=text)

    def _inclusion_changed(self, what: str):
        """A group or playlist was ticked / unticked: update counts, grey rows and the status bar."""
        self.refresh_groups()
        if self.v_show.get().startswith(("Included", "Excluded")) or self.v_hide_excluded.get():
            self.refresh_channels()
        else:
            for iid in self.tree.get_children():
                c = self.by_uid.get(int(iid))
                if c is not None:
                    self.tree.item(iid, tags=self._row_tags(c))
            self._update_shown_label()
        included = sum(1 for c in self.channels if self._included(c))
        self.set_status(f"{what} · {included} of {len(self.channels)} channels included (these will be saved).")

    def refresh_groups(self):
        stats: dict[str, list[int]] = {}
        inc_total = inc_online = 0
        for c in self.channels:
            s = stats.setdefault(c.group, [0, 0])
            if not self.source_enabled.get(c.source, True):
                continue                      # its playlist is unticked
            s[0] += 1
            s[1] += c.status == ONLINE
            if self.group_enabled.get(c.group, True):
                inc_total += 1
                inc_online += c.status == ONLINE
        for g in stats:
            if g not in self.group_order:
                self.group_order.append(g)
                self.group_enabled.setdefault(g, True)
        self.group_order = [g for g in self.group_order if g in stats]
        any_checked = any(c.status in (ONLINE, OFFLINE) for c in self.channels)

        sel = self.gtree.selection()
        self._suppress_group_select = True
        self.gtree.delete(*self.gtree.get_children())
        self.gtree.insert("", "end", iid="*", values=("", "★ All channels", inc_total,
                                                       inc_online if any_checked else ""))
        for g in self.group_order:
            total, online = stats[g]
            mark = "☑" if self.group_enabled.get(g, True) else "☐"
            self.gtree.insert("", "end", iid="g:" + g,
                              values=(mark, vis(g or NO_GROUP), total, online if any_checked else ""))
        want = sel[0] if sel and self.gtree.exists(sel[0]) else ("*" if self.current_group is None
                                                                 else "g:" + self.current_group)
        if not self.gtree.exists(want):
            want, self.current_group = "*", None
        self.gtree.selection_set(want)
        self.update_idletasks()
        self._suppress_group_select = False
        self.refresh_sources()

    def refresh_sources(self):
        stats: dict[str, list[int]] = {}
        inc_total = inc_online = 0
        for c in self.channels:
            s = stats.setdefault(c.source, [0, 0])
            if not self.group_enabled.get(c.group, True):
                continue                      # its group is unticked
            s[0] += 1
            s[1] += c.status == ONLINE
            if self.source_enabled.get(c.source, True):
                inc_total += 1
                inc_online += c.status == ONLINE
        self._source_labels = playlist_labels(stats)
        any_checked = any(c.status in (ONLINE, OFFLINE) for c in self.channels)
        order = sorted(stats, key=lambda src: self.source_color.get(src, 10 ** 6))
        self._suppress_source_select = True
        self.ptree.delete(*self.ptree.get_children())
        self.ptree.insert("", "end", iid="*", values=("", "★ All playlists", inc_total,
                                                       inc_online if any_checked else ""))
        for src in order:
            total, online = stats[src]
            mark = "☑" if self.source_enabled.get(src, True) else "☐"
            self.ptree.insert("", "end", iid="s:" + src, image=self._swatch(src),
                              values=(mark, vis(self._source_labels[src]), total, online if any_checked else ""))
        if self.current_source is not None and not self.ptree.exists("s:" + self.current_source):
            self.current_source = None
        self.ptree.selection_set("*" if self.current_source is None else "s:" + self.current_source)
        self.update_idletasks()
        self._suppress_source_select = False

    def on_source_select(self, _e=None):
        if self._suppress_source_select:
            return
        sel = self.ptree.selection()
        new = None if not sel or sel[0] == "*" else sel[0][2:]
        if new != self.current_source:
            self.current_source = new
            self.refresh_channels()
            if new is not None:
                self.set_status(f"Showing only {self._source_labels.get(new, new)} – click “All playlists” to show all.")

    def on_source_click(self, e):
        if self.ptree.identify_column(e.x) == "#1":
            row = self.ptree.identify_row(e.y)
            if row.startswith("s:"):
                src = row[2:]
                self.source_enabled[src] = not self.source_enabled.get(src, True)
                name = self._source_labels.get(src, src)
                self._inclusion_changed(f"Playlist “{name}” " + ("included" if self.source_enabled[src] else "excluded"))
                return "break"
        return None

    # ------------------------------------------------------------------ groups
    def _selected_group(self) -> str | None:
        sel = self.gtree.selection()
        return sel[0][2:] if sel and sel[0].startswith("g:") else None

    def on_group_select(self, _e=None):
        if self._suppress_group_select:
            return
        sel = self.gtree.selection()
        new = None if not sel or sel[0] == "*" else sel[0][2:]
        if new != self.current_group:
            self.current_group = new
            self.refresh_channels()

    def on_group_click(self, e):
        if self.gtree.identify_column(e.x) == "#1":
            row = self.gtree.identify_row(e.y)
            if row.startswith("g:"):
                self.toggle_group(row[2:])
                return "break"
        return None

    def toggle_group(self, g):
        self.group_enabled[g] = not self.group_enabled.get(g, True)
        self._inclusion_changed(f"Group “{g or NO_GROUP}” " + ("included" if self.group_enabled[g] else "excluded"))

    def toggle_selected_group(self):
        g = self._selected_group()
        if g is not None:
            self.toggle_group(g)

    def set_all_groups(self, value: bool):
        for g in self.group_order:
            self.group_enabled[g] = value
        self._inclusion_changed("All groups " + ("included" if value else "excluded"))

    def move_group(self, step: int):
        g = self._selected_group()
        if g is None:
            return
        i = self.group_order.index(g)
        j = i + step
        if 0 <= j < len(self.group_order):
            self.group_order[i], self.group_order[j] = self.group_order[j], self.group_order[i]
            self.refresh_groups()
            self.gtree.see("g:" + g)

    def rename_group(self):
        g = self._selected_group()
        if g is None:
            messagebox.showinfo(APP_TITLE, "Select a group in the list first.", parent=self)
            return
        others = [x for x in self.group_order if x and x != g]
        dlg = ComboDialog(self, "Rename group",
                          f"New name for “{g or NO_GROUP}”\n(choose an existing group to merge into it):", others, g)
        new = dlg.result
        if not new or new == g:
            return
        merging = new in self.group_enabled
        for c in self.channels:
            if c.group == g:
                c.group = new
        if merging:
            self.group_order.remove(g)
        else:
            self.group_order[self.group_order.index(g)] = new
            self.group_enabled[new] = self.group_enabled.get(g, True)
        self.group_enabled.pop(g, None)
        self.current_group = new
        self.recompute_duplicates()
        self.refresh_all()
        self.gtree.selection_set("g:" + new)
        self.set_status(f"Group “{g or NO_GROUP}” {'merged into' if merging else 'renamed to'} “{new}”.")

    # ------------------------------------------------------------------ channel edits
    def _selected_channels(self) -> list[Channel]:
        return [self.by_uid[int(i)] for i in self.tree.selection() if int(i) in self.by_uid]

    def on_right_click(self, e):
        row = self.tree.identify_row(e.y)
        if row and row not in self.tree.selection():
            self.tree.selection_set(row)
        elif not row:
            self.tree.selection_remove(self.tree.selection())
        has_sel = bool(self.tree.selection())
        for i in range(self.cmenu.index("end") + 1):
            if self.cmenu.type(i) != "command":
                continue
            label = self.cmenu.entrycget(i, "label")
            if label.startswith("Paste"):
                state = "normal" if self._clipboard_text().strip() else "disabled"
            elif label.startswith("Recheck all"):
                state = "normal"
            else:
                state = "normal" if has_sel else "disabled"
            self.cmenu.entryconfigure(i, state=state)
        self.tree.focus_set()
        self.cmenu.tk_popup(e.x_root, e.y_root)

    def select_all(self):
        self.tree.selection_set(self.tree.get_children())

    def rename_channel(self):
        sel = self._selected_channels()
        if len(sel) != 1:
            messagebox.showinfo(APP_TITLE, "Select one channel to rename.", parent=self)
            return
        c = sel[0]
        new = simpledialog.askstring("Rename channel", "Channel name:", initialvalue=c.name, parent=self)
        if new and new.strip():
            c.name = new.strip()
            self.recompute_duplicates()
            self.refresh_channels()

    def move_to_group(self):
        sel = self._selected_channels()
        if not sel:
            messagebox.showinfo(APP_TITLE, "Select channels first.", parent=self)
            return
        groups = [g for g in self.group_order if g]
        dlg = ComboDialog(self, "Move to group", f"Move {len(sel)} channel(s) to group\n(pick one or type a new name):",
                          groups, sel[0].group)
        if dlg.result is None:
            return
        new = dlg.result
        for c in sel:
            c.group = new
        if new not in self.group_enabled:
            self.group_enabled[new] = True
            self.group_order.append(new)
        self.refresh_all()
        self.set_status(f"Moved {len(sel)} channel(s) to “{new or NO_GROUP}”.")

    def _remove(self, chans: list[Channel]):
        gone = {c.uid for c in chans}
        self.channels = [c for c in self.channels if c.uid not in gone]
        for uid in gone:
            self.by_uid.pop(uid, None)
        self.recompute_duplicates()
        self.refresh_all()

    def delete_selected(self):
        sel = self._selected_channels()
        if not sel:
            return
        if len(sel) > 1 and not messagebox.askyesno(APP_TITLE, f"Delete {len(sel)} channels from the list?", parent=self):
            return
        self._remove(sel)
        self.set_status(f"Deleted {len(sel)} channel(s).")

    def remove_offline(self):
        off = [c for c in self.channels if c.status == OFFLINE]
        if not off:
            messagebox.showinfo(APP_TITLE, "No offline channels (run “Check streams” first).", parent=self)
            return
        if messagebox.askyesno(APP_TITLE, f"Remove {len(off)} offline channels from the list?", parent=self):
            self._remove(off)
            self.set_status(f"Removed {len(off)} offline channels.")

    def remove_duplicates(self):
        dups = [c for c in self.channels if c.dup_of]
        if not dups:
            messagebox.showinfo(APP_TITLE, "No duplicates found.", parent=self)
            return
        if messagebox.askyesno(APP_TITLE, f"Remove {len(dups)} duplicates from the list?\n"
                                          "(the online / first copy of each channel stays)", parent=self):
            self._remove(dups)
            self.set_status(f"Removed {len(dups)} duplicates.")

    # ------------------------------------------------------------------ clipboard
    def _clipboard_text(self) -> str:
        try:
            return self.clipboard_get()
        except tk.TclError:
            return ""

    def _ctrl_letter(self, e) -> str:
        """Letter of a Ctrl+key press, also when a non-Latin keyboard layout is active."""
        ks = (e.keysym or "").lower()
        if len(ks) == 1 and "a" <= ks <= "z":
            return ks
        table = KEYCODE_LETTERS.get(self.tk.call("tk", "windowingsystem"), {})
        return table.get(e.keycode, "")

    def _tree_ctrl_key(self, e):
        letter = self._ctrl_letter(e)
        if letter == "c":
            self.copy_url()
        elif letter == "v":
            self.paste_channels()
        elif letter == "a":
            self.select_all()
        else:
            return None
        return "break"

    def paste_channels(self):
        """Add channels from the clipboard: stream links (one per line) or copied playlist text."""
        text = self._clipboard_text()
        if not text.strip():
            self.set_status("The clipboard is empty.")
            return
        group = self.current_group or ""
        if "#EXTINF" in text.upper() or text.lstrip("\ufeff \t\r\n").upper().startswith("#EXTM3U"):
            playlist = text
        else:
            urls = [ln.strip() for ln in text.splitlines() if STREAM_URL_RE.match(ln)]
            if not urls:
                messagebox.showinfo(APP_TITLE, "The clipboard has no stream links.\n\n"
                                    "Copy one or more addresses like http://…, https://… or rtmp://… "
                                    "(one per line), or the text of an M3U playlist.", parent=self)
                return
            before = self.uid_counter
            added = self.add_stream_urls(urls, "clipboard", group)
            playlist = None
        if playlist is not None:
            before = self.uid_counter
            added = self.add_playlist_text(playlist, "clipboard", "")
        self.after_load(added)
        new = [str(uid) for uid in range(before + 1, self.uid_counter + 1) if self.tree.exists(str(uid))]
        if new:
            self.tree.selection_set(new)
            self.tree.see(new[-1])
        self.set_status(f"Pasted {added} channel(s) from the clipboard. Right-click → Check selected to test them.")

    def _install_text_field_menus(self):
        """Right-click menu (Cut / Copy / Paste / Delete / Select all) for every text field,
        including the ones in dialogs, plus Ctrl+A/C/V/X that work with any keyboard layout."""
        menu = tk.Menu(self, tearoff=0)
        self._text_menu = menu

        def editable(w) -> bool:
            try:
                if hasattr(w, "instate"):
                    return not w.instate(["disabled"]) and not w.instate(["readonly"])
                return str(w.cget("state")) == "normal"
            except tk.TclError:
                return False

        def has_selection(w) -> bool:
            try:
                return bool(w.selection_present())
            except (tk.TclError, AttributeError):
                return False

        def paste(w):
            text = self._clipboard_text()
            if not text or not editable(w):
                return
            text = " ".join(text.splitlines()).strip() if "\n" in text.strip() else text.strip("\r\n")
            try:
                if has_selection(w):
                    w.delete("sel.first", "sel.last")
            except tk.TclError:
                pass
            w.insert("insert", text)

        def copy(w):
            if has_selection(w):
                try:
                    self.clipboard_clear()
                    self.clipboard_append(w.selection_get())
                except tk.TclError:
                    pass

        def cut(w):
            if has_selection(w) and editable(w):
                copy(w)
                w.delete("sel.first", "sel.last")

        def delete(w):
            if has_selection(w) and editable(w):
                w.delete("sel.first", "sel.last")

        def select_all(w):
            try:
                w.selection_range(0, "end")
                w.icursor("end")
            except tk.TclError:
                pass

        def popup(e):
            w = e.widget
            if isinstance(w, str):
                try:
                    w = self.nametowidget(w)
                except KeyError:
                    return None
            try:
                w.focus_set()
            except tk.TclError:
                pass
            can_edit, sel = editable(w), has_selection(w)
            clip = bool(self._clipboard_text())
            menu.delete(0, "end")
            menu.add_command(label="Cut", accelerator="Ctrl+X", command=lambda: cut(w),
                             state="normal" if can_edit and sel else "disabled")
            menu.add_command(label="Copy", accelerator="Ctrl+C", command=lambda: copy(w),
                             state="normal" if sel else "disabled")
            menu.add_command(label="Paste", accelerator="Ctrl+V", command=lambda: paste(w),
                             state="normal" if can_edit and clip else "disabled")
            menu.add_command(label="Delete", command=lambda: delete(w),
                             state="normal" if can_edit and sel else "disabled")
            menu.add_separator()
            menu.add_command(label="Select all", accelerator="Ctrl+A", command=lambda: select_all(w))
            menu.tk_popup(e.x_root, e.y_root)
            return "break"

        def ctrl_key(e):
            w = e.widget
            if isinstance(w, str) or w.winfo_class() not in TEXT_FIELD_CLASSES:
                return None
            ks = (e.keysym or "").lower()
            latin = len(ks) == 1 and "a" <= ks <= "z"
            letter = self._ctrl_letter(e)
            if letter == "a":                 # Tk on Linux would jump to the line start instead
                select_all(w)
                return "break"
            if letter in ("c", "v", "x") and not latin:   # Latin layout: Tk's own bindings do it
                {"c": copy, "v": paste, "x": cut}[letter](w)
                return "break"
            return None

        # Ctrl+A = select all (Tk on Linux uses it for "go to line start")
        try:
            self.event_delete("<<LineStart>>", "<Control-Key-a>")
            self.event_add("<<SelectAll>>", "<Control-Key-a>", "<Control-Key-A>")
        except tk.TclError:
            pass
        self._text_ctrl_key = ctrl_key  # (used by tests)
        for cls in TEXT_FIELD_CLASSES:
            self.bind_class(cls, "<Button-3>", popup)
            self.bind_class(cls, "<Button-2>", popup) if sys.platform == "darwin" else None
            self.bind_class(cls, "<Control-KeyPress>", ctrl_key, add="+")

    def copy_url(self):
        sel = self._selected_channels()
        if sel:
            self.clipboard_clear()
            self.clipboard_append("\n".join(c.url for c in sel))
            self.set_status(f"Copied {len(sel)} URL(s).")

    def play_selected(self):
        sel = self._selected_channels()
        if not sel:
            return
        c = sel[0]
        url, headers = split_url_headers(c.export_url())
        player = find_player()
        try:
            if player:
                args = [player, url]
                ua, ref = c.http_options()
                ua = ua or headers.get("User-Agent") or (self.v_ua.get().strip() if
                                                        self.v_ua.get().strip() != DEFAULT_UA else None)
                ref = ref or headers.get("Referer")
                if "vlc" in Path(player).name.lower():
                    if ua:
                        args.append(f":http-user-agent={ua}")
                    if ref:
                        args.append(f":http-referrer={ref}")
                subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL, start_new_session=True)
                self.set_status(f"Playing “{c.name}” in {Path(player).stem}.")
            else:
                if sys.platform.startswith("win"):
                    os.startfile(url)  # type: ignore[attr-defined]
                else:
                    webbrowser.open(url)
                self.set_status("VLC not found – opened with the default program. Install VLC for best results.")
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not start the player:\n{e}", parent=self)

    # ------------------------------------------------------------------ duplicates
    def recompute_duplicates(self):
        mark_duplicates(self.channels, self.v_dup_url.get(), self.v_dup_name.get(), self.v_dup_quality.get())

    def on_dup_options(self):
        self.recompute_duplicates()
        self.refresh_channels()
        self.set_status(f"{sum(1 for c in self.channels if c.dup_of)} duplicates with the current settings.")

    # ------------------------------------------------------------------ saving
    def select_for_export(self, o: dict) -> list[Channel]:
        items = [c for c in self.channels
                 if not (o["drop_offline"] and c.status == OFFLINE)
                 and not (o["drop_unchecked"] and c.status in (UNCHECKED, CHECKING))
                 and not (o["only_enabled_groups"] and not self.group_enabled.get(c.group, True))
                 and not (o["only_enabled_groups"] and not self.source_enabled.get(c.source, True))]
        if o["drop_dups"]:
            # decided among the channels that are really saved: a channel is never dropped
            # because its "original" sits in an excluded group
            dups = find_duplicates(items, self.v_dup_url.get(), self.v_dup_name.get(), self.v_dup_quality.get())
            items = [c for c in items if c.uid not in dups]
        order = {g: i for i, g in enumerate(self.group_order)}
        gkey = (lambda c: (c.group == "", natural_key(c.group))) if o["sort_groups"] else (lambda c: order.get(c.group, 10 ** 6))
        ckey = (lambda c: natural_key(c.name)) if o["sort_channels"] else (lambda c: c.uid)
        items.sort(key=lambda c: (gkey(c), ckey(c)))
        return items

    def export_dialog(self):
        if not self.channels:
            messagebox.showinfo(APP_TITLE, "Open a playlist first.", parent=self)
            return
        if self.checking:
            messagebox.showinfo(APP_TITLE, "Wait until the check finishes (or press Stop).", parent=self)
            return
        on = sum(c.status == ONLINE for c in self.channels)
        off = sum(c.status == OFFLINE for c in self.channels)
        dups = sum(1 for c in self.channels if c.dup_of)
        included = sum(1 for c in self.channels if self._included(c))
        summary = f"{len(self.channels)} channels:  {on} online · {off} offline · {dups} duplicates"
        if included != len(self.channels):
            summary += f"\n{included} in ticked groups and playlists"
        opts = ExportDialog(self, summary, self.settings.get("export")).result
        if not opts:
            return
        self.settings["export"] = opts
        self.save_settings()
        items = self.select_for_export(opts)
        if not items:
            messagebox.showwarning(APP_TITLE, "Nothing to save with these options.", parent=self)
            return
        ext = opts["format"]
        try:
            if opts["split"]:
                folder = self._fd().askdirectory(parent=self, title="Folder for the group playlists",
                                                 initialdir=self.settings.get("last_dir") or str(Path.home()))
                if not folder:
                    return
                by_group: dict[str, list[Channel]] = {}
                for c in items:
                    by_group.setdefault(c.group, []).append(c)
                used = set()
                for g, chans in by_group.items():
                    base = fname = safe_filename(g or "No group")
                    n = 2
                    while fname.casefold() in used:
                        fname, n = f"{base} ({n})", n + 1
                    used.add(fname.casefold())
                    self._write(os.path.join(folder, dated_name(fname, ext, self.v_date_names.get(),
                                                                    self.v_prefix_names.get())), chans, ext)
                messagebox.showinfo(APP_TITLE, f"Saved {len(by_group)} playlists ({len(items)} channels) to:\n{folder}",
                                    parent=self)
            else:
                path = self._fd().asksaveasfilename(
                    parent=self, title="Save new playlist", defaultextension="." + ext,
                    initialdir=self.settings.get("last_dir") or str(Path.home()),
                    initialfile=dated_name(self._default_basename(), ext, self.v_date_names.get(),
                                           self.v_prefix_names.get()),
                    filetypes=[(f"{ext.upper()} playlist", f"*.{ext}"), ("All files", "*.*")])
                if not path:
                    return
                self._write(path, items, ext)
                self.settings["last_dir"] = str(Path(path).parent)
                messagebox.showinfo(APP_TITLE, f"Saved {len(items)} channels to:\n{path}", parent=self)
            self.set_status(f"Saved {len(items)} channels.")
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not save:\n{e}", parent=self)

    def _default_basename(self) -> str:
        """Name of the opened playlist if there is just one local file, otherwise empty."""
        sources = {c.source for c in self.channels}
        if len(sources) == 1:
            src = next(iter(sources))
            if "://" not in src:
                return safe_filename(Path(src).stem)
        return ""

    def _write(self, path, items, ext):
        if ext == "pls":
            write_pls(path, items)
        else:
            write_m3u(path, items, self.header)

    def export_report(self):
        if not self.channels:
            messagebox.showinfo(APP_TITLE, "Open a playlist first.", parent=self)
            return
        path = self._fd().asksaveasfilename(
            parent=self, title="Save check report", defaultextension=".csv",
            initialdir=self.settings.get("last_dir") or str(Path.home()),
            initialfile=dated_name(self._default_basename(), "csv", self.v_date_names.get(),
                                   self.v_prefix_names.get(), suffix="report"),
            filetypes=[("CSV (Excel)", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow(["#", "Status", "Check result", "Response ms", "Duplicate", "Channel", "Group", "URL", "Playlist"])
                for c in self.channels:
                    w.writerow([c.uid, c.status, c.info, c.latency if c.status == ONLINE else "",
                                f"{c.dup_reason} as #{c.dup_of}" if c.dup_of else "",
                                c.name, c.group, c.url, c.source])
            self.set_status(f"Report saved: {path}")
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not save:\n{e}", parent=self)

    # ------------------------------------------------------------------ settings menu
    def _fd(self):
        """File dialogs: apply 'hide hidden files' before every dialog (Linux Tk dialog)."""
        if self.tk.call("tk", "windowingsystem") == "x11":
            try:
                try:  # load the Tk file dialog code so its variables exist
                    self.tk.call("tk_getOpenFile", "-foobarbaz")
                except tk.TclError:
                    pass
                self.tk.call("set", "::tk::dialog::file::showHiddenBtn", "1")
                self.tk.call("set", "::tk::dialog::file::showHiddenVar", "0" if self.v_hide_hidden.get() else "1")
            except tk.TclError:
                pass
        return filedialog

    def on_bidi_option(self):
        BIDI["enabled"] = self.v_bidi.get()
        self.save_settings()
        self.refresh_all()
        self.set_status("Right-to-left text fix is " + ("on." if BIDI["enabled"] else "off."))

    def on_user_agent(self, name: str):
        self.save_settings()
        self.set_status(f"User-Agent: {name}. Press “Check streams” or “Recheck offline” to check with it.")

    def custom_user_agent(self):
        value = simpledialog.askstring("Custom User-Agent",
                                       "User-Agent text (exactly as your player or provider requires):",
                                       initialvalue=self.v_ua.get(), parent=self)
        if value and value.strip():
            self.v_ua.set(value.strip())
            self.on_user_agent(user_agent_name(value.strip()))

    def on_hidden_option(self):
        self.save_settings()
        self.set_status("Hidden files and folders are now " +
                        ("hidden in dialogs and folder scans." if self.v_hide_hidden.get() else "shown."))

    def _set_app_icon(self):
        try:
            self._icons = [tk.PhotoImage(master=self, data=ICON_PNGS[px]) for px in (256, 64, 32)]
            self.iconphoto(True, *self._icons)
        except tk.TclError:
            pass

    @staticmethod
    def _xdg_data() -> Path:
        return Path(os.environ.get("XDG_DATA_HOME") or Path.home() / ".local" / "share")

    @staticmethod
    def _desktop_dir() -> Path | None:
        try:
            out = subprocess.run(["xdg-user-dir", "DESKTOP"], capture_output=True, text=True, timeout=3).stdout.strip()
            if out and Path(out).is_dir() and Path(out) != Path.home():
                return Path(out)
        except Exception:
            pass
        d = Path.home() / "Desktop"
        return d if d.is_dir() else None

    def _install_icon(self) -> Path:
        base = self._xdg_data() / "icons" / "hicolor"
        for px in (32, 64, 256):
            d = base / f"{px}x{px}" / "apps"
            d.mkdir(parents=True, exist_ok=True)
            (d / f"{LAUNCHER_ID}.png").write_bytes(base64.b64decode(ICON_PNGS[px]))
        return base / "256x256" / "apps" / f"{LAUNCHER_ID}.png"

    def _desktop_entry(self) -> str:
        system_entry = Path("/usr/share/applications") / f"{LAUNCHER_ID}.desktop"
        if INSTALLED and system_entry.is_file():
            return system_entry.read_text(encoding="utf-8")
        script = Path(__file__).resolve()
        icon = self._install_icon()
        return "\n".join([
            "[Desktop Entry]",
            "Type=Application",
            f"Name={APP_TITLE}",
            "Comment=Check IPTV and radio playlists for dead streams and duplicates",
            f"Exec={desktop_quote(sys.executable)} {desktop_quote(str(script))} %F",
            f"Icon={icon}",
            "Terminal=false",
            "Categories=AudioVideo;Video;",
            "Keywords=IPTV;M3U;playlist;radio;TV;stream;",
            "MimeType=audio/x-mpegurl;audio/mpegurl;application/vnd.apple.mpegurl;application/x-mpegurl;"
            "audio/x-scpls;application/xspf+xml;",
            "StartupWMClass=Playlistchecker",  # Tk class name of the window
        ]) + "\n"

    def _replace_old_launchers(self):
        """Installed from the package: a menu entry made earlier by the stand-alone version
        (Settings -> Add to applications menu) has the same name and hides the package's entry -
        with the old program path and icon. Remove it, and point an old desktop shortcut to the
        installed program."""
        if not (INSTALLED and sys.platform.startswith("linux")):
            return
        system_entry = Path("/usr/share/applications") / f"{LAUNCHER_ID}.desktop"
        if not system_entry.is_file():
            return

        def is_old(f: Path) -> bool:
            try:
                text = f.read_text(encoding="utf-8")
            except OSError:
                return False
            return "playlist_checker_gui.py" in text and "Exec=playlist-checker" not in text

        fixed = []
        user_entry = self._xdg_data() / "applications" / f"{LAUNCHER_ID}.desktop"
        if user_entry.is_file() and is_old(user_entry):
            try:
                user_entry.unlink()
                for px in (32, 64, 256):
                    icon = self._xdg_data() / "icons" / "hicolor" / f"{px}x{px}" / "apps" / f"{LAUNCHER_ID}.png"
                    if icon.is_file():
                        icon.unlink()
                fixed.append("menu entry")
            except OSError:
                pass
            try:  # refresh the personal file-type index that still names the old entry
                subprocess.run(["update-desktop-database", str(user_entry.parent)], capture_output=True, timeout=15)
            except Exception:
                pass
        desktop = self._desktop_dir()
        shortcut = desktop / f"{LAUNCHER_ID}.desktop" if desktop else None
        if shortcut and shortcut.is_file() and is_old(shortcut):
            try:
                shortcut.write_text(system_entry.read_text(encoding="utf-8"), encoding="utf-8")
                shortcut.chmod(0o755)
                fixed.append("desktop shortcut")
            except OSError:
                pass
        if fixed:
            self.set_status("Replaced the old " + " and ".join(fixed) +
                            " from the stand-alone version with the installed one.")

    def add_to_app_menu(self):
        try:
            apps = self._xdg_data() / "applications"
            apps.mkdir(parents=True, exist_ok=True)
            f = apps / f"{LAUNCHER_ID}.desktop"
            f.write_text(self._desktop_entry(), encoding="utf-8")
            f.chmod(0o755)
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not add the app to the menu:\n{e}", parent=self)
            return
        try:
            subprocess.run(["update-desktop-database", str(apps)], capture_output=True, timeout=15)
        except Exception:
            pass  # optional tool - the menu entry works without it
        messagebox.showinfo(APP_TITLE, f"“{APP_TITLE}” was added to your applications menu.\n\n"
                                       "If you move this program file, use this option again.", parent=self)

    def create_desktop_shortcut(self):
        d = self._desktop_dir()
        if d is None:
            messagebox.showerror(APP_TITLE, "Could not find your Desktop folder.", parent=self)
            return
        f = d / f"{LAUNCHER_ID}.desktop"
        try:
            f.write_text(self._desktop_entry(), encoding="utf-8")
            f.chmod(0o755)
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not create the shortcut:\n{e}", parent=self)
            return
        try:  # GNOME / Ubuntu: mark the launcher as trusted
            subprocess.run(["gio", "set", str(f), "metadata::trusted", "true"], capture_output=True, timeout=5)
        except Exception:
            pass
        messagebox.showinfo(APP_TITLE, f"Shortcut created on your desktop:\n{f}\n\n"
                                       "On Ubuntu, if the icon looks inactive the first time, right-click it and "
                                       "choose “Allow Launching”.", parent=self)

    def remove_launchers(self):
        removed = []
        targets = [] if INSTALLED else [self._xdg_data() / "applications" / f"{LAUNCHER_ID}.desktop"]
        d = self._desktop_dir()
        if d:
            targets.append(d / f"{LAUNCHER_ID}.desktop")
        if not INSTALLED:
            targets += [self._xdg_data() / "icons" / "hicolor" / f"{px}x{px}" / "apps" / f"{LAUNCHER_ID}.png"
                        for px in (32, 64, 256)]
        for t in targets:
            try:
                if t.exists():
                    t.unlink()
                    removed.append(t)
            except OSError:
                pass
        done = "Removed the desktop shortcut." if INSTALLED else "Removed the menu entry and desktop shortcut."
        messagebox.showinfo(APP_TITLE, done if removed else "Nothing to remove.", parent=self)

    # ------------------------------------------------------------------ misc
    def clear_all(self):
        if self.channels and not messagebox.askyesno(APP_TITLE, "Clear the whole list?", parent=self):
            return
        self.stop_event.set()
        if self.downloading:
            self._dl_stop.set()
            self._dl_gen += 1
        self.channels.clear()
        self.by_uid.clear()
        self.header.clear()
        self.group_enabled.clear()
        self.group_order.clear()
        self.source_color.clear()
        self.source_enabled.clear()
        self.current_source = None
        self.current_group = None
        self.progress.configure(value=0)
        self.refresh_all()

    def show_help(self):
        messagebox.showinfo("How to use", (
            "1. Open playlists: files, a whole folder, a web address (IPTV provider link), or a .txt list "
            "with one playlist address per line (File → Open list of playlist URLs, Ctrl+L).\n"
            "2. Press “Check streams” (F5). Green = online, red = offline, yellow rows = duplicates.\n"
            "3. Groups on the left: click a group to see its channels; click ☑ to exclude it; "
            "▲ ▼ to reorder; Rename… to rename or merge groups.\n"
            "4. Right-click channels: play in VLC, check again, rename, move to group, delete.\n"
            "5. “Save new playlist” writes a clean playlist (offline and duplicates removed by default). "
            "Logos, EPG (tvg-id, url-tvg) and VLC options are kept.\n\n"
            "Tips: some providers block unknown players – keep the VLC User-Agent. "
            "UDP/multicast links can only be tested inside your provider's network."), parent=self)

    def open_link(self, url: str):
        try:
            if not webbrowser.open(url):
                raise RuntimeError("no web browser found")
            self.set_status(f"Opened {url}")
        except Exception:
            self.clipboard_clear()
            self.clipboard_append(url)
            messagebox.showinfo(APP_TITLE, f"Could not open a web browser.\nThe address was copied:\n{url}",
                                parent=self)

    def show_about(self):
        dlg = tk.Toplevel(self)
        dlg.title("About")
        dlg.transient(self)
        dlg.resizable(False, False)
        body = ttk.Frame(dlg, padding=18)
        body.pack(fill="both", expand=True)
        try:
            self._about_icon = tk.PhotoImage(master=dlg, data=ICON_PNGS[64])
            ttk.Label(body, image=self._about_icon).grid(row=0, column=0, rowspan=3, sticky="n", padx=(0, 16))
        except tk.TclError:
            pass
        big = tkfont.nametofont("TkDefaultFont").copy()
        big.configure(size=big.cget("size") + 4, weight="bold")
        link_font = tkfont.nametofont("TkDefaultFont").copy()
        link_font.configure(underline=True)
        dlg._fonts = [big, link_font]  # keep references while the window is open
        ttk.Label(body, text=APP_TITLE, font=big).grid(row=0, column=1, sticky="w")
        ttk.Label(body, text=f"Version {APP_VERSION}").grid(row=1, column=1, sticky="w", pady=(2, 8))
        ttk.Label(body, wraplength=380, justify="left",
                  text="Checks IPTV and radio playlists for dead streams and duplicates, "
                       "organises groups and saves clean playlists.").grid(row=2, column=1, sticky="w")

        ttk.Label(body, text="Project page:").grid(row=3, column=1, sticky="w", pady=(14, 0))
        link = ttk.Label(body, text=PROJECT_URL, foreground="#1a5fb4", cursor="hand2", font=link_font)
        link.grid(row=4, column=1, sticky="w")
        link.bind("<Button-1>", lambda e: self.open_link(PROJECT_URL))
        link.bind("<Enter>", lambda e: link.configure(foreground="#0b3d91"))
        link.bind("<Leave>", lambda e: link.configure(foreground="#1a5fb4"))

        info = (f"Python {sys.version.split()[0]} · Tk {self.tk.call('info', 'patchlevel')}\n"
                f"Settings: {SETTINGS_FILE}")
        ttk.Label(body, text=info, foreground="#666666", justify="left").grid(row=5, column=1, sticky="w", pady=(14, 0))

        buttons = ttk.Frame(body)
        buttons.grid(row=6, column=0, columnspan=2, sticky="e", pady=(16, 0))

        def copy_link():
            self.clipboard_clear()
            self.clipboard_append(PROJECT_URL)
            copy_btn.configure(text="Copied ✓")
        ttk.Button(buttons, text="Open project page", command=lambda: self.open_link(PROJECT_URL)).pack(side="left", padx=3)
        copy_btn = ttk.Button(buttons, text="Copy link", command=copy_link)
        copy_btn.pack(side="left", padx=3)
        close = ttk.Button(buttons, text="Close", command=dlg.destroy)
        close.pack(side="left", padx=3)
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        dlg.bind("<Return>", lambda e: dlg.destroy())
        dlg.update_idletasks()
        x = self.winfo_rootx() + (self.winfo_width() - dlg.winfo_width()) // 2
        y = self.winfo_rooty() + (self.winfo_height() - dlg.winfo_height()) // 3
        dlg.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        close.focus_set()
        try:
            dlg.grab_set()
        except tk.TclError:
            pass

    def set_status(self, text: str):
        self.lbl_status.configure(text=vis(text))

    @staticmethod
    def _int(var: tk.Variable, default: int) -> int:
        try:
            return int(float(var.get()))
        except (ValueError, tk.TclError):
            return default

    def save_settings(self):
        self.settings.update({
            "timeout": self._int(self.v_timeout, 8), "threads": self._int(self.v_threads, 20),
            "user_agent": self.v_ua.get().strip() or DEFAULT_UA, "deep_hls": self.v_deep.get(),
            "ignore_ssl": self.v_ssl.get(), "dup_url": self.v_dup_url.get(),
            "dup_name": self.v_dup_name.get(), "dup_quality": self.v_dup_quality.get(),
            "hide_hidden": self.v_hide_hidden.get(), "date_names": self.v_date_names.get(),
            "prefix_names": self.v_prefix_names.get(), "auto_check": self.v_auto_check.get(),
            "tint_rows": self.v_tint.get(), "hide_excluded": self.v_hide_excluded.get(),
            "bidi_fix": self.v_bidi.get(), "confirm_exit": self.v_confirm_exit.get(),
            "encoding": self.v_encoding.get()})
        try:
            SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
            SETTINGS_FILE.write_text(json.dumps(self.settings, indent=2, ensure_ascii=False), encoding="utf-8")
        except OSError:
            pass

    def on_close(self):
        if self.v_confirm_exit.get():
            question = "Exit the program?"
            if self.checking:
                question = "A stream check is still running.\nStop it and exit?"
            elif self.downloading:
                question = "Playlists are still being downloaded.\nStop and exit?"
            elif self.channels:
                question = "Exit the program?\nChanges that were not saved to a playlist will be lost."
            if not messagebox.askyesno(APP_TITLE, question, icon="question", parent=self):
                return
        self.stop_event.set()
        self.save_settings()
        self.destroy()


# Application icon (TV with play button, radio waves and a green check) - PNG, base64
ICON_PNGS = {
    32: "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",
    64: "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",
    256: "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",
}


USAGE = f"""Usage: playlist-checker [PLAYLIST | URL | LIST.txt ...]

{APP_TITLE} {APP_VERSION}
Checks IPTV / internet radio playlists (M3U, M3U8, PLS, XSPF) for dead streams
and duplicates, organises groups and saves clean playlists.

  PLAYLIST   playlist files to open (.m3u .m3u8 .pls .xspf)
  URL        web address of a playlist to download
  LIST.txt   text file with one playlist address per line (all are downloaded)

Options:
  -h, --help       show this help and exit
  -V, --version    show the version and exit

Project page: {PROJECT_URL}
"""


def main():
    args = sys.argv[1:]
    if any(a in ("-h", "--help") for a in args):
        print(USAGE)
        return
    if any(a in ("-V", "--version") for a in args):
        print(f"playlist-checker {APP_VERSION}")
        return
    if sys.platform.startswith("win"):
        try:  # sharp text on high-DPI screens
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    try:
        app = App([a for a in args if a != "--"])
    except tk.TclError as e:
        print(f"playlist-checker: cannot open the window: {e}\n"
              "This program needs a graphical desktop (it can't run over plain SSH).", file=sys.stderr)
        sys.exit(1)
    app.mainloop()
    # stream checks still waiting for a slow server must not keep the process alive after the window closed
    sys.stdout.flush()
    sys.stderr.flush()
    if threading.active_count() > 1:
        os._exit(0)


if __name__ == "__main__":
    main()

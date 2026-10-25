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
import copy
import shlex
import tempfile
import hashlib
import csv
import gzip
import http.client
import io
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
APP_VERSION = "1.7.0"
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
RESULTS_FILE = CONFIG_DIR / "results.json"      # Settings -> Remember check results between sessions
RESULTS_MAX = 50_000          # remembered streams (the oldest results are dropped first)
RESULTS_MAX_DAYS = 180        # results older than this are forgotten
OLD_SETTINGS_FILE = Path.home() / ".playlist_checker_gui.json"  # used by earlier versions
# installed as a system package (deb) -> the menu entry already exists
INSTALLED = str(Path(__file__).resolve()).startswith(("/usr/", "/opt/"))
LEGACY_ENCODINGS = [("auto", "Auto-detect"), ("cp1255", "Hebrew (Windows-1255)"),
                    ("cp1251", "Cyrillic (Windows-1251)"), ("cp1256", "Arabic (Windows-1256)"),
                    ("cp1252", "Western European (Windows-1252)")]
PLAYLIST_EXT = (".m3u", ".m3u8", ".pls", ".xspf")
PLAYLIST_EXT_ALL = PLAYLIST_EXT + tuple(ext + ".gz" for ext in PLAYLIST_EXT)


def is_playlist_name(name: str) -> bool:
    """A playlist file name, including gzip-compressed .m3u.gz / .m3u8.gz / .pls.gz / .xspf.gz."""
    return name.lower().endswith(PLAYLIST_EXT_ALL)


NO_GROUP = "(no group)"
UNDO_MAX_STEPS = 30           # Edit -> Undo remembers this many changes ...
UNDO_MAX_CHANNELS = 300_000   # ... but not more channel copies than this in all (huge playlists)
# what a check found out about a channel: an undo keeps the newest of these (it does not "un-check")
CHECK_FIELDS = ("status", "info", "latency", "seg_hash", "audio", "quality", "pic_hash", "pic_spread", "pic_gray",
                "pic_motion", "pic_colors", "pic_src", "pic_time", "checked_at", "remembered", "prev_status",
                "prev_time", "checked_ua")
LAUNCHER_ID = "playlist-checker"
# physical key codes of A, C, V, X, Y, Z: Ctrl+A/C/V/X/Z/Y must also work while a Hebrew or
# Russian keyboard layout is active (Tk on Linux sees "hebrew_bet", not "c")
KEYCODE_LETTERS = {"x11": {38: "a", 54: "c", 55: "v", 53: "x", 52: "z", 29: "y"},
                   "win32": {65: "a", 67: "c", 86: "v", 88: "x", 90: "z", 89: "y"}}
TEXT_FIELD_CLASSES = ("Entry", "TEntry", "TCombobox", "Spinbox", "TSpinbox")
STREAM_URL_RE = re.compile(r"^\s*(?:https?|rtmpe?|rtmps|rtmpt|rtsps?|mmsh?|mmst|udp|rtp|srt)://\S+", re.I)
AUDIO_URL_RE = re.compile(r"\.(?:mp3|aac|ogg|oga|opus|flac|m4a|m4b|wav|wma)(?:$|[?|])", re.I)

ONLINE, OFFLINE, UNCHECKED, CHECKING = "online", "offline", "unchecked", "checking"
BLOCKED = "blocked"   # answers, but "not available in your country" / placeholder video
STATUS_TEXT = {ONLINE: "● Online", OFFLINE: "✖ Offline", UNCHECKED: "○ Not checked", CHECKING: "… Checking",
               BLOCKED: "⛔ Geo-blocked"}
STATUS_RANK = {ONLINE: 0, UNCHECKED: 1, CHECKING: 1, OFFLINE: 2, BLOCKED: 2}
FINAL_STATUSES = (ONLINE, OFFLINE, BLOCKED)     # results worth remembering / comparing
STATUS_WORD = {ONLINE: "online", OFFLINE: "offline", BLOCKED: "geo-blocked"}
SHOW_CHANGED = "Changed since the last check"

# ---- "not available in your country" detection
# addresses a server redirects to, or takes the video from, when a channel is blocked
GEO_URL_RE = re.compile(
    r"geo[-_.]?(?:block\w*|restrict\w*|fenc\w*|lock\w*|error|denied|forbidden|filter\w*)|"
    r"not[-_.]?available|unavailable|out[-_.]?of[-_.]?(?:region|country|area)|"
    r"(?:region|country|territory)[-_.]?(?:block\w*|lock\w*|restrict\w*|error|denied)|"
    r"blocked[-_.]?(?:region|country|content|video|stream)|(?:^|[/_.-])blocked(?:$|[/_.-])|"
    r"access[-_.]?denied|no[-_.]?rights|zaglushk\w*|stub[-_.]?video", re.I)
# text of an error page / 403 answer that means "blocked where you are"
GEO_TEXT_RE = re.compile(
    r"\bgeo|your (?:country|region|location|area|territory)|not available in|outside (?:of )?(?:the )?"
    r"(?:country|region|us|uk|eu)|territor|region|country|"
    r"недоступ|регион|стран[еыа]|территори|местоположени|регіон|країн|"
    r"אינו זמין|לא זמין|מחוץ ל|בארצך|באזורך|במיקומך", re.I)
# answers that mean "try again later", not "this channel is gone": a second try often works
TEMP_ERROR_RE = re.compile(
    r"timeout|timed out|HTTP (?:408|425|429|50[0234]|52[0-9])\b|closed the connection|connection reset|"
    r"reset by peer|aborted|broken pipe|temporar|remote end closed|EOF occurred|incomplete read", re.I)
RETRY_PAUSE = 3            # seconds to wait before the second try
RETRY_THREADS = 8          # fewer at once, so a busy server gets a chance to answer
LOOP_MAX_SECONDS = 600     # a "live" HLS stream that ends after <= 10 min is a looping placeholder
PIC_W, PIC_H = 80, 45      # thumbnail taken from each video channel
PIC_MAX_DIST = 6           # pictures whose fingerprints differ in <= 6 of 64 bits are "the same"
PIC_MIN_SPREAD = 8.0       # (almost) plain black / one-color frames are not compared
PIC_FRAMES = 3             # frames taken from one download: at 0 s, ~0.8 s and ~1.6 s
PIC_FRAME_GAP = 0.8        # seconds between them
PIC_MOVING = 0.006         # > 0.6 % of the picture changes between frames = moving, i.e. live TV
LEARNED_MOVING = 0.10      # a learned banner may have a small animation; still compare it up to 10 %
PIC_COLOR_MAX = 20         # colour layouts differing by more than this (0-255 average) are not the same
PIC_COLOR_GRID = 4         # colour layout: average colour of 4 x 4 areas
STILL_CHECK_GAP = 8         # seconds between the two pictures of the still-banner test
SAME_PICTURE_MIN = 3       # this many different channels with one picture = probably a banner
BLACK_MAX_GRAY = 16        # average brightness (0-255) below this = black screen (a small logo may stay)
BLACK_CHANGE_MAX = 0.02    # black screen: at most 2 % of the picture changed in STILL_CHECK_GAP seconds
BLACK_STEP = 4             # ... counting changes of more than 4 brightness steps (dark scenes change little)
PREVIEW_W, PREVIEW_H = 640, 360   # sharper picture shown when asking about a banner

TCP_PORTS = {"rtmp": 1935, "rtmpe": 1935, "rtmpt": 80, "rtmps": 443, "rtsp": 554, "rtsps": 322,
             "mms": 1755, "mmst": 1755, "mmsh": 80}
NOT_CHECKABLE = {"udp", "rtp", "igmp", "srt", "acestream", "magnet", "p2p", "sop"}

SHOW_OPTIONS = ["All", "Online", "Offline", "Geo-blocked", "Not checked", "Duplicates", SHOW_CHANGED,
                "Problems (offline, blocked, duplicates)", "Good (online, unique)",
                "Included (will be saved)", "Excluded (unticked)"]

ATTR_RE = re.compile(r'([A-Za-z0-9_\-:.]+)\s*=\s*(?:"([^"]*)"|\'([^\']*)\'|([^\s"\',]+))')
QUALITY_RE = re.compile(r"\b(?:uhd|fhd|hd|sd|hq|lq|4k|8k|hevc|h\.?26[45]|\d{3,4}p|\d{2}\s?fps|backup|orig(?:inal)?)\b", re.I)
# words that name another version of the SAME channel (quality, subtitles, second source ...)
VARIANT_RE = re.compile(
    r"\b(?:subs?|subtitles?|cc|mobile|lite|low|high|multi|alt|mirror|reserve|backup\s*\d*|"
    r"(?:source|src|feed|link|stream|server|option|var|alt|mirror)\s*\d+)\b"
    r"|כתוביות|מתורגם|מקור\s*\d*|גיבוי|резерв\w*|источник\s*\d*|запасн\w*|субтитр\w*", re.I)
VARIANT_ID_PART = re.compile(
    r"hevc|h26[45]|avc|uhd|fhd|hd|sd|hq|lq|4k|8k|\d{3,4}[pi]|\d{2}fps|subs?|subtitles?|cc|mobile|lite|"
    r"low|high|multi|orig(?:inal)?|(?:src|source|backup|alt|mirror|feed|link|stream|server|reserve)\d*")
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
    pic_hash: int | None = None   # fingerprint of one video frame (needs ffmpeg)
    pic_spread: float = 0.0
    pic_gray: float = 0.0
    pic_motion: float | None = None   # share of the picture that moves (None: unknown)
    pic_colors: list | None = None    # colour layout of the picture
    seg_hash: str | None = None   # fingerprint of the first HLS video segment
    pic_src: tuple | None = None  # (address ffmpeg used for the picture, is HLS)
    pic_time: float = 0.0         # when the picture was taken (time.monotonic)
    audio: bool = False           # the last check found audio, not video (no picture check)
    quality: dict | None = None   # resolution, codec, frame rate, bitrate (see quality_text)
    checked_at: float = 0.0       # when the shown result was found (time.time(); 0 = never)
    remembered: bool = False      # the result comes from an earlier session (not checked now)
    checked_ua: str | None = None  # Settings User-Agent the shown result was found with (None: not known)
    prev_status: str | None = None   # result before the latest check (to show what changed)
    prev_time: float = 0.0

    @property
    def changed(self) -> bool:
        """The latest check gave another result than the check before it (this or an earlier session)."""
        return self.prev_status is not None and self.status in FINAL_STATUSES and self.status != self.prev_status

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
        if not is_local(u):
            return u
        p = os.path.expanduser(u)            # ~/videos/a.ts -> /home/me/videos/a.ts
        if not os.path.isabs(p) and self.base_dir:
            return os.path.normpath(os.path.join(self.base_dir, p))
        return p

    def result_key(self, global_ua: str = "") -> str:
        """Where the remembered check result of this channel is kept: the stream address plus the
        headers the check sends with it (a server may answer another User-Agent or Referer
        differently), the same way the checker picks them: Kodi 'url|User-Agent=…' first, then
        #EXTVLCOPT / attributes, then the User-Agent of Settings. Relative local paths are resolved,
        so "stream.ts" in two different folders does not share one result. The key is a hash, so
        results.json holds no stream addresses or logins."""
        if is_local(self.url):
            return result_hash(norm_url(self.export_url()))
        base, extra = split_url_headers(self.url.strip())
        ua, ref = self.http_options()
        headers = {k.strip().lower(): v for k, v in extra.items()}
        ua = headers.pop("user-agent", None) or ua or (global_ua or "").strip() or DEFAULT_UA
        ref = headers.pop("referer", None) or ref
        if ua != DEFAULT_UA:              # the default adds nothing: keys of plain streams stay short
            headers["user-agent"] = ua
        if ref:
            headers["referer"] = ref
        key = norm_url(base)
        if headers:
            key += "|" + "&".join(f"{k}={v}" for k, v in sorted(headers.items()))
        return result_hash(key)


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


class DamagedFileError(ValueError):
    """A compressed playlist that can't be unpacked (damaged or cut off)."""


def unpack_bytes(data: bytes, max_bytes: int = 200 * 1024 * 1024) -> bytes:
    """A gzip-compressed playlist (.m3u.gz, or sent compressed by a server) -> plain bytes.
    Raises DamagedFileError when the compressed data is damaged or incomplete."""
    if data[:2] == b"\x1f\x8b":
        try:
            with gzip.GzipFile(fileobj=io.BytesIO(data)) as gz:
                return gz.read(max_bytes)
        except (OSError, EOFError) as e:
            raise DamagedFileError("not a readable playlist (the compressed .gz file is damaged "
                                   "or incomplete)") from e
    return data


def has_unicode_bom(data: bytes) -> bool:
    return data[:2] in (b"\xff\xfe", b"\xfe\xff") or data[:4] in (b"\x00\x00\xfe\xff", b"\xff\xfe\x00\x00")


def decode_bytes(data: bytes, legacy: str = "auto") -> str:
    """UTF-8 first (the normal case); otherwise the chosen or detected Windows code page."""
    data = unpack_bytes(data)
    if data[:4] in (b"\x00\x00\xfe\xff", b"\xff\xfe\x00\x00"):
        return data.decode("utf-32", "replace")
    if data[:2] in (b"\xff\xfe", b"\xfe\xff"):          # "Unicode" files from Windows Notepad
        return data.decode("utf-16", "replace")
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


URL_LINE_RE = re.compile(r"^[a-z][a-z0-9+.\-]*://\S", re.I)
MEDIA_FILE_RE = re.compile(r"\.(?:m3u8?|pls|xspf|ts|m2ts|mts|mp4|m4v|m4a|mkv|webm|avi|mov|flv|mpe?g|mp3|aac|"
                           r"ac3|ogg|oga|opus|flac|wav|wma|wmv)(?:[?#|].*)?$", re.I)
HLS_TAG_RE = re.compile(r"(?m)^[ \t]*#EXT-X-(?:TARGETDURATION|STREAM-INF|MEDIA-SEQUENCE|VERSION|KEY|MAP)",
                        re.I)
HLS_TAG_BYTES_RE = re.compile(rb"(?m)^[ \t]*#EXT-X-(?:TARGETDURATION|STREAM-INF|MEDIA-SEQUENCE|VERSION|KEY|MAP)",
                              re.I)
# line breaks that start a new entry in a saved playlist (splitlines() knows more than \n)
LINE_BREAK_RE = re.compile(r"[\r\n\v\f\x1c-\x1e\x85\u2028\u2029]+")


def one_line(value) -> str:
    """Text that must stay on one playlist line: a name, group, URL or attribute value."""
    return LINE_BREAK_RE.sub(" ", str(value))


def plausible_entry(line: str) -> bool:
    """Could this playlist line be a stream address or a file path? (Not JSON, HTML or a message.)"""
    if URL_LINE_RE.match(line):
        return True
    # not a player option (e.g. --sout=...) pretending to be a channel address
    return not (line.startswith("-") or line[0] in "{[<" or any(ch in line for ch in '<>"'))


def is_hls_text(text: str) -> bool:
    """An HLS stream (one channel: its segments or quality variants), not a list of channels."""
    head = text.lstrip("﻿ \t\r\n")
    return head[:7].upper() == "#EXTM3U" and HLS_TAG_RE.search(head[:65536].upper()) is not None


def parse_m3u(text: str, source: str, base_dir: str) -> tuple[dict, list[Channel]]:
    header: dict = {}
    channels: list[Channel] = []
    pending = None
    for raw in text.splitlines():
        line = raw.strip().lstrip("﻿")
        if not line:
            continue
        upper = line.upper()
        if upper.startswith("#EXTM3U"):
            for k, v in parse_attrs(line[7:]).items():
                header.setdefault(k, v)
            continue
        if line.startswith("#"):
            if upper.startswith("#EXTINF") and pending is not None and pending.get("inf"):
                pending = None            # the previous #EXTINF had no address: don't inherit from it
            if pending is None:
                pending = {"name": "", "duration": "-1", "attrs": {}, "group": "", "extra": []}
            if upper.startswith("#EXTINF"):
                pending["inf"] = True
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
        if not plausible_entry(line):
            pending = None                # e.g. a JSON / HTML error message, not an address
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
        info = {local(c.tag): one_line((c.text or "").strip()) for c in el}
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
    # a letter and the combining marks after it (Hebrew niqqud, Arabic harakat) move as one unit,
    # so the marks stay after their letter, where a left-to-right renderer expects them
    units, unit_levels = [], []
    for ch, t, lv in zip(text, types, levels):
        if t == "NSM" and units:
            units[-1] += ch
        else:
            units.append(ch.translate(MIRROR) if lv % 2 else ch)
            unit_levels.append(lv)
    levels, n = unit_levels, len(units)
    for lvl in range(max(levels), 0, -1):
        i = 0
        while i < n:
            if levels[i] >= lvl:
                j = i
                while j < n and levels[j] >= lvl:
                    j += 1
                units[i:j] = units[i:j][::-1]
                levels[i:j] = levels[i:j][::-1]
                i = j
            else:
                i += 1
    return "".join(units)


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


def header_value(headers: dict, name: str) -> str | None:
    """Case-insensitive value of one header (playlist url|Header=value style)."""
    want = name.lower()
    return next((v for k, v in headers.items() if k.lower() == want), None)


def split_userinfo(url: str) -> tuple[str, str | None]:
    """'http://user:pass@host/x' -> ('http://host/x', 'Basic …'). Python's HTTP client would take
    'user:pass@host' for the server name, so the login goes into an Authorization header instead."""
    try:
        p = urllib.parse.urlsplit(url)
    except ValueError:
        return url, None
    if p.scheme.lower() not in ("http", "https") or "@" not in p.netloc:
        return url, None
    userinfo, _, hostport = p.netloc.rpartition("@")
    user, _, password = userinfo.partition(":")
    token = base64.b64encode(f"{urllib.parse.unquote(user)}:{urllib.parse.unquote(password)}"
                             .encode("utf-8")).decode("ascii")
    return urllib.parse.urlunsplit((p.scheme, hostport, p.path, p.query, p.fragment)), f"Basic {token}"


def effective_port(p) -> int | None:
    port = p.port
    return port if port is not None else {"http": 80, "https": 443}.get((p.scheme or "").lower())


def same_host(a: str, b: str) -> bool:
    try:
        pa, pb = urllib.parse.urlsplit(a), urllib.parse.urlsplit(b)
        return ((pa.hostname or "").lower() == (pb.hostname or "").lower()
                and effective_port(pa) == effective_port(pb))
    except ValueError:
        return False


def can_share_login(from_url: str, to_url: str) -> bool:
    """May the login of from_url be used for to_url? Same server, or an http -> https
    upgrade (the login stays on the same host and is sent encrypted), never a downgrade."""
    try:
        src, dst = urllib.parse.urlsplit(from_url), urllib.parse.urlsplit(to_url)
    except ValueError:
        return False
    if (src.hostname or "").lower() != (dst.hostname or "").lower():
        return False
    src_scheme, dst_scheme = (src.scheme or "").lower(), (dst.scheme or "").lower()
    if src_scheme == "https" and dst_scheme != "https":
        return False
    if same_host(from_url, to_url):
        return True
    return src_scheme == "http" and dst_scheme == "https"


def with_login(url: str, login_url: str | None) -> str:
    """Put the user:pass@ of login_url back into url (same server / a secure upgrade) - for ffmpeg."""
    if not login_url or not can_share_login(login_url, url):
        return url
    try:
        userinfo = urllib.parse.urlsplit(login_url).netloc.rpartition("@")[0]
        p = urllib.parse.urlsplit(url)
    except ValueError:
        return url
    if not userinfo or "@" in p.netloc:
        return url
    return urllib.parse.urlunsplit((p.scheme, f"{userinfo}@{p.netloc}", p.path, p.query, p.fragment))


class AuthSafeRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Follow redirects, but don't send the login (user:pass@) on to another server."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new is not None and not can_share_login(req.full_url, new.full_url):
            new.remove_header("Authorization")
        return new


def build_opener(ctx: ssl.SSLContext):
    return urllib.request.build_opener(urllib.request.HTTPSHandler(context=ctx), AuthSafeRedirectHandler())


def short_error(err) -> str:
    if isinstance(err, urllib.error.HTTPError):
        return f"HTTP {err.code} {err.reason or ''}".strip()
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


HLS_MAX_BYTES = 16 * 1024 * 1024   # biggest HLS playlist read when checking
HLS_VARIANT_TRIES = 3              # quality variants of a master playlist tried before "offline"


def read_upto(resp, limit: int, deadline: float) -> tuple[bytes, bool]:
    """Read up to `limit` bytes, but stop at `deadline` - a server that sends data
    very slowly can't hold one channel's check for minutes.
    Returns (data, complete): complete is True when the whole answer was read."""
    parts, size, complete = [], 0, False
    read = getattr(resp, "read1", resp.read)
    try:
        while size < limit and time.monotonic() < deadline:
            chunk = read(min(65536, limit - size))
            if not chunk:
                complete = True
                break
            parts.append(chunk)
            size += len(chunk)
    except (socket.timeout, TimeoutError, OSError, http.client.HTTPException):
        if not parts:
            raise
    return b"".join(parts), complete


def read_some(resp, limit: int, deadline: float) -> bytes:
    return read_upto(resp, limit, deadline)[0]


def hls_variants(text: str) -> list[tuple[str, bool]]:
    """Quality variants of an HLS master playlist as (address, has video): video variants from the
    LOWEST bandwidth up (small segments, fast), then audio-only variants."""
    out = []
    lines = [ln.strip() for ln in text.splitlines()]
    for i, ln in enumerate(lines):
        if not ln.upper().startswith("#EXT-X-STREAM-INF"):
            continue
        uri = next((x for x in lines[i + 1:] if x and not x.startswith("#")), None)
        if not uri:
            continue
        codecs = (re.search(r'CODECS="([^"]*)"', ln, re.I) or [None, ""])[1].lower()
        video = not codecs or re.search(r"avc|hvc|hev|vp0?9|av01|mp4v", codecs) is not None
        m = re.search(r"(?<![-A-Z])BANDWIDTH=(\d+)", ln, re.I)
        bw = int(m.group(1)) if m else 10 ** 12
        out.append((not video, bw, len(out), uri, video))
    seen, result = set(), []
    for *_, uri, video in sorted(out):
        if uri not in seen:
            seen.add(uri)
            result.append((uri, video))
    return result


# ---------------------------------------------------------------- stream quality
VIDEO_CODECS = (("avc", "H.264"), ("h264", "H.264"), ("hvc", "H.265"), ("hev", "H.265"), ("h265", "H.265"),
                ("vp09", "VP9"), ("vp9", "VP9"), ("av01", "AV1"), ("av1", "AV1"), ("mpeg2", "MPEG-2"),
                ("mp4v", "MPEG-4"), ("mpeg4", "MPEG-4"), ("vp8", "VP8"))
AUDIO_TYPES = {"audio/mpeg": "MP3", "audio/mp3": "MP3", "audio/aac": "AAC", "audio/aacp": "AAC+",
               "audio/x-aac": "AAC", "audio/mp4": "AAC", "audio/ogg": "Ogg", "application/ogg": "Ogg",
               "audio/opus": "Opus", "audio/flac": "FLAC", "audio/x-flac": "FLAC", "audio/wav": "WAV",
               "audio/x-wav": "WAV", "audio/x-ms-wma": "WMA"}


def codec_name(text: str) -> str:
    low = (text or "").lower()
    return next((name for key, name in VIDEO_CODECS if key in low), "")


def hls_master_quality(text: str) -> dict | None:
    """Best video quality offered by an HLS master playlist (from its #EXT-X-STREAM-INF lines)."""
    best, count = None, 0
    for ln in text.splitlines():
        ln = ln.strip()
        if not ln.upper().startswith("#EXT-X-STREAM-INF"):
            continue
        codecs = (re.search(r'CODECS="([^"]*)"', ln, re.I) or [None, ""])[1]
        if codecs and not re.search(r"avc|hvc|hev|vp0?9|av01|mp4v", codecs, re.I):
            continue                                   # audio-only variant
        count += 1
        res = re.search(r"RESOLUTION=(\d+)x(\d+)", ln, re.I)
        bw = re.search(r"(?<![-A-Z])BANDWIDTH=(\d+)", ln, re.I)
        fps = re.search(r"FRAME-RATE=([\d.]+)", ln, re.I)
        q = {"w": int(res.group(1)) if res else 0, "h": int(res.group(2)) if res else 0,
             "codec": codec_name(codecs), "fps": float(fps.group(1)) if fps else 0.0,
             "bw": int(bw.group(1)) if bw else 0, "src": "hls"}
        if best is None or (q["h"], q["bw"]) > (best["h"], best["bw"]):
            best = q
    if best:
        best["variants"] = count
    return best


def ffmpeg_video_quality(err: bytes) -> dict | None:
    """Resolution, codec, frame rate from ffmpeg's line 'Stream #0:0: Video: h264 (High), …, 1920x1080, 25 fps'."""
    text = (err or b"").decode("utf-8", "ignore")
    m = re.search(r"Stream #\d+:\d+.*?: Video: ([^\n]*)", text)
    if not m:
        return None
    line = m.group(1)
    res = re.search(r"\b(\d{2,5})x(\d{2,5})\b", line)
    fps = re.search(r"([\d.]+) fps", line)
    if not res:
        return None
    return {"w": int(res.group(1)), "h": int(res.group(2)), "codec": codec_name(line.split(",")[0]),
            "fps": float(fps.group(1)) if fps else 0.0, "bw": 0, "src": "ffmpeg"}


def quality_text(q: dict | None) -> str:
    """'1080p · H.264 · 25 fps · 5.0 Mb/s' or 'audio · MP3 · 128 kb/s'."""
    if not q:
        return ""
    if q.get("audio"):
        parts = ["audio"] + ([q["audio"]] if q["audio"] != "audio" else [])
        if q.get("bw"):
            parts.append(f"{q['bw'] // 1000} kb/s")
        return " · ".join(parts)
    parts = []
    if q.get("h"):
        parts.append(f"{q['h']}p")
    if q.get("codec"):
        parts.append(q["codec"])
    if q.get("fps"):
        parts.append(f"{q['fps']:.2f}".rstrip("0").rstrip(".") + " fps")
    if q.get("bw"):
        bw = q["bw"]
        parts.append(f"{bw / 1e6:.1f} Mb/s" if bw >= 1_000_000 else f"{bw // 1000} kb/s")
    return " · ".join(parts)


def quality_rank(q: dict | None) -> tuple:
    """Sort order of the Quality column: no information first, then radio, then video by height and bitrate."""
    if not q:
        return (0, 0, 0)
    if q.get("audio"):
        return (1, 0, q.get("bw", 0))
    return (2, q.get("h", 0), q.get("bw", 0))


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
        if is_playlist_name(p.name) and p.is_file() and str(p) not in seen:
            seen.add(str(p))
            local.append(p)
    return web, streams, local


def classify_download(head: bytes, ctype: str) -> str:
    """What a web address returned: 'playlist', 'stream' (one TV/radio channel) or 'page'."""
    h = head.lstrip(b"\xef\xbb\xbf \t\r\n")
    low = h[:300].lower()
    if h.startswith(b"#EXTM3U") or h.startswith(b"#EXTINF"):
        # an HLS stream (one channel) also starts with #EXTM3U, but uses #EXT-X- tags
        if HLS_TAG_BYTES_RE.search(head):
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
    # plain text: a simple list of stream links is a playlist; anything else (a JSON or text error
    # message such as {"status":"error"} or "Access denied") is not
    if looks_like_link_list(head.decode("utf-8", "ignore")):
        return "playlist"
    return "page"


def looks_like_link_list(text: str) -> bool:
    """Plain text with stream addresses / media files, one per line (most of its lines)."""
    lines = [ln.strip() for ln in text.lstrip("﻿").splitlines()]
    lines = [ln for ln in lines if ln and not ln.startswith("#")]
    if not lines:
        return False
    good = sum(1 for ln in lines if URL_LINE_RE.match(ln) or
               (plausible_entry(ln) and MEDIA_FILE_RE.search(ln)))
    return good > 0 and good * 2 >= len(lines)


def answer_snippet(data: bytes, ctype: str) -> str:
    """Start of a non-playlist answer for the error message (JSON / text error messages)."""
    if ctype.startswith("text/html") or data.lstrip()[:20].lower().startswith((b"<!doctype", b"<html")):
        return ""
    text = data.decode("utf-8", "ignore").lstrip("﻿").strip()
    if not text or any(ord(ch) < 32 and ch not in "\r\n\t" for ch in text[:200]):
        return ""
    text = " ".join(text.split())
    return text[:160] + ("…" if len(text) > 160 else "")


def fetch_playlist(url: str, ua: str, ignore_ssl: bool, legacy: str, timeout: float = 40,
                   max_seconds: float = 300, max_bytes: int = 100 * 1024 * 1024) -> tuple[str, str, str]:
    """Download a playlist. Returns (kind, text, base): kind 'playlist' with its text, 'stream' or
    'page' (text: the start of the server's answer, if it is readable text). base is the address
    the playlist really came from after a redirect ("" when not redirected) - its relative links
    are relative to that address. A live stream is recognised from its first bytes and not downloaded."""
    ctx = ssl.create_default_context()
    if ignore_ssl:
        ctx.check_hostname, ctx.verify_mode = False, ssl.CERT_NONE
    opener = build_opener(ctx)
    plain, extra_headers = split_url_headers(url.strip())     # Kodi style 'url|User-Agent=…'
    plain, auth = split_userinfo(plain)
    headers = {"User-Agent": ua or DEFAULT_UA, "Accept": "*/*"}
    if auth:
        headers["Authorization"] = auth
    headers.update(extra_headers)
    sent = request_url(plain)
    req = urllib.request.Request(sent, headers=headers)
    with opener.open(req, timeout=timeout) as r:
        ctype = (r.headers.get("Content-Type") or "").split(";")[0].strip().lower()
        final = r.geturl()
        base = final if final != sent else ""
        start = time.monotonic()
        head = read_some(r, 4096, start + timeout)
        compressed = head[:2] == b"\x1f\x8b"
        if compressed:                                   # .m3u.gz / server sent it compressed
            data = unpack_bytes(head + read_some(r, max_bytes, start + max_seconds))
            head = data[:4096]
        if has_unicode_bom(head):
            kind = "playlist"
        else:
            kind = classify_download(head, "" if compressed else ctype)
        if kind == "page":
            return kind, answer_snippet(head, ctype), base
        if kind != "playlist":
            return kind, "", base
        if not compressed:
            data = head + read_some(r, max_bytes, start + max_seconds)
    return "playlist", decode_bytes(data, legacy), base


def request_url(url: str) -> str:
    """Address as a web request needs it: spaces and non-Latin letters encoded (players accept
    them raw, Python's HTTP client does not). Already encoded parts (%20) are kept."""
    if all(33 <= ord(ch) < 127 for ch in url):
        return url
    try:
        p = urllib.parse.urlsplit(url.strip())
        netloc = p.netloc
        if p.hostname and not p.hostname.isascii():
            host = p.hostname.encode("idna").decode("ascii")
            userinfo = netloc.rpartition("@")[0]
            netloc = (userinfo + "@" if userinfo else "") + host + (f":{p.port}" if p.port else "")
        path = urllib.parse.quote(p.path, safe="/%:@!$&'()*+,;=~")
        query = urllib.parse.quote(p.query, safe="=&%:/?@!$'()*+,;~")
        return urllib.parse.urlunsplit((p.scheme, netloc, path, query, p.fragment))
    except (ValueError, UnicodeError):
        return url


def find_ffmpeg() -> str | None:
    cands = [shutil.which("ffmpeg")]
    if sys.platform.startswith("win"):
        for base in (os.environ.get("ProgramFiles", r"C:\Program Files"), r"C:\ffmpeg"):
            cands += [os.path.join(base, "ffmpeg", "bin", "ffmpeg.exe"), os.path.join(base, "bin", "ffmpeg.exe")]
    return next((c for c in cands if c and os.path.isfile(c)), None)


def hamming(a: int, b: int) -> int:
    x = a ^ b
    return x.bit_count() if hasattr(x, "bit_count") else bin(x).count("1")


def pic_close(h1: int, g1: float, h2: int, g2: float, c1=None, c2=None) -> bool:
    """Same picture: same shape (fingerprint), same brightness and - when both are known -
    the same colours (a navy/white banner is not the same as a green/pink slate with the same layout)."""
    if hamming(h1, h2) > PIC_MAX_DIST or abs(g1 - g2) > 25:
        return False
    if c1 and c2 and len(c1) == len(c2):
        return sum(abs(a - b) for a, b in zip(c1, c2)) / len(c1) <= PIC_COLOR_MAX
    return True


def picture_extras(pic) -> tuple:
    """(motion, colour layout) of a grab_picture() result."""
    return (pic[4], pic[5]) if len(pic) >= 6 else (None, None)


def is_moving(c) -> bool:
    return c.pic_motion is not None and c.pic_motion > PIC_MOVING


def looks_black(pic) -> bool:
    """A grab_picture() result that is (almost) black and still: no programme, at most a logo.
    The brightness decides, not the contrast - a bright channel logo on black has high contrast."""
    if pic is None:
        return False
    motion = picture_extras(pic)[0]       # a blinking "live" sign on the logo may move a little
    return pic[2] < BLACK_MAX_GRAY and (motion is None or motion <= BLACK_CHANGE_MAX)


def still_black(first, second) -> bool:
    """Both pictures, taken STILL_CHECK_GAP seconds apart, are black and (almost) the same -
    not a fade to black or a dark scene, the channel shows nothing."""
    if not (looks_black(first) and looks_black(second)):
        return False
    a, b = parse_ppm(first[3]), parse_ppm(second[3])
    if not a or not b or a[:2] != b[:2]:
        return True
    # a dark scene changes only a little in brightness: count small changes too
    # (a black slate from an encoder is the same picture every time, it changes by 0)
    return frame_motion(a[2], b[2], BLACK_STEP) <= BLACK_CHANGE_MAX


def parse_ppms(data: bytes) -> list:
    """All frames ffmpeg wrote one after another: [(w, h, pixels, raw PPM bytes), ...]."""
    frames, pos = [], 0
    while True:
        m = PPM_HEADER_RE.match(data or b"", pos)
        if not m:
            return frames
        w, h = int(m.group(1)), int(m.group(2))
        end = m.end() + w * h * 3
        if end > len(data):
            return frames
        frames.append((w, h, data[m.end():end], data[pos:end]))
        pos = end


PPM_HEADER_RE = re.compile(rb"P6\s+(\d+)\s+(\d+)\s+(\d+)\s")


def gray_pixels(px: bytes) -> list:
    return [(px[i] * 299 + px[i + 1] * 587 + px[i + 2] * 114) // 1000 for i in range(0, len(px), 3)]


def frame_motion(a: bytes, b: bytes, step: int = 12) -> float:
    """Share of the picture whose brightness changed noticeably (by more than `step`) between two frames."""
    ga, gb = gray_pixels(a), gray_pixels(b)
    return sum(1 for x, y in zip(ga, gb) if abs(x - y) > step) / max(len(ga), 1)


def color_layout(w: int, h: int, px: bytes, n: int = PIC_COLOR_GRID) -> list:
    """Average colour of n x n areas of the frame (R, G, B each)."""
    sig = []
    for gy in range(n):
        for gx in range(n):
            r = g = b = cnt = 0
            for y in range(gy * h // n, max((gy + 1) * h // n, gy * h // n + 1)):
                base = y * w
                for x in range(gx * w // n, max((gx + 1) * w // n, gx * w // n + 1)):
                    i = (base + x) * 3
                    r += px[i]; g += px[i + 1]; b += px[i + 2]; cnt += 1
            sig += [r // cnt, g // cnt, b // cnt]
    return sig


_FFMPEG_FPS_ARGS: dict = {}


def ffmpeg_passthrough_args(ffmpeg: str) -> list:
    """Option that stops ffmpeg from repeating frames (otherwise every picture looks 'still'):
    -fps_mode passthrough since ffmpeg 5.1, -vsync 0 before."""
    if ffmpeg not in _FFMPEG_FPS_ARGS:
        args = ["-fps_mode", "passthrough"]
        try:
            out = subprocess.run([ffmpeg, "-hide_banner", "-version"], capture_output=True, timeout=10).stdout
            m = re.search(rb"version\s+n?(\d+)\.(\d+)", out)
            if m and (int(m.group(1)), int(m.group(2))) < (5, 1):
                args = ["-vsync", "0"]
        except (OSError, subprocess.SubprocessError):
            pass
        _FFMPEG_FPS_ARGS[ffmpeg] = args
    return _FFMPEG_FPS_ARGS[ffmpeg]


def parse_ppm(data: bytes):
    m = re.match(rb"P6\s+(\d+)\s+(\d+)\s+(\d+)\s", data or b"")
    if not m:
        return None
    w, h = int(m.group(1)), int(m.group(2))
    px = data[m.end(): m.end() + w * h * 3]
    return (w, h, px) if len(px) == w * h * 3 else None


def picture_fingerprint(w: int, h: int, px: bytes) -> tuple[int, float, float]:
    """64-bit difference hash of a frame (robust to re-encoding and size), its contrast and brightness."""
    gray = [(px[i] * 299 + px[i + 1] * 587 + px[i + 2] * 114) // 1000 for i in range(0, len(px), 3)]
    mean = sum(gray) / len(gray)
    spread = (sum((v - mean) ** 2 for v in gray) / len(gray)) ** 0.5
    cells = []
    for gy in range(8):
        y0, y1 = gy * h // 8, max((gy + 1) * h // 8, gy * h // 8 + 1)
        row = []
        for gx in range(9):
            x0, x1 = gx * w // 9, max((gx + 1) * w // 9, gx * w // 9 + 1)
            tot = cnt = 0
            for y in range(y0, y1):
                base = y * w
                for x in range(x0, x1):
                    tot += gray[base + x]
                    cnt += 1
            row.append(tot / cnt)
        cells.append(row)
    bits = 0
    for row in cells:
        for x in range(8):
            bits = (bits << 1) | (1 if row[x] > row[x + 1] else 0)
    return bits, spread, mean


class StreamChecker:
    def __init__(self, timeout: float, user_agent: str, deep_hls: bool, ignore_ssl: bool,
                 geo_server: bool = True, geo_loop: bool = True, ffmpeg: str | None = None):
        self.timeout = timeout
        self.ua = user_agent or DEFAULT_UA
        self.deep = deep_hls
        self.geo_server = geo_server
        self.geo_loop = geo_loop
        self.ffmpeg = ffmpeg
        self._procs: set = set()
        self._procs_lock = threading.Lock()
        self.ctx = ssl.create_default_context()
        if ignore_ssl:
            self.ctx.check_hostname = False
            self.ctx.verify_mode = ssl.CERT_NONE

    def check_full(self, url: str, base_dir: str = "", ua: str | None = None, referer: str | None = None):
        """Returns (status, info, milliseconds, extra) - extra: seg_hash, audio, ..."""
        t0 = time.monotonic()
        self._extra = extra = {}
        try:
            status, info = self._check(url.strip(), base_dir, ua, referer)
        except Exception as e:  # never let one channel stop the whole check
            status, info = OFFLINE, f"error: {short_error(e)}"
        finally:
            self._extra = None
        if status == ONLINE and self.geo_loop and extra.get("vod_seconds") is not None:
            secs = extra["vod_seconds"]
            if secs <= LOOP_MAX_SECONDS:
                status, info = BLOCKED, (f"not live: a {secs:.0f} s video plays instead of the channel "
                                         "(usually a 'not available' banner)")
        return status, info, int((time.monotonic() - t0) * 1000), extra

    # each worker thread has its own "extra" dict
    _tls = threading.local()

    @property
    def _extra(self):
        return getattr(self._tls, "extra", None)

    @_extra.setter
    def _extra(self, value):
        self._tls.extra = value

    def _note(self, **kw):
        if self._extra is not None:
            self._extra.update(kw)

    def _note_picture_source(self, text: str, url: str):
        """Which address ffmpeg should open for the picture: the LOWEST video quality of a master
        playlist (small segments, fast) - the fingerprint does not depend on the resolution."""
        if self._extra is None or "pic_url" in self._extra:
            return
        if "#EXT-X-STREAM-INF" not in text:
            pic = url                                     # already a single-quality playlist
        else:
            variants = hls_variants(text)
            if not (variants and variants[0][1]):
                return
            pic = urllib.parse.urljoin(url, variants[0][0])
        self._note(pic_url=with_login(pic, self._extra.get("login_url")), pic_hls=True)

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
            plain, auth = split_userinfo(url)
            if auth:                           # http://user:pass@host/… -> Authorization header
                headers["Authorization"] = auth
                self._note(login_url=url)      # ffmpeg (picture) understands user:pass@ itself
            headers.update(extra_headers)
            return self._http(plain, headers, 0)
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
        opener = build_opener(self.ctx)
        url = request_url(url)
        req = urllib.request.Request(url, headers=headers)
        try:
            with opener.open(req, timeout=self.timeout) as r:
                code = r.status
                ctype = (r.headers.get("Content-Type") or "").split(";")[0].strip().lower()
                try:      # Icecast / Shoutcast tell the bitrate (kb/s), sometimes as "128,128"
                    icy_br = int((r.headers.get("icy-br") or "0").split(",")[0].strip() or 0)
                except ValueError:
                    icy_br = 0
                final_url = r.geturl()
                deadline = time.monotonic() + self.timeout
                # some servers send an HLS playlist gzip-compressed even without Accept-Encoding;
                # read through GzipFile so #EXTM3U is visible and the real segments are checked
                encoding = (r.headers.get("Content-Encoding") or "").split(",")[0].strip().lower()
                stream = gzip.GzipFile(fileobj=r) if encoding in ("gzip", "x-gzip") else r
                data = read_some(stream, 2048, deadline)
                head = data.lstrip(b"\xef\xbb\xbf \t\r\n")
                is_hls = (head.startswith(b"#EXTM3U")
                          and HLS_TAG_BYTES_RE.search(head) is not None)
                complete = True
                if is_hls:
                    # rest of the HLS playlist - channels with a long rewind window (24 h of
                    # 6-second segments) have playlists of 1-2 MB
                    rest, complete = read_upto(stream, HLS_MAX_BYTES, deadline)
                    data += rest
                elif depth > 0:
                    data += read_some(stream, 65536 - len(data), deadline)  # video segment: fingerprint
                elif ctype.startswith("text/html"):
                    data += read_some(stream, 65536 - len(data), deadline)  # error page: look for "your country"
        except urllib.error.HTTPError as e:
            if self.geo_server:
                if e.code == 451:
                    return BLOCKED, "HTTP 451 – blocked in this country"
                if e.code in (401, 403):
                    try:
                        body = e.read(8192).decode("utf-8", "ignore")
                    except Exception:
                        body = ""
                    if GEO_TEXT_RE.search(body) or GEO_TEXT_RE.search(str(e.reason or "")):
                        return BLOCKED, f"HTTP {e.code} – not available in this country / region"
            return OFFLINE, f"HTTP {e.code} {e.reason}".strip()
        except http.client.BadStatusLine as e:
            line = str(getattr(e, "line", e)).strip()
            if line.upper().startswith("ICY 200"):
                self._note(audio=True)
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

        if self.geo_server and (GEO_URL_RE.search(final_url if depth == 0 else url) or
                                (final_url != url and GEO_URL_RE.search(final_url))):
            if depth == 0 and final_url != url:
                return BLOCKED, "redirected to a 'not available' address"
            if depth > 0:
                return BLOCKED, "the video comes from a 'not available' address"

        if is_hls:
            if not complete:
                # only part of a huge playlist arrived: its last line may be cut in the middle,
                # and a cut segment name gives a false "HTTP 404" - use complete lines only
                data = data[:data.rfind(b"\n") + 1]
            text = data.decode("utf-8", "ignore").lstrip("﻿ \t\r\n")
            uris = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.strip().startswith("#")]
            if "#EXT-X-STREAM-INF" not in text and ("#EXT-X-ENDLIST" in text or "PLAYLIST-TYPE:VOD" in text):
                durations = re.findall(r"#EXTINF:\s*([\d.]+)", text)
                self._note(vod_seconds=sum(float(d) for d in durations if d.replace(".", "", 1).isdigit()))
            if not uris:
                return OFFLINE, f"HTTP {code} · HLS playlist is empty"
            self._note_picture_source(text, final_url)
            if "#EXT-X-STREAM-INF" in text and self._extra is not None and "quality" not in self._extra:
                q = hls_master_quality(text)
                if q:
                    self._note(quality=q)
            variants = hls_variants(text) if "#EXT-X-STREAM-INF" in text else []
            if variants and all(not video for _, video in variants):
                self._note(audio=True)          # an HLS radio playlist: no video to fingerprint
            elif not variants and all(AUDIO_URL_RE.search(u) for u in uris):
                self._note(audio=True)
            if not self.deep or depth >= 3:
                return ONLINE, f"HTTP {code} · HLS playlist"
            # master playlist -> quality variants (lowest first) until one works;
            # media playlist -> newest segment
            if variants:
                tries = [u for u, _ in variants][:HLS_VARIANT_TRIES] or uris[:1]
            else:
                tries = uris[-1:]
            for nxt in tries:
                nxt_url = urllib.parse.urljoin(final_url, nxt)
                sub = headers if can_share_login(url, nxt_url) else \
                    {k: v for k, v in headers.items() if k.lower() != "authorization"}
                status, info = self._http(nxt_url, sub, depth + 1)
                if status != OFFLINE:
                    break
            if info.startswith("HLS"):
                return status, info
            return status, ("HLS · " if status == ONLINE else "HLS segment: ") + info

        if not data:
            return OFFLINE, f"HTTP {code} · empty answer"
        if ctype.startswith("text/html") or data.lstrip()[:20].lower().startswith((b"<!doctype html", b"<html")):
            if self.geo_server and GEO_TEXT_RE.search(data.decode("utf-8", "ignore")):
                return BLOCKED, f"HTTP {code} · page says 'not available in your country / region'"
            return OFFLINE, f"HTTP {code} · web page, not a stream"
        # HTTP 200 does not have to be a stream: panels often answer with a JSON or
        # text error, and a channel address can point to a normal playlist.
        kind = classify_download(data[:4096], ctype)
        textual = (ctype.startswith(("text/", "application/json", "application/xml"))
                   or "mpegurl" in ctype or ctype in ("audio/x-scpls", "application/xspf+xml")
                   or data.lstrip()[:1] in (b"{", b"[", b"<"))
        if not textual and not ctype:      # no content type: trust readable text only
            try:
                data[:2048].decode("utf-8")
                textual = True
            except UnicodeDecodeError:
                pass
        if kind == "page" and textual and ctype != "text/vtt":
            if self.geo_server and GEO_TEXT_RE.search(data.decode("utf-8", "ignore")):
                return BLOCKED, f"HTTP {code} · message says 'not available in your country / region'"
            snippet = answer_snippet(data, ctype)
            return OFFLINE, f"HTTP {code} · " + (
                f"not a stream: {snippet}" if snippet else "web page, not a stream")
        if kind == "playlist":
            return ONLINE, f"HTTP {code} · playlist (not a single stream)"
        if depth > 0:
            self._note(seg_hash=hashlib.sha1(data[:65536]).hexdigest())
        if ctype.startswith("audio/") or ctype in ("application/ogg",):
            self._note(audio=True, quality={"audio": AUDIO_TYPES.get(ctype, "audio"), "bw": icy_br * 1000})
        return ONLINE, f"HTTP {code}" + (f" · {ctype}" if ctype else "")

    # ------------------------------------------------------------------ picture (ffmpeg)
    def grab_picture(self, url: str, ua: str | None = None, referer: str | None = None, hls: bool = False):
        """Up to 3 frames, ~0.8 s apart, from ONE download of the stream ->
        (fingerprint, contrast, brightness, PPM thumbnail, motion, colour layout) or None (no picture).
        The fingerprint comes from the first frame that is not plain black (fade-in), motion is how
        much of the picture changes between the frames (None when only one frame came)."""
        if not self.ffmpeg:
            return None
        # log level "info": ffmpeg then also prints the stream line (resolution, codec, fps) for Quality
        cmd = [("info" if a == "error" else a) for a in self._ffmpeg_input(url, ua, referer, hls)] + [
            "-map", "0:v:0",
            "-vf", f"select='eq(n\\,0)+gte(t-prev_selected_t\\,{PIC_FRAME_GAP})',scale={PIC_W}:{PIC_H}"]
        tail = ["-frames:v", str(PIC_FRAMES), "-f", "image2pipe", "-vcodec", "ppm", "-"]
        prints: list = []

        def enough(frames) -> bool:
            """Stop downloading as soon as the answer is clear: live TV (moving picture) after the
            2nd frame; only still pictures (cheap - they compress to almost nothing) need all 3."""
            while len(prints) < len(frames):
                w, h, px, _ = frames[len(prints)]
                prints.append(picture_fingerprint(w, h, px))
            usable = [f[2] for f, fp in zip(frames, prints) if fp[1] >= PIC_MIN_SPREAD]
            return len(frames) >= PIC_FRAMES or (len(usable) >= 2 and frame_motion(usable[-2], usable[-1]) > PIC_MOVING)

        fps_args = ffmpeg_passthrough_args(self.ffmpeg)
        frames, err = self._read_frames(cmd + fps_args + tail, enough)
        if not frames and re.search(rb"(?:Unrecognized option|not supported)[^\n]*(?:fps_mode|vsync)|"
                                    rb"(?:fps_mode|vsync)[^\n]*not supported|Option not found", err or b""):
            fps_args = ["-vsync", "0"] if fps_args[0] == "-fps_mode" else ["-fps_mode", "passthrough"]
            _FFMPEG_FPS_ARGS[self.ffmpeg] = fps_args
            prints.clear()
            frames, err = self._read_frames(cmd + fps_args + tail, enough)
        self._tls.video_quality = ffmpeg_video_quality(err)
        if not frames:
            return None
        enough(frames)
        best = next((i for i, fp in enumerate(prints) if fp[1] >= PIC_MIN_SPREAD), 0)
        bits, spread, mean = prints[best]
        w, h, px, raw = frames[best]
        # motion between the usable frames (a black fade-in frame does not count as movement)
        usable = [f[2] for f, fp in zip(frames, prints) if fp[1] >= PIC_MIN_SPREAD] or [f[2] for f in frames]
        motion = max((frame_motion(a, b) for a, b in zip(usable, usable[1:])), default=None)
        return bits, spread, mean, raw, motion, color_layout(w, h, px)

    def _ffmpeg_input(self, url: str, ua: str | None, referer: str | None, hls: bool) -> list:
        """ffmpeg command up to and including '-i address' (User-Agent, Referer, extra headers)."""
        url, extra_headers = split_url_headers(url.strip())
        url = request_url(url)
        ua = extra_headers.pop("User-Agent", None) or ua or self.ua
        referer = extra_headers.pop("Referer", None) or referer
        cmd = [self.ffmpeg, "-hide_banner", "-loglevel", "error", "-nostdin",
               "-analyzeduration", "2000000", "-probesize", "1500000"]
        if url.lower().startswith(("http://", "https://")):
            cmd += ["-rw_timeout", str(int(self.timeout * 1_000_000)), "-user_agent", ua]
            hdrs = ([("Referer", referer)] if referer else []) + list(extra_headers.items())
            if hdrs:
                cmd += ["-headers", "".join(f"{k}: {v}\r\n" for k, v in hdrs)]
        if hls:
            cmd += ["-live_start_index", "-1"]   # only the newest segment
        return cmd + ["-threads", "1", "-i", url]

    def grab_preview(self, url: str, ua: str | None = None, referer: str | None = None,
                     hls: bool = False) -> bytes | None:
        """One sharper frame (at most PREVIEW_W x PREVIEW_H, true shape of the picture) as PPM -
        only for showing to the user, the 80 x 45 thumbnail is too small to read a banner."""
        if not self.ffmpeg:
            return None
        # sar: SD channels often have non-square pixels - show them with the shape the TV shows
        cmd = self._ffmpeg_input(url, ua, referer, hls) + [
            "-map", "0:v:0", "-vf",
            ("scale='trunc(iw*if(gt(sar\\,0)\\,sar\\,1)/2)*2':ih,"
             f"scale={PREVIEW_W}:{PREVIEW_H}:force_original_aspect_ratio=decrease,setsar=1"),
            "-frames:v", "1", "-f", "image2pipe", "-vcodec", "ppm", "-"]
        frames, _ = self._read_frames(cmd, lambda f: len(f) >= 1)
        return frames[0][3] if frames else None

    def _read_frames(self, cmd, enough) -> tuple[list, bytes]:
        """Run ffmpeg and collect the frames as they arrive; stop it as soon as enough(frames)
        says so, at the time limit, or when it ends. Frames that arrived are always used."""
        try:
            proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        except OSError:
            return [], b""
        with self._procs_lock:
            self._procs.add(proc)
        chunks: queue.Queue = queue.Queue()
        err: list = []

        def pump(stream, put):
            try:
                read = getattr(stream, "read1", stream.read)
                while True:
                    data = read(65536)
                    put(data)
                    if not data:
                        return
            except (OSError, ValueError):
                put(b"")
        threading.Thread(target=pump, args=(proc.stdout, chunks.put), daemon=True).start()
        err_reader = threading.Thread(target=pump, args=(proc.stderr, err.append), daemon=True)
        err_reader.start()
        buf, frames = b"", []
        deadline = time.monotonic() + self.timeout + 6
        try:
            while True:
                left = deadline - time.monotonic()
                if left <= 0:
                    break
                try:
                    data = chunks.get(timeout=left)
                except queue.Empty:
                    break
                if not data:
                    break
                buf += data
                got = parse_ppms(buf)
                if len(got) > len(frames):
                    frames = got
                    if enough(frames):
                        break
        finally:
            if proc.poll() is None:
                proc.kill()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            with self._procs_lock:
                self._procs.discard(proc)
        # the error text decides whether to retry; with frames it still holds the stream line (quality)
        err_reader.join(2 if not frames else 0.5)
        return frames, b"".join(x for x in err if x)

    def video_quality(self) -> dict | None:
        """Resolution / codec / frame rate ffmpeg reported during this thread's last grab_picture()."""
        return getattr(self._tls, "video_quality", None)

    def kill_all(self):
        with self._procs_lock:
            for proc in list(self._procs):
                try:
                    proc.kill()
                except OSError:
                    pass


# =============================================================================
#  Duplicates, sorting, saving
# =============================================================================

def norm_url(url: str) -> str:
    u = url.strip().split("|", 1)[0]
    p = urllib.parse.urlsplit(u)
    if p.scheme and p.netloc:
        # the host is case-insensitive; a login / password is not
        userinfo, at, hostport = p.netloc.rpartition("@")
        netloc = (userinfo + at if at else "") + hostport.lower()
        u = urllib.parse.urlunsplit((p.scheme.lower(), netloc, p.path, p.query, ""))
    return u.rstrip("/")


def result_hash(key: str) -> str:
    """Remembered results are stored under a hash of the address, not the address itself:
    results.json then shows no stream addresses, logins (user:pass@) or tokens."""
    return hashlib.sha256(("playlist-checker results\0" + key).encode("utf-8", "surrogatepass")).hexdigest()[:32]


def current_status(c) -> str:
    """The status to act on (remove offline, keep one of the duplicates, leave out of a saved
    playlist). An online / offline result from an earlier session may be months old, so it counts
    as not checked. A geo-block is kept: it depends on your country rather than on the stream,
    and it is often your own mark."""
    if getattr(c, "remembered", False) and c.status in (ONLINE, OFFLINE):
        return UNCHECKED
    return c.status


def norm_name(name: str, ignore_quality: bool) -> str:
    s = name.casefold()
    if ignore_quality:
        s = QUALITY_RE.sub(" ", s)
        s = re.sub(r"[\(\[\{]\s*[\)\]\}]", " ", s)
    return re.sub(r"[\W_]+", " ", s).strip()


def channel_identity(c) -> tuple[str, str]:
    """(name, tvg-id) without quality / subtitle / source words: "כאן 11 HEVC", "כאן 11 - מקור 2"
    and "כאן 11 כתוביות" (kan11_hevc, kan11_src2, kan11_subs) are all the same channel."""
    name = norm_name(VARIANT_RE.sub(" ", c.name or ""), True)
    tid = (c.attrs.get("tvg-id") or "").casefold()
    parts = [x for x in re.split(r"[\W_]+", tid) if x and not VARIANT_ID_PART.fullmatch(x)]
    return name, "".join(parts)


def count_distinct_channels(members) -> int:
    """How many really different channels: versions of one channel (same name or same tvg-id
    apart from quality / source words) count once."""
    parent = list(range(len(members)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    seen: dict[tuple, int] = {}
    for i, m in enumerate(members):
        name, tid = channel_identity(m)
        for key in (("n", name or m.url), ("i", tid)):
            if not key[1]:
                continue
            if key in seen:
                parent[find(i)] = find(seen[key])
            else:
                seen[key] = i
    return len({find(i) for i in range(len(members))})


def find_duplicates(channels: list[Channel], by_url: bool, by_name: bool,
                    ignore_quality: bool) -> dict[int, tuple[int, str]]:
    """{uid of duplicate: (uid of the copy that is kept, reason)}.
    The copy that is kept: online first, then the one that appears first. A result from an earlier
    session counts as not checked (current_status), so a months-old "offline" never loses a stream."""
    dups: dict[int, tuple[int, str]] = {}

    def run(keyfunc, reason):
        buckets = defaultdict(list)
        for idx, c in enumerate(channels):
            if c.uid not in dups:
                k = keyfunc(c)
                if k:
                    buckets[k].append((STATUS_RANK.get(current_status(c), 1), idx, c))
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
    return "".join(f' {one_line(k)}="{one_line(v).replace(chr(34), chr(39))}"'
                   for k, v in attrs.items())


def write_m3u(path: str, items: list[Channel], header: dict) -> None:
    lines = ["#EXTM3U" + attrs_to_str(header)]
    for c in items:
        attrs = dict(c.attrs)
        if c.group:
            attrs["group-title"] = c.group
        else:
            attrs.pop("group-title", None)
        lines.append(f"#EXTINF:{one_line(c.duration)}{attrs_to_str(attrs)},{one_line(c.name)}")
        lines.extend(one_line(x) for x in c.extra)
        lines.append(one_line(c.export_url()))
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_pls(path: str, items: list[Channel]) -> None:
    lines = ["[playlist]"]
    for i, c in enumerate(items, 1):
        lines += [f"File{i}={one_line(c.export_url())}", f"Title{i}={one_line(c.name)}", f"Length{i}=-1"]
    lines += [f"NumberOfEntries={len(items)}", "Version=2"]
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")


FILE_PREFIX = "Playlist Checker"


def csv_text(value) -> str:
    """Text for a CSV cell: Excel / LibreOffice must not run a name like '=HYPERLINK(…)' as a formula."""
    text = "" if value is None else str(value)
    return "'" + text if text[:1] in ("=", "+", "-", "@", "\t", "\r") else text


def dated_name(base: str, ext: str, with_date: bool, with_prefix: bool = False, suffix: str = "") -> str:
    """'tv' -> 'Playlist Checker_tv_2026-10-23.m3u8'.
    When the date / prefix option is on, a date / prefix already in the name (a file saved by this
    program earlier) is replaced, so they never pile up; when it is off, the name is kept as it is."""
    if with_date:       # only replace what this program adds - keep the user's own date / name
        base = re.sub(r"[ _-]*\d{4}-\d{2}-\d{2}$", "", base)
    if with_prefix:
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


# video players the program can start: key -> (name shown in the menu, program names to look for)
PLAYERS = [
    ("vlc", "VLC", ["vlc"]),
    ("mpv", "mpv", ["mpv"]),
    ("celluloid", "Celluloid", ["celluloid"]),
    ("smplayer", "SMPlayer", ["smplayer"]),
    ("totem", "GNOME Videos (Totem)", ["totem"]),
    ("ffplay", "ffplay (from ffmpeg)", ["ffplay"]),
]
PLAYER_NAMES = {k: n for k, n, _ in PLAYERS}


def find_program(key: str) -> str | None:
    names = next((exes for k, _, exes in PLAYERS if k == key), [key])
    cands = [shutil.which(n) for n in names]
    if sys.platform.startswith("win"):
        pf = [os.environ.get("ProgramFiles", r"C:\Program Files"), os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")]
        extra = {"vlc": [r"VideoLAN\VLC\vlc.exe"], "mpv": [r"mpv\mpv.exe"], "smplayer": [r"SMPlayer\smplayer.exe"]}
        cands += [os.path.join(b, rel) for b in pf for rel in extra.get(key, [])]
    elif sys.platform == "darwin":
        cands += {"vlc": ["/Applications/VLC.app/Contents/MacOS/VLC"],
                  "mpv": ["/Applications/mpv.app/Contents/MacOS/mpv"]}.get(key, [])
    return next((c for c in cands if c and os.path.isfile(c)), None)


def player_command(key: str, exe: str, url: str, name: str, ua: str | None, ref: str | None) -> list[str]:
    """Command line that plays one stream, passing the channel's User-Agent / Referer where possible."""
    if key == "vlc":
        cmd = [exe, url, f":meta-title={name}"]
        cmd += [f":http-user-agent={ua}"] if ua else []
        cmd += [f":http-referrer={ref}"] if ref else []
        return cmd
    if key == "mpv":
        cmd = [exe, "--force-window=immediate", f"--title={name}"]
        cmd += [f"--user-agent={ua}"] if ua else []
        cmd += [f"--referrer={ref}"] if ref else []
        return cmd + ["--", url]
    if key == "celluloid":
        cmd = [exe, "--new-window"]
        cmd += [f"--mpv-user-agent={ua}"] if ua else []
        cmd += [f"--mpv-referrer={ref}"] if ref else []
        return cmd + [url]
    if key == "ffplay":
        cmd = [exe, "-hide_banner", "-loglevel", "error", "-window_title", name]
        cmd += ["-user_agent", ua] if ua else []
        cmd += ["-headers", f"Referer: {ref}\r\n"] if ref else []
        return cmd + ["-i", url]
    return [exe, url]


def split_command_line(template: str, windows: bool | None = None) -> list[str]:
    """Split a custom player command. Windows follows the MS C runtime quoting rules,
    so quoted paths such as "C:\\Program Files\\VideoLAN\\VLC\\vlc.exe" work."""
    if windows is None:
        windows = sys.platform.startswith("win")
    if not windows:
        return shlex.split(template)
    args: list[str] = []
    buf: list[str] = []
    token = quoted = False
    i = 0
    while i < len(template):
        ch = template[i]
        if ch == "\\":
            j = i
            while j < len(template) and template[j] == "\\":
                j += 1
            count = j - i
            if j < len(template) and template[j] == '"':
                buf.append("\\" * (count // 2))
                if count % 2:
                    buf.append('"')
                    j += 1
            else:
                buf.append("\\" * count)
            token = True
            i = j
        elif ch == '"':
            quoted = not quoted
            token = True
            i += 1
        elif ch in " \t\r\n" and not quoted:
            if token:
                args.append("".join(buf))
                buf, token = [], False
            i += 1
        else:
            buf.append(ch)
            token = True
            i += 1
    if quoted:
        raise ValueError("unbalanced quotes in the command")
    if token:
        args.append("".join(buf))
    return args


def custom_command(template: str, url: str, name: str, ua: str | None, ref: str | None) -> list[str]:
    parts = split_command_line(template)
    values = {"{url}": url, "{name}": name, "{ua}": ua or DEFAULT_UA, "{referer}": ref or ""}
    out = []
    for part in parts:
        for k, v in values.items():
            part = part.replace(k, v)
        out.append(part)
    if "{url}" not in template:
        out.append(url)
    return out


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
            if is_playlist_name(p.name) and not (skip_hidden and is_hidden(p)):
                found.append(p)
    return found


def desktop_quote(arg: str) -> str:
    """Quote one argument for the Exec= line of a .desktop file."""
    if arg and not re.search(r'[\s"`$\\\'<>~|&;*?#()]', arg):
        return arg
    return '"' + re.sub(r'(["`$\\])', r'\\\1', arg) + '"'


def desktop_exec_arg(arg: str) -> str:
    """Quoted argument for Exec=; a literal % must be written %% there (%F etc. are field codes)."""
    return desktop_quote(arg).replace("%", "%%")


SETTING_TYPES = {
    "timeout": (int, float), "threads": (int, float), "user_agent": str, "player": str, "player_custom": str,
    "encoding": str, "last_dir": str, "theme": str, "export": dict, "geo_learned": dict,
    "remembered_ticks": dict,
}
BOOL_SETTINGS = ("deep_hls", "ignore_ssl", "dup_url", "dup_name", "dup_quality", "hide_hidden", "date_names",
                 "prefix_names", "bidi_fix", "confirm_exit", "auto_check", "tint_rows", "hide_excluded",
                 "remember_ticks", "geo_server", "geo_loop", "geo_picture", "geo_ask", "click_play",
                 "replace_player", "retry_temporary", "black_screen", "remember_results")


def clean_settings(data: dict) -> dict:
    """Drop settings with a wrong type (damaged or hand-edited file) instead of failing to start."""
    out = {}
    for k, v in data.items():
        want = SETTING_TYPES.get(k, bool if k in BOOL_SETTINGS else None)
        if want is None:
            ok = True                                     # unknown / free-form setting
        elif want is bool:
            ok = isinstance(v, bool)
        elif want == (int, float):
            ok = isinstance(v, (int, float)) and not isinstance(v, bool)
        else:
            ok = isinstance(v, want)
        if ok:
            out[k] = v
    gl = out.get("geo_learned")
    if isinstance(gl, dict):
        def ok_pic(p, n):
            return isinstance(p, list) and len(p) >= n and isinstance(p[0], int) and isinstance(p[1], (int, float))
        # older versions stored only [fingerprint, brightness] - such entries still work
        out["geo_learned"] = {"pics": [p[:4] for p in gl.get("pics", []) if ok_pic(p, 2)]
                              if isinstance(gl.get("pics"), list) else [],
                              "segs": [x for x in gl.get("segs", []) if isinstance(x, str)]
                              if isinstance(gl.get("segs"), list) else [],
                              "rejected": [p[:3] for p in gl.get("rejected", []) if ok_pic(p, 2)]
                              if isinstance(gl.get("rejected"), list) else []}
    rt = out.get("remembered_ticks")
    if isinstance(rt, dict):
        out["remembered_ticks"] = {k: [x for x in rt.get(k, []) if isinstance(x, str)]
                                   if isinstance(rt.get(k), list) else [] for k in ("groups_off", "playlists_off")}
    return out


def age_text(seconds: float) -> str:
    """'just now', '5 min ago', '3 h ago', '2 days ago', '3 weeks ago', '4 months ago'."""
    s = max(0, int(seconds))
    if s < 60:
        return "just now"
    if s < 3600:
        return f"{s // 60} min ago"
    if s < 86400:
        return f"{s // 3600} h ago"
    days = s // 86400
    if days < 14:
        return "1 day ago" if days == 1 else f"{days} days ago"
    if days < 60:
        return f"{days // 7} weeks ago"
    return f"{days // 30} months ago"


def quality_dict_ok(q) -> bool:
    """Is this the quality part of a remembered result - or None? (the file may be hand-edited)"""
    if q is None:
        return True
    if not isinstance(q, dict):
        return False
    for k in ("w", "h", "bw", "fps", "variants"):
        if k in q and (not isinstance(q[k], (int, float)) or isinstance(q[k], bool)):
            return False                   # quality_text / quality_rank would fail on these
    for k in ("codec", "audio", "src"):
        if k in q and not isinstance(q[k], str):
            return False
    return True


def load_results() -> dict:
    """Remembered check results: result_key() hash -> [status, info, ms, quality, time].
    A version 1 file (keys were plain stream addresses) is converted and rewritten at once."""
    try:
        data = json.loads(RESULTS_FILE.read_text("utf-8"))
        items = data.get("results", {}) if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}
    hashed = isinstance(data, dict) and data.get("version") == 2
    oldest = time.time() - RESULTS_MAX_DAYS * 86400
    out = {}
    for url, e in items.items() if isinstance(items, dict) else ():
        # skip damaged / hand-edited entries instead of failing
        if (isinstance(url, str) and isinstance(e, list) and len(e) >= 5 and e[0] in FINAL_STATUSES
                and isinstance(e[1], str) and (e[2] is None or isinstance(e[2], int))
                and quality_dict_ok(e[3]) and isinstance(e[4], (int, float)) and e[4] >= oldest):
            out[url if hashed else result_hash(url)] = e[:5]
    if not hashed and items:
        save_results(out)                  # no plain addresses / logins left on disk
    return out


def save_results(results: dict) -> None:
    if len(results) > RESULTS_MAX:      # keep the newest
        keep = sorted(results.items(), key=lambda kv: kv[1][4])[-RESULTS_MAX:]
        results.clear()
        results.update(keep)
    try:
        RESULTS_FILE.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp_name = tempfile.mkstemp(prefix=".results-", suffix=".json.tmp", dir=RESULTS_FILE.parent)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump({"version": 2, "results": results}, f, ensure_ascii=False, separators=(",", ":"))
            os.replace(tmp_name, RESULTS_FILE)      # atomic: a crash can't leave half a file
        except OSError:
            try:
                os.unlink(tmp_name)
            except OSError:
                pass
            raise
    except OSError:
        pass


def load_settings() -> dict:
    for f in (SETTINGS_FILE, OLD_SETTINGS_FILE):
        try:
            data = json.loads(f.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return clean_settings(data)
        except Exception:
            continue
    return {}


# =============================================================================
#  Look (colours of the light theme drawn on top of ttk "clam" on Linux)
# =============================================================================

THEMES = {
    "light": {
        "bg": "#f3f4f6",          # window background
        "surface": "#ffffff",     # lists, tables, text fields
        "header": "#eceef2",      # table headings
        "border": "#d3d7de",
        "border_strong": "#b9bfc9",
        "text": "#1f2328",
        "muted": "#5f6b7a",
        "disabled": "#9aa2ad",
        "accent": "#2f6fdb",
        "accent_hover": "#285fc0",
        "accent_pressed": "#2252a6",
        "accent_soft": "#c3d6f6",  # selected row of a list without keyboard focus
        "accent_disabled": "#a9c1ec",
        "accent_disabled_text": "#eef3fc",
        "on_accent": "#ffffff",    # text on the accent colour
        "hover": "#e8ebf0",
        "pressed": "#dce0e7",
        "thumb": "#c4c9d2",
        "thumb_hover": "#a7aeb9",
        "link": "#1f5fc4",
        "link_hover": "#143f86",
        # channel table: status colours (readable on the surface and on the playlist tints)
        "status": {ONLINE: "#1a7f37", OFFLINE: "#cf222e", BLOCKED: "#8250df", CHECKING: "#0969da",
                   UNCHECKED: "#57606a"},
        "excluded": "#a3aab4",
        "dup_bg": "#fff3c4",
        "tint": 0.0,               # 0: the light tints of PLAYLIST_COLORS
    },
    "dark": {
        "bg": "#1d1f23",
        "surface": "#25282d",
        "header": "#2c3036",
        "border": "#3a3f47",
        "border_strong": "#4b515b",
        "text": "#e4e7eb",
        "muted": "#9aa3ad",
        "disabled": "#646b75",
        "accent": "#3b7be4",
        "accent_hover": "#4a88ec",
        "accent_pressed": "#2d64c2",
        "accent_soft": "#2a426b",
        "accent_disabled": "#2b3d5c",
        "accent_disabled_text": "#8496b3",
        "on_accent": "#ffffff",
        "hover": "#31353c",
        "pressed": "#3a3f47",
        "thumb": "#4b515b",
        "thumb_hover": "#5f6671",
        "link": "#79aaf7",
        "link_hover": "#a8c8fb",
        "status": {ONLINE: "#4ac26b", OFFLINE: "#ff6b62", BLOCKED: "#b98dfa", CHECKING: "#5aa9ff",
                   UNCHECKED: "#8b949e"},
        "excluded": "#5f666f",
        "dup_bg": "#3f3a1c",
        "tint": 0.14,              # playlist tints: this much of the playlist colour on the surface
    },
}
THEME_CHOICES = (("auto", "Same as the system"), ("light", "Light"), ("dark", "Dark"))
UI = dict(THEMES["light"])      # the colours in use; changed in place by App._apply_theme
THEMED = {"on": False}          # True while the colours above are drawn (ttk "clam")


def system_prefers_dark() -> bool:
    """Does the desktop use a dark colour scheme? (GNOME / Cinnamon / MATE / KDE, Windows, macOS)"""
    def run(cmd) -> str:
        try:
            return subprocess.run(cmd, capture_output=True, text=True, timeout=2).stdout.strip().lower()
        except (OSError, subprocess.SubprocessError):
            return ""
    try:
        if sys.platform == "win32":
            import winreg
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize") as k:
                return winreg.QueryValueEx(k, "AppsUseLightTheme")[0] == 0
        if sys.platform == "darwin":
            return run(["defaults", "read", "-g", "AppleInterfaceStyle"]) == "dark"
        if ":dark" in os.environ.get("GTK_THEME", "").lower():
            return True
        if shutil.which("gsettings"):
            if "dark" in run(["gsettings", "get", "org.gnome.desktop.interface", "color-scheme"]):
                return True
            for schema in ("org.gnome.desktop.interface", "org.cinnamon.desktop.interface",
                           "org.mate.interface"):
                if "dark" in run(["gsettings", "get", schema, "gtk-theme"]):
                    return True
        kde = Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config") / "kdeglobals"
        if kde.is_file():
            m = re.search(r"^ColorScheme\s*=\s*(.*)$", kde.read_text("utf-8", "ignore"), re.M)
            return bool(m and "dark" in m.group(1).lower())
    except Exception:
        pass
    return False


def playlist_tint(i: int) -> str:
    """Row background of the i-th playlist colour in the current theme."""
    base, light = PLAYLIST_COLORS[i % len(PLAYLIST_COLORS)]
    if not UI.get("tint"):
        return light
    mixed = _mix(_hex_rgb(UI["surface"]), _hex_rgb(base), UI["tint"])
    return "#%02x%02x%02x" % tuple(int(round(v)) for v in mixed)


def _hex_rgb(color: str) -> tuple[int, int, int]:
    return int(color[1:3], 16), int(color[3:5], 16), int(color[5:7], 16)


def _mix(a: tuple, b: tuple, t: float) -> tuple:
    return tuple(x + (y - x) * t for x, y in zip(a, b))


def indicator_image(master, size: int, shape: str, border: str, fill: str, mark: str | None,
                    gap: int, back: str) -> tk.PhotoImage:
    """Smooth (anti-aliased) check box or radio button picture, `gap` empty pixels on its right."""
    s = float(size)
    half, radius = s / 2, (max(2.0, s / 5) if shape == "box" else s / 2)

    def shape_dist(px, py, inset):   # signed distance to the (rounded) outline, < 0 = inside
        if shape == "box":
            hx = half - inset - radius
            qx, qy = abs(px - half) - hx, abs(py - half) - hx
            out = (max(qx, 0) ** 2 + max(qy, 0) ** 2) ** 0.5
            return out + min(max(qx, qy), 0) - radius
        return ((px - half) ** 2 + (py - half) ** 2) ** 0.5 - (half - inset)

    def seg_dist(px, py, a, b):
        ax, ay = a
        bx, by = b
        dx, dy = bx - ax, by - ay
        t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
        return ((px - ax - t * dx) ** 2 + (py - ay - t * dy) ** 2) ** 0.5

    tick = [(s * .25, s * .52), (s * .43, s * .70), (s * .76, s * .32)]
    width = max(1.6, s / 8)
    bg, bc, fc = _hex_rgb(back), _hex_rgb(border), _hex_rgb(fill)
    mc = _hex_rgb(mark) if mark else None
    img = tk.PhotoImage(master=master, width=size + gap, height=size)
    rows, clear = [], []
    for y in range(size):
        row = []
        for x in range(size + gap):
            px, py = x + .5, y + .5
            outer = max(0.0, min(1.0, .5 - shape_dist(px, py, 0))) if x < size else 0.0
            if outer <= .02:
                clear.append((x, y))
                row.append(back)
                continue
            col = _mix(bg, bc, outer)
            col = _mix(col, fc, max(0.0, min(1.0, .5 - shape_dist(px, py, 1))))
            if mc:
                if shape == "box":
                    d = min(seg_dist(px, py, tick[0], tick[1]), seg_dist(px, py, tick[1], tick[2])) - width / 2
                else:
                    d = ((px - half) ** 2 + (py - half) ** 2) ** 0.5 - s * .2
                col = _mix(col, mc, max(0.0, min(1.0, .5 - d)))
            row.append("#%02x%02x%02x" % tuple(int(round(v)) for v in col))
        rows.append("{" + " ".join(row) + "}")
    img.put(" ".join(rows))
    for x, y in clear:
        master.tk.call(img, "transparency", "set", x, y, 1)
    return img


def _ttk_buttonbox(self):
    """OK / Cancel of the simple dialogs as themed buttons, right-aligned, OK highlighted."""
    box = ttk.Frame(self, padding=(10, 4, 10, 10))
    ttk.Button(box, text="Cancel", command=self.cancel).pack(side="right", padx=(6, 0))
    ttk.Button(box, text=getattr(self, "ok_text", "OK"), style="Accent.TButton", command=self.ok,
               default="active").pack(side="right")
    self.bind("<Return>", self.ok)
    self.bind("<Escape>", self.cancel)
    box.pack(fill="x", side="bottom")


simpledialog.Dialog.buttonbox = _ttk_buttonbox


class FlowFrame(ttk.Frame):
    """Lays its items out left to right and wraps them onto a new row when the window is too narrow
    (small screens such as 1024 x 768). An item can have a separator line before it, which is only
    shown when the item is not the first one of its row."""

    LEAD_PAD = (4, 6)       # space left / right of a separator line

    def __init__(self, master, gap: int = 0, row_gap: int = 6, **kw):
        super().__init__(master, **kw)
        self._items: list[tuple[tk.Widget, bool, tk.Widget | None]] = []
        self.gap, self.row_gap, self._width = gap, row_gap, 0
        self._pending = False
        self.bind("<Configure>", self._on_configure)

    def add(self, widget, right: bool = False, lead: bool = False):
        """Add a child of this frame; right=True keeps it at the right edge of its row;
        lead=True draws a separator line before it (not when it starts a row)."""
        sep = ttk.Separator(self, orient="vertical") if lead else None
        self._items.append((widget, right, sep))
        # a button whose text changes ("Stop" -> "Skip pictures") makes its group wider: lay out again
        widget.bind("<Configure>", lambda e: self._schedule(), add="+")
        self._schedule()

    def _schedule(self):
        if not self._pending:
            self._pending = True
            self.after_idle(self.relayout)

    def _on_configure(self, e):
        if e.width != self._width:
            self._width = e.width
            self.relayout()

    def relayout(self):
        self._pending = False
        width = self.winfo_width()
        if width <= 1 or not self._items:
            return
        lead_w = sum(self.LEAD_PAD) + 1
        rows, row, x = [], [], 0
        for w, right, sep in self._items:
            extra = (self.gap + (lead_w if sep is not None else 0)) if row else 0
            if row and x + extra + w.winfo_reqwidth() > width:
                rows.append(row)
                row, x, extra = [], 0, 0
            row.append((w, right, sep, extra))
            x += extra + w.winfo_reqwidth()
        rows.append(row)
        y = 0
        for row in rows:
            x, height = 0, max(w.winfo_reqheight() for w, _, _, _ in row)
            for i, (w, right, sep, extra) in enumerate(row):
                if sep is not None:
                    if i:
                        sep.place(x=x + self.gap + self.LEAD_PAD[0], y=y + 4, width=1, height=height - 6)
                    else:
                        sep.place_forget()
                wx = x + extra
                if right:
                    wx = max(wx, width - w.winfo_reqwidth())
                w.place(x=wx, y=y + height - w.winfo_reqheight(), height=w.winfo_reqheight())
                x = wx + w.winfo_reqwidth()
            y += height + self.row_gap
        total = y - self.row_gap
        if int(self.cget("height") or 0) != total:
            self.configure(height=total)


# =============================================================================
#  Dialogs
# =============================================================================

class ComboDialog(simpledialog.Dialog):
    """Ask for a value with a drop-down of existing values (groups)."""

    def __init__(self, parent, title, prompt, values, initial=""):
        self.prompt, self.values, self.initial, self.result = prompt, values, initial, None
        super().__init__(parent, title)

    def body(self, master):
        ttk.Label(master, text=vis(self.prompt)).pack(anchor="w", padx=8, pady=(10, 4))
        self.var = tk.StringVar(value=self.initial)
        self.to_logical = {vis(v): v for v in self.values}
        if vis(self.initial) != self.initial:
            self.var.set(vis(self.initial))
        cb = ttk.Combobox(master, textvariable=self.var, values=list(self.to_logical), width=45)
        cb.pack(fill="x", padx=8, pady=(2, 8))
        return cb

    def apply(self):
        value = one_line(self.var.get()).strip()
        self.result = self.to_logical.get(value, value)


class TextDialog(simpledialog.Dialog):
    """Ask for a text, showing a Hebrew / Arabic initial value the right way round."""

    def __init__(self, parent, title, prompt, initial=""):
        self.prompt, self.initial, self.result = prompt, initial, None
        super().__init__(parent, title)

    def body(self, master):
        ttk.Label(master, text=vis(self.prompt)).pack(anchor="w", padx=8, pady=(10, 4))
        self.var = tk.StringVar(value=vis(self.initial))
        entry = ttk.Entry(master, textvariable=self.var, width=48)
        entry.pack(fill="x", padx=8, pady=(2, 8))
        entry.select_range(0, "end")
        return entry

    def apply(self):
        value = one_line(self.var.get()).strip()
        # unchanged: give back the real (logical) text, not the reordered one shown on screen
        self.result = self.initial.strip() if value == vis(self.initial).strip() else value


def ppm_to_photo(master, ppm: bytes) -> tk.PhotoImage | None:
    """Thumbnail -> Tk image (raw PPM where Tk accepts it, else pixel by pixel)."""
    try:
        return tk.PhotoImage(master=master, data=ppm)
    except tk.TclError:
        pass
    img_data = parse_ppm(ppm)
    if not img_data:
        return None
    w, h, px = img_data
    img = tk.PhotoImage(master=master, width=w, height=h)
    rows = []
    for y in range(h):
        row = px[y * w * 3:(y + 1) * w * 3]
        rows.append("{" + " ".join("#%02x%02x%02x" % (row[i], row[i + 1], row[i + 2])
                                   for i in range(0, len(row), 3)) + "}")
    img.put(" ".join(rows))
    return img


class SamePictureDialog(tk.Toplevel):
    """Several channels show exactly the same picture: probably a 'not available in your country' banner."""

    def __init__(self, parent, members, ppm: bytes | None, distinct: int | None = None,
                 preview: bytes | None = None):
        super().__init__(parent)
        self.result = None
        self.title("Same picture on several channels")
        self.transient(parent)
        self.resizable(False, False)
        body = ttk.Frame(self, padding=18)
        body.pack(fill="both", expand=True)
        # the sharp preview (taken just now) when there is one, else the small thumbnail enlarged
        self._img = None
        for data, zoom in ((preview, 1), (ppm, 3)):
            if not data:
                continue
            try:
                img = ppm_to_photo(self, data)
            except tk.TclError:
                img = None
            if img is not None:
                self._img = img.zoom(zoom) if zoom > 1 else img
                break
        wrap = max(480, self._img.width() if self._img else 0)
        if self._img:
            ttk.Label(body, image=self._img, relief="solid").grid(row=0, column=0, sticky="n", pady=(0, 12))
        ttk.Label(body, wraplength=wrap, justify="left",
                  text=vis(f"{distinct or len(members)} different channels ({len(members)} streams) show "
                           "exactly this picture, and it did not change a few seconds later.\n\n"
                           "This is usually a “not available in your country” banner (or another "
                           "placeholder). Mark them as geo-blocked? They will be left out when saving, "
                           "and the program will recognise this picture in future checks.")
                  ).grid(row=1, column=0, sticky="nw")
        lf = ttk.Frame(body)
        lf.grid(row=2, column=0, sticky="nsew", pady=(10, 0))
        lb = tk.Listbox(lf, height=min(6, len(members)), width=48, activestyle="none")
        for m in members:
            lb.insert("end", vis(f"{m.name}   ({m.group or NO_GROUP})"))
        sb = ttk.Scrollbar(lf, orient="vertical", command=lb.yview)
        lb.configure(yscrollcommand=sb.set)
        lb.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        bf = ttk.Frame(body)
        bf.grid(row=3, column=0, sticky="e", pady=(14, 0))
        ttk.Button(bf, text="Decide later", command=lambda: self._done(None)).pack(side="left", padx=(0, 6))
        ttk.Button(bf, text="Not a banner", command=lambda: self._done("not")).pack(side="left", padx=(0, 6))
        ttk.Button(bf, text="⛔  Mark as geo-blocked", style="Accent.TButton",
                   command=lambda: self._done("block")).pack(side="left")
        self.protocol("WM_DELETE_WINDOW", lambda: self._done(None))
        self.bind("<Escape>", lambda e: self._done(None))
        self.update_idletasks()
        x = parent.winfo_rootx() + (parent.winfo_width() - self.winfo_width()) // 2
        y = parent.winfo_rooty() + (parent.winfo_height() - self.winfo_height()) // 3
        self.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        try:
            self.grab_set()
        except tk.TclError:
            pass
        self.wait_window(self)

    def _done(self, value):
        self.result = value
        self.destroy()


class ExportDialog(simpledialog.Dialog):
    OPTIONS = [
        ("drop_offline", "Remove offline channels", True),
        ("drop_blocked", "Remove geo-blocked channels (“not available in your country”)", True),
        ("drop_dups", "Remove duplicates", True),
        ("drop_unchecked", "Remove channels not checked in this session", False),
        ("only_enabled_groups", "Only groups and playlists ticked ☑ on the left", True),
        ("sort_groups", "Sort groups A-Z  (otherwise: order of the group list)", False),
        ("sort_channels", "Sort channels A-Z inside each group  (otherwise: original order)", False),
        ("split", "Save one playlist file per group (into a folder)", False),
    ]

    ok_text = "Save…"

    def __init__(self, parent, summary, saved):
        self.summary, self.saved, self.result = summary, saved or {}, None
        super().__init__(parent, "Save new playlist")

    def body(self, master):
        bold = tkfont.nametofont("TkDefaultFont").copy()
        bold.configure(weight="bold")
        self._bold = bold
        ttk.Label(master, text=self.summary, font=bold).grid(
            row=0, column=0, sticky="w", padx=8, pady=(10, 8))
        self.vars = {}
        for r, (key, text, default) in enumerate(self.OPTIONS, 1):
            self.vars[key] = tk.BooleanVar(value=self.saved.get(key, default))
            ttk.Checkbutton(master, text=text, variable=self.vars[key]).grid(row=r, column=0, sticky="w", padx=8, pady=1)
        fmt = ttk.LabelFrame(master, text="Format", padding=(10, 6))
        fmt.grid(row=len(self.OPTIONS) + 1, column=0, sticky="we", padx=8, pady=(12, 6))
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
        self._fit_to_screen()
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
        self._dl_queue: list[tuple] = []   # downloads asked for while others were running
        self._dl_last_refresh = 0.0
        self._previous: dict[int, tuple] = {}
        self._manual_locked: set[int] = set()   # manually marked while a check was running
        self._aux_checkers: set = set()         # picture checkers of Mark / same-picture dialogs
        self._undo: list[dict] = []             # Edit -> Undo / Redo: list states before / after changes
        self.v_remember_results = tk.BooleanVar(value=self.settings.get("remember_results", True))
        self._results: dict = load_results() if self.v_remember_results.get() else {}
        self._restored_results: list[float] = []   # times of the results restored during the last load
        self._results_forgotten_at = 0.0   # Forget remembered check results: older results are not saved again
        self._redo: list[dict] = []

        self.v_hide_hidden = tk.BooleanVar(value=self.settings.get("hide_hidden", True))
        self.v_date_names = tk.BooleanVar(value=self.settings.get("date_names", True))
        self.v_prefix_names = tk.BooleanVar(value=self.settings.get("prefix_names", True))
        self.v_encoding = tk.StringVar(value=self.settings.get("encoding", "auto"))
        self.v_ua = tk.StringVar(value=self.settings.get("user_agent", DEFAULT_UA))
        self.v_confirm_exit = tk.BooleanVar(value=self.settings.get("confirm_exit", True))
        self.v_auto_check = tk.BooleanVar(value=self.settings.get("auto_check", False))
        self.v_tint = tk.BooleanVar(value=self.settings.get("tint_rows", True))
        self.v_hide_excluded = tk.BooleanVar(value=self.settings.get("hide_excluded", True))
        self.v_remember_ticks = tk.BooleanVar(value=self.settings.get("remember_ticks", True))
        self.v_player = tk.StringVar(value=self.settings.get("player", "auto"))
        self.v_click_play = tk.BooleanVar(value=self.settings.get("click_play", True))
        self.v_replace_player = tk.BooleanVar(value=self.settings.get("replace_player", True))
        self._player_proc = None
        self._last_play = (None, 0.0)
        self._restored_groups: set[str] = set()     # unticked from memory during the last load
        self._restored_sources: set[str] = set()
        self.ffmpeg = find_ffmpeg()
        self.v_geo_server = tk.BooleanVar(value=self.settings.get("geo_server", True))
        self.v_geo_loop = tk.BooleanVar(value=self.settings.get("geo_loop", True))
        self.v_retry = tk.BooleanVar(value=self.settings.get("retry_temporary", True))
        self._retrying = 0
        self._retry_result = None
        self._finish_text = ""
        self._finish_stopped = False
        self._finish_pic_skipped = False
        self._finish_rechecked: list[int] | None = None
        self._finish_retry: tuple | None = None
        self.v_geo_picture = tk.BooleanVar(value=self.settings.get("geo_picture", True) and bool(self.ffmpeg))
        self.v_geo_ask = tk.BooleanVar(value=self.settings.get("geo_ask", True))
        self.v_black = tk.BooleanVar(value=self.settings.get("black_screen", True) and bool(self.ffmpeg))
        self._banner_pics = False          # this check looks for banners (not only black screens)
        self._thumbs: dict[int, bytes] = {}
        self.pic_total = self.pic_done = 0
        self._pictures_only = False
        self._pic_phase = False
        self._pic_phase_start = 0.0
        self.source_color: dict[str, int] = {}     # playlist -> color number
        self.source_enabled: dict[str, bool] = {}  # playlist ticked for saving
        self.current_source: str | None = None
        self._swatch_images: dict[int, tk.PhotoImage] = {}
        is_x11 = self.tk.call("tk", "windowingsystem") == "x11"  # Windows / macOS draw RTL text themselves
        self.v_bidi = tk.BooleanVar(value=self.settings.get("bidi_fix", is_x11))
        BIDI["enabled"] = self.v_bidi.get()
        self.v_theme = tk.StringVar(value=self.settings.get("theme", "auto"))
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
    def _fit_to_screen(self, width: int = 1320, height: int = 800):
        """Open at 1320 x 800, or smaller on a small screen (1024 x 768, 1280 x 720 ...)."""
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        # leave room for the window frame and the desktop's panels / taskbar
        w, h = min(width, sw - 20), min(height, sh - 90)
        self.minsize(min(800, w), min(520, h))
        if w == width and h == height:
            self.geometry(f"{w}x{h}")
            return
        self.geometry(f"{w}x{h}+{max((sw - w) // 2, 0)}+{max((sh - h) // 3, 0)}")
        # a small screen: use all of it (the window manager keeps the panels free)
        try:
            if self.tk.call("tk", "windowingsystem") == "x11":
                self.attributes("-zoomed", True)
            else:
                self.state("zoomed")
        except tk.TclError:
            pass

    def _setup_style(self):
        st = ttk.Style(self)
        self._native_theme = st.theme_use()
        base = tkfont.nametofont("TkDefaultFont")
        self._line = base.metrics("linespace")
        self._bold_font = base.copy()
        self._bold_font.configure(weight="bold")
        self._italic_font = base.copy()
        self._italic_font.configure(slant="italic")
        self._caption_font = base.copy()
        size = int(base.cget("size"))
        self._caption_font.configure(size=size - 1 if size > 0 else size + 1)
        self._theme_gen = 0
        self._apply_theme()

    def _theme_name(self) -> str:
        choice = self.v_theme.get()
        if choice in THEMES:
            return choice
        return "dark" if system_prefers_dark() else "light"

    def on_theme(self):
        self._apply_theme()
        self.save_settings()

    def _apply_theme(self):
        """Draw the window in the chosen colours; can be called again to switch theme at once."""
        name = self._theme_name()
        UI.clear()
        UI.update(THEMES[name])
        st = ttk.Style(self)
        # Linux: always the drawn theme; Windows / macOS: their native look, the drawn one only for dark
        use_clam = "clam" in st.theme_names() and (sys.platform.startswith("linux") or name == "dark")
        st.theme_use("clam" if use_clam else self._native_theme)
        line = self._line
        st.configure("Treeview", rowheight=line + 8)
        st.configure("Accent.TButton", padding=(12, 4))
        st.configure("Small.TButton", padding=(6, 1))
        st.configure("Section.TLabel", font=self._bold_font)
        st.configure("Muted.TLabel", foreground="#666666")
        st.configure("Caption.TLabel", foreground="#666666", font=self._caption_font)
        was_themed = THEMED["on"]
        THEMED["on"] = use_clam
        if not use_clam:   # Windows / macOS: keep the native look
            self._tool_styles(st)
            if was_themed:            # back from dark: undo the dark colours of the classic widgets
                self.configure(background=UI["bg"])
                self._classic_colors()
                self._recolor_widgets()
            self._retint_tree()
            return
        c = UI
        self.configure(background=c["bg"])
        self._classic_colors()
        self._style_ttk(st, c, line)
        self._recolor_widgets()
        self._retint_tree()

    def _classic_colors(self):
        """Colours of classic Tk widgets created from now on (menus, simple dialogs, file dialog...)."""
        c = UI
        # classic Tk widgets: menus, simple dialogs, drop-down lists, file dialog
        for pattern, value in (
                ("*Toplevel.background", c["bg"]), ("*Frame.background", c["bg"]),
                ("*Label.background", c["bg"]), ("*Label.foreground", c["text"]),
                ("*Menu.background", c["surface"]), ("*Menu.foreground", c["text"]),
                ("*Menu.activeBackground", c["accent"]), ("*Menu.activeForeground", c["on_accent"]),
                ("*Menu.disabledForeground", c["disabled"]), ("*Menu.selectColor", c["accent"]),
                ("*Menu.relief", "flat"), ("*Menu.borderWidth", 1), ("*Menu.activeBorderWidth", 0),
                ("*Entry.background", c["surface"]), ("*Entry.foreground", c["text"]),
                ("*Entry.relief", "flat"), ("*Entry.highlightThickness", 1),
                ("*Entry.highlightBackground", c["border_strong"]), ("*Entry.highlightColor", c["accent"]),
                ("*Entry.selectBackground", c["accent"]), ("*Entry.selectForeground", c["on_accent"]),
                ("*Entry.insertBackground", c["text"]),
                ("*Listbox.background", c["surface"]), ("*Listbox.foreground", c["text"]),
                ("*Listbox.relief", "flat"), ("*Listbox.highlightThickness", 1),
                ("*Listbox.highlightBackground", c["border"]), ("*Listbox.highlightColor", c["border"]),
                ("*Listbox.selectBackground", c["accent"]), ("*Listbox.selectForeground", c["on_accent"]),
                ("*TCombobox*Listbox.highlightThickness", 0), ("*Button.background", c["surface"]),
                ("*Button.activeBackground", c["hover"]), ("*Button.relief", "flat"),
                ("*Button.highlightThickness", 1), ("*Button.highlightBackground", c["border_strong"]),
                ("*Checkbutton.background", c["bg"]), ("*Radiobutton.background", c["bg"]),
                ("*Scrollbar.background", c["thumb"]), ("*Scrollbar.troughColor", c["bg"]),
                ("*Text.background", c["surface"]), ("*Text.foreground", c["text"])):
            self.option_add(pattern, value)

    def _style_ttk(self, st: ttk.Style, c: dict, line: int):
        flat = {"lightcolor": c["surface"], "darkcolor": c["surface"]}
        st.configure(".", background=c["bg"], foreground=c["text"], bordercolor=c["border_strong"],
                     troughcolor=c["header"], focuscolor=c["accent"], selectbackground=c["accent"],
                     selectforeground=c["on_accent"], insertcolor=c["text"], lightcolor=c["bg"], darkcolor=c["bg"])
        st.map(".", foreground=[("disabled", c["disabled"])],
               background=[("disabled", c["bg"]), ("active", c["hover"])])
        st.configure("Muted.TLabel", foreground=c["muted"])
        st.configure("Caption.TLabel", foreground=c["muted"])
        st.configure("TSeparator", background=c["border"])

        # buttons: flat, thin border; the main actions in the accent colour
        st.configure("TButton", background=c["surface"], bordercolor=c["border_strong"], padding=(10, 4),
                     anchor="center", **flat)
        st.map("TButton",
               background=[("disabled", c["bg"]), ("pressed", c["pressed"]), ("active", c["hover"])],
               lightcolor=[("disabled", c["bg"]), ("pressed", c["pressed"]), ("active", c["hover"])],
               darkcolor=[("disabled", c["bg"]), ("pressed", c["pressed"]), ("active", c["hover"])],
               bordercolor=[("disabled", c["border"]), ("focus", c["accent"])])
        st.configure("Accent.TButton", background=c["accent"], foreground=c["on_accent"],
                     bordercolor=c["accent_pressed"], lightcolor=c["accent"], darkcolor=c["accent"])
        off = c["accent_disabled"]
        st.map("Accent.TButton",
               foreground=[("disabled", c["accent_disabled_text"])],
               background=[("disabled", off), ("pressed", c["accent_pressed"]), ("active", c["accent_hover"])],
               lightcolor=[("disabled", off), ("pressed", c["accent_pressed"]), ("active", c["accent_hover"])],
               darkcolor=[("disabled", off), ("pressed", c["accent_pressed"]), ("active", c["accent_hover"])],
               bordercolor=[("disabled", off), ("focus", c["accent_pressed"])])
        st.configure("Small.TButton", padding=(7, 1))
        self._tool_styles(st)

        # check / radio buttons: smooth accent-filled box / circle with a white tick / dot
        for cls in ("TCheckbutton", "TRadiobutton"):
            st.configure(cls, background=c["bg"], padding=(2, 2))
            st.map(cls, background=[("active", c["bg"])])
        try:
            self._make_indicators(st, max(13, round(line * .78)))
        except tk.TclError:
            pass   # keep the theme's own indicators

        # text fields
        for cls in ("TEntry", "TCombobox", "TSpinbox"):
            st.configure(cls, fieldbackground=c["surface"], background=c["surface"], bordercolor=c["border_strong"],
                         arrowcolor=c["muted"], padding=(6, 3), **flat)
            st.map(cls, bordercolor=[("focus", c["accent"])], lightcolor=[("focus", c["accent_soft"])],
                   fieldbackground=[("disabled", c["bg"]), ("readonly", c["surface"])],
                   background=[("active", c["hover"]), ("pressed", c["pressed"])],
                   arrowcolor=[("disabled", c["disabled"]), ("active", c["text"])])
        st.map("TCombobox", selectbackground=[("readonly", "!focus", c["surface"]), ("readonly", c["accent_soft"])],
               selectforeground=[("readonly", c["text"])])
        st.configure("TSpinbox", arrowsize=12)
        st.configure("TMenubutton", background=c["surface"], bordercolor=c["border_strong"], arrowcolor=c["muted"],
                     padding=(8, 3), **flat)
        st.map("TMenubutton", background=[("disabled", c["bg"]), ("active", c["hover"])],
               lightcolor=[("disabled", c["bg"]), ("active", c["hover"])],
               darkcolor=[("disabled", c["bg"]), ("active", c["hover"])],
               bordercolor=[("disabled", c["border"])])

        # tables
        st.configure("Treeview", background=c["surface"], fieldbackground=c["surface"], foreground=c["text"],
                     bordercolor=c["border"], **flat)
        st.map("Treeview", background=[("selected", "focus", c["accent"]), ("selected", c["accent_soft"])],
               foreground=[("selected", "focus", c["on_accent"]), ("selected", c["text"])])
        st.configure("Treeview.Heading", background=c["header"], foreground=c["muted"], bordercolor=c["border"],
                     lightcolor=c["header"], darkcolor=c["border"], relief="flat", padding=(6, 4), font=self._bold_font)
        st.map("Treeview.Heading", background=[("pressed", c["pressed"]), ("active", c["hover"])],
               lightcolor=[("pressed", c["pressed"]), ("active", c["hover"])],
               foreground=[("active", c["text"])])

        # slim scroll bars without arrow buttons
        for orient, sticky in (("Vertical", "ns"), ("Horizontal", "we")):
            st.layout(f"{orient}.TScrollbar",
                      [(f"{orient}.Scrollbar.trough",
                        {"sticky": sticky,
                         "children": [(f"{orient}.Scrollbar.thumb", {"expand": "1", "sticky": "nswe"})]})])
            st.configure(f"{orient}.TScrollbar", troughcolor=c["bg"], background=c["thumb"], bordercolor=c["bg"],
                         lightcolor=c["thumb"], darkcolor=c["thumb"], arrowsize=11, gripcount=0, relief="flat")
            st.map(f"{orient}.TScrollbar",
                   background=[("pressed", c["thumb_hover"]), ("active", c["thumb_hover"])],
                   lightcolor=[("pressed", c["thumb_hover"]), ("active", c["thumb_hover"])],
                   darkcolor=[("pressed", c["thumb_hover"]), ("active", c["thumb_hover"])])

        st.configure("Horizontal.TProgressbar", background=c["accent"], troughcolor=c["header"],
                     bordercolor=c["border"], lightcolor=c["accent"], darkcolor=c["accent"], thickness=10)
        st.configure("TLabelframe", background=c["bg"], bordercolor=c["border"], lightcolor=c["bg"], darkcolor=c["bg"])
        st.configure("TLabelframe.Label", background=c["bg"], foreground=c["text"], font=self._bold_font)
        st.configure("Sash", sashthickness=8, gripcount=0, background=c["bg"], lightcolor=c["bg"],
                     darkcolor=c["bg"], bordercolor=c["bg"])
        st.configure("TPanedwindow", background=c["bg"])

    @staticmethod
    def _tool_styles(st: ttk.Style):
        """Slimmer toolbar buttons (the toolbar has to fit a 1024-pixel screen)."""
        st.configure("Tool.TButton", padding=(7, 4))
        st.configure("Tool.Accent.TButton", padding=(8, 4))

    def _make_indicators(self, st: ttk.Style, size: int):
        c, gap = UI, max(5, size // 3)
        disabled_on, mark = c["accent_disabled"], c["on_accent"]
        looks = {  # state -> (border, fill, mark)
            "off": (c["border_strong"], c["surface"], None),
            "off_hover": (c["accent"], c["surface"], None),
            "off_disabled": (c["border"], c["bg"], None),
            "on": (c["accent_pressed"], c["accent"], mark),
            "on_hover": (c["accent_pressed"], c["accent_hover"], mark),
            "on_disabled": (disabled_on, disabled_on, c["accent_disabled_text"]),
        }
        self._indicator_images = {}
        self._theme_gen += 1          # an element name can be created only once
        for cls, shape, name in (("TCheckbutton", "box", "Checkbutton"), ("TRadiobutton", "circle", "Radiobutton")):
            im = {k: indicator_image(self, size, shape, *v, gap=gap, back=c["bg"]) for k, v in looks.items()}
            self._indicator_images[cls] = im
            element = f"pc{self._theme_gen}.{name}.indicator"
            st.element_create(element, "image", im["off"],
                              ("disabled", "selected", im["on_disabled"]), ("disabled", im["off_disabled"]),
                              ("selected", "active", im["on_hover"]), ("selected", im["on"]),
                              ("active", im["off_hover"]), sticky="")
            st.layout(cls, [(f"{name}.padding", {"sticky": "nswe", "children": [
                (element, {"side": "left", "sticky": ""}),
                (f"{name}.focus", {"side": "left", "sticky": "w", "children": [
                    (f"{name}.label", {"sticky": "nswe"})]})]})])

    def _color_menubar(self):
        mb = getattr(self, "_menubar", None)
        if mb is not None and THEMED["on"]:   # the menu bar blends with the window, the menus are lighter
            mb.configure(background=UI["bg"], foreground=UI["text"], activebackground=UI["hover"],
                         activeforeground=UI["text"], borderwidth=0)

    def _recolor_widgets(self):
        """Give the classic Tk widgets that already exist the colours of the theme (ttk ones follow the style)."""
        c = UI
        looks = {
            "Menu": {"-background": c["surface"], "-foreground": c["text"], "-activebackground": c["accent"],
                     "-activeforeground": c["on_accent"], "-disabledforeground": c["disabled"],
                     "-selectcolor": c["accent"]},
            "Toplevel": {"-background": c["bg"]},
            "Frame": {"-background": c["bg"]},
            "Label": {"-background": c["bg"], "-foreground": c["text"]},
            "Listbox": {"-background": c["surface"], "-foreground": c["text"], "-selectbackground": c["accent"],
                        "-selectforeground": c["on_accent"], "-highlightbackground": c["border"],
                        "-highlightcolor": c["border"]},
            "Entry": {"-background": c["surface"], "-foreground": c["text"], "-insertbackground": c["text"],
                      "-highlightbackground": c["border_strong"], "-highlightcolor": c["accent"],
                      "-selectbackground": c["accent"], "-selectforeground": c["on_accent"]},
        }
        root_class = self.winfo_class()
        todo = ["."]
        while todo:      # walk the Tcl widget tree: it also has widgets Tk made itself (menu bar copies, drop-downs)
            path = todo.pop()
            try:
                cls = self.tk.call("winfo", "class", path)
                look = looks.get("Toplevel" if cls == root_class else cls)
                if look:
                    for opt, value in look.items():
                        self.tk.call(path, "configure", opt, value)
                todo.extend(self.tk.splitlist(self.tk.call("winfo", "children", path)))
            except tk.TclError:
                continue
        self._color_menubar()

    def _retint_tree(self):
        """Status colours and row tints of the channel table in the current theme."""
        tree = getattr(self, "tree", None)
        if tree is None:
            return
        tree.tag_configure("excluded", foreground=UI["excluded"])
        for status, color in UI["status"].items():
            tree.tag_configure(status, foreground=color)
        tree.tag_configure("dup", background=UI["dup_bg"])
        for tag in self._swatch_images.get("_tags", ()):
            tree.tag_configure(tag, background=playlist_tint(int(tag[3:])))

    def _build_menu(self):
        mb = tk.Menu(self)
        self._menubar = mb
        self._color_menubar()
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
        m.configure(postcommand=lambda mm=m: self._edit_menu_post(mm))
        m.add_command(label="Undo", accelerator="Ctrl+Z", command=self.undo, state="disabled")
        m.add_command(label="Redo", accelerator="Ctrl+Y", command=self.redo, state="disabled")
        m.add_separator()
        m.add_command(label="Copy stream URLs", accelerator="Ctrl+C", command=self.copy_url)
        m.add_command(label="Paste stream links / playlist", accelerator="Ctrl+V", command=self.paste_channels)
        m.add_separator()
        m.add_command(label="Select all shown", accelerator="Ctrl+A", command=self.select_all)
        m.add_command(label="Rename channel…", accelerator="F2", command=self.rename_channel)
        m.add_command(label="Move selected to group…", accelerator="Ctrl+G", command=self.move_to_group)
        m.add_command(label="Delete selected", accelerator="Del", command=self.delete_selected)
        m.add_separator()
        m.add_command(label="Remove all offline channels from list", command=self.remove_offline)
        m.add_command(label="Remove all geo-blocked channels from list", command=self.remove_blocked)
        m.add_command(label="Remove all duplicates from list", command=self.remove_duplicates)
        mb.add_cascade(label="Edit", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Check all channels", accelerator="F5", command=self.check_all)
        m.add_command(label="Check shown channels", command=self.check_visible)
        m.add_command(label="Check selected channels", command=self.check_selected)
        m.add_separator()
        m.add_command(label="Recheck offline / broken channels", accelerator="Shift+F5", command=self.recheck_offline)
        m.add_command(label="Find “not available” banners in online channels (picture check)",
                      command=self.find_banners)
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
        m.add_checkbutton(label="Try again channels with temporary errors (timeout, HTTP 5xx)",
                          variable=self.v_retry, command=self.save_settings)
        m.add_checkbutton(label="Remember ticked / unticked groups and playlists", variable=self.v_remember_ticks,
                          command=self.on_remember_option)
        m.add_command(label="Forget remembered groups and playlists…", command=self.forget_ticks)
        m.add_checkbutton(label="Remember check results between sessions", variable=self.v_remember_results,
                          command=self.on_remember_results)
        m.add_command(label="Forget remembered check results…", command=self.forget_results)
        m.add_checkbutton(label="Hide unticked groups and playlists in the channel list",
                          variable=self.v_hide_excluded,
                          command=lambda: (self.save_settings(), self.refresh_channels()))
        m.add_checkbutton(label="Tint rows with the playlist color", variable=self.v_tint,
                          command=lambda: (self.save_settings(), self.refresh_channels()))
        thm = tk.Menu(m, tearoff=0)
        for value, label in THEME_CHOICES:
            thm.add_radiobutton(label=label, value=value, variable=self.v_theme, command=self.on_theme)
        m.add_cascade(label="Theme (light / dark)", menu=thm)
        m.add_separator()
        geo = tk.Menu(m, tearoff=0)
        geo.add_checkbutton(label="By the server's answer (451, 403 “your country”, redirects)",
                            variable=self.v_geo_server, command=self.save_settings)
        geo.add_checkbutton(label="Short looping video instead of live TV", variable=self.v_geo_loop,
                            command=self.save_settings)
        geo.add_checkbutton(label="By the picture – “not available” banners" +
                            ("" if self.ffmpeg else "  (needs ffmpeg)"),
                            variable=self.v_geo_picture, command=self.on_picture_option)
        geo.add_checkbutton(label="Ask when several channels show the same picture", variable=self.v_geo_ask,
                            command=self.save_settings)
        geo.add_separator()
        geo.add_command(label="Forget learned banners…", command=self.forget_banners)
        m.add_cascade(label="Detect geo-blocked channels", menu=geo)
        m.add_checkbutton(label="Black screen (no programme, only a logo) = offline" +
                          ("" if self.ffmpeg else "  (needs ffmpeg)"),
                          variable=self.v_black, command=self.on_black_option)
        enc = tk.Menu(m, tearoff=0)
        for value, label in LEGACY_ENCODINGS:
            enc.add_radiobutton(label=label, value=value, variable=self.v_encoding, command=self.save_settings)
        m.add_cascade(label="Encoding of old (non-UTF-8) playlists", menu=enc)
        pm = tk.Menu(m, tearoff=0, postcommand=lambda: self._fill_player_menu(pm))
        m.add_cascade(label="Video player", menu=pm)
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
        outer = ttk.Frame(self, padding=(8, 8, 8, 8))
        outer.pack(fill="x")
        tb = FlowFrame(outer, row_gap=8)     # wraps onto two rows on small screens
        tb.pack(fill="x")

        def group(title, right=False, lead=True):
            """A captioned cluster of buttons (with a separator before it when it follows another)."""
            f = ttk.Frame(tb)
            ttk.Label(f, text=title, style="Caption.TLabel").grid(row=0, column=0, sticky="w", padx=2, pady=(0, 3))
            row = ttk.Frame(f)
            row.grid(row=1, column=0, sticky="w")
            tb.add(f, right, lead)
            return row

        def btn(parent, text, cmd, style="Tool.TButton"):
            # width 0 = as wide as the text: the whole toolbar fits on one row at 1024 pixels
            b = ttk.Button(parent, text=text, command=cmd, style=style, width=0)
            b.pack(side="left", padx=2)
            return b

        g = group("Playlists", lead=False)    # the caption says what the short labels open
        btn(g, "Files…", self.open_files)
        btn(g, "Folder…", self.open_folder)
        btn(g, "URL…", self.open_url)
        ttk.Separator(g, orient="vertical").pack(side="left", fill="y", padx=4, pady=5)
        btn(g, "Clear list", self.clear_all)     # set apart by a line: it empties the list
        g = group("Check")
        self.btn_check = btn(g, "▶  Check streams", self.check_all, "Tool.Accent.TButton")
        self.btn_recheck = btn(g, "↻  Recheck offline", self.recheck_offline)
        self.btn_stop = btn(g, "■  Stop", self.stop_check)
        self.btn_stop.state(["disabled"])
        g = group("Save")
        btn(g, "💾  Save playlist…", self.export_dialog, "Tool.Accent.TButton")
        btn(g, "Export report…", self.export_report)

    def _build_settings(self):
        s = self.settings
        self.v_timeout = tk.StringVar(value=str(s.get("timeout", 8)))
        self.v_threads = tk.StringVar(value=str(s.get("threads", 20)))
        self.v_deep = tk.BooleanVar(value=s.get("deep_hls", True))
        self.v_ssl = tk.BooleanVar(value=s.get("ignore_ssl", True))
        self.v_dup_url = tk.BooleanVar(value=s.get("dup_url", True))
        self.v_dup_name = tk.BooleanVar(value=s.get("dup_name", False))
        self.v_dup_quality = tk.BooleanVar(value=s.get("dup_quality", True))

        ttk.Separator(self, orient="horizontal").pack(fill="x")
        outer = ttk.Frame(self, padding=(12, 6, 12, 10))
        outer.pack(fill="x")
        box = FlowFrame(outer, gap=10, row_gap=8)    # wraps onto two rows on small screens
        box.pack(fill="x")

        def card(title):
            """One category of options: a titled box, its options in two rows."""
            lf = ttk.LabelFrame(box, text=title, padding=(8, 2, 8, 6))
            box.add(lf)
            rows = []
            for r in range(2):
                f = ttk.Frame(lf)
                f.pack(anchor="w", pady=(4 if r else 0, 0))
                rows.append(f)
            return rows

        # connection: how the program talks to the servers (the User-Agent is in Settings -> User-Agent)
        r1, r2 = card("Connection")
        ttk.Label(r1, text="Timeout (s)").pack(side="left")
        ttk.Spinbox(r1, from_=2, to=60, width=3, textvariable=self.v_timeout).pack(side="left", padx=(6, 12))
        ttk.Label(r1, text="Parallel checks").pack(side="left")
        ttk.Spinbox(r1, from_=1, to=100, width=3, textvariable=self.v_threads).pack(side="left", padx=(6, 0))
        ttk.Checkbutton(r2, text="Ignore SSL certificate errors", variable=self.v_ssl).pack(side="left")

        # stream test: how deep a channel is tested
        r1, r2 = card("Stream test")
        ttk.Checkbutton(r1, text="Deep HLS check (test the video)", variable=self.v_deep).pack(side="left")
        # same variable as Settings -> "Black screen ... = offline", so both stay in step
        ttk.Checkbutton(r2, text="Black screen = offline" + ("" if self.ffmpeg else "  (needs ffmpeg)"),
                        variable=self.v_black, command=self.on_black_option).pack(side="left")

        r1, r2 = card("Duplicates")
        for row, text, var in ((r1, "Same stream URL", self.v_dup_url), (r1, "Same channel name", self.v_dup_name),
                               (r2, "Ignore HD / FHD / 4K / 1080p in names", self.v_dup_quality)):
            ttk.Checkbutton(row, text=text, variable=var, command=self.on_dup_options).pack(side="left", padx=(0, 12))
        ttk.Separator(self, orient="horizontal").pack(fill="x")

    def _build_statusbar(self):
        sb = ttk.Frame(self, padding=(12, 6, 12, 7))
        sb.pack(fill="x", side="bottom")
        ttk.Separator(self, orient="horizontal").pack(fill="x", side="bottom")
        self.progress = ttk.Progressbar(sb, length=220, mode="determinate")
        self.progress.pack(side="left", pady=1)
        self.lbl_status = ttk.Label(sb, text="")
        self.lbl_status.pack(side="left", padx=12)

    def _build_main(self):
        pw = ttk.Panedwindow(self, orient="horizontal")
        pw.pack(fill="both", expand=True, padx=12, pady=(10, 8))
        left, right = ttk.Frame(pw), ttk.Frame(pw)
        pw.add(left, weight=0)
        pw.add(right, weight=1)

        # ---- groups
        self._section_title(left, "Groups", "click ☑ to include / exclude").pack(fill="x", pady=(0, 5))
        gf = ttk.Frame(left)       # packed last (below): on a small screen it shrinks, not the playlists
        self.gtree = ttk.Treeview(gf, columns=("inc", "name", "total", "online"), show="headings", selectmode="browse")
        for col, text, w, anchor, stretch in (("inc", "✓", 30, "center", False), ("name", "Group", 200, "w", True),
                                              ("total", "Ch.", 48, "e", False), ("online", "Online", 60, "e", False)):
            self.gtree.heading(col, text=text, anchor=anchor)
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
        for text, cmd, w in (("All ☑", lambda: self.set_all_groups(True), 6), ("None ☐", lambda: self.set_all_groups(False), 7),
                             ("▲", lambda: self.move_group(-1), 2), ("▼", lambda: self.move_group(1), 2),
                             ("Rename…", self.rename_group, 8)):
            ttk.Button(gb, text=text, width=w, command=cmd, style="Small.TButton").pack(side="left", padx=(0, 4))

        # ---- playlists (color legend, filter, include / exclude)
        ptitle = self._section_title(left, "Playlists", "click a name to show only it")
        pf = ttk.Frame(left)
        self.ptree = ttk.Treeview(pf, columns=("inc", "name", "total", "online"), show="tree headings",
                                  selectmode="browse", height=5)
        self.ptree.column("#0", width=30, minwidth=30, stretch=False, anchor="center")
        for col, text, w, anchor, stretch in (("inc", "✓", 30, "center", False), ("name", "Playlist", 170, "w", True),
                                              ("total", "Ch.", 48, "e", False), ("online", "Online", 60, "e", False)):
            self.ptree.heading(col, text=text, anchor=anchor)
            self.ptree.column(col, width=w, anchor=anchor, stretch=stretch)
        psb = ttk.Scrollbar(pf, orient="vertical", command=self.ptree.yview)
        self.ptree.configure(yscrollcommand=psb.set)
        self.ptree.pack(side="left", fill="x", expand=True)
        psb.pack(side="right", fill="y")
        self.ptree.bind("<<TreeviewSelect>>", self.on_source_select)
        self.ptree.bind("<Button-1>", self.on_source_click)
        self._suppress_source_select = False
        # bottom-up, so the playlists and the group buttons always keep their room
        pf.pack(side="bottom", fill="x")
        ptitle.pack(side="bottom", fill="x", pady=(14, 5))
        gb.pack(side="bottom", fill="x", pady=(6, 0))
        gf.pack(fill="both", expand=True)

        # ---- filter bar
        fb = ttk.Frame(right, padding=(8, 0, 0, 0))
        fb.pack(fill="x")
        ttk.Label(fb, text="Search").pack(side="left")
        self.v_search = tk.StringVar()
        ttk.Entry(fb, textvariable=self.v_search, width=32).pack(side="left", padx=(6, 18))
        self.v_search.trace_add("write", lambda *a: self._debounced_refresh())
        ttk.Label(fb, text="Show").pack(side="left")
        self.v_show = tk.StringVar(value="All")
        cb = ttk.Combobox(fb, textvariable=self.v_show, values=SHOW_OPTIONS, state="readonly", width=28)
        cb.pack(side="left", padx=6)
        cb.bind("<<ComboboxSelected>>", lambda e: self.refresh_channels())
        self.lbl_shown = ttk.Label(fb, text="", style="Muted.TLabel")
        self.lbl_shown.pack(side="right")

        # ---- channel table
        tf = ttk.Frame(right, padding=(8, 0, 0, 0))
        tf.pack(fill="both", expand=True, pady=(7, 0))
        self.cols = ("num", "status", "name", "group", "quality", "info", "dup", "url", "source")
        self.col_titles = {"num": "#", "status": "Status", "name": "Channel", "group": "Group", "quality": "Quality",
                           "info": "Check result", "dup": "Duplicate", "url": self._url_title(), "source": "Playlist"}
        widths = {"num": 50, "status": 125, "name": 210, "group": 130, "quality": 235, "info": 230, "dup": 120,
                  "url": 330, "source": 110}
        self.tree = ttk.Treeview(tf, columns=self.cols, show="tree headings", selectmode="extended")
        self.tree.column("#0", width=30, minwidth=30, stretch=False, anchor="center")  # playlist color
        for c in self.cols:
            self.tree.heading(c, text=self.col_titles[c], command=lambda c=c: self.sort_by(c),
                              anchor="e" if c == "num" else "w")
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
        self._retint_tree()
        self.tree.tag_configure("remembered", font=self._italic_font)   # result from an earlier session
        self.tree.tag_configure("changed", font=self._bold_font)        # other result than last time

        self.cmenu = tk.Menu(self, tearoff=0)
        self.cmenu.add_command(label="▶ Play", command=self.play_selected)
        self.cmenu.add_command(label="Copy URL", accelerator="Ctrl+C", command=self.copy_url)
        self.cmenu.add_command(label="Paste stream links / playlist", accelerator="Ctrl+V", command=self.paste_channels)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="Check selected", command=self.check_selected)
        self.cmenu.add_command(label="Recheck all offline / broken", command=self.recheck_offline)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="⛔ Mark as geo-blocked (shows “not available” banner)", command=self.mark_blocked)
        self.cmenu.add_command(label="Not geo-blocked (undo, check again)", command=self.unmark_blocked)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="Rename channel…", command=self.rename_channel)
        self.cmenu.add_command(label="Move to group…", command=self.move_to_group)
        self.cmenu.add_separator()
        self.cmenu.add_command(label="Delete from list", command=self.delete_selected)
        self.tree.bind("<Button-3>", self.on_right_click)
        self.tree.bind("<Button-2>", self.on_right_click)  # macOS
        self.tree.bind("<Control-KeyPress>", self._tree_ctrl_key)
        self.tree.bind("<ButtonPress-1>", self.on_tree_press, add="+")
        self.tree.bind("<ButtonRelease-1>", self.on_tree_click, add="+")
        self.tree.bind("<Motion>", self.on_tree_motion, add="+")
        self.tree.bind("<Leave>", lambda e: self.tree.configure(cursor=""), add="+")
        self.tree.bind("<Double-1>", lambda e: self.play_selected())
        self.tree.bind("<Return>", lambda e: self.play_selected())

    @staticmethod
    def _section_title(parent, title: str, hint: str = "") -> ttk.Frame:
        """Bold section name with a short grey hint next to it."""
        f = ttk.Frame(parent)
        ttk.Label(f, text=title, style="Section.TLabel").pack(side="left")
        if hint:
            ttk.Label(f, text=hint, style="Muted.TLabel").pack(side="left", padx=(8, 0))
        return f

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
        def undo_key(e):
            try:
                w = str(e.widget)
                typing = self.tk.call("winfo", "class", w) in TEXT_FIELD_CLASSES and not (
                    self.tk.call("winfo", "class", w) == "TCombobox" and self.tk.call(w, "instate", "readonly"))
                if str(self.tk.call("grab", "current")) or \
                        str(self.tk.call("winfo", "toplevel", w)) != "." or typing:
                    return None               # a dialog is open, or typing in the search field
            except tk.TclError:
                return None
            letter = self._ctrl_letter(e)
            if letter == "z":
                self.redo() if e.state & 0x0001 else self.undo()    # Ctrl+Shift+Z = redo
            elif letter == "y":
                self.redo()
            else:
                return None
            return "break"
        self.bind_all("<Control-KeyPress>", undo_key, add="+")
        self.tree.bind("<Control-a>", lambda e: (self.select_all(), "break")[1])
        self.tree.bind("<Delete>", lambda e: self.delete_selected())
        self.tree.bind("<F2>", lambda e: self.rename_channel())
        self.tree.bind("<Control-g>", lambda e: self.move_to_group())

    # ------------------------------------------------------------------ loading
    def open_files(self):
        paths = self._fd().askopenfilenames(
            parent=self, title="Open playlists", initialdir=self.settings.get("last_dir") or str(Path.home()),
            filetypes=[("Playlists", "*.m3u *.m3u8 *.pls *.xspf "
                                      "*.m3u.gz *.m3u8.gz *.pls.gz *.xspf.gz"),
                       ("Lists of playlist URLs", "*.txt *.list"), ("All files", "*.*")])
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
            messagebox.showinfo(APP_TITLE, "No playlist files (.m3u .m3u8 .pls .xspf, also .gz) "
                                            "in this folder.", parent=self)
            return
        self.after_load(sum(self.load_path(f) for f in files))

    def open_url(self):
        url = simpledialog.askstring(APP_TITLE, "Playlist web address (http://… or https://…):", parent=self)
        if not url or not url.strip():
            return
        self._start_download(url.strip())

    def _start_download(self, url: str):
        """One playlist address (File → Open URL / command line): a download of one, so it can be
        stopped, is cancelled by “Clear list” and waits for downloads that are already running."""
        self._download_many([url], url, source=url, single=True)

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
            text = decode_bytes(path.read_bytes(), self.v_encoding.get())
        except (OSError, DamagedFileError) as e:
            messagebox.showerror(APP_TITLE, f"Could not open {path}:\n{e}", parent=self)
            return
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
            self.after_load(added, defer_check=bool(web))   # checked when the downloads are done
        if web:
            self._download_many(web, path.name, source=str(path), shown=added)

    def add_stream_urls(self, urls: list[str], source: str, group: str = "") -> int:
        g_attr = f' group-title="{group.replace(chr(34), chr(39))}"' if group else ""
        playlist = "#EXTM3U\n" + "".join(f"#EXTINF:-1{g_attr},{name_from_url(u)}\n{u}\n" for u in urls)
        return self.add_playlist_text(playlist, source, "")

    def _download_many(self, urls: list[str], label: str, source: str = "", single: bool = False,
                       shown: int = 0):
        """Download playlists in the background. shown: channels of the same list (direct links,
        local files) that were already added - they count for the automatic check at the end.
        While other downloads are running, this one waits for them."""
        if self.downloading:
            self._dl_queue.append((urls, label, source, single, shown))
            self.set_status(f"{label}: waits until the running downloads are finished …")
            return
        self.downloading = True
        self._dl_stop = stop = threading.Event()      # a new one: an old worker stays stopped
        for u in urls:  # colors follow the order of the list, not the order the downloads finish
            self._source_index(u)
        self._dl = {"label": label, "source": source, "total": len(urls), "done": 0, "ok": 0, "streams": 0,
                    "channels": 0, "shown": shown, "failed": [], "gen": self._dl_gen, "single": single}
        if not self.checking:                         # the progress bar belongs to a running check
            self.progress.stop()
            if single:
                self.progress.configure(mode="indeterminate")
                self.progress.start(12)
            else:
                self.progress.configure(mode="determinate", maximum=len(urls), value=0)
        self.btn_stop.state(["!disabled"])
        self.set_status(f"Downloading playlist {label} …" if single else
                        f"Downloading {len(urls)} playlists from {label} …")
        args = (urls, self.v_ua.get().strip() or DEFAULT_UA, self.v_ssl.get(), self.v_encoding.get(),
                self._dl_gen, stop)
        threading.Thread(target=self._download_worker, args=args, daemon=True).start()

    def _download_worker(self, urls, ua, ignore_ssl, legacy, gen, stop):
        def task(url):
            if stop.is_set():
                return url, "skipped", "", ""
            try:
                return (url,) + fetch_playlist(url, ua, ignore_ssl, legacy)
            except Exception as e:
                return url, "error", short_error(e), ""

        ex = ThreadPoolExecutor(max_workers=DOWNLOAD_PARALLEL)
        try:
            pending = {ex.submit(task, u) for u in urls}
            while pending and not stop.is_set():
                done, pending = wait(pending, timeout=0.25, return_when=FIRST_COMPLETED)
                for f in done:
                    if not stop.is_set():
                        self.q.put(("dl_item", gen) + f.result())
        finally:
            ex.shutdown(wait=False, cancel_futures=True)
            self.q.put(("dl_done", gen, stop.is_set()))

    def _download_item(self, gen, url, kind, text, base=""):
        if gen != self._dl_gen:
            return
        d = self._dl
        d["done"] += 1
        if kind == "playlist":
            n = self.add_playlist_text(text, url, "", quiet=True, base_url=base)
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
            why = ("the server answered with a web page or a message instead of a playlist "
                   "(wrong address, login needed or not available)")
            d["failed"].append((url, why + (f":\n   {text}" if text else "")))
        elif kind != "skipped":
            d["failed"].append((url, text or "download failed"))
        if not self.checking and not d["single"]:
            self.progress["value"] = d["done"]
        if not d["single"]:
            self.set_status(f"Downloading playlists from {d['label']}: {d['done']} / {d['total']} · "
                            f"{d['channels']} channels so far")
        now = time.monotonic()
        if now - self._dl_last_refresh > 1.5:  # keep the window responsive with big lists
            self._dl_last_refresh = now
            self.refresh_all()

    def _download_finished(self, gen, stopped):
        if gen != self._dl_gen:            # cleared meanwhile: clear_all() already reset everything
            return
        d = self._dl
        self.downloading = False
        if not self.checking:
            self.btn_stop.state(["disabled"])
            self.progress.stop()
            self.progress.configure(mode="determinate", value=0 if d["single"] else d["done"])
        if stopped:
            self._dl_queue.clear()         # Stop stops the waiting downloads too
        # channels added before the download (direct links / files of the same list) were already
        # reported - only start the automatic check for them now
        self.after_load(d["channels"], check_also=d["shown"])
        if d["single"]:
            self._single_download_finished(d, stopped)
        else:
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
                messagebox.showwarning(APP_TITLE, f"{len(d['failed'])} of {d['total']} addresses could not be "
                                       "loaded:\n\n" + "\n".join(lines) + more, parent=self)
        if self._dl_queue and not self.downloading:
            self._download_many(*self._dl_queue.pop(0))

    def _single_download_finished(self, d, stopped):
        url = d["label"]
        if stopped and not d["done"]:
            self.set_status(f"Download stopped: {url}")
        elif d["streams"]:
            self.set_status("That address is a single TV/radio stream, not a playlist – "
                            "it was added as one channel.")
        elif d["failed"]:
            self.set_status("Download failed.")
            why = d["failed"][0][1]
            if why.startswith("the server answered with"):
                why += ("\n\nCheck the address, or whether the provider needs a login or another "
                        "User-Agent (Settings → User-Agent).")
            messagebox.showerror(APP_TITLE, f"Could not download the playlist:\n{url}\n\n{why}", parent=self)

    def load_path(self, path: Path) -> int:
        try:
            data = path.read_bytes()
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not open {path}:\n{e}", parent=self)
            return 0
        try:
            data = unpack_bytes(data)
        except DamagedFileError as e:
            messagebox.showerror(APP_TITLE, f"{path.name}: {e}.", parent=self)
            return 0
        if b"\x00" in data[:4096] and not has_unicode_bom(data):
            messagebox.showerror(APP_TITLE, f"{path.name} is not a text playlist.", parent=self)
            return 0
        text = decode_bytes(data, self.v_encoding.get())
        if is_hls_text(text):
            # an HLS stream saved as a file (its segments / quality variants), not a channel list
            n = self.add_stream_urls([str(path)], str(path))
            self.set_status(f"{path.name} is a single HLS stream, not a list of channels – "
                            "it was added as one channel.")
            return n
        return self.add_playlist_text(text, str(path), str(path.parent.resolve()))

    def add_playlist_text(self, text: str, source: str, base_dir: str = "", quiet: bool = False,
                          base_url: str = "") -> int:
        """Add the channels of a playlist; returns how many (or -1 if quiet and it can't be read).
        base_url: the address the playlist really came from (after a redirect) - for relative links."""
        try:
            header, chans = parse_playlist(text, source, base_dir)
        except Exception as e:
            if quiet:
                return -1
            messagebox.showerror(APP_TITLE, f"Could not read {source}:\n{e}", parent=self)
            return 0
        for k, v in header.items():
            if k.lower() in ("url-tvg", "x-tvg-url", "tvg-url") and k in self.header and v:
                have = [u.strip() for u in self.header[k].split(",") if u.strip()]
                for u in (x.strip() for x in v.split(",")):
                    if u and u not in have:
                        have.append(u)                       # several guides: comma-separated list
                self.header[k] = ",".join(have)
            else:
                self.header.setdefault(k, v)
        remote = re.match(r"^https?://", source, re.I) is not None
        # the login of the playlist address belongs to the download, not to a Kodi |header suffix
        source_base = split_url_headers(source)[0] if remote else source
        for c in chans:
            if remote and is_local(c.url) and not re.match(r"^[a-zA-Z]:[\\/]", c.url):
                # relative to the address the playlist really came from; keep a login on the
                # same server (or an http -> https upgrade), never send it to another server
                c.url = with_login(urllib.parse.urljoin(base_url or source_base, c.url), source_base)
            self.uid_counter += 1
            c.uid = self.uid_counter
            self._apply_remembered(c)
            self.channels.append(c)
            self.by_uid[c.uid] = c
            self._source_index(c.source)
            if c.group not in self.group_enabled:
                self.group_enabled[c.group] = self._initial_group_state(c.group)
                self.group_order.append(c.group)
        return len(chans)

    def _apply_remembered(self, c: Channel) -> bool:
        """Show the result of the last check of this stream (an earlier session), if there is one."""
        if not self.v_remember_results.get() or c.status != UNCHECKED:
            return False
        ua = self.v_ua.get().strip()
        e = self._results.get(c.result_key(ua))
        if not e:
            return False
        c.status, c.info, c.latency, c.quality, c.checked_at = e[0], e[1], e[2], e[3], float(e[4])
        c.checked_ua = ua
        c.remembered = True
        self._restored_results.append(c.checked_at)
        return True

    def _result_key(self, c: Channel) -> str:
        """Key of c's remembered result, with the Settings User-Agent its check really used
        (Settings -> User-Agent may have been changed since)."""
        return c.result_key(self.v_ua.get() if c.checked_ua is None else c.checked_ua)

    def _store_results(self):
        """Remember the results found in this session (Settings -> Remember check results)."""
        if not self.v_remember_results.get():
            return
        changed = False
        for c in self.channels:
            if (c.status in FINAL_STATUSES and c.checked_at and not c.remembered
                    and c.checked_at > self._results_forgotten_at):
                entry = [c.status, c.info[:300], c.latency, c.quality, round(c.checked_at)]
                key = self._result_key(c)
                if self._results.get(key) != entry:
                    self._results[key] = entry
                    changed = True
        if changed:
            save_results(self._results)

    def on_remember_results(self):
        if self.v_remember_results.get():
            self._results = load_results()
            self._store_results()
            self.set_status("Check results will be remembered and shown again when you open the same streams.")
        else:
            self.set_status("Check results are no longer remembered (the ones already stored are kept – "
                            "Settings → Forget remembered check results deletes them).")
        self.save_settings()

    def forget_results(self):
        n = len(self._results) or len(load_results())
        if not n:
            messagebox.showinfo(APP_TITLE, "No check results are remembered.", parent=self)
            return
        if not messagebox.askyesno(APP_TITLE, f"Forget the remembered results of {n} streams?\n\n"
                                              "Channels in the list that show a remembered result "
                                              "(in italics) become “not checked”. Results found in "
                                              "this session stay in the list but are not remembered; "
                                              "only checks made from now on are.", parent=self):
            return
        self._results = {}
        self._results_forgotten_at = time.time()
        failed = ""
        try:
            RESULTS_FILE.unlink()
        except FileNotFoundError:
            pass
        except OSError as e:
            failed = " (the results file could not be deleted)"
            messagebox.showwarning(
                APP_TITLE, f"Could not delete the remembered results file:\n{RESULTS_FILE}\n\n{e}\n\n"
                           "The current list is cleared, but the old file may be loaded again next time.",
                parent=self)
        for c in self.channels:
            if c.remembered:
                c.status, c.info, c.latency, c.quality, c.checked_at = UNCHECKED, "", None, None, 0.0
                c.remembered, c.prev_status, c.checked_ua = False, None, None
        self.recompute_duplicates()
        self.refresh_all()
        self.set_status(f"Forgot the remembered results of {n} streams{failed}.")

    def after_load(self, added: int, check_also: int = 0, defer_check: bool = False):
        """added: new channels. check_also: channels added (and reported) earlier that still wait for
        the automatic check. defer_check: more channels are coming - check them all together later."""
        reset = added > 0 and self._reset_view_filters()
        new = added + check_also
        restored_g, restored_p = len(self._restored_groups), len(self._restored_sources)
        self._restored_groups.clear()
        self._restored_sources.clear()
        self.recompute_duplicates()
        self.refresh_all()
        if new > 0 and self.checking:
            self._pending_check = True       # checked as soon as the running check ends
        elif new > 0 and self.v_auto_check.get() and not self.downloading and not defer_check:
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
        if restored_g or restored_p:
            parts = ([f"{restored_g} group{'s' if restored_g != 1 else ''}"] if restored_g else []) + \
                    ([f"{restored_p} playlist{'s' if restored_p != 1 else ''}"] if restored_p else [])
            text += f" {' and '.join(parts)} unticked as you left them last time."
        if self._restored_results:
            n, newest = len(self._restored_results), max(self._restored_results)
            text += (f" Last results shown for {n} channel{'s' if n != 1 else ''} (in italics, newest "
                     f"{age_text(time.time() - newest)}).")
            self._restored_results.clear()
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

    @staticmethod
    def _not_checked_now(c: Channel) -> bool:
        """Not checked in this session (a remembered result from an earlier one does not count)."""
        return c.status == UNCHECKED or c.remembered

    def _auto_check(self):
        if self.checking or self.downloading:
            return
        new = [c for c in self.channels if self._not_checked_now(c) and self._included(c)]
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
        targets = [c for c in self.channels if c.status in (OFFLINE, BLOCKED) and self._included(c)]
        if not targets:
            messagebox.showinfo(APP_TITLE, "There are no offline channels to recheck.\n"
                                           "Run “Check streams” first.", parent=self)
            return
        self.start_check(targets, recheck=True)

    def check_visible(self):
        self.start_check([self.by_uid[int(i)] for i in self.tree.get_children()])

    def check_selected(self):
        self.start_check([self.by_uid[int(i)] for i in self.tree.selection()])

    def start_check(self, targets: list[Channel], recheck: bool = False, pictures_only: bool = False):
        if self.checking:
            return
        if not targets:
            messagebox.showinfo(APP_TITLE, "There are no channels to check.", parent=self)
            return
        self.save_settings()
        timeout = min(max(self._int(self.v_timeout, 8), 1), 120) * (2 if recheck else 1)
        threads = min(max(self._int(self.v_threads, 20), 1), 200)
        self.ffmpeg = self.ffmpeg or find_ffmpeg()
        black = self.v_black.get() and bool(self.ffmpeg)
        self._banner_pics = self.v_geo_picture.get() or pictures_only
        pictures = (self._banner_pics or black) and bool(self.ffmpeg)
        checker = StreamChecker(timeout, self.v_ua.get().strip(), self.v_deep.get(), self.v_ssl.get(),
                                self.v_geo_server.get(), self.v_geo_loop.get(), self.ffmpeg if pictures else None)
        self._checker = checker
        self._check_ua = checker.ua           # results are remembered with the User-Agent they were found with
        jobs = []
        self._recheck = {c.uid for c in targets} if recheck else None
        self._previous = {c.uid: (c.status, c.info, c.latency) for c in targets}  # restored if stopped
        for c in targets:
            if not pictures_only:
                # what this channel was before, to show "was online 2 days ago" if it changes
                if c.status in FINAL_STATUSES and c.checked_at:
                    c.prev_status, c.prev_time = c.status, c.checked_at
                else:
                    c.prev_status = None
                c.status, c.info, c.latency = CHECKING, "", None
                c.seg_hash = None
                c.audio = False
            c.pic_hash, c.pic_spread, c.pic_gray = None, 0.0, 0.0   # never judge by an old picture
            c.pic_motion, c.pic_colors = None, None
            ua, ref = c.http_options()
            jobs.append((c.uid, c.url, c.base_dir, ua, ref))
        self.stop_event.clear()
        self.checking = True
        self._pictures_only = pictures_only
        self.pic_total = self.pic_done = 0
        self._pic_phase = pictures_only
        self._pic_phase_start = time.monotonic()
        self._thumbs.clear()
        self.check_total, self.check_done = (0 if pictures_only else len(jobs)), 0
        self.progress.stop()
        self.progress.configure(mode="determinate", maximum=max(len(jobs), 1), value=0)
        self.btn_check.state(["disabled"])
        self.btn_recheck.state(["disabled"])
        self.btn_stop.state(["!disabled"])
        self.refresh_channels()
        self.set_status(self._progress_text())
        self._retrying = 0
        self._retry_result = None
        retry = self.v_retry.get() and not pictures_only
        threading.Thread(target=self._check_worker,
                         args=(checker, jobs, threads, pictures, pictures_only, retry, black),
                         daemon=True).start()

    def _check_worker(self, checker: StreamChecker, jobs, threads, pictures: bool, pictures_only: bool,
                      retry: bool = False, black_check: bool = False):
        stop = self.stop_event
        by_uid = {j[0]: j for j in jobs}

        def task(job, chk=checker):
            uid, url, base, ua, ref = job
            if stop.is_set():
                return uid, None
            return uid, chk.check_full(url, base, ua, ref)

        pic_src: dict[int, tuple] = {}            # uid -> (address for ffmpeg, is HLS)
        pic_same: dict[str, list] = {}            # same address -> all channels using it

        def pic_task(uid):
            _, _, _, ua, ref = by_uid[uid]
            url, hls = pic_src[uid]
            if stop.is_set():
                return uid, None, False, None
            pic = checker.grab_picture(url, ua, ref, hls)
            vq = checker.video_quality()
            black = False
            # black and still can also be a fade-out or a dark scene: look again a bit later
            if black_check and looks_black(pic) and not stop.wait(STILL_CHECK_GAP):
                black = still_black(pic, checker.grab_picture(url, ua, ref, hls))
            return uid, pic, black, vq

        def wants_picture(uid, res) -> bool:
            if not pictures or res is None or res[0] != ONLINE or res[3].get("audio"):
                return False
            url = by_uid[uid][1]
            return url.lower().startswith(("http://", "https://", "rtmp", "rtsp")) \
                and not AUDIO_URL_RE.search(url)

        pic_ex = ThreadPoolExecutor(max_workers=min(16, max(4, threads // 2))) if pictures else None
        pic_futs: set = set()

        pic_finished: dict[str, tuple] = {}      # address -> (picture, black screen, video quality)

        def queue_picture(uid, extra=None):
            extra = extra or {}
            src = (extra.get("pic_url") or by_uid[uid][1], bool(extra.get("pic_hls")))
            key = norm_url(src[0])
            self.q.put(("pic_queued",))
            if key in pic_finished:              # same stream, its picture is already there
                self.q.put(("picture", uid, *pic_finished[key]))
                return
            if key in pic_same:                  # same stream as a channel already queued
                pic_same[key].append(uid)
                return
            pic_same[key] = [uid]
            pic_src[uid] = src
            pic_futs.add(pic_ex.submit(pic_task, uid))

        def flush_pictures(block: bool):
            nonlocal pic_futs
            if not pic_futs:
                return
            if block:
                done, pic_futs = wait(pic_futs, timeout=0.25, return_when=FIRST_COMPLETED)
            else:
                done = {f for f in pic_futs if f.done()}
                pic_futs -= done
            for f in done:
                try:
                    uid, pic, black, vq = f.result()
                except Exception:
                    continue
                key = norm_url(pic_src[uid][0])
                pic_finished[key] = (pic, black, vq)
                for same_uid in pic_same.get(key, [uid]):
                    self.q.put(("picture", same_uid, pic, black, vq))

        def post(uid, res):
            self.q.put(("result", uid, res))
            if wants_picture(uid, res):
                queue_picture(uid, res[3])

        def run(executor, job_list, chk, on_result):
            pending = {executor.submit(task, j, chk) for j in job_list}
            while pending and not stop.is_set():  # short waits so "Stop" reacts at once
                done, pending = wait(pending, timeout=0.25, return_when=FIRST_COMPLETED)
                for f in done:
                    try:
                        uid, res = f.result()
                    except Exception:
                        continue
                    on_result(uid, res)
                flush_pictures(block=False)

        # offline because of a temporary server problem (timeout, HTTP 502/503/504 ...): held back
        # and checked once more at the end, slower and with a longer time limit
        held: dict[int, tuple] = {}

        def first_try(uid, res):
            if retry and res is not None and res[0] == OFFLINE and TEMP_ERROR_RE.search(res[1] or ""):
                held[uid] = res
            else:
                post(uid, res)

        recovered = 0

        def second_try(uid, res):
            nonlocal recovered
            first = held.pop(uid)
            if res is None:
                post(uid, first)
                return
            status, info, ms, extra = res
            if status == OFFLINE:
                info = f"{info} (2 tries)" if info == first[1] else f"{info} (2 tries; 1st: {first[1]})"
            else:
                recovered += status == ONLINE
                info = f"{info} · on the 2nd try (1st: {first[1]})"
            post(uid, (status, info, ms, extra))

        ex = ThreadPoolExecutor(max_workers=threads)
        rex = None
        try:
            if pictures_only:
                for j in jobs:
                    queue_picture(j[0])
            else:
                run(ex, jobs, checker, first_try)
                if held and not stop.is_set():
                    total = len(held)
                    self.q.put(("retrying", total))
                    stop.wait(RETRY_PAUSE)
                    slow = copy.copy(checker)            # same settings, shares the ffmpeg process list
                    slow.timeout = min(checker.timeout * 2, 120)
                    rex = ThreadPoolExecutor(max_workers=min(RETRY_THREADS, threads))
                    run(rex, [by_uid[u] for u in list(held)], slow, second_try)
                    if not stop.is_set():
                        self.q.put(("retried", recovered, total))
            while pic_futs and not stop.is_set():
                flush_pictures(block=True)
        finally:
            for uid, res in list(held.items()):  # stopped before the 2nd try: keep the 1st result
                self.q.put(("result", uid, res))
            if stop.is_set():
                checker.kill_all()
            ex.shutdown(wait=False, cancel_futures=True)
            if rex:
                rex.shutdown(wait=False, cancel_futures=True)
            if pic_ex:
                pic_ex.shutdown(wait=False, cancel_futures=True)
            self.q.put(("done", stop.is_set()))

    def stop_check(self):
        if self.downloading:
            self._dl_stop.set()
            self.set_status("Stopping the downloads…")
        if self.checking:
            self.stop_event.set()
            if getattr(self, "_checker", None):
                self._checker.kill_all()
            self.set_status("Skipping the rest of the picture check…" if self._pic_phase else "Stopping…")

    def _check_finished(self, stopped: bool):
        for c in self.channels:
            if c.status == CHECKING:  # stopped before this one was checked: keep its old result
                c.status, c.info, c.latency = self._previous.get(c.uid, (UNCHECKED, "", None))
        self._manual_locked.clear()
        self.checking = False
        pic_skipped = stopped and self._pic_phase and not self._pictures_only
        if pic_skipped:
            stopped = False        # every stream was checked - only the picture check was skipped
        self.btn_stop.configure(text="■  Stop")
        self.btn_check.state(["!disabled"])
        self.btn_recheck.state(["!disabled"])
        if not self.downloading:
            self.btn_stop.state(["disabled"])
            self.progress["value"] = self.check_done
        else:                                   # the download owns the bar again
            d = self._dl
            self.progress.stop()
            if d.get("single"):
                self.progress.configure(mode="indeterminate")
                self.progress.start(12)
            else:
                self.progress.configure(mode="determinate", maximum=max(int(d.get("total", 1)), 1),
                                        value=int(d.get("done", 0)))
        self.recompute_duplicates()
        self.refresh_all()
        self._store_results()
        # keep what happened during this check, so the statistics can be rebuilt after the
        # same-picture question marks more channels as geo-blocked
        self._finish_stopped = stopped
        self._finish_pic_skipped = pic_skipped
        self._finish_rechecked = ([uid for uid in self._recheck if uid in self.by_uid]
                                  if self._recheck is not None else None)
        self._finish_retry = self._retry_result
        self._recheck = None
        self._retrying, self._retry_result = 0, None
        text = self._result_text()
        self._finish_text = text
        self.set_status(text)
        pictures_taken = bool(self._thumbs)
        self._pictures_only = False
        self._pic_phase = False
        if pictures_taken and not stopped and self.v_geo_ask.get():
            self.after(300, self._ask_same_picture)
        else:
            self._thumbs.clear()
        if self._pending_check and not stopped:
            self._pending_check = False
            if any(self._not_checked_now(c) and self._included(c) for c in self.channels):
                self.after(400, self._check_added)
                return
        self._pending_check = False
        if not stopped:
            self.bell()

    def _result_text(self) -> str:
        """Statistics of the current playlist after a check, plus what happened in the check.
        Rebuilt when the same-picture question marks more channels, so the counts stay right."""
        on = sum(c.status == ONLINE for c in self.channels)
        off = sum(c.status == OFFLINE for c in self.channels)
        dups = sum(1 for c in self.channels if c.dup_of)
        blk = sum(c.status == BLOCKED for c in self.channels)
        dark = sum(c.status == OFFLINE and c.info.startswith("black screen") for c in self.channels)
        rechecked = getattr(self, "_finish_rechecked", None)
        if rechecked is not None:
            back = sum(1 for uid in rechecked if self.by_uid[uid].status == ONLINE)
            still_off = sum(1 for uid in rechecked if self.by_uid[uid].status == OFFLINE)
            still_blk = sum(1 for uid in rechecked if self.by_uid[uid].status == BLOCKED)
            return (f"Recheck {'stopped' if self._finish_stopped else 'finished'}: {back} of "
                    f"{len(rechecked)} offline / blocked channels are back online · still offline: "
                    f"{still_off} · geo-blocked: {still_blk}.")
        text = (f"{'Stopped' if self._finish_stopped else 'Check finished'}: {on} online · {off} offline"
                f"{f' ({dark} black screen)' if dark else ''} · "
                f"{blk} geo-blocked · {dups} duplicates · {len(self.channels)} channels total.")
        if self.pic_total:
            text += (f" Picture check skipped after {self.pic_done} of {self.pic_total}."
                     if self._finish_pic_skipped else f" Pictures checked: {self.pic_done}.")
        skipped = sum(1 for c in self.channels if not self._included(c))
        if skipped:
            text += f" {skipped} in unticked groups / playlists are not included."
        if self._finish_retry:
            back, tried = self._finish_retry
            text += f" {back} of {tried} channels with a temporary error worked on the 2nd try."
        changed = sum(1 for c in self.channels if c.changed)
        if changed:
            text += f" {changed} changed since the last check (bold – Show → “{SHOW_CHANGED}”)."
        return text

    # ------------------------------------------------------------------ geo-blocked channels
    def _learned(self) -> dict:
        if not isinstance(self.settings.get("geo_learned"), dict):
            self.settings["geo_learned"] = {}
        d = self.settings["geo_learned"]
        for k in ("pics", "segs", "rejected"):
            if not isinstance(d.get(k), list):
                d[k] = []

        def ok(e):     # [fingerprint, brightness, (name), (colour layout)] - skip damaged entries
            return isinstance(e, list) and len(e) >= 2 and isinstance(e[0], int) and isinstance(e[1], (int, float))
        d["pics"] = [e for e in d["pics"] if ok(e)]
        d["rejected"] = [e for e in d["rejected"] if ok(e)]
        d["segs"] = [e for e in d["segs"] if isinstance(e, str)]
        return d

    @staticmethod
    def _entry_colors(e):
        col = next((x for x in e[2:] if isinstance(x, list)), None)
        return col if col and all(isinstance(v, int) for v in col) else None

    def _entry_close(self, c: Channel, e) -> bool:
        return pic_close(c.pic_hash, c.pic_gray, e[0], e[1], c.pic_colors, self._entry_colors(e))

    def _apply_learned(self, c: Channel) -> bool:
        """Mark a working channel as geo-blocked if it shows a banner the user taught us."""
        if c.status != ONLINE:
            return False
        d = self._learned()
        if c.seg_hash and c.seg_hash in d["segs"]:
            c.status, c.info = BLOCKED, "same 'not available' video as a channel you marked"
            c.checked_at, c.remembered, c.quality = time.time(), False, None
            return True
        # a banner can have a small animation (a blinking "live" dot, a moving logo): the
        # fingerprint and colours still match, so do not reject it just because it moves a little
        if c.pic_hash is not None and c.pic_spread >= PIC_MIN_SPREAD and \
                (c.pic_motion is None or c.pic_motion <= LEARNED_MOVING):
            for e in d["pics"]:
                if self._entry_close(c, e):
                    name = e[2] if len(e) > 2 and isinstance(e[2], str) else "?"
                    c.status, c.info = BLOCKED, f"shows the 'not available' banner (like “{name}”)"
                    c.checked_at, c.remembered, c.quality = time.time(), False, None
                    return True
        return False

    def _learn(self, c: Channel) -> bool:
        d = self._learned()
        learned = False
        if c.pic_hash is not None and c.pic_spread >= PIC_MIN_SPREAD:
            d["rejected"] = [r for r in d["rejected"] if not self._entry_close(c, r)]
            if not any(self._entry_close(c, e) for e in d["pics"]):
                d["pics"].append([c.pic_hash, round(c.pic_gray, 1), c.name[:60]] +
                                 ([c.pic_colors] if c.pic_colors else []))
                d["pics"] = d["pics"][-300:]
            learned = True
        if c.seg_hash:
            if c.seg_hash not in d["segs"]:
                d["segs"] = (d["segs"] + [c.seg_hash])[-300:]
            learned = True
        return learned

    def _apply_learned_to_all(self) -> int:
        n = sum(1 for c in self.channels if self._apply_learned(c))
        if n:
            self.recompute_duplicates()
        self.refresh_all()
        return n

    def mark_blocked(self):
        sel = self._selected_channels()
        if not sel:
            return
        need_picture = []
        for c in sel:
            c.status, c.info = BLOCKED, "marked by you: 'not available in this country'"
            c.checked_at, c.remembered, c.quality = time.time(), False, None
            c.checked_ua = self.v_ua.get().strip() or DEFAULT_UA   # remember it with the UA in use now
            if self.checking:                 # the running check must not overwrite this mark
                self._manual_locked.add(c.uid)
            if not self._learn(c):
                need_picture.append(c)
        self.save_settings()
        others = self._apply_learned_to_all()
        self._store_results()                 # the new “geo-blocked” results are remembered at once
        msg = f"Marked {len(sel)} channel(s) as geo-blocked."
        if others:
            msg += f" {others} other channel(s) show the same banner and were marked too."
        self.set_status(msg)
        if need_picture:
            self.ffmpeg = self.ffmpeg or find_ffmpeg()
            if not self.ffmpeg:
                messagebox.showinfo(APP_TITLE, "To recognise this banner on other channels the program needs "
                                    "ffmpeg.\n\nInstall it with:\n    sudo apt install ffmpeg\n\n"
                                    "The marked channel(s) will be left out when saving.", parent=self)
                return
            self.set_status(msg + " Learning the banner picture…")
            checker = StreamChecker(max(self._int(self.v_timeout, 8), 5), self.v_ua.get().strip(), True,
                                    self.v_ssl.get(), ffmpeg=self.ffmpeg)
            self._aux_checkers.add(checker)

            def work(chans=need_picture):
                try:
                    for c in chans:
                        ua, ref = c.http_options()
                        self.q.put(("learn_pic", c.uid, checker.grab_picture(c.url, ua, ref)))
                finally:
                    self._aux_checkers.discard(checker)
            threading.Thread(target=work, daemon=True).start()

    def _learn_picture_result(self, uid, pic):
        c = self.by_uid.get(uid)
        if c is None:
            return
        if pic is None or pic[1] < PIC_MIN_SPREAD:
            self.set_status(f"Could not take a usable picture from “{c.name}” – only this channel is marked.")
            return
        c.pic_hash, c.pic_spread, c.pic_gray, _ = pic[:4]
        c.pic_motion, c.pic_colors = picture_extras(pic)
        self._learn(c)
        self.save_settings()
        n = self._apply_learned_to_all()
        self._store_results()             # the channels marked from the learned picture are remembered
        self.set_status(f"Learned the banner of “{c.name}”." +
                        (f" {n} other channel(s) show it and were marked as geo-blocked." if n else
                         " Channels showing it will be marked as geo-blocked in the next checks."))

    def unmark_blocked(self):
        sel = [c for c in self._selected_channels() if c.status == BLOCKED]
        if not sel:
            self.set_status("Select geo-blocked channels first.")
            return
        d = self._learned()
        for c in sel:
            if c.pic_hash is not None:
                d["pics"] = [p for p in d["pics"] if not self._entry_close(c, p)]
                if c.pic_spread >= PIC_MIN_SPREAD:
                    d["rejected"] = (d["rejected"] + [[c.pic_hash, round(c.pic_gray, 1)] +
                                                      ([c.pic_colors] if c.pic_colors else [])])[-300:]
            if c.seg_hash in d["segs"]:
                d["segs"].remove(c.seg_hash)
            c.status, c.info, c.latency, c.quality, c.checked_at = UNCHECKED, "", None, None, 0.0
            c.remembered = False
            if self.checking:                 # the running check must not overwrite this change
                self._manual_locked.add(c.uid)
        self._forget_saved_results(sel)
        for c in sel:                         # the old UA must not be used for a later result
            c.checked_ua = None
        self.save_settings()
        self.refresh_all()
        if not self.checking:
            self.start_check(sel)

    def _forget_saved_results(self, chans: list[Channel]):
        """Drop the remembered results of these channels (the user unmarked them as geo-blocked)."""
        results = self._results if self.v_remember_results.get() else load_results()
        removed = False
        for c in chans:
            removed = results.pop(self._result_key(c), None) is not None or removed
        if removed:
            save_results(results)

    def forget_banners(self):
        d = self._learned()
        n = len(d["pics"]) + len(d["segs"])
        if not messagebox.askyesno(APP_TITLE, f"Forget the {n} learned 'not available' banners?\n"
                                              "Channels already marked keep their status until the next check.",
                                   parent=self):
            return
        d["pics"], d["segs"], d["rejected"] = [], [], []
        self.save_settings()
        self.set_status("Learned banners forgotten.")

    def on_picture_option(self):
        if self.v_geo_picture.get() and not (self.ffmpeg or find_ffmpeg()):
            self.v_geo_picture.set(False)
            messagebox.showinfo(APP_TITLE, "The picture check needs ffmpeg.\n\nInstall it with:\n"
                                "    sudo apt install ffmpeg\n\nthen switch this option on again.", parent=self)
        self.ffmpeg = self.ffmpeg or find_ffmpeg()
        self.save_settings()

    def on_black_option(self):
        if self.v_black.get() and not (self.ffmpeg or find_ffmpeg()):
            self.v_black.set(False)
            messagebox.showinfo(APP_TITLE, "The black screen check needs ffmpeg.\n\nInstall it with:\n"
                                "    sudo apt install ffmpeg\n\nthen switch this option on again.", parent=self)
        self.ffmpeg = self.ffmpeg or find_ffmpeg()
        self.save_settings()

    def find_banners(self):
        self.ffmpeg = self.ffmpeg or find_ffmpeg()
        if not self.ffmpeg:
            messagebox.showinfo(APP_TITLE, "The picture check needs ffmpeg.\n\nInstall it with:\n"
                                "    sudo apt install ffmpeg", parent=self)
            return
        targets = [c for c in self.channels if c.status == ONLINE and self._included(c)
                   and not c.audio and not (c.quality or {}).get("audio")
                   and not AUDIO_URL_RE.search(c.url)
                   and c.url.lower().startswith(("http://", "https://", "rtmp", "rtsp"))]
        if not targets:
            messagebox.showinfo(APP_TITLE, "There are no online video channels to check – radio / audio "
                                "channels are skipped.\nRun “Check streams” first.", parent=self)
            return
        self.start_check(targets, pictures_only=True)

    def remove_blocked(self):
        blk = [c for c in self.channels if c.status == BLOCKED]
        if not blk:
            messagebox.showinfo(APP_TITLE, "No geo-blocked channels.", parent=self)
            return
        if messagebox.askyesno(APP_TITLE, f"Remove {len(blk)} geo-blocked channels from the list?", parent=self):
            with self._undoable(f"Remove {len(blk)} geo-blocked channels"):
                self._remove(blk)
            self.set_status(f"Removed {len(blk)} geo-blocked channels.")

    def _same_picture_groups(self):
        d = self._learned()
        # a moving picture is live TV - only still pictures can be a banner
        cands = [c for c in self.channels if c.status == ONLINE and c.pic_hash is not None
                 and c.pic_spread >= PIC_MIN_SPREAD and not is_moving(c) and self._included(c)]
        clusters = []  # [hash, gray, members]
        for c in cands:
            for cl in clusters:
                first = cl[2][0]
                if pic_close(c.pic_hash, c.pic_gray, cl[0], cl[1], c.pic_colors, first.pic_colors):
                    cl[2].append(c)
                    break
            else:
                clusters.append([c.pic_hash, c.pic_gray, [c]])
        groups = []
        for h, g, members in clusters:
            if count_distinct_channels(members) >= SAME_PICTURE_MIN and \
                    not any(self._entry_close(members[0], r) for r in d["rejected"]):
                groups.append((h, g, members))
        groups.sort(key=lambda x: -len(x[2]))
        return groups[:6]

    def _ask_same_picture(self):
        """Several channels show the same picture. A 'not available' banner is a still image, so
        first take a second picture: if it has changed, it is the same live TV programme
        (e.g. one channel from several playlists under different names), not a banner."""
        groups = self._same_picture_groups()
        if not groups:
            self._thumbs.clear()
            return
        self.ffmpeg = self.ffmpeg or find_ffmpeg()
        if not self.ffmpeg:
            self._show_same_picture([(h, g, ms, None) for h, g, ms in groups], 0)
            return
        self.set_status(getattr(self, "_finish_text", "") + "   Same picture on several channels – "
                        "checking whether it is a still banner or live TV …")
        checker = StreamChecker(max(self._int(self.v_timeout, 8), 5), self.v_ua.get().strip(), True,
                                self.v_ssl.get(), ffmpeg=self.ffmpeg)
        self._aux_checkers.add(checker)
        plan = []
        for h, g, members in groups:
            picks, ids = [], set()
            for m in members:                     # two members that are different channels
                ident = channel_identity(m)
                if not ids & {("n", ident[0]), ("i", ident[1])} - {("n", ""), ("i", "")}:
                    picks.append(m)
                    ids |= {("n", ident[0]), ("i", ident[1])}
                if len(picks) == 2:
                    break
            jobs = []
            for m in picks:
                ua, ref = m.http_options()
                url, hls = m.pic_src or (m.url, False)
                jobs.append((url, ua, ref, hls))
            plan.append((h, g, members, jobs, max(m.pic_time for m in members)))

        def work():
            kept, live = [], 0
            try:
                with ThreadPoolExecutor(max_workers=6) as ex:
                    for h, g, members, jobs, taken in plan:
                        wait_s = STILL_CHECK_GAP - (time.monotonic() - taken)
                        if wait_s > 0:             # live TV needs a moment to show something else
                            time.sleep(min(wait_s, STILL_CHECK_GAP))
                        # a sharp picture for the question, taken while the still test runs
                        preview = ex.submit(checker.grab_preview, *jobs[0]) if jobs else None
                        pics = list(ex.map(lambda j: checker.grab_picture(*j), jobs))
                        cols = members[0].pic_colors
                        moved = any(p is not None and p[1] >= PIC_MIN_SPREAD and
                                    ((picture_extras(p)[0] or 0) > PIC_MOVING or
                                     not pic_close(p[0], p[2], h, g, picture_extras(p)[1], cols))
                                    for p in pics)
                        if moved:
                            live += 1
                        else:
                            try:
                                big = preview.result() if preview else None
                            except Exception:
                                big = None
                            kept.append((h, g, members, big))
                self.q.put(("same_pic_ready", kept, live))
            finally:
                self._aux_checkers.discard(checker)
        threading.Thread(target=work, daemon=True).start()

    def _show_same_picture(self, groups, live: int):
        if live:
            self.set_status(getattr(self, "_finish_text", "") +
                            f"   {live} group(s) of channels showed the same picture, but it changed a few "
                            "seconds later – the same live programme, not a banner.")
        if self.checking:                 # a new check started meanwhile: it asks again when it ends
            return
        if not live:
            self.set_status(getattr(self, "_finish_text", ""))
        groups = [(h, g, ms, big) for h, g, ms, big in
                  ((h, g, [m for m in members if m.status == ONLINE and m.uid in self.by_uid], big)
                   for h, g, members, big in groups)
                  if count_distinct_channels(ms) >= SAME_PICTURE_MIN]
        if not groups:
            self._thumbs.clear()
            return
        try:
            marked = 0
            for h, g, members, big in groups:
                thumb = next((self._thumbs[m.uid] for m in members if m.uid in self._thumbs), None)
                answer = SamePictureDialog(self, members, thumb, count_distinct_channels(members),
                                           preview=big).result
                d = self._learned()
                first = members[0]
                cols = [first.pic_colors] if first.pic_colors else []
                if answer == "block":
                    for m in members:
                        m.status, m.info = BLOCKED, "same picture as other channels ('not available' banner)"
                        m.checked_at, m.remembered, m.quality = time.time(), False, None
                        m.checked_ua = getattr(self, "_check_ua", None) or m.checked_ua
                    # the same picture can't be "a banner" and "not a banner" at the same time
                    d["rejected"] = [r for r in d["rejected"] if not self._entry_close(first, r)]
                    d["pics"] = (d["pics"] + [[h, round(g, 1), first.name[:60]] + cols])[-300:]
                    marked += len(members)
                elif answer == "not":
                    d["pics"] = [p for p in d["pics"] if not self._entry_close(first, p)]
                    d["rejected"] = (d["rejected"] + [[h, round(g, 1)] + cols])[-300:]
            if groups:
                self.save_settings()
                marked += self._apply_learned_to_all()
                self._store_results()             # the dialog's “geo-blocked” answers are remembered
                if marked:
                    # keep the full playlist statistics in the status bar; the counts changed
                    # because the channels above were just marked as geo-blocked
                    self._finish_text = self._result_text()
                    live_note = (f"   {live} group(s) of channels showed the same picture, but it "
                                 "changed a few seconds later – the same live programme, not a banner."
                                 if live else "")
                    self.set_status(f"{self._finish_text}{live_note}   {marked} channels marked as "
                                    "geo-blocked – they are left out when saving.")
        finally:
            self._thumbs.clear()

    def _check_added(self):
        """Continue with the playlists that were opened while the previous check was running."""
        targets = [c for c in self.channels if self._not_checked_now(c) and self._included(c)]
        if targets and not self.checking:
            self.start_check(targets)
            self.set_status(f"Checking {len(targets)} channels added during the previous check …")

    def _progress_text(self) -> str:
        skipped = sum(1 for c in self.channels if not self._included(c))
        note = f"   ·   {skipped} unticked skipped" if skipped else ""
        return self._progress_core() + note

    def _time_left(self) -> str:
        done = self.pic_done - getattr(self, "_pic_phase_done0", 0)
        elapsed = time.monotonic() - self._pic_phase_start
        if done < 5 or elapsed < 3:
            return ""
        left = (self.pic_total - self.pic_done) * elapsed / done
        return f" · about {max(1, round(left / 60))} min left" if left >= 60 else f" · about {int(left) + 1} s left"

    def _progress_core(self) -> str:
        on = sum(c.status == ONLINE for c in self.channels)
        off = sum(c.status == OFFLINE for c in self.channels)
        blk = sum(c.status == BLOCKED for c in self.channels)
        if self._pic_phase:
            head = "" if self._pictures_only else f"Streams done ✓ ({on} online · {off} offline)   ·   "
            what = ("“not available” banners and black screens" if self._banner_pics and self.v_black.get()
                    else "“not available” banners" if self._banner_pics else "black screens")
            return (f"{head}Looking for {what}: picture {self.pic_done} / {self.pic_total}"
                    f"{self._time_left()} · geo-blocked {blk}   –   “Skip pictures” keeps all results")
        pics = f"   ·   pictures {self.pic_done} / {self.pic_total}" if self.pic_total else ""
        if self._retrying:
            left = self.check_total - self.check_done
            return (f"Trying again: {left} of {self._retrying} channels with a temporary error "
                    f"(timeout, HTTP 5xx) left   ·   online {on}   ·   offline {off}{pics}")
        return (f"Checking {self.check_done} / {self.check_total}   ·   online {on}   ·   offline {off}"
                f"   ·   geo-blocked {blk}{pics}")

    def _poll(self):
        updated = False
        try:
            for _ in range(2000):
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "result":
                    c = self.by_uid.get(msg[1])
                    # a channel marked by the user during this check keeps that status
                    if c is not None and msg[2] is not None and c.uid not in self._manual_locked:
                        c.status, c.info, c.latency, extra = msg[2]
                        c.checked_at, c.remembered = time.time(), False
                        c.checked_ua = getattr(self, "_check_ua", None)
                        c.seg_hash = extra.get("seg_hash")
                        c.audio = bool(extra.get("audio"))
                        c.pic_src = (extra["pic_url"], bool(extra.get("pic_hls"))) if extra.get("pic_url") \
                            else None
                        # quality of a working stream only (a banner's resolution means nothing);
                        # a picture taken later fills it in for streams the server did not describe
                        c.quality = extra.get("quality") if c.status == ONLINE else None
                        self._apply_learned(c)
                        self._update_row(c)
                    self.check_done += 1
                    updated = True
                elif kind == "retrying":
                    self._retrying = msg[1]
                    updated = True
                elif kind == "retried":
                    self._retrying = 0
                    self._retry_result = (msg[1], msg[2])
                    updated = True
                elif kind == "pic_queued":
                    self.pic_total += 1
                    updated = True
                elif kind == "picture":
                    c = self.by_uid.get(msg[1])
                    black = len(msg) > 3 and msg[3]
                    vq = msg[4] if len(msg) > 4 else None
                    if c is not None and vq and c.status == ONLINE \
                            and not (c.quality or {}).get("h") and not (c.quality or {}).get("audio"):
                        # an HLS master playlist names its best quality (+ bitrate); ffmpeg opened the
                        # lowest one - so ffmpeg only fills in what the playlist did not say
                        q = c.quality or {}
                        several = q.get("src") == "hls" and q.get("variants", 1) > 1
                        c.quality = {**vq, "bw": q.get("bw", 0), "codec": q.get("codec") or vq["codec"],
                                     "fps": q.get("fps") or vq["fps"]}
                        if several:                  # the resolution ffmpeg saw is the lowest quality
                            c.quality.update(w=0, h=0)
                        self._update_row(c)
                    if c is not None and msg[2] is not None:
                        c.pic_hash, c.pic_spread, c.pic_gray, thumb = msg[2][:4]
                        c.pic_motion, c.pic_colors = picture_extras(msg[2])
                        c.pic_time = time.monotonic()
                        if black and c.status == ONLINE and c.uid not in self._manual_locked:
                            c.status, c.info = OFFLINE, (
                                "black screen – the stream works but shows no programme "
                                f"(black and still, again {STILL_CHECK_GAP} s later)")
                            c.checked_at, c.remembered = time.time(), False
                            c.checked_ua = getattr(self, "_check_ua", None) or c.checked_ua
                            c.quality = None
                        elif self._banner_pics:
                            if c.pic_spread >= PIC_MIN_SPREAD and not is_moving(c):
                                self._thumbs[c.uid] = thumb   # only a still picture can be a banner
                            if self._apply_learned(c):
                                c.checked_ua = getattr(self, "_check_ua", None) or c.checked_ua
                        self._update_row(c)
                    self.pic_done += 1
                    updated = True
                elif kind == "same_pic_ready":
                    self._show_same_picture(msg[1], msg[2])
                elif kind == "learn_pic":
                    self._learn_picture_result(msg[1], msg[2])
                elif kind == "done":
                    self._check_finished(msg[1])
                elif kind == "dl_item":
                    self._download_item(*msg[1:])
                elif kind == "dl_done":
                    self._download_finished(msg[1], msg[2])
        except queue.Empty:
            pass
        if updated and self.checking:
            if self.check_done >= self.check_total and self.pic_total > self.pic_done and not self._pic_phase:
                self._pic_phase = True                     # streams done, only pictures are left
                self._pic_phase_start = time.monotonic()
                self._pic_phase_done0 = self.pic_done
                self.btn_stop.configure(text="■  Skip pictures")
            if self.check_done >= self.check_total and self.pic_total:
                self.progress.configure(maximum=max(self.pic_total, 1), value=self.pic_done)
            else:
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

    # ------------------------------------------------------------------ undo / redo
    def _list_state(self) -> dict:
        """Copy of everything an edit can change (the channel objects themselves are copied shallowly:
        edits replace their name / group, they never change the tvg attributes in place)."""
        return {"channels": [copy.copy(c) for c in self.channels], "header": dict(self.header),
                "group_enabled": dict(self.group_enabled), "group_order": list(self.group_order),
                "source_enabled": dict(self.source_enabled), "source_color": dict(self.source_color),
                "current_group": self.current_group, "current_source": self.current_source,
                "counter": self.uid_counter}

    def _list_signature(self) -> tuple:
        return (tuple((c.uid, c.name, c.group) for c in self.channels), tuple(self.group_order),
                tuple(sorted(self.group_enabled.items())), tuple(sorted(self.source_enabled.items())))

    class _Undoable:
        """with self._undoable("Delete 3 channels"): ...  - remembers the list as it was, if it changes."""

        def __init__(self, app, label):
            self.app, self.label = app, label

        def __enter__(self):
            self.state = self.app._list_state()
            self.sig = self.app._list_signature()
            return self

        def __exit__(self, exc_type, *_):
            if exc_type is None and self.app._list_signature() != self.sig:
                self.state["label"] = self.label
                self.state["counter_after"] = self.app.uid_counter
                self.app._undo.append(self.state)
                self.app._redo.clear()
                self.app._trim_undo()
            return False

    def _undoable(self, label: str) -> "App._Undoable":
        return App._Undoable(self, label)

    def _trim_undo(self):
        while len(self._undo) > UNDO_MAX_STEPS or (
                len(self._undo) > 1 and sum(len(u["channels"]) for u in self._undo) > UNDO_MAX_CHANNELS):
            self._undo.pop(0)

    def undo(self):
        self._undo_redo(self._undo, self._redo, "Undone")

    def redo(self):
        self._undo_redo(self._redo, self._undo, "Redone")

    def _undo_redo(self, source: list, target: list, verb: str):
        if not source:
            self.set_status("Nothing to " + verb[:-2].lower() + ".")
            return
        entry = source.pop()
        now = self._list_state()
        now["label"], now["counter_after"] = entry["label"], self.uid_counter
        target.append(now)
        self._restore_list(entry)
        self.set_status(f"{verb}: {entry['label']}.")

    def _restore_list(self, st: dict):
        current = {c.uid: c for c in self.channels}
        restored = []
        for old in st["channels"]:
            c = copy.copy(old)
            cur = current.get(c.uid)
            if cur is not None:          # keep what a check found out since then
                for f in CHECK_FIELDS:
                    setattr(c, f, getattr(cur, f))
            elif c.status == CHECKING:   # removed while its check ran: that check was stopped
                c.status, c.info, c.latency = self._previous.get(c.uid, (UNCHECKED, "", None))
            restored.append(c)
        # channels loaded AFTER the change (playlist downloads, opened files) are not part of it: keep them
        later = [c for c in self.channels if c.uid > st["counter_after"]]
        self.channels = restored + later
        self.by_uid = {c.uid: c for c in self.channels}
        self.header = dict(st["header"]) if st["header"] or not later else self.header
        self.group_enabled, self.group_order = dict(st["group_enabled"]), list(st["group_order"])
        self.source_enabled, self.source_color = dict(st["source_enabled"]), dict(st["source_color"])
        for c in later:
            if c.group not in self.group_enabled:
                self.group_enabled[c.group] = self._initial_group_state(c.group)
                self.group_order.append(c.group)
            self._source_index(c.source)
        self.current_group = st["current_group"] if st["current_group"] in self.group_enabled else None
        self.current_source = st["current_source"] if st["current_source"] in self.source_enabled else None
        self._manual_locked &= set(self.by_uid)
        self._remember_ticks()
        self.recompute_duplicates()
        self.refresh_all()

    def _edit_menu_post(self, menu: tk.Menu):
        """Edit menu: 'Undo delete 3 channels' / 'Redo …', greyed out when there is nothing."""
        for i, stack, word in ((0, self._undo, "Undo"), (1, self._redo, "Redo")):
            label = word + (" " + stack[-1]["label"][:1].lower() + stack[-1]["label"][1:] if stack else "")
            menu.entryconfigure(i, label=label, state="normal" if stack else "disabled")

    def _debounced_refresh(self):
        if self._search_job:
            self.after_cancel(self._search_job)
        self._search_job = self.after(250, self.refresh_channels)

    def _row_values(self, c: Channel):
        info = c.info
        if c.status == ONLINE and c.latency is not None:
            info += f" · {c.latency} ms"
        if c.remembered and c.checked_at:
            info = f"last check {age_text(time.time() - c.checked_at)}: {info}"
        elif c.changed:
            # first, so it is visible even in a narrow column
            info = f"was {STATUS_WORD.get(c.prev_status, c.prev_status)} {age_text(time.time() - c.prev_time)} · {info}"
        dup = f"{c.dup_reason} as #{c.dup_of}" if c.dup_of else ""
        return (c.uid, STATUS_TEXT[c.status], vis(c.name), vis(c.group or NO_GROUP), quality_text(c.quality),
                vis(info), dup,
                ("▶  " if self.v_click_play.get() else "") + vis(c.url),
                vis(self._source_labels.get(c.source, short_source(c.source))))

    def _included(self, c: Channel) -> bool:
        """In a ticked group and a ticked playlist = will be saved."""
        return self.group_enabled.get(c.group, True) and self.source_enabled.get(c.source, True)

    def _row_tags(self, c: Channel):
        tags = [c.status]
        if not self._included(c):
            tags.append("excluded")
        if c.dup_of:
            tags.append("dup")                # created first, so its yellow wins over the playlist tint
        if c.remembered:
            tags.append("remembered")
        elif c.changed:
            tags.append("changed")
        if self.v_tint.get():
            tags.append(self._source_tag(c.source))
        return tuple(tags)

    # ------------------------------------------------------------------ playlist colors
    def _source_index(self, src: str) -> int:
        if src not in self.source_color:
            self.source_color[src] = len(self.source_color)
            if src not in self.source_enabled:
                self.source_enabled[src] = self._initial_source_state(src)
        return self.source_color[src] % len(PLAYLIST_COLORS)

    def _source_tag(self, src: str) -> str:
        i = self._source_index(src)
        tag = f"src{i}"
        if tag not in self._swatch_images.get("_tags", ()):  # configure each tint once (after "dup")
            self.tree.tag_configure(tag, background=playlist_tint(i))
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
        if show == SHOW_CHANGED and not c.changed:
            return False
        if show == "Geo-blocked" and c.status != BLOCKED:
            return False
        if show.startswith("Problems") and not (c.status in (OFFLINE, BLOCKED) or c.dup_of):
            return False
        if show.startswith("Good") and not (c.status == ONLINE and not c.dup_of):
            return False
        if show.startswith("Included") and not self._included(c):
            return False
        if show.startswith("Excluded") and self._included(c):
            return False
        if q and q not in c.name.casefold() and q not in c.url.casefold() and q not in c.group.casefold() \
                and q not in quality_text(c.quality).casefold():      # "1080p", "h.265", "mp3" ...
            return False
        return True

    def _sort_key(self, col):
        return {
            "num": lambda c: c.uid,
            "status": lambda c: (STATUS_RANK[c.status], c.uid),
            "name": lambda c: natural_key(c.name),
            "group": lambda c: (natural_key(c.group), c.uid),
            "quality": lambda c: (quality_rank(c.quality), c.uid),
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
        if self._search_job:
            try:
                self.after_cancel(self._search_job)
            except tk.TclError:
                pass
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

    # ------------------------------------------------------------------ remembered ticks
    def _ticks(self) -> dict:
        if not isinstance(self.settings.get("remembered_ticks"), dict):
            self.settings["remembered_ticks"] = {}
        d = self.settings["remembered_ticks"]
        d.setdefault("groups_off", [])
        d.setdefault("playlists_off", [])
        return d

    def _initial_group_state(self, g: str) -> bool:
        if self.v_remember_ticks.get() and g in self._ticks()["groups_off"]:
            self._restored_groups.add(g)
            return False
        return True

    def _initial_source_state(self, src: str) -> bool:
        if self.v_remember_ticks.get() and src in self._ticks()["playlists_off"]:
            self._restored_sources.add(src)
            return False
        return True

    def _remember_ticks(self):
        """Store the ticks of the loaded groups and playlists (others keep what was stored before)."""
        if not self.v_remember_ticks.get():
            return
        d = self._ticks()
        off_g = set(d["groups_off"])
        for g, on in self.group_enabled.items():
            (off_g.discard if on else off_g.add)(g)
        off_p = set(d["playlists_off"])
        for src, on in self.source_enabled.items():
            if src != "clipboard":
                (off_p.discard if on else off_p.add)(src)
        d["groups_off"] = sorted(off_g)[-2000:]
        d["playlists_off"] = sorted(off_p)[-500:]
        self.save_settings()

    def on_remember_option(self):
        if self.v_remember_ticks.get():
            self._remember_ticks()           # also remember the ticks that are set right now
            self.set_status("Unticked groups and playlists are remembered – also the current ones.")
        else:
            self.save_settings()
            self.set_status("Groups and playlists are no longer remembered – every new playlist starts all ticked.")

    def forget_ticks(self):
        d = self._ticks()
        n = len(d["groups_off"]) + len(d["playlists_off"])
        if not n:
            messagebox.showinfo(APP_TITLE, "No unticked groups or playlists are remembered.", parent=self)
            return
        shown = ", ".join((g or NO_GROUP) for g in d["groups_off"][:12])
        more = " …" if len(d["groups_off"]) > 12 else ""
        if not messagebox.askyesno(APP_TITLE, f"Forget {len(d['groups_off'])} remembered unticked group(s) and "
                                              f"{len(d['playlists_off'])} playlist(s)?\n\n{shown}{more}\n\n"
                                              "The groups in the list now are not changed.", parent=self):
            return
        d["groups_off"], d["playlists_off"] = [], []
        self.save_settings()
        self.set_status("Remembered groups and playlists forgotten.")

    def _inclusion_changed(self, what: str):
        """A group or playlist was ticked / unticked: update counts, grey rows and the status bar."""
        self._remember_ticks()
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
                if g not in self.group_enabled:
                    self.group_enabled[g] = self._initial_group_state(g)
        self.group_order = [g for g in self.group_order if g in stats]
        any_checked = any(c.status in (ONLINE, OFFLINE, BLOCKED) for c in self.channels)

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
        any_checked = any(c.status in (ONLINE, OFFLINE, BLOCKED) for c in self.channels)
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
                name = self._source_labels.get(src, src)
                with self._undoable(("Untick" if self.source_enabled.get(src, True) else "Tick") +
                                    f" playlist “{name}”"):
                    self.source_enabled[src] = not self.source_enabled.get(src, True)
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
        with self._undoable(("Untick" if self.group_enabled.get(g, True) else "Tick") + f" group “{g or NO_GROUP}”"):
            self.group_enabled[g] = not self.group_enabled.get(g, True)
        self._inclusion_changed(f"Group “{g or NO_GROUP}” " + ("included" if self.group_enabled[g] else "excluded"))

    def toggle_selected_group(self):
        g = self._selected_group()
        if g is not None:
            self.toggle_group(g)

    def set_all_groups(self, value: bool):
        with self._undoable("Tick all groups" if value else "Untick all groups"):
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
            with self._undoable(f"Move group “{g or NO_GROUP}” {'up' if step < 0 else 'down'}"):
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
        with self._undoable(f"{'Merge' if merging else 'Rename'} group “{g or NO_GROUP}”"):
            for c in self.channels:
                if c.group == g:
                    c.group = new
            if merging:
                self.group_order.remove(g)
            else:
                self.group_order[self.group_order.index(g)] = new
                self.group_enabled[new] = self.group_enabled.get(g, True)
            self.group_enabled.pop(g, None)
        self._remember_ticks()
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
            if label.startswith("▶ Play"):
                self.cmenu.entryconfigure(i, label=f"▶ Play in {self._player_label()}")
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
        new = TextDialog(self, "Rename channel", "Channel name:", c.name).result
        if new and new.strip():
            with self._undoable(f"Rename “{c.name}”"):
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
        with self._undoable(f"Move {len(sel)} channel(s) to “{new or NO_GROUP}”"):
            for c in sel:
                c.group = new
            if new not in self.group_enabled:
                self.group_enabled[new] = self._initial_group_state(new)
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
        with self._undoable(f"Delete {len(sel)} channel(s)"):
            self._remove(sel)
        self.set_status(f"Deleted {len(sel)} channel(s).  (Ctrl+Z to undo)")

    def remove_offline(self):
        off = [c for c in self.channels if current_status(c) == OFFLINE]
        old = sum(1 for c in self.channels if c.remembered and c.status == OFFLINE)
        note = (f"\n\n{old} channel{'s' if old != 1 else ''} showing “offline” from an earlier session "
                f"(in italics) {'are' if old != 1 else 'is'} kept – that result may be out of date. "
                f"“Recheck offline” checks {'them' if old != 1 else 'it'} again.") if old else ""
        if not off:
            messagebox.showinfo(APP_TITLE, "No channels were found offline in this session "
                                           "(run “Check streams” first)." + note, parent=self)
            return
        if messagebox.askyesno(APP_TITLE, f"Remove {len(off)} offline channels from the list?" + note,
                               parent=self):
            with self._undoable(f"Remove {len(off)} offline channels"):
                self._remove(off)
            self.set_status(f"Removed {len(off)} offline channels.")

    def remove_duplicates(self):
        dups = [c for c in self.channels if c.dup_of]
        if not dups:
            messagebox.showinfo(APP_TITLE, "No duplicates found.", parent=self)
            return
        if messagebox.askyesno(APP_TITLE, f"Remove {len(dups)} duplicates from the list?\n"
                                          "(the online / first copy of each channel stays)", parent=self):
            with self._undoable(f"Remove {len(dups)} duplicates"):
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
        with self._undoable("Paste channels"):
            self._paste_text(text)

    def _paste_text(self, text: str):
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
        if sel:
            self.play_channel(sel[0])

    # ------------------------------------------------------------------ video player
    def _col_at(self, x: int) -> str | None:
        col = self.tree.identify_column(x)
        try:
            i = int(col.lstrip("#"))
        except ValueError:
            return None
        return self.cols[i - 1] if 1 <= i <= len(self.cols) else None

    def on_tree_press(self, e):
        self._press = (self.tree.identify_row(e.y), e.x, e.y)

    def on_tree_click(self, e):
        """Single click on the stream address plays the channel."""
        if not self.v_click_play.get() or e.state & 0x0005:          # not with Shift / Ctrl (multi-select)
            return
        if self.tree.identify_region(e.x, e.y) != "cell" or self._col_at(e.x) != "url":
            return
        row = self.tree.identify_row(e.y)
        press = getattr(self, "_press", None)
        if not press or press[0] != row or abs(press[1] - e.x) > 6 or abs(press[2] - e.y) > 6:
            return                                                   # a drag, not a click
        if row and int(row) in self.by_uid:
            self.tree.selection_set(row)
            self.play_channel(self.by_uid[int(row)])

    def on_tree_motion(self, e):
        over = (self.v_click_play.get() and self.tree.identify_region(e.x, e.y) == "cell"
                and self._col_at(e.x) == "url")
        want = "hand2" if over else ""
        if str(self.tree.cget("cursor")) != want:
            self.tree.configure(cursor=want)

    def _resolve_player(self):
        """(key, program) of the player to use; key 'system' = default app for .m3u files."""
        choice = self.v_player.get()
        if choice == "custom":
            return ("custom", self.settings.get("player_custom", "")) if self.settings.get("player_custom") else (None, None)
        if choice == "system":
            return "system", None
        if choice != "auto":
            exe = find_program(choice)
            return (choice, exe) if exe else (None, None)
        for key, _, _ in PLAYERS:
            exe = find_program(key)
            if exe:
                return key, exe
        return "system", None

    def _player_label(self) -> str:
        key, _ = self._resolve_player()
        if key == "custom":
            return "your player"
        if key == "system":
            return "the default player"
        return PLAYER_NAMES.get(key, "player") if key else "player (not installed)"

    def play_channel(self, c: Channel):
        last_uid, last_t = self._last_play
        if last_uid == c.uid and time.monotonic() - last_t < 1.5:   # click + double-click = play once
            return
        self._last_play = (c.uid, time.monotonic())
        url, headers = split_url_headers(c.export_url())
        ua, ref = c.http_options()
        # a Kodi url|User-Agent=... wins over #EXTVLCOPT, exactly as in the checker
        ua = header_value(headers, "user-agent") or ua or \
            (self.v_ua.get().strip() if self.v_ua.get().strip() != DEFAULT_UA else None)
        ref = header_value(headers, "referer") or ref
        key, exe = self._resolve_player()
        if key is None:
            choice = self.v_player.get()
            name = PLAYER_NAMES.get(choice, "the chosen player")
            pkg = {"totem": "totem", "ffplay": "ffmpeg"}.get(choice, choice)
            messagebox.showinfo(APP_TITLE, f"{name} is not installed.\n\nInstall it with:\n    sudo apt install {pkg}\n\n"
                                "or choose another one in Settings → Video player.", parent=self)
            return
        if self.v_replace_player.get() and self._player_proc and self._player_proc.poll() is None:
            try:
                self._player_proc.terminate()
            except OSError:
                pass
        try:
            if key == "system":
                self._play_with_default_app(c, url, ua, ref)
                self.set_status(f"Playing “{c.name}” with the default player for playlists. "
                                "Install VLC (sudo apt install vlc) or choose one in Settings → Video player.")
                return
            cmd = custom_command(exe, url, c.name, ua, ref) if key == "custom" else \
                player_command(key, exe, url, c.name, ua, ref)
            self._player_proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                                 stderr=subprocess.DEVNULL, start_new_session=True)
            self.set_status(f"▶ Playing “{c.name}” in {self._player_label()}.")
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not start the player:\n{e}\n\n"
                                 "Choose another one in Settings → Video player.", parent=self)

    def _play_with_default_app(self, c: Channel, url: str, ua: str | None, ref: str | None):
        """No known player: a one-channel .m3u opened with the system's default app for playlists."""
        lines = ["#EXTM3U", f"#EXTINF:-1,{one_line(c.name)}"]
        lines += [f"#EXTVLCOPT:http-user-agent={one_line(ua)}"] if ua else []
        lines += [f"#EXTVLCOPT:http-referrer={one_line(ref)}"] if ref else []
        # the file may contain a login: create it with mkstemp (0600, unpredictable name)
        now = time.time()
        for old in Path(tempfile.gettempdir()).glob("playlist-checker-play-*.m3u"):
            try:
                if now - old.stat().st_mtime > 24 * 3600:
                    old.unlink()                 # a player has read it long ago
            except OSError:
                pass
        fd, path = tempfile.mkstemp(prefix="playlist-checker-play-", suffix=".m3u")
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                f.write("\n".join(lines + [one_line(url)]) + "\n")
            try:
                os.chmod(path, 0o600)
            except OSError:
                pass
        except Exception:
            try:
                os.unlink(path)
            except OSError:
                pass
            raise
        if sys.platform.startswith("win"):
            os.startfile(path)  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            opener = shutil.which("xdg-open")
            if not opener:
                raise RuntimeError("no video player found – install VLC:  sudo apt install vlc")
            subprocess.Popen([opener, path], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL, start_new_session=True)

    def _fill_player_menu(self, menu: tk.Menu):
        menu.delete(0, "end")
        auto_key, _ = (None, None)
        for key, _, _ in PLAYERS:
            if find_program(key):
                auto_key = key
                break
        menu.add_radiobutton(label="Automatic" + (f"  ({PLAYER_NAMES[auto_key]})" if auto_key else "  (default app)"),
                             value="auto", variable=self.v_player, command=self.save_settings)
        menu.add_separator()
        for key, name, _ in PLAYERS:
            installed = bool(find_program(key))
            menu.add_radiobutton(label=name + ("" if installed else "  – not installed"), value=key,
                                 variable=self.v_player, command=self.save_settings,
                                 state="normal" if installed else "disabled")
        menu.add_radiobutton(label="System default app for playlists", value="system", variable=self.v_player,
                             command=self.save_settings)
        menu.add_radiobutton(label="Custom command…", value="custom", variable=self.v_player,
                             command=self._custom_player)
        menu.add_separator()
        menu.add_checkbutton(label="Single click on the stream URL plays it", variable=self.v_click_play,
                             command=self._on_click_play_option)
        menu.add_checkbutton(label="Close the previous player when playing another channel",
                             variable=self.v_replace_player, command=self.save_settings)

    def _custom_player(self):
        cur = self.settings.get("player_custom", "") or "vlc --fullscreen {url}"
        val = simpledialog.askstring("Custom video player",
                                     "Command to play a stream. Placeholders:\n"
                                     "{url}  stream address    {name}  channel name\n"
                                     "{ua}  User-Agent    {referer}  Referer\n\n"
                                     "Example:  mpv --fs --user-agent={ua} {url}",
                                     initialvalue=cur, parent=self)
        if val and val.strip():
            self.settings["player_custom"] = val.strip()
        elif not self.settings.get("player_custom"):
            self.v_player.set("auto")
        self.save_settings()

    def _url_title(self) -> str:
        return "Stream URL   (click ▶ to play)" if self.v_click_play.get() else "Stream URL"

    def _on_click_play_option(self):
        self.save_settings()
        title = self._url_title()
        self.col_titles["url"] = title
        self.tree.heading("url", text=title + ((" ▼" if self.sort_rev else " ▲") if self.sort_col == "url" else ""))
        self.refresh_channels()

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
                 if not (o["drop_offline"] and current_status(c) == OFFLINE)
                 and not (o.get("drop_blocked", True) and c.status == BLOCKED)
                 and not (o["drop_unchecked"] and current_status(c) in (UNCHECKED, CHECKING))
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
        on = sum(current_status(c) == ONLINE for c in self.channels)
        off = sum(current_status(c) == OFFLINE for c in self.channels)
        dups = sum(1 for c in self.channels if c.dup_of)
        included = sum(1 for c in self.channels if self._included(c))
        summary = f"{len(self.channels)} channels:  {on} online · {off} offline · {dups} duplicates"
        old = sum(1 for c in self.channels if current_status(c) != c.status)
        if old:
            summary += (f"\n{old} show a result from an earlier session (in italics) – "
                        "counted as not checked")
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
                # the final file names (after date / prefix) must all differ - "News" and
                # "News_2026-10-24" both become "…News_2026-10-24.m3u8"
                used, plan = set(), []
                for g, chans in by_group.items():
                    first = dated_name(safe_filename(g or "No group"), ext,
                                       self.v_date_names.get(), self.v_prefix_names.get())
                    fname, n = first, 2
                    while fname.casefold() in used:
                        fname, n = f"{first[:-len(ext) - 1]} ({n}).{ext}", n + 1
                    used.add(fname.casefold())
                    plan.append((os.path.join(folder, fname), chans))
                existing = [os.path.basename(f) for f, _ in plan if os.path.exists(f)]
                if existing:
                    names = "\n".join(f"• {n}" for n in existing[:10])
                    more = f"\n…and {len(existing) - 10} more" if len(existing) > 10 else ""
                    if not messagebox.askyesno(APP_TITLE, f"{len(existing)} of these files already exist in the "
                                               f"folder:\n\n{names}{more}\n\nReplace them?", parent=self):
                        return
                for f, chans in plan:
                    self._write(f, chans, ext)
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
            if src == "clipboard":
                return ""
            if "://" not in src:
                name = Path(src).name
                if name.lower().endswith(".gz"):
                    name = name[:-3]
                return safe_filename(Path(name).stem)
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
                w.writerow(["#", "Status", "Check result", "Response ms", "Quality", "Duplicate", "Channel", "Group",
                            "URL", "Playlist", "Checked (local time)"])
                for c in self.channels:
                    checked = (time.strftime("%Y-%m-%d %H:%M", time.localtime(c.checked_at))
                               if c.checked_at else "")
                    if checked and c.remembered:
                        checked += " (earlier session)"
                    w.writerow([c.uid, c.status, csv_text(c.info), c.latency if c.status == ONLINE else "",
                                quality_text(c.quality),
                                f"{c.dup_reason} as #{c.dup_of}" if c.dup_of else "",
                                csv_text(c.name), csv_text(c.group), csv_text(c.url), csv_text(c.source),
                                checked])
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
            f"Exec={desktop_exec_arg(sys.executable)} {desktop_exec_arg(str(script))} %F",
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
        if self.channels:
            with self._undoable(f"Clear the list ({len(self.channels)} channels)"):
                self._clear_list()
            self.set_status("List cleared.  (Ctrl+Z brings it back)")
        else:
            self._clear_list()

    def _clear_list(self):
        self.stop_event.set()
        self._dl_stop.set()
        self._dl_gen += 1                     # results of downloads still running are ignored
        self._dl_queue.clear()
        if self.downloading:
            self.downloading = False
            self.progress.stop()
            self.progress.configure(mode="determinate")
            if not self.checking:
                self.btn_stop.state(["disabled"])
        self.channels.clear()
        self.by_uid.clear()
        self._manual_locked.clear()
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
            "5. “Save playlist” (File → Save new playlist, Ctrl+S) writes a clean playlist "
            "(offline and duplicates removed by default). "
            "Logos, EPG (tvg-id, url-tvg) and VLC options are kept.\n\n"
            "Geo-blocked (⛔): channels that only show “not available in your country”. They are found by the "
            "server's answer, by short looping videos and – with ffmpeg installed – by the picture. "
            "Right-click a channel that shows such a banner → “Mark as geo-blocked” and the program "
            "recognises the same banner on all other channels.\n\n"
            "Black screen: a stream that works but shows only black (maybe with the channel logo) for "
            f"{STILL_CHECK_GAP}+ seconds counts as offline – Settings → “Black screen … = offline” (needs ffmpeg).\n\n"
            "Undo: Edit → Undo (Ctrl+Z) and Redo (Ctrl+Y) reverse deleting, removing, renaming, moving, "
            "ticking groups, pasting and Clear list – check results are kept.\n\n"
            "Remembered results: when you open a playlist again, each channel shows the result of its "
            "last check (in italics, with its age) until it is checked again; after a check, channels "
            "that changed since then are bold (Show → “Changed since the last check”). Settings → "
            "“Remember check results between sessions”.\n\n"
            "Quality column: resolution, codec, frame rate and bitrate of working streams (radio: format "
            "and bitrate). It is filled during the check; for streams that don't describe themselves it "
            "needs the picture or black-screen check (ffmpeg).\n\n"
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
        body = ttk.Frame(dlg, padding=20)
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

        ttk.Label(body, text="Project page", style="Section.TLabel").grid(row=3, column=1, sticky="w", pady=(14, 2))
        link = ttk.Label(body, text=PROJECT_URL, foreground=UI["link"], cursor="hand2", font=link_font)
        link.grid(row=4, column=1, sticky="w")
        link.bind("<Button-1>", lambda e: self.open_link(PROJECT_URL))
        link.bind("<Enter>", lambda e: link.configure(foreground=UI["link_hover"]))
        link.bind("<Leave>", lambda e: link.configure(foreground=UI["link"]))

        info = (f"Python {sys.version.split()[0]} · Tk {self.tk.call('info', 'patchlevel')}\n"
                f"Settings: {SETTINGS_FILE}")
        ttk.Label(body, text=info, style="Muted.TLabel", justify="left").grid(row=5, column=1, sticky="w", pady=(14, 0))

        buttons = ttk.Frame(body)
        buttons.grid(row=6, column=0, columnspan=2, sticky="e", pady=(16, 0))

        def copy_link():
            self.clipboard_clear()
            self.clipboard_append(PROJECT_URL)
            copy_btn.configure(text="Copied ✓")
        ttk.Button(buttons, text="Open project page", command=lambda: self.open_link(PROJECT_URL)).pack(side="left", padx=3)
        copy_btn = ttk.Button(buttons, text="Copy link", command=copy_link)
        copy_btn.pack(side="left", padx=3)
        close = ttk.Button(buttons, text="Close", style="Accent.TButton", command=dlg.destroy)
        close.pack(side="left", padx=(3, 0))
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
        except (ValueError, OverflowError, tk.TclError):
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
            "remember_ticks": self.v_remember_ticks.get(), "player": self.v_player.get(),
            "player_custom": self.settings.get("player_custom", ""), "click_play": self.v_click_play.get(),
            "replace_player": self.v_replace_player.get(), "retry_temporary": self.v_retry.get(),
            "geo_server": self.v_geo_server.get(), "geo_loop": self.v_geo_loop.get(),
            "geo_picture": self.v_geo_picture.get(), "geo_ask": self.v_geo_ask.get(),
            "black_screen": self.v_black.get(), "theme": self.v_theme.get(),
            "remember_results": self.v_remember_results.get(),
            "bidi_fix": self.v_bidi.get(), "confirm_exit": self.v_confirm_exit.get(),
            "encoding": self.v_encoding.get()})
        try:
            SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
            fd, tmp_name = tempfile.mkstemp(prefix=".settings-", suffix=".json.tmp",
                                            dir=SETTINGS_FILE.parent)
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as f:
                    f.write(json.dumps(self.settings, indent=2, ensure_ascii=False))
                os.replace(tmp_name, SETTINGS_FILE)   # atomic: a crash can't leave half a file
            except OSError:
                try:
                    os.unlink(tmp_name)
                except OSError:
                    pass
                raise
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
        self._dl_stop.set()
        if getattr(self, "_checker", None):
            self._checker.kill_all()          # don't leave ffmpeg picture processes behind
        for checker in list(getattr(self, "_aux_checkers", ())):
            checker.kill_all()
        self.save_settings()
        self._store_results()                 # e.g. channels marked geo-blocked by hand
        self.destroy()


# Application icon (TV with play button, radio waves and a green check) - PNG, base64
ICON_PNGS = {
    32: "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",
    64: "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAUPElEQVR42s2beZQV1bXGf+ecqjv37bmZmkkGBUQmg8aoQKKJcYovsTUxiQExxull0OiCaCK8pybGibygxqcgvjhEMPo0QWJQEZ4TQUQFGhFUZoSm59t3qqpz3h91u+mZbnCqtfbqXnfdqjp7n2/v/e29zxX0+jKCigsk+0eLKXwxrpUAZZWGJYs1CPMpvaZCUbFY8UW/KioUFRU9Xqc49Fdukv7fuRpg+OSb4tmMHquNOVoY0xdMUKM/F10lYBAOqI8x3hZ0ev2uyrtrWpDKHNG87sMzQMVixZILPIDysTecipSXYsxpQqh+Qlo9s9+nfvmIN8bFGG8/RrzsCWfB3nd+98/2OvTOALkb+4+97mhpRW4TiG8JqTDawRjPYPC+YOCXQioppI0xGmO85V6qYdbe9+a91Z0ROjfAlJssVs51y8ff8D2UfZ8UVr72UtogjPCRJ76gEcAY0AIjpApLrd20dhPX7Hn3jvu6MoLqSvl+E351tQpEF4AX0tpxkVIhhEQIgRD0XGTuL3wG94nmNRrjeggCKph3VrRkoki89IsVTLnJYvtK3bUBKioUz93r9T/+hgutQGyh9rIeaHLK904BBNKSGOPjRVrK/19+Sve1FykkGGOM56lg/KvR4mPrE6tve629EVSbaF95jymfkBmOHVpmMBZCC4SUvVXeCIFUkmTawbIVQkqaUlkCAQuDv1Gf5H3dIwJhMFpYkdND+UNWJN+ct42bbpKsXGmaM0lOfwBhPDvwB2EFowatjZTSSEFvRVqSprTDCROGsPyRy3np8Sv56skjSWYdf3e7uk9JkhmXEycNbblv2ldGkMh0f1/3IoVBg2VbVrTvPCDK3Jdl2yCYCxD9Tvz1V6QKv2K04yFQHCanElKQybisePQKjh3ZF4APdlRzUsUfCdgKbUzrDOavwoBSksamNCseuYLxowcAsG13DV+pmO9/TfhRrvcLAozxhAqpVO3mH9VsfOh/mnWWbRcurxKWDUKYnB8dngiBEZB1/aCrtaGoIEKf0jySGRdlSUyr5xuRQ03GoX/fAgb0zUdrX1PH0WhBy/cOdz0IAUoaO9ZnJhDlw9tkcwwQVC7RhZMuy7eCBfMMJoowovfR/qAIKch6mnc37+WoQcWUFkWJx0KMGzWAJ/+5Hi+32yYX4aWUuNqglOTROy/imKFlJNMOazfuYvbd/2Db7loCQT8OHO6akAiDFkhV5mUan3O3rN0LxkgqFkuAYKR0nLACpaANQh628giBBiKRAO9u3ccZly3ku9c+RjLtcNKEwTx4y/mkHRcjfFcR0kdL2nF58JbzOWn8YJJph+9e+xinX/ogq9fvJBoNos0RKC9yL8NoGQiHQyWjJvkpf46S7N+YIzVqFCoAUnqHDf1W4mEIBm2Ki6IsX72Vy+Y8hetpzp4yinmzz6U2kUYqiVSS2kSaebPP5ewpo3A9zWVznmL56q0UFUYJhQN4GD6JNSGEEcpChuJHAwGqKqXVQqGk6IeSGC1aRacjqKHwkaC1oawkjyUvbKCsJMZdvzyL6edNYn9tEzfd94JfZl11OtPP8zfl+ruXseSFDfQpycNxc+layh7GY3PISt5IAVagDAjSsNMcNICQAZ91da+glH548LTpcUh2PE1ZcYz5T6ympDDKr2ZO5foZp7L94zpf6RmnAnDrgpeZ/8Rq+hTHcDzdC8ItUEpgjGkJnl0ayA9tQcDGczJW69qyOXd2mkUAJSWpjEMq45IXCaCk7HEmcoGykhg3L1hJaVGMS8+bxPxZ5+QIvOHB/13LzQtWUlYSw9UGevFsT2vqGzMEA4pIKICnNZ3i2OR0FDmN3ZRsY4CDdLSt9iYXtRuaMowcVMxVFSfwpdEDCAWt3Cb1bKuEAN2yS6LlVcbAqROH8M4TVyOF6EWuNxggm/V4a/Ne7n1yNeu37iM/FsJrRpDpZBHiINatNu2F5mDRvmJSgsZklhOOLWfxby+kKB4+4rJNa91G0aMHlxzR88YMK+Pfpo3iol8/yYo3PyIeDeLpdm7UXFPItk0Vf0GtXKC1IAWu8dPan2afS1E8TNY58laAlLKNHOmVdTxi4QD3zz6HwoIwWa198tSJaHHwfa1cQB5kTe2CXn1Thm9+eTjDy4twXU3AVtTVN3LbHYvYsHErylKHyVGP5BJ4nsfIEYOZ9csZlJYW4rge/YrzOG3yMB5fvoHCeNh3hfYu0AoWbWNAJy4glMQ1hvKyOMb4Xqe1Zublc3nqL0sJxuM+1D6HS0nJ359ezvqNW/j7039ESj8TlPfJx6OZ+4i2LqBEmxrYgqnAXD/XdpIFWmCTC1q2pdi+fS8vrfgXxf37+iUqhs/risdjvPra22zZsp0xo4f57mxauXM7AxiZa7Z0QABdZQFxsDOTuzLZLEoJPE93+Poh00Bz2P+kHEEYlFJksg4d0NyVPtBVDKBjFpAdu4CiV6nq4IuN64LRyGAI431yPVVjTA6JrYhLszu3d4F2bi5bsUS08MvUDiIlRsh2+oi2Lz2k8g52UQmBvuW4tTW58vtTmrN0pYcQaCHa2EQytX0QpBMRHbiOm82STaV6bgDHwS7rx9A7H6DkwhlgDF6iASFlG5/8RKcm7UW1+r89Ag5dSbXKuYkEX77kUqb9/Be46TRSKQ4ZDHIokJE4/S7/GUNvf4C8E0/FSzRismlET57Rmw5Qt7rk1C4tRXaI+F1A5+DiDNH+5Zz440uQSuE5Dk4qjXacQ7uEEOB5uHVNBIcezaCb7mLgr35HYMBg3Ppa0No3xJHGBCG6lU5jQAsR6q6t5CcZdgfjVO2p5pX5f6B0+Ai+fdftREtK8BynR0gQSmHSKXQyRXzqaRx15wL6TL8aYdu4DfX+Wo4EDd0iQLZBs+w0dbRXvLULeIbtWdizbh31+z9m/PkVDJ58Atp1e7doKUFKvIYkKJuyH85k6J0LKZh2BropgemJMbtDWlcGUKJNpdmqFpCHhg6Q9QwJDY17dyOEZMBx49iy8hVqd+7ECgR6neOFUmA0bn2SQFl/Bv76Fobe/iB2aR8/bR6OEUQXbkBzJuAQVFi05wEHP5M5JiltG2MMTjpNMJaHshTmcAmONggpkSGb7N4qEmtfRyeb/AxxuAhQveQBLX7X2SyuVQywlKBAQeHQ4Ugp2fLyCkZMmUTJsBG4mXTPuUGOERrPQ0bCCNuiZunTfHTtTPb/+T50KulH68MxquhilCY7slqrM97fGnatM0OzoYYHYdCk8fQfM5YNf3sG7WVJ1tYgLbvHKDCehwwGUUFFYt1a9j9yP03vvIkMh7EKi3NM0XRbTjePALXSbQzvr1d2Wgv4u99dOdy+JO7gFpK86j0oJ8bUa69jydVX8NZfFmOFgj2CrMlVjlZ+hMzuPVQ9vpD6F5ditIeVX4DRukuaLIRAKYnrejQlU2SyWYw24DhkXafN97qlwqqrGCBaSRs4tf0s1dDAc7+5HRUKYQWC2JGInwV6AHkVtfEaPaqeeITqv/4Zp6YKFYv79UU39YFSimzWoaamjlg8yvhjR3LMsKH0KS2iKZlmQEkpxhg8NBnPQ0iBFO0ZbEdG22IALUCqLlyg3WfBaIxtq1/HdTyCsWiPlUcqGle/zr6H7iG1eSMyGsOKF/iKd+M6lqWorqmnrKyIWT+dwfcqzqBgcB51MkGjl8SSFtrzN9gSisHF+RjPJeVpbEsd7FcY09IlOgwXaGUUo7HDYVQQMD1ohmi/Asxs/4Adc3+J8VysgsJu4X5w5yVVB2q54DtfZ/7vZ1FVWM/dGxfzwtI17GmsIuM5SCGIB6OMyB/IuYNOYfqUsxjR5wIuWfQ8NYkMsVAg1yQ1HXSRndf+nUkHZ27x554XRFmEbSPDkUPuejPsD1TXceP1P+aJR27j9j2PcfxjM7jv7afY23SAgGWTH4qRF4zgGo911e8za829nPy3nxAbsJe1v7mIoX3iJLJO24Fs50ywq/l7q8lsu46u6C1JaZ5v98BwlqU4UF3LVZddyH/OvZIzl13D7W89Sn4oRmm4gIC0cxRCo41BIohaYfqEi/g4Vc20Z67hlcaVrLyugvxokIw2COXrqDtjgn6gk10dN2mxmjFQWlJEOBwik8li2xZKyU9UbNsilUpz3NiRzL97FtNX3cyynW9QHitDG41rvNxEoG2AN8bgao+IFaY4FOOi5bewy7zHwzPOIJHNIpXshgd0EQOae2ie8V/ieB5FRXHm/voKfnbt76mpqafzCcSRtcyzjQ3c/ed5LKt+g4crlzIgXkZWO92ckRO42sPRHtrTxO0oUTvAxS/exobzF/HNsUNZXrmdeCSvDRO0Ws8FZCcRXwuBFVCs/7gWkevEamOYOf08Tj15Ips2f4RS8hPtixpjUJbi5GkTmbrsSuLhGF43wVYKQdZzCVtBHp12A4veX8qSj16if6SEjbXb+Mu2f3Lt1yazbOOHHarBtpMh0bGRqIFYOMCa7VU88+52vnXcYBxP4xrNiOGDGDF80KfW8X1t/3rW13xAzI6gcwYQQiARLQYRCLQxONrl0VPm8PXyyZw+4EvkBSI8vnU5eXaYR99/kUdP/gZ9i+IktG4ziJGdFkPtxAgIBCwue/xV/rFpF7aSBKzeNy48z+uRGONniDf2bfTTXG7LlJA4nkttthEpZI7yC+qyCf7rpGs4Y+CJuMajLpvgg4bdKCkJWTbrq7fhWY2M6VdKyvMQqjMeIBBGNft8Rw5j24pGx+W8B1/kzNHlnDS0D+GAys0ZO0JStKoeM47HKcP7Mq5/Edp0On5seY8Q8PbuA5RF86jKVLd6pqQm08DowqFM7TeRP216mqJgnH2pGuZMnMn0kWfiaBcD/GDFHFbtXUdpuBBXa+qzTdS7DQwsyMPbVesHw44GEG6barAdg9T4RgB4esMOnn5nexfTVyDrQvNISgpIZXn2+vMY17/IL5a6SJ8Gg0Cwsy5JfZMiYNGSbjNuhgnFI1k45QZGFQwhrILc+ub9XHHcRdwwYTpZ7RKQFpeu+i3Ld6+hLFyEo92ci2i00dhWLtBr43UMgnj7lfC7JUZ0XmHq3N/8aLCLnYeU43H8yH4MKYr5Y3UhSDkuQ4tjnc0lOj13MrAwgjQWBU4+BoMUgrSXZXLZGEYVDMHRLrd86ScMjw/gu8NOxzOagLSY89YCHt7yXIvyvl6aiB0ipqJ8nEyDUnhuqgYwWAFjMabKAJhs0xajHYwQMncQv9PDJ8bviuVOW7SFfWPGYcqwviy79DQCSna4382d3tDdMUBjOLZfIUpIPnKGEFAKV2sKAjH+tOkpioNxfjPxEhztMuPos/GMhxKSB957lt+ue5jSUCFuTnkpBEkny5iiciKygE3VtSKgwKvdtwMwRBq1xQUVGsC898Z6XdCnTth2Ado1vaV5Qgo8A2V54Q7KN++uJXv6SN/Vvlo+nn6RUuqzCSyhKA7mc/O6h7ClxezxF7fAfumOV/nFG/MoDMZbsoUf1yUJN805Q05gxwHXfFjbKGNKZpsqX9sMCBoaPAuEwRiZEmJ3dPKZ/0cofrZJJTyEsHoV4YFoJMAzm3bx78+u4Ziy/I4jq54SIQHpbJbvjz+Gmcd8kxv/tZD+0WIc7VISKmDuWwsIKIurR1fw8t63uGTVrYRUsOUESnN6dI1Hvh3jJ6POZc5zlUZbIUhVV3pb139ItMxQWem1UVJX7Vwk8wrO6aSQ7sFhldzilWD+a+8dGTGSAlIZXt1Zx5MX/ZDHt7zMtsRu4oEorvYoCOQxZ+0CHtu6nN3JKlztEVBWG9eypcWuxD7uOeXnJJsKeWDN80Rj+SLz9rq/Aw2UhDM0te6P+mdn7cjshStkQemJPgoOb3jXc6h3R4cFtY1JHv/e1zh5hGbSk1eS9JLkB2J4xgMEKTdDQNm5c0WmhSsIBHuaDnDpqHN44JTZnPzfz+s39jXJSLL2g8Y7Lp+JUjvIZPYAmYPOOrrCgMl4778zWzsZx1gBjMAczgltB45YstoQiYS5+KlVfPBxlDXfuYdh8YHsaaom4zkIIGaHsaVCIbGEz0nqs03sT9Uza8L3eeCU2Vz819fNqzsOmGhAmdQrz96L6x7ALkzkXtOqO7ZyruGyvbb3yL3b1Mhxruw76DQ8x8MYcaRHZw9XZK4Qe/idrRxbPJB5Uy+kIBRiS90e9iRrqMs20eSkSbi+WMLi1H7H8dC06ziv/BwqFq8yT67fpvPL+qj0ulWLnKULl5Cf30hj9QH8k3udOPqUH4VY+bAK/fSOW9VRx/7UpBL+uTYhJZ/55XMAbQzJdJZzjhnEf0ydyLAS2NzwPhtrP2J/qo6gshgc68u44qMpVAP4a+VeblyxRu9tTIv8klKR3rD6qcz9N95FrKiWRM0uIJGjNZ1GOsGkSWHWrg0Er7j1Wjl01CxhBy2TbtJtTxk108BP8fdT/jl/vwASgkQ6AwK+XN6HbxxVztiyQkoiQbKeZkd9E6/u3Gf+8eEOs6e6EbugQIYwJrPhX4uyi25+iGi0nqam3UB98+7Tzeolo0dHqKy07LN+dIaafPr1Ir9oghACk02D9jRGfOYHg5QQaAzJrAOOczBjGEAjsC1px/II2Qq3Zv9mZ9XfFrgvLllFNJqkqWlvTnmnM/bZuf2POy7Cu+/aQL/AD645Sxw19tsymjeOcDQilMXndbUutlrSrfYwqWTKa6zb5G5a+7yzZP7LwAHy8ppobNyXg73bFf3u2gjDhweoqopQX28DxWrs5JHqmOPHUNRnqAlFi6UUdq4f9dn+llAI4xco2jOZZK2p2rPLq1z7vt705nagAXAIF9WRqqkFMjmuRm8NcNAlJk0KsWVfiIZdNmADgZwoPv8fUuqcGIJBl7y8JAcONALpnOLmUAVYz0/ejB5tAQESyiabsvAclStiPh8jCGEQ0mBlXDKZLNXVTg7qXk8alf8PdvkyvlHcCFMAAAAASUVORK5CYII=",
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
    for stream in (sys.stdout, sys.stderr):   # None under pythonw.exe (no console)
        try:
            if stream:
                stream.flush()
        except (OSError, ValueError):
            pass
    if threading.active_count() > 1:
        os._exit(0)


if __name__ == "__main__":
    main()

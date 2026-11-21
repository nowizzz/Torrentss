#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TorrentX Personal Stremio Addon - single file, backend only, Render-ready.

- Torrentio streams ranked strictly: 4K Remux > 1080p Remux > 4K WEB-DL > 1080p WEB-DL > Encode
  (debrid: cached only, P2P: seeded only, AI-upscales rejected by default).
- Arabic subtitles only (SubDL + SubSource + optional Wyzie), best one auto-selected.
- Auto sync against timings extracted from the video itself (ffprobe): natural / constant shift /
  FPS-affine (25 <-> 23.976 ...) / piecewise (commercial-break differences).
- Zero third-party Python packages. ffprobe (ffmpeg) is needed for sync -> use the Dockerfile.

ENV VARS
  ADDON_SECRET        secret path segment (strongly recommended)
  DEBRID_SERVICE      torbox | realdebrid | alldebrid | premiumize | debridlink | offcloud | putio | p2p
  DEBRID_API_KEY      key for the debrid service (empty => P2P mode)
  SUBDL_API_KEY       SubDL key
  SUBSOURCE_API_KEY   SubSource key
  WYZIE_API_KEY       optional
  ALLOW_UPSCALE       true/false (default false)
  SUB_COUNT           1..3 subtitles returned (default 1)
  MAX_STREAMS         default 25
  REF_WAIT_SECONDS    max wait for video reference timings in /subtitles (default 14)
  SUB_BUDGET_SECONDS  total time budget for /subtitles (default 24)
  TORRENTIO_BASE      default https://torrentio.strem.fun
  PUBLIC_URL          optional; Render sets RENDER_EXTERNAL_URL automatically
  PORT                set by Render
"""
import os
import re
import io
import json
import math
import time
import uuid
import bisect
import base64
import shutil
import zipfile
import logging
import hashlib
import threading
import subprocess
import unicodedata
import urllib.parse
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError as FutTimeout
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("TorrentX")

# ======================================================================================
# Config
# ======================================================================================
def env(name, default=""):
    return (os.environ.get(name) or default).strip()


PORT = int(env("PORT", "7123"))
SECRET = env("ADDON_SECRET")
DEBRID_SERVICE = env("DEBRID_SERVICE", "torbox").lower()
DEBRID_KEY = env("DEBRID_API_KEY")
DEBRID_MODE = bool(DEBRID_KEY) and DEBRID_SERVICE not in ("none", "p2p", "")
SUBDL_KEY = env("SUBDL_API_KEY")
SUBSOURCE_KEY = env("SUBSOURCE_API_KEY")
WYZIE_KEY = env("WYZIE_API_KEY")
ALLOW_UPSCALE = env("ALLOW_UPSCALE", "false").lower() in ("1", "true", "yes")
SUB_COUNT = max(1, min(3, int(env("SUB_COUNT", "1") or 1)))
MAX_STREAMS = int(env("MAX_STREAMS", "25") or 25)
REF_WAIT = float(env("REF_WAIT_SECONDS", "14") or 14)
SUB_BUDGET = float(env("SUB_BUDGET_SECONDS", "24") or 24)
TORRENTIO_BASE = env("TORRENTIO_BASE", "https://torrentio.strem.fun")
PUBLIC_URL = env("PUBLIC_URL") or env("RENDER_EXTERNAL_URL")
FFPROBE = shutil.which("ffprobe")

UA = {"User-Agent": "Mozilla/5.0"}


# ======================================================================================
# Small utilities
# ======================================================================================
class TTLCache:
    def __init__(self, ttl, max_items=600):
        self.ttl, self.max, self.d, self.lock = ttl, max_items, {}, threading.Lock()

    def get(self, k):
        with self.lock:
            v = self.d.get(k)
            if v is None:
                return None
            if time.time() - v[0] > self.ttl:
                self.d.pop(k, None)
                return None
            return v[1]

    def set(self, k, val):
        with self.lock:
            if len(self.d) >= self.max:
                for kk in sorted(self.d, key=lambda x: self.d[x][0])[: self.max // 4]:
                    self.d.pop(kk, None)
            self.d[k] = (time.time(), val)


def http_get(url, headers=None, timeout=12):
    h = dict(UA)
    h.update(headers or {})
    with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=timeout) as r:
        return r.read()


def http_json(url, headers=None, timeout=12):
    return json.loads(http_get(url, headers, timeout).decode("utf-8"))


def nearest_dist(sorted_list, x):
    i = bisect.bisect_left(sorted_list, x)
    best = 1e9
    if i < len(sorted_list):
        best = abs(sorted_list[i] - x)
    if i > 0:
        best = min(best, abs(sorted_list[i - 1] - x))
    return best


def normalize_fancy(text):
    """Squared/negative-squared/regional letters and math-bold -> plain lowercase."""
    if not text:
        return ""
    out = []
    for ch in str(text):
        cp = ord(ch)
        if 0x1F130 <= cp <= 0x1F149:
            out.append(chr(97 + cp - 0x1F130))
        elif 0x1F170 <= cp <= 0x1F189:
            out.append(chr(97 + cp - 0x1F170))
        elif 0x1F1E6 <= cp <= 0x1F1FF:
            out.append(chr(97 + cp - 0x1F1E6))
        else:
            out.append(ch)
    return unicodedata.normalize("NFKC", "".join(out)).lower()


STREAM_META = TTLCache(3 * 3600)     # media_id -> [{"title","url"}]
SUB_CACHE = TTLCache(2 * 3600)       # token -> dict
SUB_TEXT_CACHE = TTLCache(2 * 3600)  # (prov,id,season,episode) -> text
SEARCH_CACHE = TTLCache(1800)        # (imdb,season,episode) -> raw candidates
TITLE_CACHE = TTLCache(24 * 3600)
REF_OK = TTLCache(3600)
REF_FAIL = TTLCache(180)
INFLIGHT, INFLIGHT_LOCK = {}, threading.Lock()


# ======================================================================================
# Stream ranking (Torrentio)
# ======================================================================================
RE_UPSCALE = re.compile(r"\b(upscale|upscaled|ai[-\s]?upscale|ai[-\s]?remaster|topaz|visionx|4320p|8k)\b", re.I)
RE_REMUX = re.compile(r"\b(remux|bdremux|uhd[-\s]?remux)\b", re.I)
RE_WEBDL = re.compile(r"\b(web-dl|webdl|amzn|atvp|itunes|nf|dsnp|hmax|hbo[-\s]?max|pcok|pmtp)\b", re.I)
RE_WEBRIP = re.compile(r"\b(webrip|web-rip)\b", re.I)
RE_BDRIP = re.compile(r"\b(bdrip|brrip|bluray[-\s]?rip)\b", re.I)
RE_DISC = re.compile(r"\b(bdmv|iso|complete\.bluray|complete\.uhd|bd25|bd50|bd66|bd100)\b", re.I)
RE_CAM = re.compile(r"\b(cam|hdcam|hdts|telesync|telecine|dvdscr|scr)\b", re.I)
RE_LOW = re.compile(r"\b(yts|yify|psa|galaxyrg|rarbg|lama|pahe|av1|av01)\b", re.I)
RE_BAD_EXT = re.compile(r"\.(exe|msi|bat|cmd|scr|vbs|ps1|hta|lnk|pif|dll|zip|rar|7z|apk|iso|img)\s*$", re.I)
TRUSTED_REMUX = ["framestor", "cinephiles", "epsilon", "wildcat", "pmp", "bluranium", "fgt", "triton", "playbd", "decibel"]
TRUSTED_WEB = ["flux", "ethel", "ntb", "kitsune", "cmrg", "sic", "tepes", "bynoche"]
STREAM_TAGS = ["atvp", "itunes", "amzn", "nf", "ma", "dsnp", "hmax", "pcok", "pmtp"]


def _foreign_only(t):
    if any(w in t for w in ("eng", "english", "multi", "dual", "🇬🇧", "🇺🇸")):
        return False
    pats = [r"\bfrench\b", r"\btruefrench\b", r"\bvff\b", r"\bvostfr\b", r"\bgerman\b", r"\bdeutsch\b",
            r"\bitalian\b", r"\bspanish\b", r"\blatino\b", r"\brussian\b", r"\bhindi\b", "🇷🇺", "🇫🇷", "🇩🇪", "🇮🇹", "🇪🇸"]
    return any(re.search(p, t) for p in pats)


def parse_size_gb(text):
    m = re.search(r"💾\s*([0-9.]+)\s*(GB|MB)", text, re.I) or re.search(r"\b([0-9.]+)\s*(GB|MB)\b", text, re.I)
    if not m:
        return 0.0
    v = float(m.group(1))
    return round(v / 1024.0, 2) if m.group(2).upper() == "MB" else v


def parse_stream(s, allow_upscale):
    name = s.get("name") or ""
    desc = s.get("title") or s.get("description") or ""
    url = s.get("url") or ""
    hint = s.get("behaviorHints") or {}
    fname = hint.get("filename") or ""
    lines = [l.strip() for l in desc.split("\n") if l.strip()]
    if any(RE_BAD_EXT.search(x) for x in lines + [fname]):
        return None
    if url and RE_BAD_EXT.search(urllib.parse.urlparse(url).path):
        return None
    comb = f"{name} {desc} {fname}".lower()
    if (not allow_upscale and RE_UPSCALE.search(comb)) or RE_CAM.search(comb) or RE_DISC.search(comb) or _foreign_only(comb):
        return None

    title = fname or next((l for l in lines if re.search(r"\.(mkv|mp4|avi|m2ts|ts)$", l, re.I)), lines[0] if lines else "Stream.mkv")
    ih = (s.get("infoHash") or "").lower()
    if not ih and url:
        m = re.search(r"/([a-fA-F0-9]{40})/", url)
        ih = m.group(1).lower() if m else ""

    if any(w in comb for w in ("2160p", "4k", "uhd")):
        res = "4K"
    elif "1080p" in comb:
        res = "1080p"
    else:
        return None

    size = parse_size_gb(desc)
    sm = re.search(r"👤\s*(\d+)", desc)
    seeders = int(sm.group(1)) if sm else 0
    remux = bool(RE_REMUX.search(comb)) and not RE_BDRIP.search(comb) and not RE_WEBRIP.search(comb)
    webrip = bool(RE_WEBRIP.search(comb))
    webdl = (bool(RE_WEBDL.search(comb)) or "web" in comb) and not remux and not webrip
    if remux and res == "4K" and 0 < size < 22.0:
        remux = False
    if remux and res == "1080p" and 0 < size < 10.0:
        remux = False
    return {
        "title": title, "url": url, "hash": ih, "file_idx": s.get("fileIdx"),
        "cached": bool(re.search(r"\[[A-Z]{2}\+\]", name)),
        "res": res, "size": size, "seeders": seeders, "remux": remux, "webdl": webdl, "webrip": webrip,
        "low": bool(RE_LOW.search(comb)),
        "tag": any(re.search(rf"\b{t}\b", comb) for t in STREAM_TAGS),
        "lossless": any(w in comb for w in ("truehd", "atmos", "dts-hd", "dtshd", "dts:x", "pcm", "flac")),
        "hdr": any(w in comb for w in ("dv", "dovi", "dolby vision", "hdr10", "hdr")),
        "ar_flag": "🇸🇦" in comb or bool(re.search(r"\b(arabic|ara)\b", comb)),
        "comb": comb,
    }


def rank_streams(raw, debrid_mode, allow_upscale, is_episode):
    parsed, seen = [], set()
    for s in raw:
        c = parse_stream(s, allow_upscale)
        if not c:
            continue
        key = (c["hash"] or c["url"] or c["title"], c["file_idx"], c["cached"])
        if key in seen:
            continue
        seen.add(key)
        parsed.append(c)
    if not parsed:
        return []

    # Unlabelled 4K "upscale" detection: only 1080p remuxes exist but a random 4K encode appears.
    has_4k_remux = any(c["res"] == "4K" and c["remux"] for c in parsed)
    has_1080_remux = any(c["res"] == "1080p" and c["remux"] for c in parsed)
    has_legit_4k_web = any(c["res"] == "4K" and c["webdl"] and (c["tag"] or c["size"] >= 10) for c in parsed)
    if not allow_upscale:
        keep = [c for c in parsed if not (c["res"] == "4K" and not c["remux"] and not has_4k_remux
                                          and not has_legit_4k_web and has_1080_remux)]
        parsed = keep or parsed

    min4k, min1080 = (1.5, 0.6) if is_episode else (6.0, 2.5)
    for c in parsed:
        if c["res"] == "4K" and c["remux"]:
            c["tier"], c["rtype"] = 1, "bluray"
        elif c["res"] == "1080p" and c["remux"]:
            c["tier"], c["rtype"] = 2, "bluray"
        elif c["res"] == "4K" and c["webdl"] and not c["low"] and (c["size"] >= min4k or c["tag"]):
            c["tier"], c["rtype"] = 3, "web"
        elif c["res"] == "1080p" and c["webdl"] and not c["low"] and (c["size"] >= min1080 or c["tag"]):
            c["tier"], c["rtype"] = 4, "web"
        else:
            c["tier"], c["rtype"] = 5, ("bluray" if "bluray" in c["comb"] else "web")
        q = 0
        if any(g in c["comb"] for g in TRUSTED_REMUX): q += 400
        if any(g in c["comb"] for g in TRUSTED_WEB): q += 300
        if c["lossless"]: q += 250
        if c["hdr"]: q += 200
        if c["ar_flag"]: q += 150
        if c["low"]: q -= 1000
        q += min(int(c["size"] * 8), 400) + min(c["seeders"], 100)
        c["score"] = q

    if debrid_mode:
        pool = [c for c in parsed if c["cached"]] or [c for c in parsed if c["seeders"] > 0]
    else:
        pool = [c for c in parsed if c["seeders"] > 0]
        for c in pool:
            c["score"] += min(c["seeders"], 500) * 3
    pool.sort(key=lambda c: (c["tier"], -c["score"]))
    return pool


def short_title(c, is_series):
    stem = re.sub(r"\.(mkv|mp4|avi|ts|m2ts)$", "", os.path.basename(c["title"]).strip(), flags=re.I)
    g = re.search(r"-([A-Za-z0-9_]+)$", stem)
    group = g.group(1) if g else ""
    ep = re.search(r"\b(S\d{1,2}E\d{1,2}|\d{1,2}x\d{2})\b", stem, re.I)
    yr = re.search(r"\b(19\d{2}|20\d{2})\b", stem)
    cut = ep.end() if ep else (yr.end() if yr else len(stem))
    name = re.sub(r"[._]+", " ", stem[:cut]).strip(" -.") or stem[:40]
    qual = ("Remux" if c["remux"] else "WEB-DL" if c["webdl"] else "WEBRip" if c["webrip"]
            else "BluRay" if "bluray" in c["comb"] else "Encode")
    l1 = " • ".join([p for p in (name, f"{c['res']} {qual}", group) if p])
    dur = 2700 if (is_series or ep) else 7200
    size = f"💾 {c['size']:.1f} GB" if c["size"] > 0 else "💾 ?"
    mbps = f"⚡ ~{round(c['size'] * 8192 / dur, 1)} Mbps" if c["size"] > 0 else ""
    ar = "🇸🇦 ترجمة عربية مدمجة" if c["ar_flag"] else "🌐 ترجمة خارجية تلقائية"
    return f"{l1}\n{' | '.join(p for p in (size, mbps, ar) if p)}"


def fetch_torrentio(media_type, media_id):
    prefix = f"{DEBRID_SERVICE}={DEBRID_KEY}/" if DEBRID_MODE else ""
    url = f"{TORRENTIO_BASE.rstrip('/')}/{prefix}stream/{media_type}/{media_id}.json"
    try:
        return http_json(url, timeout=15).get("streams") or []
    except Exception as e:
        log.warning("Torrentio fetch failed: %s", e)
        return []


def build_streams(media_type, media_id):
    is_series = media_type == "series"
    ranked = rank_streams(fetch_torrentio(media_type, media_id), DEBRID_MODE, ALLOW_UPSCALE, is_series)
    STREAM_META.set(media_id, [{"title": c["title"], "url": c["url"]} for c in ranked])
    if ranked and ranked[0]["url"].startswith("http") and FFPROBE:  # pre-warm reference timings
        threading.Thread(target=get_ref_data, args=(ranked[0]["url"], is_series), daemon=True).start()

    tiers = {1: "Tier 1 • 4K Remux", 2: "Tier 2 • 1080p Remux", 3: "Tier 3 • 4K WEB-DL", 4: "Tier 4 • 1080p WEB-DL"}
    out = []
    for c in ranked[:MAX_STREAMS]:
        tier_txt = tiers.get(c["tier"], f"Tier 5 • {c['res']} Encode")
        badge = f"⚡ {DEBRID_SERVICE.upper()} مخزّن" if (DEBRID_MODE and c["cached"]) else f"🌱 {c['seeders']} سيدر"
        obj = {
            "name": f"TorrentX\n{tier_txt}\n{badge}",
            "description": short_title(c, is_series),
            "behaviorHints": {"bingeGroup": f"torrentx-{c['tier']}-{c['res']}", "filename": c["title"]},
        }
        if c["url"]:
            obj["url"] = c["url"]
        elif c["hash"]:
            obj["infoHash"] = c["hash"]
            if c["file_idx"] is not None:
                obj["fileIdx"] = c["file_idx"]
        else:
            continue
        out.append(obj)
    return out


# ======================================================================================
# Subtitle providers (SubDL / SubSource / Wyzie) - Arabic only
# ======================================================================================
BANNED = ["opensubtitles", "open subtitles", "osdb", "google translate", "machine translated", "ai translated",
          "ai-translated", "translated by ai", "chatgpt", "ترجمة آلية", "ترجمة قوقل", "ترجمة جوجل", "ترجمة الذكاء"]
AD_RE = re.compile("|".join([r"opensubtitles", r"osdb\.link", r"advertise\s+your\s+product", r"become\s+vip\s+member",
                             r"support\s+us\s+and\s+become\s+vip", r"www\.opensubtitles\.org"]), re.I)


def is_banned(item):
    blob = normalize_fancy(" ".join(str(item.get(k) or "") for k in ("name", "commentary", "author", "preview")))
    return any(b in blob for b in BANNED)


def get_title(imdb, is_series):
    key = (imdb, is_series)
    v = TITLE_CACHE.get(key)
    if v is not None:
        return v
    try:
        d = http_json(f"https://v3-cinemeta.strem.io/meta/{'series' if is_series else 'movie'}/{imdb}.json", timeout=6)
        v = (d.get("meta") or {}).get("name") or ""
    except Exception:
        v = ""
    TITLE_CACHE.set(key, v)
    return v


def search_subdl(title, imdb, season, episode):
    if not SUBDL_KEY:
        return []
    base = {"api_key": SUBDL_KEY, "languages": "AR", "subs_per_page": 30}
    if season is not None and episode is not None:
        base.update({"season_number": season, "episode_number": episode, "type": "tv"})
    else:
        base["type"] = "movie"

    def q(extra):
        return http_json("https://api.subdl.com/api/v1/subtitles?" + urllib.parse.urlencode({**base, **extra}), timeout=12).get("subtitles") or []

    try:
        subs = q({"imdb_id": imdb})
        if not subs and title:
            subs = q({"film_name": title})
    except Exception as e:
        log.warning("SubDL error: %s", e)
        return []
    out = []
    for s in subs:
        u = s.get("url") or ""
        if u.startswith("/"):
            u = "https://dl.subdl.com" + u
        if not u:
            continue
        item = {"provider": "subdl", "id": s.get("subtitlePage") or u, "name": s.get("release_name") or s.get("name") or "",
                "author": s.get("author") or "", "commentary": s.get("comment") or "", "production_type": "",
                "release_type": "", "all_releases": [s.get("release_name") or ""], "downloads": 0, "rating_good": 0,
                "rating_bad": 0, "preview": "", "download_url": u, "hi": bool(s.get("hi"))}
        if not is_banned(item):
            out.append(item)
    return out


def search_subsource(title, imdb, season, episode):
    if not SUBSOURCE_KEY:
        return []
    hd = {"X-API-Key": SUBSOURCE_KEY}
    try:
        movie_id = None
        d = http_json(f"https://api.subsource.net/api/v1/movies/search?searchType=imdb&imdb={imdb}", hd, 12)
        items = d.get("data") or []
        if season is not None:
            for it in items:
                if it.get("season") == int(season):
                    movie_id = it.get("movieId")
                    break
        if not movie_id and items:
            movie_id = items[0].get("movieId")
        if not movie_id and title:
            d = http_json("https://api.subsource.net/api/v1/movies/search?searchType=text&q=" + urllib.parse.quote(title), hd, 12)
            items = d.get("data") or []
            movie_id = items[0].get("movieId") if items else None
        if not movie_id:
            return []
        d = http_json(f"https://api.subsource.net/api/v1/subtitles?movieId={movie_id}&language=arabic", hd, 12)
    except Exception as e:
        log.warning("SubSource error: %s", e)
        return []
    out = []
    for it in d.get("data") or []:
        sid = it.get("subtitleId")
        rel = it.get("releaseInfo") or []
        contribs = it.get("contributors") or []
        rating = it.get("rating") or {}
        item = {"provider": "subsource", "id": str(sid), "name": rel[0] if rel else f"Subtitle {sid}",
                "author": contribs[0].get("displayname", "") if contribs else "",
                "release_type": it.get("releaseType") or "", "production_type": it.get("productionType") or "",
                "all_releases": rel, "downloads": it.get("downloads", 0), "rating_good": rating.get("good", 0),
                "rating_bad": rating.get("bad", 0), "commentary": it.get("commentary") or "",
                "preview": it.get("preview") or "", "hi": bool(it.get("hearingImpaired", False)),
                "download_url": f"https://api.subsource.net/api/v1/subtitles/{sid}/download"}
        if not is_banned(item):
            out.append(item)
    return out


def search_wyzie(imdb, season, episode):
    if not WYZIE_KEY:
        return []
    params = {"id": imdb, "language": "ar", "key": WYZIE_KEY}
    if season is not None and episode is not None:
        params.update({"season": season, "episode": episode})
    try:
        data = http_json("https://sub.wyzie.io/search?" + urllib.parse.urlencode(params), timeout=12)
    except Exception as e:
        log.warning("Wyzie error: %s", e)
        return []
    out = []
    for s in data if isinstance(data, list) else []:
        u = s.get("url") or ""
        if not u:
            continue
        rel = str(s.get("release") or s.get("media") or "Wyzie")
        item = {"provider": "wyzie", "id": u, "name": rel, "author": str(s.get("source") or ""),
                "commentary": str(s.get("source") or ""), "production_type": "", "release_type": "",
                "all_releases": [rel], "downloads": 0, "rating_good": 0, "rating_bad": 0, "preview": "",
                "download_url": u, "hi": bool(s.get("isHearingImpaired", False))}
        if not is_banned(item):
            out.append(item)
    return out


# ---------- classification & scoring ----------
PLATFORMS = [
    ("Netflix", [r"\bnf\b", r"\bnetflix\b", "نتفلكس", "نتفليكس"]),
    ("iTunes", [r"\bitunes\b", r"\batvp\b", r"\bapple\s*tv\+?\b", "ايتونز", "آيتونز"]),
    ("OSN+", [r"\bosn\+?\b"]),
    ("Amazon", [r"\bamzn\b", r"\bamazon\b", "امازون", "أمازون"]),
    ("Disney+", [r"\bdsnp\b", r"\bdisney\+?\b", "ديزني"]),
    ("Max", [r"\bhmax\b", r"\bhbo\s*max\b"]),
    ("Shahid", [r"\bshahid\b", "شاهد"]),
]
FAN_RE = re.compile(r"(ترجمة\s*وتعديل|ترجمة\s*وتدقيق|تـرجـمـة|فريق|ترجمة\s*:|&)")
OFFICIAL_WORDS = ["ترجمة أصلية", "ترجمة اصلية", "ترجمة المنصة", "ترجمة رسمية", "نسخة أصلية", "retail", "official"]
TRUSTED_TRANSLATORS = ["علي طلال", "ali talal", "dr.ali", "فؤاد الخفاجي", "محمد النعيمي", "حيدر المدني", "haider",
                       "زياد ياسر", "كريم الحاج", "أحمد السيد", "ahmed elsayed", "nizar", "loki"]


def classify(item):
    comm = normalize_fancy(item.get("commentary"))
    name = normalize_fancy(item.get("name"))
    prev = normalize_fancy(item.get("preview"))
    prod = (item.get("production_type") or "").lower()
    official_hit = any(w in comm for w in OFFICIAL_WORDS)
    fan = (bool(FAN_RE.search(comm)) and not official_hit) or bool(FAN_RE.search(prev))
    official = prod == "retail" or official_hit
    plat = None
    for label, pats in PLATFORMS:
        if any(re.search(p, comm) for p in pats):
            plat = label
            break
    if not plat and not fan and item.get("provider") == "subsource" and prod != "translated" and len(name) <= 120:
        for label, pats in PLATFORMS:
            if any(re.search(p, name) for p in pats):
                plat = label
                break
    if not plat and official and not fan:
        plat = "Official-Retail"
    category = "platform" if (plat and (official or (prod != "translated" and not fan))) else "translator"
    if category == "translator":
        plat = None
    return category, plat, (item.get("author") or "").strip() or "Unknown"


def deduce_release_type(name, rels, comm):
    t = (name or "").lower() + " " + " ".join(str(r).lower() for r in (rels or [])) + " " + normalize_fancy(comm)
    bd = any(s in t for s in ("bluray", "blu-ray", "bdrip", "brrip", "remux", "uhd", "framestor", "cinephiles", "epsilon", "fgt", "ctrlhd", "wildcat"))
    wb = any(s in t for s in ("web-dl", "webrip", "web", "atvp", "amzn", "nf", "dsnp", "hmax", "itunes", "flux", "ethel", "ntb"))
    return "both" if (bd and wb) else "bluray" if bd else "web" if wb else "other"


def episode_match(blob, season, episode):
    """exact | pack | conflict | unknown"""
    if episode is None:
        return "exact"
    s_i = int(season) if season else 1
    e_i = int(episode)
    n = normalize_fancy(blob)
    m = re.findall(r"(?:^|[^a-z0-9])s0*(\d{1,2})[._\-\s]*e0*(\d{1,3})(?:[._\-\s]*e?0*(\d{1,3}))?(?:$|[^a-z0-9])", n)
    if m:
        for ms, e1, e2 in m:
            if int(ms) == s_i and int(e1) <= e_i <= int(e2 or e1):
                return "exact"
        return "conflict"
    m = re.findall(r"(?:^|[^a-z0-9])0*(\d{1,2})x0*(\d{1,3})(?:$|[^a-z0-9])", n)
    if m:
        return "exact" if any(int(a) == s_i and int(b) == e_i for a, b in m) else "conflict"
    m = re.findall(r"(?:^|[^a-z0-9])(?:ep|episode|e|حلقة|الحلقة)[._\-\s]*0*(\d{1,3})(?:$|[^a-z0-9])", n)
    if m:
        return "exact" if any(int(x) == e_i for x in m) else "conflict"
    if any(re.search(p, n) for p in (rf"s0*{s_i}\b", rf"season\s*0*{s_i}\b", r"complete", r"pack", "الموسم", "كامل")):
        return "pack"
    return "unknown"


def score_candidates(cands, season, episode, release_hint):
    target = (release_hint or "").lower()
    want_bd = any(k in target for k in ("remux", "bluray", "blu-ray", "uhd", "bdrip", "brrip"))
    want_web = any(k in target for k in ("web", "amzn", "nf", "atvp", "itunes", "dsnp", "hmax"))
    gm = re.search(r"-([a-zA-Z0-9_]{2,15})(?:\.[a-z0-9]{2,4})?$", target)
    group = gm.group(1).lower() if gm else ""
    out = []
    for s in cands:
        blob = f"{s.get('name', '')} {' '.join(s.get('all_releases') or [])} {s.get('commentary', '')}"
        ep = episode_match(blob, season, episode)
        if ep == "conflict":
            continue
        s["ep_match"] = ep
        s["category"], s["platform"], s["translator"] = classify(s)
        deduced = deduce_release_type(s.get("name"), s.get("all_releases"), s.get("commentary"))
        raw_rel = (s.get("release_type") or "").lower()
        s["deduced"] = deduced if deduced != "other" else (raw_rel if raw_rel in ("bluray", "web") else "other")

        sc = 0
        if episode is not None:
            sc += 450 if ep == "exact" else 200 if ep == "pack" else 0
        if s["category"] == "platform":
            sc += 1000 + (200 if s.get("production_type") == "retail" else 0)
        else:
            sc += 300
        if want_bd:
            sc += 220 if s["deduced"] in ("bluray", "both") else (-40 if s["deduced"] == "web" else 0)
        elif want_web:
            sc += 220 if s["deduced"] in ("web", "both") else (-40 if s["deduced"] == "bluray" else 0)
        nb = blob.lower()
        if group and len(group) >= 3 and re.search(rf"\b{re.escape(group)}\b", nb):
            sc += 260
        for t in ("amzn", "nf", "netflix", "atvp", "itunes", "dsnp", "hmax", "bluray", "remux", "web-dl", "webrip"):
            if t in target and t in nb:
                sc += 90
        tl = f"{s['translator']} {s.get('author', '')} {s.get('commentary', '')}".lower()
        if any(t in tl for t in TRUSTED_TRANSLATORS):
            sc += 90
        sc += min(int(s.get("downloads", 0)) // 20, 80) + min(int(s.get("rating_good", 0)) * 5, 60)
        if s.get("rating_bad", 0) > s.get("rating_good", 0):
            sc -= 100
        if s.get("hi"):
            sc -= 25
        s["score"] = sc
        out.append(s)
    out.sort(key=lambda x: x["score"], reverse=True)
    return out


def search_candidates(imdb, season, episode, release_hint):
    key = (imdb, season, episode)
    raw = SEARCH_CACHE.get(key)
    if raw is None:
        title = get_title(imdb, season is not None)
        with ThreadPoolExecutor(3) as pool:
            futs = [pool.submit(search_subdl, title, imdb, season, episode),
                    pool.submit(search_subsource, title, imdb, season, episode),
                    pool.submit(search_wyzie, imdb, season, episode)]
            raw = []
            for f in futs:
                try:
                    raw.extend(f.result())
                except Exception:
                    pass
        SEARCH_CACHE.set(key, raw)
    return score_candidates([dict(x) for x in raw], season, episode, release_hint)


# ======================================================================================
# Subtitle download + normalization (zip/ass/vtt -> clean UTF-8 SRT with RTL fixes)
# ======================================================================================
TS_LINE = re.compile(r"(\d{2}):(\d{2}):(\d{2})[,.](\d{3})\s*-->\s*(\d{2}):(\d{2}):(\d{2})[,.](\d{3})")
AR_RE = re.compile(r"[\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF]")
_SS_SEM = threading.Semaphore(2)
_SS_LOCK = threading.Lock()
_SS_LAST = [0.0]


def clean_ads(text):
    blocks = re.split(r"\n\s*\n", text.strip())
    out, n = [], 1
    for b in blocks:
        if AD_RE.search(b):
            continue
        lines = b.splitlines()
        if len(lines) >= 2 and lines[0].strip().isdigit() and TS_LINE.search(lines[1]):
            lines[0] = str(n)
            n += 1
        out.append("\n".join(lines))
    return "\n\n".join(out) + "\n"


def fix_rtl(text):
    RLM, RLE, PDF = "\u200f", "\u202b", "\u202c"
    trailing = re.compile(r"([.!?؟:;،,\-'\"\)\]\}]+)$")
    leading = re.compile(r"^([.!؟:;،,]+)\s*([\u0600-\u06FF].*)")
    out = []
    for line in text.split("\n"):
        s = line.strip()
        if not s or s.isdigit() or TS_LINE.search(s) or not AR_RE.search(s):
            out.append(line)
            continue
        l = line.strip(" \t\u200e\u200f\u202a\u202b\u202c\u2066\u2067\u2069")
        m = leading.match(l)
        if m and m.group(1) != "...":
            l = f"{m.group(2)}{m.group(1)}"
        if l[:1] in ("-", "–", "—"):
            l = f"{RLM}{l[0]} {l[1:].strip()}"
        if trailing.search(l) and not l.endswith(RLM):
            l += RLM
        out.append(f"{RLE}{l}{PDF}")
    return "\n".join(out)


def vtt_to_srt(vtt):
    lines, out, n, i = vtt.splitlines(), [], 1, 0
    while i < len(lines):
        if "-->" in lines[i]:
            out += [str(n), re.sub(r"(\d{2}:\d{2}:\d{2})\.(\d{3})", r"\1,\2", lines[i].strip())]
            n += 1
            i += 1
            while i < len(lines) and lines[i].strip():
                out.append(re.sub(r"<[^>]+>", "", lines[i]))
                i += 1
            out.append("")
        i += 1
    return "\n".join(out)


def ass_to_srt(ass):
    def t2ms(t):
        m = re.match(r"(\d+):(\d{2}):(\d{2})\.(\d{2})", t.strip())
        return 0 if not m else ((int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3))) * 1000 + int(m.group(4)) * 10)

    in_ev, fields, cues = False, [], []
    for line in ass.splitlines():
        s = line.strip()
        if s.lower() == "[events]":
            in_ev = True
            continue
        if not in_ev:
            continue
        if s.startswith("[") and s.endswith("]"):
            break
        if s.lower().startswith("format:"):
            fields = [f.strip().lower() for f in s[7:].split(",")]
        elif s.lower().startswith("dialogue:") and fields:
            vals = s[9:].split(",", len(fields) - 1)
            if len(vals) == len(fields):
                row = dict(zip(fields, vals))
                st, et = t2ms(row.get("start", "")), t2ms(row.get("end", ""))
                txt = re.sub(r"\{[^}]*\}", "", row.get("text", "")).replace("\\N", "\n").replace("\\n", "\n").strip()
                if txt and et > st:
                    cues.append((st, et, txt))
    cues.sort()
    return "\n".join(f"{i}\n{fmt_ts(a)} --> {fmt_ts(b)}\n{t}\n" for i, (a, b, t) in enumerate(cues, 1))


def fmt_ts(ms):
    ms = max(0, int(round(ms)))
    return f"{ms // 3600000:02d}:{(ms % 3600000) // 60000:02d}:{(ms % 60000) // 1000:02d},{ms % 1000:03d}"


def decode_bytes(raw):
    if raw.startswith((b"\xff\xfe", b"\xfe\xff")):
        return raw.decode("utf-16", errors="replace")
    for enc in ("utf-8-sig", "cp1256"):
        try:
            return raw.decode(enc)
        except Exception:
            continue
    return raw.decode("utf-8", errors="replace")


def pick_zip_entry(names, season, episode):
    media = [n for n in names if n.lower().endswith((".srt", ".ass", ".ssa", ".vtt"))
             and not n.startswith("__MACOSX") and not os.path.basename(n).startswith(".")]
    srt = [n for n in media if n.lower().endswith(".srt")]
    pool = srt or media
    if not pool:
        return None
    if episode is None:
        return pool[0]
    s_i, e_i = int(season or 1), int(episode)
    pats = [rf"(?:^|[^a-zA-Z0-9])[sS]0*{s_i}[._\-\s]*[eE]0*{e_i}(?!\d)", rf"(?:^|[^0-9])0*{s_i}[xX]0*{e_i}(?!\d)",
            rf"(?:^|[^a-zA-Z0-9])[eE][pP]?[._\-\s]*0*{e_i}(?!\d)", rf"(?:episode|حلقة|الحلقة)[._\-\s]*0*{e_i}(?!\d)",
            rf"(?:^|[/\\._\-\s])0*{e_i:02d}(?=\.(?:srt|ass|ssa|vtt)$)"]
    for p in pats:
        for n in pool:
            if re.search(p, n, re.I):
                return n
    if len(pool) == 1 and episode_match(pool[0], s_i, e_i) != "conflict":
        return pool[0]
    return None  # season pack without our episode


def download_raw_text(cand, season, episode):
    headers = {"X-API-Key": SUBSOURCE_KEY} if cand.get("provider") == "subsource" else {}
    raw = http_get(cand["download_url"], headers, 20)
    if raw.startswith(b"PK\x03\x04"):
        z = zipfile.ZipFile(io.BytesIO(raw))
        entry = pick_zip_entry(z.namelist(), season, episode)
        if not entry:
            return None
        raw = z.read(entry)
    text = decode_bytes(raw).replace("\r\r\n", "\n").replace("\r\n", "\n").replace("\r", "\n")
    if "[Events]" in text and "Dialogue:" in text:
        text = ass_to_srt(text)
    elif text.lstrip().startswith("WEBVTT"):
        text = vtt_to_srt(text)
    text = re.sub(r"\{\\[^}]*\}", "", text)
    text = fix_rtl(clean_ads(text))
    letters = re.findall(r"[^\W\d_]", text)
    if len(text.strip()) < 100 or not letters:
        return None
    if len(AR_RE.findall(text)) / float(len(letters)) < 0.4:  # not really Arabic
        return None
    return text


def get_sub_text(cand, season, episode):
    key = (cand.get("provider"), str(cand.get("id")), season, episode)
    t = SUB_TEXT_CACHE.get(key)
    if t:
        return t
    try:
        if cand.get("provider") == "subsource":  # be gentle with SubSource rate limits
            with _SS_SEM:
                with _SS_LOCK:
                    wait = 0.22 - (time.time() - _SS_LAST[0])
                    if wait > 0:
                        time.sleep(wait)
                    _SS_LAST[0] = time.time()
                t = download_raw_text(cand, season, episode)
        else:
            t = download_raw_text(cand, season, episode)
    except Exception as e:
        log.info("Sub download failed (%s): %s", cand.get("provider"), e)
        t = None
    if t:
        SUB_TEXT_CACHE.set(key, t)
    return t


def parse_cues(text):
    cues = []
    for m in TS_LINE.finditer(text):
        h1, m1, s1, ms1, h2, m2, s2, ms2 = (int(x) for x in m.groups())
        st = h1 * 3600 + m1 * 60 + s1 + ms1 / 1000.0
        et = h2 * 3600 + m2 * 60 + s2 + ms2 / 1000.0
        if st >= 0.5 and et > st:
            cues.append((st, et))
    return cues


def dialogue_signature(text):
    credit = re.compile(r"(ترجمة|تعديل|تدقيق|إعداد|مزامنة|رفع|فريق|subsource|subdl|@|http|www\.)", re.I)
    lines = []
    for ln in text.splitlines():
        s = ln.strip()
        if not s or s.isdigit() or TS_LINE.search(s):
            continue
        s = re.sub(r"<[^>]*>|\{[^}]*\}", "", s)
        if credit.search(s):
            continue
        words = re.findall(r"[\u0621-\u064A]+", s)
        if len(words) >= 2:
            n = "".join(words)
            n = re.sub(r"[أإآ]", "ا", n).replace("ة", "ه").replace("ى", "ي")
            if len(n) >= 5:
                lines.append(n)
    core = lines[2:-2] if len(lines) > 10 else lines
    step = max(1, len(core) // 120)
    return {"hash": hashlib.md5("|".join(core[:80]).encode()).hexdigest() if core else "",
            "sample": set(core[::step]), "count": len(lines)}


def is_dup(a, b, thr=0.82):
    if a["hash"] and a["hash"] == b["hash"]:
        return True
    if not a["sample"] or not b["sample"]:
        return False
    small = min(len(a["sample"]), len(b["sample"]))
    if small < 3:
        return a["sample"] == b["sample"]
    return len(a["sample"] & b["sample"]) / float(small) >= thr


# ======================================================================================
# Reference timings from the video (ffprobe): embedded text subs or PGS display sets
# ======================================================================================
def resolve_redirect(url):
    try:
        req = urllib.request.Request(url, headers={**UA, "Range": "bytes=0-1"})
        with urllib.request.urlopen(req, timeout=8) as r:
            return r.geturl() or url
    except Exception:
        return url


def ffprobe_json(args, timeout):
    try:
        p = subprocess.run([FFPROBE, "-v", "quiet", "-print_format", "json"] + args, capture_output=True,
                           text=True, timeout=timeout, encoding="utf-8", errors="replace")
        if p.returncode == 0 and p.stdout:
            return json.loads(p.stdout)
    except Exception:
        pass
    return None


def build_windows(duration):
    d = duration if duration and duration > 300 else 6000.0
    wins = [(8.0, min(130.0, d * 0.15))]
    for frac in (0.25, 0.52, 0.78):
        s = float(round(d * frac))
        e = min(d - 30.0, s + 110.0)
        if e - s >= 45.0 and s > wins[-1][1] + 30.0:
            wins.append((s, e))
    return wins


def extract_ref_timestamps(media_url):
    if not FFPROBE or not media_url or not media_url.startswith("http"):
        return None
    url = resolve_redirect(media_url)
    info = ffprobe_json(["-show_format", "-show_streams", url], 25)
    if not info:
        return None
    fmt, streams = info.get("format") or {}, info.get("streams") or []
    duration = float(fmt.get("duration") or 0)
    fps, subs = 23.976, []
    for st in streams:
        if st.get("codec_type") == "video" and fps == 23.976:
            r = st.get("r_frame_rate") or ""
            if "/" in r:
                a, b = r.split("/", 1)
                try:
                    if float(b) > 0:
                        fps = round(float(a) / float(b), 3)
                except Exception:
                    pass
        elif st.get("codec_type") == "subtitle":
            subs.append(st)

    text_codecs = {"subrip", "srt", "ass", "ssa", "mov_text", "webvtt", "text", "subviewer"}
    best = None
    for pos, st in enumerate(subs):
        codec = str(st.get("codec_name") or "").lower()
        tags = st.get("tags") or {}
        lang = str(tags.get("language") or "").lower()
        title = str(tags.get("title") or "").lower()
        if (st.get("disposition") or {}).get("forced") == 1 or any(w in title for w in ("forced", "commentary", "signs")):
            continue
        is_text, is_bmp = codec in text_codecs, codec == "hdmv_pgs_subtitle"
        if not (is_text or is_bmp):
            continue
        rank = (0 if is_text else 1, 0 if lang in ("eng", "en") else 1 if lang in ("ara", "ar") else 2)
        if best is None or rank < best[0]:
            best = (rank, pos, is_bmp)
    if best is None:
        return None
    _, pos, is_bmp = best
    windows = build_windows(duration)

    def probe(win):
        ws, we = win
        d = ffprobe_json(["-select_streams", f"s:{pos}", "-show_packets", "-show_entries", "packet=pts_time,size",
                          "-read_intervals", f"{int(ws)}%+{int(we - ws)}", url], 35)
        return (d or {}).get("packets") or []

    pkts = []
    with ThreadPoolExecutor(max_workers=3) as pool:
        for res in pool.map(probe, windows):
            pkts.extend(res)
    max_t = duration + 60 if duration else 14400.0
    vals = []
    for p in pkts:
        try:
            t = float(p.get("pts_time"))
            if is_bmp and int(p.get("size") or 0) < 120:  # tiny PGS packets are "clear" events
                continue
            if 1.0 <= t <= max_t:
                vals.append(t)
        except Exception:
            continue
    clean = []
    for v in sorted(vals):
        if not clean or v - clean[-1] > 0.30:
            clean.append(v)
    if len(clean) < 12:
        return None
    return {"times": clean, "windows": windows, "duration": duration, "fps": fps}


def get_ref_data(media_url, is_series=False):
    """Shared, de-duplicated, cached extraction (used by /stream pre-warm and /subtitles)."""
    if not FFPROBE or not media_url or not media_url.startswith("http"):
        return None
    c = REF_OK.get(media_url)
    if c is not None:
        return c["data"]
    if REF_FAIL.get(media_url) is not None:
        return None
    with INFLIGHT_LOCK:
        entry = INFLIGHT.get(media_url)
        owner = entry is None
        if owner:
            entry = {"ev": threading.Event(), "data": None}
            INFLIGHT[media_url] = entry
    if owner:
        try:
            data = extract_ref_timestamps(media_url)
        except Exception as e:
            log.info("ref extraction failed: %s", e)
            data = None
        entry["data"] = data
        (REF_OK if data else REF_FAIL).set(media_url, {"data": data} if data else True)
        entry["ev"].set()
        with INFLIGHT_LOCK:
            INFLIGHT.pop(media_url, None)
        return data
    entry["ev"].wait(timeout=60)
    return entry["data"]


def ref_with_deadline(url, is_series, wait):
    if not url or not FFPROBE:
        return None
    box = {}
    t = threading.Thread(target=lambda: box.setdefault("d", get_ref_data(url, is_series)), daemon=True)
    t.start()
    t.join(wait)
    return box.get("d")


# ======================================================================================
# Sync solver: natural / constant / FPS-affine / piecewise
# ======================================================================================
def window_offset(ref_w, sub_w, ws, we, max_shift=75.0, tol=0.5):
    """Best constant offset (ref - sub) inside one window, with a significance test."""
    if len(ref_w) < 5 or len(sub_w) < 5:
        return None
    bins = Counter()
    for r in ref_w:
        for s in sub_w:
            d = r - s
            if -max_shift <= d <= max_shift:
                bins[int(round(d * 10))] += 1
    if not bins:
        return None
    total = sum(bins.values())
    best_c, best_v = None, 0
    for c in bins:
        v = sum(bins.get(c + k, 0) for k in range(-3, 4))
        if v > best_v:
            best_c, best_v = c, v
    mean_v = total / float(int(2 * max_shift * 10) + 1) * 7.0
    if best_v < max(8, 2.5 * mean_v):
        return None
    center = best_c / 10.0
    diffs = sorted(r - s for r in ref_w for s in sub_w if abs((r - s) - center) <= 0.35)
    if not diffs:
        return None
    off = diffs[len(diffs) // 2]
    sub_in = [s for s in sub_w if ws <= s + off <= we]
    if len(sub_in) < 5:
        return None
    inl = sum(1 for s in sub_in if nearest_dist(ref_w, s + off) <= tol)
    if inl < 5 or inl / float(len(sub_in)) < 0.30:
        return None
    return {"off": off, "inl": inl, "ws": ws, "we": we, "center_sub": 0.5 * (ws + we) - off}


def eval_transform(ref_data, starts, fn, tol=0.5):
    tr = [fn(s) for s in starts]
    ref = ref_data["times"]
    total = ok = 0
    for ws, we in ref_data["windows"]:
        ref_w = [r for r in ref if ws <= r <= we]
        if len(ref_w) < 5:
            continue
        sub_w = [t for t in tr if ws <= t <= we]
        if len(sub_w) < 5:
            continue
        inl = sum(1 for t in sub_w if nearest_dist(ref_w, t) <= tol)
        null = 1.0 - math.exp(-2.0 * tol * len(ref_w) / max(1.0, we - ws))
        if inl >= 5 and inl / float(len(sub_w)) >= max(0.40, null + 0.20):
            ok += 1
        total += inl
    return total, ok


def make_fn(mode, a, b, segs):
    if mode == "piecewise":
        bounds = [s[0] for s in segs]
        offs = [s[1] for s in segs]

        def f(t):
            return t + offs[max(bisect.bisect_right(bounds, t) - 1, 0)]
        return f
    return lambda t: a * t + b


def solve_sync(ref_data, cues):
    none = {"mode": "none", "tier": 2, "label": "", "fn": None}
    if not ref_data or len(cues) < 10:
        return none
    starts = [c[0] for c in cues]
    ref = ref_data["times"]
    windows = ref_data["windows"]
    nwin = sum(1 for ws, we in windows if sum(1 for r in ref if ws <= r <= we) >= 5)
    if nwin == 0:
        return none

    stats = []
    for ws, we in windows:
        ref_w = [r for r in ref if ws <= r <= we]
        st = window_offset(ref_w, [s for s in starts if ws - 80 <= s <= we + 80], ws, we)
        if st:
            stats.append(st)
    stats.sort(key=lambda x: x["ws"])

    cands = [("natural", 1.0, 0.0, None, 0)]
    offs = set(round(s["off"], 2) for s in stats)
    if stats:
        wsum = sum(s["inl"] for s in stats)
        offs.add(round(sum(s["off"] * s["inl"] for s in stats) / wsum, 2))
    for b in offs:
        if abs(b) >= 0.12:
            cands.append(("constant", 1.0, b, None, 3))

    # FPS-ratio candidates (offset estimated on the first two usable windows)
    ratios = [25 / 23.976, 23.976 / 25, 24 / 23.976, 23.976 / 24, 25 / 24, 24 / 25]
    usable = [(ws, we) for ws, we in windows if sum(1 for r in ref if ws <= r <= we) >= 5][:2]
    for a in ratios:
        for ws, we in usable:
            ref_w = [r for r in ref if ws <= r <= we]
            sw = [a * s for s in starts if ws - 80 <= a * s <= we + 80]
            r = window_offset(ref_w, sw, ws, we)
            if r:
                cands.append(("affine", a, round(r["off"], 3), None, 8))
    # Empirical drift from first/last verified window
    if len(stats) >= 2:
        s1, s2 = stats[0], stats[-1]
        dt = s2["center_sub"] - s1["center_sub"]
        if dt >= 250.0:
            m = (s2["off"] - s1["off"]) / dt
            b = s1["off"] - m * s1["center_sub"]
            if abs(m) <= 0.05 and abs(b) <= 40.0:
                cands.append(("affine", 1.0 + m, b, None, 8))
    # Piecewise (act-break differences)
    if len(stats) >= 2 and (max(s["off"] for s in stats) - min(s["off"] for s in stats)) >= 0.60:
        segs = [(-1e9, stats[0]["off"])]
        valid = True
        for i in range(1, len(stats)):
            prev_end = stats[i - 1]["we"] - stats[i - 1]["off"]
            cur_start = stats[i]["ws"] - stats[i]["off"]
            bound, gap_best = 0.5 * (prev_end + cur_start), 0.0
            for k in range(len(cues) - 1):
                e0, s1_ = cues[k][1], cues[k + 1][0]
                if prev_end - 20 <= e0 <= cur_start + 20 and s1_ - e0 > gap_best:
                    gap_best, bound = s1_ - e0, 0.5 * (e0 + s1_)
            if bound <= segs[-1][0]:
                valid = False
                break
            segs.append((bound, stats[i]["off"]))
        if valid:
            cands.append(("piecewise", 1.0, 0.0, segs, 10))

    best = None
    for mode, a, b, segs, pen in cands:
        fn = make_fn(mode, a, b, segs)
        inl, ok = eval_transform(ref_data, starts, fn)
        key = (ok, inl - pen)
        if best is None or key > best[0]:
            best = (key, mode, a, b, segs, fn, ok)
    _, mode, a, b, segs, fn, ok = best
    if not (ok >= 1 and ok >= min(2, nwin)):
        return none
    if mode == "natural" or (mode == "constant" and abs(b) < 0.35):
        tier, label = 0, "✅ متزامنة"
    elif mode == "constant":
        tier, label = 1, f"🔄 تمت المزامنة ({b:+.1f}s)"
    elif mode == "affine":
        tier, label = 1, "🔄 تمت المزامنة (FPS + توقيت)"
    else:
        tier, label = 1, "🔄 تمت المزامنة (متعددة الفصول)"
    return {"mode": mode, "tier": tier, "label": label, "fn": fn}


def apply_model(text, model):
    fn = model.get("fn")
    if not fn or model.get("mode") in ("none", "natural"):
        return text

    def _shift(m):
        h1, m1, s1, ms1, h2, m2, s2, ms2 = (int(x) for x in m.groups())
        st = h1 * 3600 + m1 * 60 + s1 + ms1 / 1000.0
        et = h2 * 3600 + m2 * 60 + s2 + ms2 / 1000.0
        ns = max(0.0, fn(st))
        ne = max(ns + 0.45, fn(et))
        return f"{fmt_ts(ns * 1000)} --> {fmt_ts(ne * 1000)}"
    return TS_LINE.sub(_shift, text)


# ======================================================================================
# Subtitle selection pipeline
# ======================================================================================
def evaluate_candidate(cand, ref_data, season, episode):
    text = get_sub_text(cand, season, episode)
    if not text:
        return None
    sig = dialogue_signature(text)
    if sig["count"] < 10:
        return None
    model = solve_sync(ref_data, parse_cues(text)) if ref_data else {"mode": "none", "tier": 2, "label": "", "fn": None}
    out = apply_model(text, model) if model["tier"] <= 1 else text
    label = model["label"] or ("⚠️ غير مؤكدة" if ref_data else "")
    return {"cand": cand, "tier": model["tier"], "label": label, "sig": sig,
            "bytes": ("\ufeff" + out.lstrip("\ufeff")).encode("utf-8")}


def resolve_sub_bytes(token):
    item = SUB_CACHE.get(token)
    if not item:
        return None
    if item.get("bytes"):
        return item["bytes"]
    ref = ref_with_deadline(item.get("cdn_url"), item.get("is_series"), 30)
    r = evaluate_candidate(item["cand"], ref, item["season"], item["episode"])
    if r:
        item["bytes"] = r["bytes"]
        return r["bytes"]
    return None


def make_sub_entry(c, label, data, base, season, episode, cdn_url, pos):
    token = uuid.uuid4().hex
    SUB_CACHE.set(token, {"cand": c, "bytes": data, "season": season, "episode": episode,
                          "cdn_url": cdn_url, "is_series": season is not None})
    trans = re.sub(r"\s+", " ", normalize_fancy_keep(c.get("translator") or c.get("author") or "")).strip()
    parts = [p for p in (label, (c.get("provider") or "").upper(), c.get("platform") or trans or (c.get("name") or "")[:28]) if p]
    return {"id": f"tx-{token[:12]}", "lang": "ara", "url": f"{base}/sub/{token}.srt",
            "label": "[TorrentX] " + (" • ".join(parts) if parts else f"Arabic #{pos + 1}")}


def normalize_fancy_keep(s):
    import html
    return html.unescape(str(s))


def select_subtitles(media_id, filename, base):
    t0 = time.time()
    ids = media_id.split(":")
    imdb = ids[0]
    season = int(ids[1]) if len(ids) > 1 and ids[1].isdigit() else None
    episode = int(ids[2]) if len(ids) > 2 and ids[2].isdigit() else None
    is_series = season is not None and episode is not None
    if not is_series:
        season = episode = None

    # Which stream is being played -> release hint + CDN url for reference timings
    release_hint, cdn_url = filename or "", None
    items = STREAM_META.get(media_id) or []
    if items:
        chosen = items[0]
        if filename:
            fl = filename.lower()
            for it in items:
                tl = (it.get("title") or "").lower()
                if tl == fl or fl in tl or tl in fl:
                    chosen = it
                    break
        release_hint = filename or chosen.get("title") or ""
        cdn_url = chosen.get("url") or None

    candidates = search_candidates(imdb, season, episode, release_hint)
    if not candidates:
        return []

    remaining = max(3.0, SUB_BUDGET - (time.time() - t0))
    ref = ref_with_deadline(cdn_url, is_series, min(REF_WAIT, remaining))

    pool_size = 6 if ref else 0
    results = []
    if pool_size:
        # mix providers: top 3 SubSource + top 3 SubDL + others, keep metadata order
        ss = [c for c in candidates if c["provider"] == "subsource"][:3]
        sd = [c for c in candidates if c["provider"] == "subdl"][:3]
        ot = [c for c in candidates if c["provider"] not in ("subsource", "subdl")][:2]
        pool_c = sorted(ss + sd + ot, key=lambda c: c["score"], reverse=True)[:pool_size]
        budget = max(4.0, SUB_BUDGET - (time.time() - t0))
        ex = ThreadPoolExecutor(max_workers=4)
        futs = [ex.submit(evaluate_candidate, c, ref, season, episode) for c in pool_c]
        try:
            for f in as_completed(futs, timeout=budget):
                try:
                    r = f.result()
                    if r:
                        results.append(r)
                except Exception:
                    pass
        except FutTimeout:
            log.info("subtitle evaluation budget exhausted")
        ex.shutdown(wait=False, cancel_futures=True)

    if results:
        # verified (tier 0/1) first, then by metadata score (+ bonus for no-shift-needed)
        results.sort(key=lambda r: (0 if r["tier"] <= 1 else 1, -(r["cand"]["score"] + (60 if r["tier"] == 0 else 0))))
        picked, sigs = [], []
        for r in results:
            if any(is_dup(r["sig"], s) for s in sigs if r["sig"]["sample"]):
                continue
            sigs.append(r["sig"])
            picked.append(r)
            if len(picked) >= SUB_COUNT:
                break
        return [make_sub_entry(r["cand"], r["label"], r["bytes"], base, season, episode, cdn_url, i)
                for i, r in enumerate(picked)]

    # No reference available in time -> metadata ranking, sync lazily when the player downloads the file
    return [make_sub_entry(c, "", None, base, season, episode, cdn_url, i) for i, c in enumerate(candidates[:SUB_COUNT])]


# ======================================================================================
# HTTP server (no frontend)
# ======================================================================================
def build_manifest():
    mode = f"{DEBRID_SERVICE.upper()} مخزّن" if DEBRID_MODE else "P2P"
    return {
        "id": "com.torrentx.personal",
        "version": "3.0.0",
        "name": f"TorrentX ({mode})",
        "description": "أفضل نسخ الأفلام والمسلسلات بترتيب صارم (Remux > WEB-DL) مع أفضل ترجمة عربية متزامنة تلقائياً (SubDL + SubSource).",
        "resources": ["stream", {"name": "subtitles", "types": ["movie", "series"], "idPrefixes": ["tt"]}],
        "types": ["movie", "series"],
        "idPrefixes": ["tt"],
        "catalogs": [],
        "behaviorHints": {"configurable": False, "configurationRequired": False},
    }


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass

    def _cors(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "*")

    def _send(self, data, ctype, status=200, head=False):
        try:
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self._cors()
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            if not head:
                self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _json(self, obj, status=200, head=False):
        self._send(json.dumps(obj, ensure_ascii=False).encode("utf-8"), "application/json; charset=utf-8", status, head)

    def do_OPTIONS(self):
        self.send_response(204)
        self._cors()
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_HEAD(self):
        self._route(True)

    def do_GET(self):
        self._route(False)

    def _base(self):
        if PUBLIC_URL:
            return PUBLIC_URL.rstrip("/")
        proto = (self.headers.get("X-Forwarded-Proto") or "http").split(",")[0].strip()
        host = self.headers.get("X-Forwarded-Host") or self.headers.get("Host") or f"127.0.0.1:{PORT}"
        return f"{proto}://{host}"

    def _route(self, head):
        try:
            parsed = urllib.parse.urlparse(self.path)
            raw_parts = [p for p in parsed.path.strip("/").split("/") if p]
            parts = [urllib.parse.unquote(p) for p in raw_parts]

            if not parts or parts == ["health"]:
                return self._send(b"TorrentX addon is running", "text/plain; charset=utf-8", head=head)

            # Subtitle files: unguessable 128-bit token
            if parts[0] == "sub" and len(parts) == 2:
                data = resolve_sub_bytes(parts[1].replace(".srt", ""))
                if not data:
                    return self._send(b"", "text/plain", 404, head)
                return self._send(data, "application/x-subrip; charset=utf-8", head=head)

            if SECRET:
                if parts[0] != SECRET:
                    return self._json({"error": "Not found"}, 404, head)
                parts, raw_parts = parts[1:], raw_parts[1:]

            if parts == ["manifest.json"]:
                return self._json(build_manifest(), head=head)

            if len(parts) == 3 and parts[0] == "stream" and parts[2].endswith(".json"):
                streams = build_streams(parts[1], parts[2][:-5])
                return self._json({"streams": streams}, head=head)

            if len(parts) >= 3 and parts[0] == "subtitles":
                media_id = parts[2][:-5] if (len(parts) == 3 and parts[2].endswith(".json")) else parts[2]
                filename = None
                if len(parts) > 3:
                    extra = "/".join(raw_parts[3:])
                    extra = extra[:-5] if extra.endswith(".json") else extra
                    filename = (urllib.parse.parse_qs(extra).get("filename") or [None])[0]
                if not filename:
                    filename = (urllib.parse.parse_qs(parsed.query).get("filename") or [None])[0]
                subs = select_subtitles(media_id, filename, self._base())
                return self._json({"subtitles": subs}, head=head)

            return self._json({"error": "Not found"}, 404, head)
        except Exception as e:
            log.exception("request failed: %s", e)
            return self._json({"error": "internal"}, 500, head)


if __name__ == "__main__":
    if not FFPROBE:
        log.warning("ffprobe not found: subtitles will be ranked by metadata only (no auto-sync). Use the Dockerfile.")
    if not (SUBDL_KEY or SUBSOURCE_KEY or WYZIE_KEY):
        log.warning("No subtitle API keys configured.")
    if not SECRET:
        log.warning("ADDON_SECRET is empty: anyone with the URL can use your debrid key. Set it!")
    log.info("Mode: %s | port %s", f"DEBRID/{DEBRID_SERVICE}" if DEBRID_MODE else "P2P", PORT)
    srv = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    srv.daemon_threads = True
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        srv.server_close()

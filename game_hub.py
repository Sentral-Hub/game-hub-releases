"""
Game Hub - one beautiful library for every game installed on this PC.

Finds installed games from: Steam, Epic, GOG, Ubisoft Connect, EA app,
Battle.net, Riot, Amazon Games, Xbox / Game Pass, plus games you add by hand.

Play time:
  * Steam       - total, last 2 weeks and last played, read from Steam's own files
  * GOG Galaxy  - total and last played, read from Galaxy's local database
  * Everything  - Game Hub watches which installed games are running and logs
    else           sessions itself (total, last 2 weeks, last played)

It only READS launcher data - it never changes your launchers or games.
Your library data is saved to %APPDATA%\\GameHub\\library.json

Setup (once):   pip install pywebview pystray pillow
Run:            python game_hub.py        (or double-click "Start Game Hub.bat")
"""
import base64
import ctypes
import glob
import hashlib
import html as htmllib
import json
import platform
import struct
import mimetypes
import os
import re
import shutil
import sqlite3
import string
import subprocess
import sys
import threading
import time
import webbrowser
from datetime import datetime, timezone
import difflib
from urllib.parse import quote, urlencode
from urllib.error import HTTPError
from urllib.request import HTTPSHandler, ProxyHandler, Request, build_opener, pathname2url, urlopen

try:
    import winreg
except ImportError:  # not on Windows
    winreg = None

try:
    import webview
except ImportError:
    webview = None

try:
    import pystray
    from PIL import Image, ImageDraw
except Exception:
    pystray = None

APP_NAME = "Game Hub"
APPDATA = os.environ.get("APPDATA", os.path.expanduser("~"))
PROGRAMDATA = os.environ.get("PROGRAMDATA", r"C:\ProgramData")
DATA_DIR = os.path.join(APPDATA, "GameHub")
DATA_FILE = os.path.join(DATA_DIR, "library.json")
ART_DIR = os.path.join(DATA_DIR, "covers")
UA = "GameHub/1.0 (personal game library app)"
ART_VERSION = 2   # bump to re-fetch art (v2 added hero banners + logos)
VERSION = "0.025"
DEFAULT_UPDATE_URL = __import__("base64").b64decode("aHR0cHM6Ly9naXRodWIuY29tL1NlbnRyYWwtSHViL2dhbWUtaHViLXJlbGVhc2VzL2Jsb2IvbWFpbi9nYW1lX2h1Yi5weQ==").decode()
WHATS_NEW = "More personality: a greeting on Home, badges your games earn from play time, a Miss these? row for old favorites, and livelier loading, toasts and favorites."
PID_FILE = os.path.join(DATA_DIR, "running.pid")
INSTALL_DIR = os.path.join(os.environ.get("LOCALAPPDATA", APPDATA), "Programs", "Game Hub")
UNINSTALL_KEY = r"Software\Microsoft\Windows\CurrentVersion\Uninstall\GameHub"
# The downloadable installer (GameHubSetup.exe, built with Inno Setup) registers under its own key
SETUP_KEY = r"Software\Microsoft\Windows\CurrentVersion\Uninstall\{B6F1C2E4-7A3D-4C59-9E21-5D8A6F3B0C71}_is1"
POLL_SECONDS = 15
MIN_SESSION = 30          # seconds; shorter runs are ignored
TWO_WEEKS = 14 * 86400


# ======================================================================= registry helpers
def _view(flag):
    return getattr(winreg, flag, 0) if winreg else 0


def reg_get(root, path, name, view=0):
    if not winreg:
        return None
    try:
        with winreg.OpenKey(root, path, 0, winreg.KEY_READ | view) as k:
            return winreg.QueryValueEx(k, name)[0]
    except OSError:
        return None


def reg_subkeys(root, path, view=0):
    """Yield (subkey_name, {value_name: data}) for every subkey of path."""
    if not winreg:
        return
    try:
        key = winreg.OpenKey(root, path, 0, winreg.KEY_READ | view)
    except OSError:
        return
    with key:
        i = 0
        while True:
            try:
                sub = winreg.EnumKey(key, i)
            except OSError:
                break
            i += 1
            try:
                with winreg.OpenKey(key, sub, 0, winreg.KEY_READ | view) as sk:
                    vals, j = {}, 0
                    while True:
                        try:
                            n, d, _ = winreg.EnumValue(sk, j)
                        except OSError:
                            break
                        vals[n] = d
                        j += 1
                    yield sub, vals
            except OSError:
                continue


def game(gid, name, launcher, path, launch=None, size=None):
    return {"id": gid, "name": (name or os.path.basename(path or "") or "Unknown").strip(),
            "launcher": launcher, "path": path, "launch": launch, "size": size}


def num(x):
    try:
        return int(x)
    except (TypeError, ValueError):
        return 0


# ======================================================================= small caches
_mt_cache = {}


def by_mtime(key, paths, compute):
    """Return compute() but only re-run it when one of `paths` changed on disk."""
    sig = []
    for p in paths:
        try:
            st = os.stat(p)
            sig.append((p, st.st_mtime_ns, st.st_size))
        except OSError:
            sig.append((p, None, None))
    sig = tuple(sig)
    hit = _mt_cache.get(key)
    if hit and hit[0] == sig:
        return hit[1]
    val = compute()
    _mt_cache[key] = (sig, val)
    return val


# ======================================================================= Steam
_steam_root = None


def find_steam_root():
    global _steam_root
    if _steam_root and os.path.isdir(_steam_root):
        return _steam_root
    candidates = []
    if winreg:
        candidates.append(reg_get(winreg.HKEY_CURRENT_USER, r"Software\Valve\Steam", "SteamPath"))
    candidates += [r"C:\Program Files (x86)\Steam", r"C:\Program Files\Steam"]
    _steam_root = next((os.path.normpath(c) for c in candidates if c and os.path.isdir(c)), None)
    return _steam_root


def parse_vdf(text):
    """Minimal parser for Valve's KeyValues text format -> nested dicts."""
    root, stack, key = {}, [], None
    cur = root
    for s, brace in re.findall(r'"((?:\\.|[^"\\])*)"|([{}])', text):
        if brace == "{":
            new = {}
            cur[key if key is not None else ""] = new
            stack.append(cur)
            cur, key = new, None
        elif brace == "}":
            cur = stack.pop() if stack else root
            key = None
        elif key is None:
            key = s
        else:
            cur[key] = s
            key = None
    return root


def ci_get(d, *keys):
    """Case-insensitive nested dict lookup."""
    for k in keys:
        if not isinstance(d, dict):
            return None
        lk = k.lower()
        d = next((v for kk, v in d.items() if kk.lower() == lk), None)
    return d


# Steam appmanifest StateFlags bits
_UPDATING = 256 | 1024 | 8192 | 16384 | 32768 | 65536 | 131072 | 262144 | 524288
_PAUSED, _NEEDS_UPDATE, _BROKEN = 512, 2, 32 | 128


def steam_update_state(fields):
    """'' when ready to play, else 'update' / 'updating' / 'paused' / 'repair'."""
    f = num(fields.get("StateFlags"))
    if f & _UPDATING:
        return "updating"
    if f & _PAUSED:
        return "paused"
    if f & _NEEDS_UPDATE:
        return "update"
    if f & _BROKEN:
        return "repair"
    target, build = fields.get("TargetBuildID", "0"), fields.get("buildid", "0")
    if target not in ("", "0") and target != build and num(fields.get("BytesToDownload")) > num(fields.get("BytesDownloaded")):
        return "update"
    return ""


def steam_update_states():
    """Fresh update state for every installed Steam game (cheap: just re-reads the manifests)."""
    out = {}
    steam = find_steam_root()
    if not steam:
        return out
    libs = {os.path.normcase(steam)}
    try:
        with open(os.path.join(steam, "steamapps", "libraryfolders.vdf"), encoding="utf-8", errors="ignore") as f:
            for p in re.findall(r'"path"\s+"([^"]+)"', f.read()):
                libs.add(os.path.normcase(os.path.normpath(p.replace("\\\\", "\\"))))
    except OSError:
        pass
    for lib in libs:
        for acf in glob.glob(os.path.join(lib, "steamapps", "appmanifest_*.acf")):
            out.update(by_mtime("acf:" + acf, [acf], lambda acf=acf: _acf_state(acf)))
    return out


def _acf_state(acf):
    try:
        with open(acf, encoding="utf-8", errors="ignore") as f:
            fields = {}
            for k, v in re.findall(r'"(\w+)"\s+"([^"]*)"', f.read()):
                fields.setdefault(k, v)
    except OSError:
        return {}
    return {f"steam:{fields['appid']}": steam_update_state(fields)} if fields.get("appid") else {}


def epic_update_states():
    out = {}
    base = os.path.join(PROGRAMDATA, "Epic", "EpicGamesLauncher", "Data", "Manifests")
    for item in glob.glob(os.path.join(base, "*.item")):
        out.update(by_mtime("item:" + item, [item], lambda item=item: _item_state(item)))
    return out


def _item_state(item):
    try:
        with open(item, encoding="utf-8", errors="ignore") as f:
            d = json.load(f)
    except (OSError, ValueError):
        return {}
    return {f"epic:{d['AppName']}": "repair" if d.get("bNeedsValidation") else ""} if d.get("AppName") else {}


def update_states():
    states = {}
    for fn in (steam_update_states, epic_update_states):
        try:
            states.update(fn())
        except Exception as e:
            print(f"{fn.__name__} failed: {e}")
    return states


def library_signature():
    """Folder timestamps that change when launchers add or remove a game (a few stat calls)."""
    dirs = []
    steam = find_steam_root()
    if steam:
        dirs.append(os.path.join(steam, "steamapps"))
        try:
            with open(os.path.join(steam, "steamapps", "libraryfolders.vdf"), encoding="utf-8", errors="ignore") as f:
                dirs += [os.path.join(os.path.normpath(p.replace("\\\\", "\\")), "steamapps")
                         for p in re.findall(r'"path"\s+"([^"]+)"', f.read())]
        except OSError:
            pass
    dirs.append(os.path.join(PROGRAMDATA, "Epic", "EpicGamesLauncher", "Data", "Manifests"))
    dirs.append(os.path.join(os.environ.get("LOCALAPPDATA", ""), "Amazon Games", "Data", "Games", "Sql", "GameInstallInfo.sqlite"))
    dirs.append(os.path.join(APPDATA, "itch", "db", "butler.db"))
    dirs += sorted(_xbox_roots) + sorted(_sa_roots)
    sig = []
    for d in dirs:
        try:
            sig.append((d, os.stat(d).st_mtime_ns))
        except OSError:
            pass
    return tuple(sig)


def scan_steam():
    out = []
    steam = find_steam_root()
    if not steam:
        return out
    libs = {os.path.normcase(steam)}
    try:
        with open(os.path.join(steam, "steamapps", "libraryfolders.vdf"), encoding="utf-8", errors="ignore") as f:
            for p in re.findall(r'"path"\s+"([^"]+)"', f.read()):
                libs.add(os.path.normcase(os.path.normpath(p.replace("\\\\", "\\"))))
    except OSError:
        pass
    skip_names = ("steamworks common", "proton", "steam linux runtime", "steamvr")
    for lib in libs:
        for acf in glob.glob(os.path.join(lib, "steamapps", "appmanifest_*.acf")):
            try:
                with open(acf, encoding="utf-8", errors="ignore") as f:
                    txt = f.read()
            except OSError:
                continue
            fields = {}
            for k, v in re.findall(r'"(\w+)"\s+"([^"]*)"', txt):
                fields.setdefault(k, v)  # first occurrence = top-level value
            appid, name = fields.get("appid"), fields.get("name", "")
            if not appid or appid == "228980" or name.lower().startswith(skip_names):
                continue
            path = os.path.join(lib, "steamapps", "common", fields.get("installdir", ""))
            if not os.path.isdir(path):
                continue
            out.append(game(f"steam:{appid}", name, "Steam", path, f"steam://rungameid/{appid}",
                            num(fields.get("SizeOnDisk")) or None))
    return out


def steam_playtime():
    """{game_id: {total, recent, last, source}} from every Steam user's localconfig.vdf."""
    stats = {}
    steam = find_steam_root()
    if not steam:
        return stats
    for cfg in glob.glob(os.path.join(steam, "userdata", "*", "config", "localconfig.vdf")):
        try:
            with open(cfg, encoding="utf-8", errors="ignore") as f:
                data = parse_vdf(f.read())
        except OSError:
            continue
        apps = ci_get(data, "UserLocalConfigStore", "Software", "Valve", "Steam", "apps")
        if not isinstance(apps, dict):
            continue
        for appid, a in apps.items():
            if not isinstance(a, dict):
                continue
            total = num(ci_get(a, "Playtime")) * 60
            recent = num(ci_get(a, "Playtime2wks")) * 60
            last = num(ci_get(a, "LastPlayed"))
            if not (total or last):
                continue
            s = stats.setdefault(f"steam:{appid}", {"total": 0, "recent": 0, "last": 0, "source": "Steam"})
            s["total"] = max(s["total"], total)
            s["recent"] = max(s["recent"], recent)
            s["last"] = max(s["last"], last)
    return stats


def local_steam_art(appid, stem, ext="jpg"):
    root = find_steam_root()
    if not root:
        return None
    lc = os.path.join(root, "appcache", "librarycache")
    for p in (os.path.join(lc, f"{appid}_{stem}.{ext}"), os.path.join(lc, appid, f"{stem}.{ext}")):
        if os.path.isfile(p):
            return p
    hits = glob.glob(os.path.join(lc, appid, "**", f"{stem}*.{ext}"), recursive=True)
    return hits[0] if hits else None


# ======================================================================= GOG Galaxy
def galaxy_playtime():
    stats = {}
    db = os.path.join(PROGRAMDATA, "GOG.com", "Galaxy", "storage", "galaxy-2.0.db")
    if not os.path.isfile(db):
        return stats
    try:
        con = sqlite3.connect("file:" + pathname2url(db) + "?mode=ro&immutable=1", uri=True, timeout=2)
    except sqlite3.Error:
        return stats

    def gid(release_key):
        plat, _, ident = (release_key or "").partition("_")
        return f"{plat}:{ident}" if plat in ("gog", "steam") and ident else None

    try:
        for key, minutes in con.execute("SELECT releaseKey, minutesInGame FROM GameTimes"):
            g = gid(key)
            if g and minutes:
                s = stats.setdefault(g, {"total": 0, "recent": None, "last": 0, "source": "GOG Galaxy"})
                s["total"] = max(s["total"], num(minutes) * 60)
    except sqlite3.Error:
        pass
    try:
        for key, when in con.execute("SELECT gameReleaseKey, lastPlayedDate FROM LastPlayedDates"):
            g = gid(key)
            if not g or not when:
                continue
            try:
                dt = datetime.fromisoformat(str(when).replace("Z", "+00:00"))
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                ts = int(dt.timestamp())
            except ValueError:
                continue
            s = stats.setdefault(g, {"total": 0, "recent": None, "last": 0, "source": "GOG Galaxy"})
            s["last"] = max(s["last"], ts)
    except sqlite3.Error:
        pass
    con.close()
    return stats


def launcher_playtime():
    stats = {}
    steam = find_steam_root()
    db = os.path.join(PROGRAMDATA, "GOG.com", "Galaxy", "storage", "galaxy-2.0.db")
    sources = ((galaxy_playtime, [db, db + "-wal"]),
               (steam_playtime, glob.glob(os.path.join(steam, "userdata", "*", "config", "localconfig.vdf")) if steam else []))
    for source, files in sources:  # Steam wins for Steam games
        try:
            stats.update(by_mtime(source.__name__, files, source))  # only re-parse when the files change
        except Exception as e:
            print(f"{source.__name__} failed: {e}")
    return stats


# ======================================================================= other launchers
def scan_epic():
    out = []
    base = os.path.join(PROGRAMDATA, "Epic", "EpicGamesLauncher", "Data", "Manifests")
    for item in glob.glob(os.path.join(base, "*.item")):
        try:
            with open(item, encoding="utf-8", errors="ignore") as f:
                d = json.load(f)
        except (OSError, ValueError):
            continue
        loc = d.get("InstallLocation", "")
        cats = d.get("AppCategories") or []
        if not os.path.isdir(loc) or d.get("bIsIncompleteInstall"):
            continue
        if cats and "games" not in cats:
            continue  # plugins, engines, etc.
        if d.get("MainGameAppName") and d.get("MainGameAppName") != d.get("AppName"):
            continue  # DLC
        uri = ("com.epicgames.launcher://apps/{}%3A{}%3A{}?action=launch&silent=true"
               .format(d.get("CatalogNamespace", ""), d.get("CatalogItemId", ""), d.get("AppName", "")))
        g = game(f"epic:{d.get('AppName')}", d.get("DisplayName"), "Epic", loc, uri, d.get("InstallSize") or None)
        g["catalog"], g["ns"] = d.get("CatalogItemId"), d.get("CatalogNamespace")
        out.append(g)
    return out


def scan_gog():
    out = []
    if not winreg:
        return out
    for sub, v in reg_subkeys(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\GOG.com\Games"):
        path = v.get("path", "")
        if not os.path.isdir(path):
            continue
        exe = v.get("exe", "")
        out.append(game(f"gog:{sub}", v.get("gameName"), "GOG", path,
                        exe if exe and os.path.isfile(exe) else None))
    return out


def scan_ubisoft():
    out = []
    if not winreg:
        return out
    for sub, v in reg_subkeys(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Ubisoft\Launcher\Installs"):
        path = os.path.normpath(v.get("InstallDir", "") or "")
        if not os.path.isdir(path):
            continue
        out.append(game(f"ubisoft:{sub}", os.path.basename(path), "Ubisoft", path, f"uplay://launch/{sub}/0"))
    return out


PUBLISHERS = {"electronic arts": "EA app", "blizzard entertainment": "Battle.net", "activision": "Battle.net",
              "riot games": "Riot", "rockstar games": "Rockstar", "wargaming": "Wargaming", "gaijin": "Gaijin",
              "cognosphere": "HoYoPlay", "mihoyo": "HoYoPlay", "hoyoverse": "HoYoPlay", "nexon": "Nexon"}
LAUNCHER_APPS = {"ea app", "origin", "battle.net", "riot client", "riot vanguard", "amazon games",
                 "ea desktop", "ea javascript sdk", "rockstar games launcher", "rockstar games social club",
                 "wargaming.net game center", "wargaming game center", "hoyoplay", "nexon launcher", "gaijin.net agent"}
NOT_GAMES = re.compile(r"\b(launcher|anti-?cheat|easyanticheat|battleye|redistributable|social club|vanguard|"
                       r"game center|updater|uninstaller|sdk|toolkit)\b", re.I)


def _icon_exe(icon):
    if not icon:
        return None
    exe = icon.split(",")[0].strip().strip('"')
    return exe if exe.lower().endswith(".exe") and os.path.isfile(exe) else None


def scan_uninstall_entries():
    out = []
    if not winreg:
        return out
    path = r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall"
    roots = [(winreg.HKEY_LOCAL_MACHINE, _view("KEY_WOW64_64KEY")),
             (winreg.HKEY_LOCAL_MACHINE, _view("KEY_WOW64_32KEY")),
             (winreg.HKEY_CURRENT_USER, 0)]
    for root, view in roots:
        for sub, v in reg_subkeys(root, path, view):
            name = (v.get("DisplayName") or "").strip()
            loc = (v.get("InstallLocation") or "").strip().strip('"')
            if not name or name.lower() in LAUNCHER_APPS or not os.path.isdir(loc) or NOT_GAMES.search(name):
                continue
            pub = (v.get("Publisher") or "").lower()
            launcher = next((l for p, l in PUBLISHERS.items() if pub.startswith(p)), None)
            if not launcher and "amazon game remover" in (v.get("UninstallString") or "").lower():
                launcher = "Amazon"
            if not launcher:
                if _STANDALONE_ON[0]:
                    hit = sa_cached_detect(loc)
                    if hit and (hit.get("exe") or _icon_exe(v.get("DisplayIcon"))):
                        hit = dict(hit, exe=hit.get("exe") or _icon_exe(v.get("DisplayIcon")))
                        g = sa_game(loc, hit, name)
                        g["uninst"] = True
                        out.append(g)
                continue
            out.append(game(f"{launcher.lower()}:{sub}", name, launcher, loc, _icon_exe(v.get("DisplayIcon"))))
    return out


_STANDALONE_ON = [True]


# ---------- standalone games (no launcher)
SA_SKIP = re.compile(r"^(steam|steamlibrary|epic games|gog galaxy|gog games|ubisoft|ubisoft game launcher|origin|origin games|"
                     r"ea app|ea games|electronic arts|battle\.net|riot games|rockstar games|amazon games|xboxgames|windowsapps|"
                     r"modifiablewindowsapps|common files|microsoft.*|windows.*|internet explorer|nvidia.*|amd|ati technologies|"
                     r"intel|realtek|dotnet|reference assemblies|msbuild|package cache|uninstall information|installshield.*|"
                     r"java|python\d*|nodejs|git|7-zip|winrar|google|mozilla.*|vlc|obs-studio|discord|roberts space industries|"
                     r"itch|wargaming\.net|gaijin|hoyoplay|nexon|\$.*|\..*)$", re.I)
SA_DLLS = {"unityplayer.dll", "steam_api.dll", "steam_api64.dll", "eossdk-win64-shipping.dll", "eossdk-win32-shipping.dll",
           "galaxy.dll", "galaxy64.dll", "bink2w64.dll", "binkw32.dll", "binkw64.dll", "fmod.dll", "fmod64.dll",
           "fmodstudio.dll", "fmodstudio64.dll", "fmodex.dll", "fmodex64.dll", "monogame.framework.dll", "fna.dll",
           "microsoft.xna.framework.dll", "love.dll", "physx3_x64.dll", "physx_64.dll", "nvngx_dlss.dll",
           "amd_ags_x64.dll", "discord_game_sdk.dll", "data.win"}
BAD_EXE = re.compile(r"unins|uninstall|setup|install|crash|report|redist|vc_?redist|dxsetup|dotnet|directx|update|patch|"
                     r"helper|dedicated|server|config|settings|benchmark|editor|tool|cef|webhelper|prereq|easyanticheat|"
                     r"battleye|be_service|notification|overlay|activation|register|support|readme|manual|7z|python|java", re.I)
BAD_PRODUCT = re.compile(r"bootstrap|godot engine|unity player|unreal engine|^game$|^launcher$|electron|python|java|"
                         r"^love$|runtime|microsoft|windows|setup|installer", re.I)
SA_ROOT_NAMES = ("Games", "Game", "Gaming", "PC Games", "Program Files", "Program Files (x86)")
_sa_roots = set()


def _entries(d):
    try:
        return list(os.scandir(d))
    except OSError:
        return []


def best_exe(d, prefer=()):
    exes = [e for e in _entries(d) if e.name.lower().endswith(".exe") and not BAD_EXE.search(e.name) and e.is_file()]
    if not exes:
        return None
    for p in prefer:
        hit = next((e for e in exes if e.name.lower() == p.lower()), None)
        if hit:
            return hit.path
    folder = _norm(os.path.basename(d))
    hit = next((e for e in exes if _norm(os.path.splitext(e.name)[0]) == folder), None)
    if hit:
        return hit.path

    def score(e):
        try:
            size = e.stat().st_size
        except OSError:
            size = 0
        return ("launcher" not in e.name.lower(), size)
    return max(exes, key=score).path


def sa_detect(d):
    """If folder d holds a game, return {kind, exe, name?, gog?}; else None. Only looks one level down."""
    ents = _entries(d)
    if not ents:
        return None
    low = {e.name.lower(): e for e in ents}
    dirs = {n for n, e in low.items() if e.is_dir()}
    # GOG offline installer leaves goggame-<id>.info with the exact name and the exe to start
    for n, e in low.items():
        if n.startswith("goggame-") and n.endswith(".info"):
            try:
                with open(e.path, encoding="utf-8", errors="ignore") as f:
                    info = json.load(f)
                task = next((t for t in info.get("playTasks") or [] if t.get("isPrimary")), None) or (info.get("playTasks") or [{}])[0]
                exe = os.path.join(d, task.get("path", "")) if task.get("path") else best_exe(d)
                return {"kind": "gog", "exe": exe if exe and os.path.isfile(exe) else best_exe(d),
                        "name": info.get("name"), "gog": str(info.get("gameId") or "")}
            except (OSError, ValueError, AttributeError):
                pass
    data_dirs = [low[n].name for n in dirs if n.endswith("_data")]
    if "unityplayer.dll" in low or any(os.path.exists(os.path.join(d, x, "globalgamemanagers")) for x in data_dirs):
        return {"kind": "unity", "exe": best_exe(d, [x[:-5] + ".exe" for x in data_dirs])}
    if "data.win" in low:
        return {"kind": "gamemaker", "exe": best_exe(d)}
    if "renpy" in dirs and "game" in dirs:
        return {"kind": "renpy", "exe": best_exe(d)}
    if os.path.isfile(os.path.join(d, "www", "js", "rpg_core.js")) or os.path.isfile(os.path.join(d, "js", "rmmz_core.js")) \
            or ("game.ini" in low and any(n.startswith("rgss") for n in low)):
        return {"kind": "rpgmaker", "exe": best_exe(d, ["Game.exe", "nw.exe"])}
    pcks = [os.path.splitext(n)[0] for n in low if n.endswith(".pck")]
    if pcks and any(p + ".exe" in low for p in pcks):
        return {"kind": "godot", "exe": next(low[p + ".exe"].path for p in pcks if p + ".exe" in low)}
    if "engine" in dirs:
        for n in dirs - {"engine"}:
            if os.path.isdir(os.path.join(d, low[n].name, "Content", "Paks")):
                exe = best_exe(d)
                if not exe:
                    exe = best_exe(os.path.join(d, low[n].name, "Binaries", "Win64"))
                return {"kind": "unreal", "exe": exe}
    if "hl2.exe" in low or os.path.isfile(os.path.join(d, "bin", "engine.dll")):
        return {"kind": "source", "exe": best_exe(d, ["hl2.exe"])}
    if SA_DLLS & set(low):
        return {"kind": "game", "exe": best_exe(d)}
    for sub in ("bin", "bin64", "x64", "binaries"):   # exe one folder down, e.g. Game\bin\x64\game.exe
        if sub in dirs:
            inner = os.path.join(d, low[sub].name)
            for dd in [inner] + [e.path for e in _entries(inner) if e.is_dir()][:6]:
                names = {e.name.lower() for e in _entries(dd)}
                if SA_DLLS & names:
                    return {"kind": "game", "exe": best_exe(dd)}
    return None


def exe_product_name(path):
    """The name a game's .exe gives itself (Windows file details), if it's a sensible one."""
    if os.name != "nt" or not path:
        return None
    try:
        import ctypes
        from ctypes import wintypes
        ver = ctypes.WinDLL("version")
        ver.GetFileVersionInfoSizeW.argtypes = [wintypes.LPCWSTR, ctypes.POINTER(wintypes.DWORD)]
        ver.GetFileVersionInfoW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p]
        ver.VerQueryValueW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR, ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(wintypes.UINT)]
        size = ver.GetFileVersionInfoSizeW(path, None)
        if not size:
            return None
        buf = ctypes.create_string_buffer(size)
        if not ver.GetFileVersionInfoW(path, 0, size, buf):
            return None
        lp, ln = ctypes.c_void_p(), wintypes.UINT()
        langs = []
        if ver.VerQueryValueW(buf, "\\VarFileInfo\\Translation", ctypes.byref(lp), ctypes.byref(ln)) and ln.value >= 4:
            arr = ctypes.cast(lp, ctypes.POINTER(wintypes.WORD * 2)).contents
            langs.append((arr[0], arr[1]))
        for lang, cp in langs + [(0x0409, 0x04B0), (0x0409, 0x04E4), (0x0000, 0x04B0)]:
            for key in ("ProductName", "FileDescription"):
                q = f"\\StringFileInfo\\{lang:04x}{cp:04x}\\{key}"
                if ver.VerQueryValueW(buf, q, ctypes.byref(lp), ctypes.byref(ln)) and ln.value:
                    text = ctypes.wstring_at(lp.value, ln.value).strip("\0 ").strip()
                    if text and len(text) > 1 and not BAD_PRODUCT.search(text):
                        return text
    except Exception:
        pass
    return None


def pretty_folder(name):
    n = re.sub(r"(?i)[ _\-.]*(v?\d+(\.\d+)+[a-z]?|win(32|64)|x64|x86|portable|drm[ _-]?free|gog|repack)(?=$|[ _\-.])", "", name)
    n = re.sub(r"[_\-.]+", " ", n)
    n = re.sub(r"(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|(?<=[A-Za-z])(?=\d)", " ", n)
    return re.sub(r"\s+", " ", n).strip() or name


def sa_game(d, hit, name=None):
    exe = hit.get("exe")
    if hit.get("gog"):
        g = game(f"gog:{hit['gog']}", hit.get("name") or name or pretty_folder(os.path.basename(d)), "GOG", d, exe)
        return g
    nm = name or hit.get("name") or exe_product_name(exe) or pretty_folder(os.path.basename(d))
    gid = "sa:" + hashlib.sha1(os.path.normcase(os.path.normpath(d)).encode()).hexdigest()[:12]
    return game(gid, nm, "Standalone", d, exe)


def sa_cached_detect(d):
    return by_mtime("sa:" + d, [d], lambda: sa_detect(d))


def scan_standalone(known, extra=()):
    """Games with no launcher: portable or self-installed. `known` = folders other launchers already claimed."""
    known = {os.path.normcase(os.path.normpath(k)).rstrip("\\/") for k in known if k}
    out, taken = [], set()

    def claimed(p):
        p = os.path.normcase(os.path.normpath(p)).rstrip("\\/")
        return p in known or p in taken or any(p.startswith(k + os.sep) or k.startswith(p + os.sep) for k in known | taken)

    def consider(d, name=None):
        if claimed(d):
            return False
        hit = sa_cached_detect(d)
        if not hit or not hit.get("exe"):
            return False
        out.append(sa_game(d, hit, name))
        taken.add(os.path.normcase(os.path.normpath(d)).rstrip("\\/"))
        return True

    roots = []
    for letter in string.ascii_uppercase:
        drive = f"{letter}:\\"
        if os.path.exists(drive):
            roots += [os.path.join(drive, n) for n in SA_ROOT_NAMES if os.path.isdir(os.path.join(drive, n))]
    local = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Programs")
    if os.path.isdir(local):
        roots.append(local)
    user = [e for e in extra if os.path.isdir(e)]
    _sa_roots.clear()
    _sa_roots.update(r for r in roots + user if "program files" not in r.lower())
    for r in user:
        consider(r)   # the folder itself might be a game
    for r in roots + user:
        for c in _entries(r):
            if not c.is_dir() or SA_SKIP.match(c.name) or NOT_GAMES.search(c.name):
                continue
            if consider(c.path):
                continue
            for cc in _entries(c.path)[:40]:   # one level down, e.g. Games\Publisher\Game
                if cc.is_dir() and not SA_SKIP.match(cc.name) and not NOT_GAMES.search(cc.name):
                    consider(cc.path)
    return out


_xbox_roots = set()


def scan_xbox():
    out = []
    _xbox_roots.clear()
    for letter in string.ascii_uppercase:
        if not os.path.exists(f"{letter}:\\"):
            continue
        for root in (f"{letter}:\\XboxGames", f"{letter}:\\Program Files\\ModifiableWindowsApps"):
            if not os.path.isdir(root):
                continue
            _xbox_roots.add(root)
            try:
                for name in os.listdir(root):
                    p = os.path.join(root, name)
                    if os.path.isdir(p) and name.lower() != "gamesave":
                        out.append(game(f"xbox:{name}", name, "Xbox", p))
            except OSError:
                pass
    return out


def _sqlite_ro(path):
    return sqlite3.connect("file:" + pathname2url(path) + "?mode=ro&immutable=1", uri=True, timeout=2)


def scan_amazon():
    """Amazon Games keeps an exact list of installed games in its own database."""
    out = []
    db = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Amazon Games", "Data", "Games", "Sql", "GameInstallInfo.sqlite")
    if not os.path.isfile(db):
        return out
    try:
        con = _sqlite_ro(db)
        for gid, title, path, installed in con.execute("SELECT Id, ProductTitle, InstallDirectory, Installed FROM DbSet"):
            if installed and path and os.path.isdir(path):
                out.append(game(f"amazon:{gid}", title, "Amazon", path, f"amazon-games://play/{gid}"))
        con.close()
    except sqlite3.Error:
        pass
    return out


def scan_itch():
    """Games installed through the itch.io app (its local 'butler' database)."""
    out = []
    db = os.path.join(APPDATA, "itch", "db", "butler.db")
    if not os.path.isfile(db):
        return out
    try:
        con = _sqlite_ro(db)
        con.row_factory = sqlite3.Row
        locs = {r["id"]: r["path"] for r in con.execute("SELECT id, path FROM install_locations")}
        games = {r["id"]: r for r in con.execute("SELECT * FROM games")}
        for c in con.execute("SELECT * FROM caves"):
            keys = c.keys()
            path = None
            if "install_location_id" in keys and "install_folder_name" in keys and locs.get(c["install_location_id"]):
                path = os.path.join(locs[c["install_location_id"]], c["install_folder_name"] or "")
            if (not path or not os.path.isdir(path)) and "verdict" in keys and c["verdict"]:
                try:
                    path = json.loads(c["verdict"]).get("basePath")
                except ValueError:
                    pass
            if not path or not os.path.isdir(path):
                continue
            gm = games.get(c["game_id"])
            title = (gm["title"] if gm is not None and "title" in gm.keys() else None) or os.path.basename(path)
            g = game(f"itch:{c['game_id']}", title, "itch.io", path, f"itch://caves/{c['id']}/launch")
            if gm is not None:
                gk = gm.keys()
                g["cover_url"] = (gm["still_cover_url"] if "still_cover_url" in gk else None) or (gm["cover_url"] if "cover_url" in gk else None)
            out.append(g)
        con.close()
    except sqlite3.Error:
        pass
    return out


# ---------- RSI Launcher (Star Citizen)
RSI_CHANNELS = {"LIVE": "", "PTU": " (PTU)", "EPTU": " (EPTU)", "TECH-PREVIEW": " (Tech Preview)", "HOTFIX": " (Hotfix)"}


def find_rsi_launcher():
    """Path to 'RSI Launcher.exe', or None."""
    cands = []
    if winreg:
        path = r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall"
        for root, view in ((winreg.HKEY_LOCAL_MACHINE, _view("KEY_WOW64_64KEY")),
                           (winreg.HKEY_LOCAL_MACHINE, _view("KEY_WOW64_32KEY")), (winreg.HKEY_CURRENT_USER, 0)):
            for _, v in reg_subkeys(root, path, view):
                if (v.get("DisplayName") or "").lower().startswith("rsi launcher"):
                    loc = (v.get("InstallLocation") or "").strip().strip('"')
                    if loc:
                        cands.append(os.path.join(loc, "RSI Launcher.exe"))
                    icon = _icon_exe(v.get("DisplayIcon"))
                    if icon:
                        cands.append(icon)
    for base in (os.environ.get("ProgramFiles", r"C:\Program Files"), os.environ.get("LOCALAPPDATA", "")):
        cands.append(os.path.join(base, "Roberts Space Industries", "RSI Launcher", "RSI Launcher.exe"))
        cands.append(os.path.join(base, "Programs", "rsilauncher", "RSI Launcher.exe"))
    return next((c for c in cands if c and os.path.isfile(c)), None)


def _rsi_library_roots():
    """Folders that may hold StarCitizen\\<channel>: the usual spots plus anything the launcher mentions."""
    roots = set()
    for letter in string.ascii_uppercase:
        drive = f"{letter}:\\"
        if not os.path.exists(drive):
            continue
        for sub in ("Program Files", "", "Games", "Program Files (x86)"):
            roots.add(os.path.join(drive, sub, "Roberts Space Industries", "StarCitizen"))
    # the launcher's own settings/logs record custom library folders
    base = os.path.join(APPDATA, "rsilauncher")
    pat = re.compile(r'([A-Za-z]:[\\/][^"\r\n<>|*?]*?StarCitizen)[\\/]+(?:LIVE|PTU|EPTU|TECH-PREVIEW|HOTFIX)\b', re.I)
    lib = re.compile(r'"?(?:library|libraryFolder|installDir|install_dir)[^"]*"?\s*[:=]\s*"([A-Za-z]:[^"]+)"', re.I)
    for dirpath, dirnames, files in os.walk(base):
        if dirpath.count(os.sep) - base.count(os.sep) > 2:
            dirnames[:] = []
            continue
        for fn in files:
            if not fn.lower().endswith((".json", ".log", ".txt")):
                continue
            fp = os.path.join(dirpath, fn)
            try:
                if os.path.getsize(fp) > 8_000_000:
                    continue
                with open(fp, encoding="utf-8", errors="ignore") as f:
                    text = f.read()
            except OSError:
                continue
            for m in pat.finditer(text):
                roots.add(os.path.normpath(m.group(1).replace("\\\\", "\\")))
            for m in lib.finditer(text):
                folder = os.path.normpath(m.group(1).replace("\\\\", "\\"))
                roots.add(os.path.join(folder, "StarCitizen"))
                roots.add(os.path.join(folder, "Roberts Space Industries", "StarCitizen"))
    return roots


def scan_rsi():
    out, seen = [], set()
    launcher = find_rsi_launcher()
    for root in _rsi_library_roots():
        if not os.path.isdir(root):
            continue
        for channel, suffix in RSI_CHANNELS.items():
            path = os.path.join(root, channel)
            key = os.path.normcase(path)
            if key in seen or not os.path.isfile(os.path.join(path, "Bin64", "StarCitizen.exe")):
                continue
            seen.add(key)
            g = game(f"rsi:{channel}", "Star Citizen" + suffix, "RSI", path, launcher)
            g["lookup"] = "Star Citizen"
            out.append(g)
    return out


# Order matters: launchers with exact data first; the Windows installed-programs list fills in the rest.
SCANNERS = [scan_steam, scan_epic, scan_gog, scan_ubisoft, scan_amazon, scan_itch, scan_xbox, scan_rsi, scan_uninstall_entries]


# ======================================================================= not-installed games
def install_uri(gid, extra=None):
    """Launcher link that opens the install prompt, or None if the launcher has no such link."""
    plat, _, ident = gid.partition(":")
    extra = extra or {}
    if plat == "steam":
        return f"steam://install/{ident}"
    if plat == "gog":
        return f"goggalaxy://openGameView/{ident}"
    if plat == "epic" and extra.get("ns") and extra.get("catalog"):
        return f"com.epicgames.launcher://apps/{extra['ns']}%3A{extra['catalog']}%3A{ident}?action=install"
    if plat == "rsi":
        return find_rsi_launcher()
    if plat == "itch":
        return f"itch://games/{ident}"
    if plat == "amazon":
        return f"amazon-games://play/{ident}"
    return None


def galaxy_library():
    """GOG games owned in GOG Galaxy: {game_id: {name, tall, wide}}."""
    out = {}
    db = os.path.join(PROGRAMDATA, "GOG.com", "Galaxy", "storage", "galaxy-2.0.db")
    if not os.path.isfile(db):
        return out
    try:
        con = sqlite3.connect("file:" + pathname2url(db) + "?mode=ro&immutable=1", uri=True, timeout=2)
        owned = {r[0] for r in con.execute("SELECT releaseKey FROM LibraryReleases") if str(r[0]).startswith("gog_")}
        rows = con.execute("SELECT gp.releaseKey, t.type, gp.value FROM GamePieces gp JOIN GamePieceTypes t "
                           "ON gp.gamePieceTypeId = t.id WHERE t.type IN ('originalTitle','title','originalImages')")
        for key, kind, value in rows:
            if key not in owned:
                continue
            try:
                v = json.loads(value) or {}
            except (TypeError, ValueError):
                continue
            e = out.setdefault("gog:" + key[4:], {})
            if kind in ("title", "originalTitle") and v.get("title"):
                e.setdefault("name", v["title"])
            elif kind == "originalImages":
                fix = lambda u: u.replace("_{formatter}", "").replace("{formatter}", "") if isinstance(u, str) else None
                e["tall"], e["wide"] = fix(v.get("verticalCover")), fix(v.get("background"))
        con.close()
    except sqlite3.Error:
        pass
    return {k: v for k, v in out.items() if v.get("name")}


def epic_library():
    """Games in the Epic library cache (add-ons and DLC skipped): {game_id: {name, tall, wide, ns, catalog}}."""
    epic_catalog()
    out, seen = {}, set()
    for it in _epic_items.values():
        if id(it) in seen:
            continue
        seen.add(id(it))
        paths = {c.get("path") for c in it.get("categories", []) or []}
        if "games" not in paths or paths & {"addons", "digitalextras", "plugins", "engines"} or it.get("mainGameItem"):
            continue
        rel = (it.get("releaseInfo") or [{}])[0]
        if not rel.get("appId") or not it.get("title"):
            continue
        imgs = {k.get("type"): k.get("url") for k in it.get("keyImages", []) if k.get("url")}
        out["epic:" + rel["appId"]] = {"name": it["title"], "ns": it.get("namespace"), "catalog": it.get("id"),
                                       "tall": imgs.get("DieselGameBoxTall") or imgs.get("OfferImageTall"),
                                       "wide": imgs.get("DieselGameBox") or imgs.get("OfferImageWide")}
    return out


def steam_names(appids):
    """Names (and game/not-game) for Steam app ids, asked in batches: {appid: name or None}."""
    out = {}
    ids = list(appids)
    for i in range(0, len(ids), 50):
        chunk = ids[i:i + 50]
        q = json.dumps({"ids": [{"appid": int(a)} for a in chunk], "context": {"language": "english", "country_code": "US"},
                        "data_request": {"include_basic_info": True}}, separators=(",", ":"))
        d = http_json("https://api.steampowered.com/IStoreBrowseService/GetItems/v1/?input_json=" + quote(q))
        items = ((d or {}).get("response") or {}).get("store_items") or []
        for it in items:
            appid = str(it.get("appid") or it.get("id") or "")
            if not appid:
                continue
            is_game = it.get("type") in (None, 0, 2, 12)  # game, mod, beta (skip DLC, tools, soundtracks...)
            out[appid] = it.get("name") if it.get("name") and is_game else None
        for a in chunk:
            out.setdefault(str(a), None)
    return out


def scan_all(custom, settings=None):
    settings = settings or {}
    _STANDALONE_ON[0] = settings.get("find_standalone", True)
    found, seen = [], set()
    for s in SCANNERS:
        try:
            results = s()
        except Exception as e:  # one broken launcher should not break the app
            print(f"{s.__name__} failed: {e}")
            continue
        for g in results:
            key = os.path.normcase(os.path.normpath(g["path"] or g["id"]))
            if key not in seen:
                seen.add(key)
                found.append(g)
    for c in custom:
        if c.get("path") and os.path.exists(c["path"]):
            found.append(game(c["id"], c["name"], "Custom", c["path"], c.get("launch")))
            seen.add(os.path.normcase(os.path.normpath(c["path"])))
    if _STANDALONE_ON[0]:
        try:
            ids = {g["id"] for g in found}
            for g in scan_standalone([g["path"] for g in found], settings.get("game_folders") or []):
                if g["id"] not in ids:
                    found.append(g)
        except Exception as e:
            print("scan_standalone failed:", e)
    return found


def folder_size(path):
    total = 0
    for dirpath, _, files in os.walk(path):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(dirpath, f))
            except OSError:
                pass
    return total


# ======================================================================= cover art lookup
def http_get(url, timeout=10):
    try:
        with urlopen(Request(url, headers={"User-Agent": UA}), timeout=timeout) as r:
            return r.read(), r.headers.get("Content-Type", "")
    except Exception:
        return None, ""


def http_json(url):
    raw, _ = http_get(url)
    try:
        return json.loads(raw.decode("utf-8")) if raw else None
    except ValueError:
        return None


def clean_name(name):
    name = re.sub(r"[™®©]", "", name or "")
    name = re.sub(r"\s*\((?:64|32)-?bit\)", "", name, flags=re.I)
    return re.sub(r"\s+", " ", name).strip()


def _norm(s):
    s = re.sub(r"^the\s+", "", clean_name(s).lower())
    return re.sub(r"[^a-z0-9]+", "", s)


def similar(a, b):
    a, b = _norm(a), _norm(b)
    if not a or not b:
        return 0
    return 1.0 if a == b else difflib.SequenceMatcher(None, a, b).ratio()


def steam_search(name):
    d = http_json("https://store.steampowered.com/api/storesearch/?cc=us&l=en&term=" + quote(clean_name(name)))
    best, score = None, 0
    for it in (d or {}).get("items", [])[:10]:
        r = similar(name, it.get("name", ""))
        if r > score:
            best, score = it, r
    return str(best["id"]) if best and score >= 0.82 else None


def steam_art_urls(appid):
    """Portrait, wide, hero-banner and logo candidates for a Steam app, newest asset system first."""
    tall, wide, hero, logo = [], [], [], []
    q = json.dumps({"ids": [{"appid": int(appid)}], "context": {"language": "english", "country_code": "US"},
                    "data_request": {"include_assets": True}}, separators=(",", ":"))
    d = http_json("https://api.steampowered.com/IStoreBrowseService/GetItems/v1/?input_json=" + quote(q))
    try:
        assets = d["response"]["store_items"][0]["assets"]
        fmt = "https://shared.akamai.steamstatic.com/store_item_assets/" + assets["asset_url_format"]
        for key, bucket in (("library_capsule_2x", tall), ("library_capsule", tall), ("header", wide), ("main_capsule", wide),
                            ("library_hero", hero), ("library_hero_2x", hero), ("library_logo", logo), ("library_logo_2x", logo)):
            if assets.get(key):
                bucket.append(fmt.replace("${FILENAME}", assets[key]))
    except (TypeError, KeyError, IndexError, ValueError):
        pass
    cdn = f"https://cdn.cloudflare.steamstatic.com/steam/apps/{appid}/"
    tall.append(cdn + "library_600x900.jpg")
    d = http_json(f"https://store.steampowered.com/api/appdetails?appids={appid}&filters=basic")
    try:
        wide.append(d[str(appid)]["data"]["header_image"])
    except (TypeError, KeyError):
        pass
    wide.append(cdn + "header.jpg")
    hero.append(cdn + "library_hero.jpg")
    logo.append(cdn + "logo.png")
    return {"tall": tall, "wide": wide, "hero": hero, "logo": logo}


_epic_cat = None
_epic_items = {}


def epic_catalog():
    """Epic keeps catalog info (incl. box art URLs) in a base64-encoded JSON cache file."""
    global _epic_cat
    if _epic_cat is not None:
        return _epic_cat
    _epic_cat = {}
    path = os.path.join(os.environ.get("LOCALAPPDATA", ""), "EpicGamesLauncher", "Saved", "Data", "Catalog", "catcache.bin")
    try:
        with open(path, "rb") as f:
            items = json.loads(base64.b64decode(f.read()))
        for it in items:
            imgs = {k.get("type"): k.get("url") for k in it.get("keyImages", []) if k.get("url")}
            keys = [it.get("id")] + [r.get("appId") for r in it.get("releaseInfo", []) or []]
            for k in keys:
                if k:
                    _epic_cat[k] = imgs
                    _epic_items[k] = it
    except Exception:
        pass
    return _epic_cat


def gog_art_urls(product_id):
    d = http_json(f"https://api.gog.com/v2/games/{product_id}")
    links = (d or {}).get("_links", {})
    get = lambda k: (links.get(k) or {}).get("href")
    tall = [u for u in (get("boxArtImage"), get("verticalCover")) if u]
    wide = [u for u in (get("galaxyBackgroundImage"), get("backgroundImage"), get("logo")) if u]
    return tall, wide


def wikipedia_art(name):
    params = urlencode({"action": "query", "format": "json", "generator": "search", "gsrlimit": 5,
                        "gsrsearch": clean_name(name) + " video game", "prop": "pageimages", "piprop": "thumbnail",
                        "pithumbsize": 600, "pilicense": "any", "redirects": 1})
    d = http_json("https://en.wikipedia.org/w/api.php?" + params)
    pages = sorted(((d or {}).get("query", {}).get("pages", {}) or {}).values(), key=lambda p: p.get("index", 99))
    for p in pages:
        title = re.sub(r"\s*\(.*?\)\s*$", "", p.get("title", ""))
        if similar(name, title) >= 0.8 and p.get("thumbnail", {}).get("source"):
            return p["thumbnail"]["source"]
    return None


def art_candidates(g):
    """Every place we might find this game's pictures, best first: {tall, wide, hero, logo} url lists."""
    tall, wide, hero, logo, appid = [], [], [], [], None
    gid = g["id"]
    if gid.startswith("steam:"):
        appid = gid.split(":", 1)[1]
    elif g["launcher"] == "Epic":
        cat = epic_catalog()
        imgs = cat.get(g.get("catalog")) or cat.get(gid.split(":", 1)[1]) or {}
        tall += [imgs[k] for k in ("DieselGameBoxTall", "OfferImageTall", "DieselGameBoxPortrait") if imgs.get(k)]
        wide += [imgs[k] for k in ("DieselGameBox", "OfferImageWide", "DieselStoreFrontWide") if imgs.get(k)]
        hero += [imgs[k] for k in ("DieselStoreFrontWide", "OfferImageWide", "DieselGameBox") if imgs.get(k)]
    elif g.get("cover_url"):
        tall.append(g["cover_url"])
        wide.append(g["cover_url"])
    if gid.startswith("gog:"):
        t, w = gog_art_urls(gid.split(":", 1)[1])
        tall += t
        wide += w
        hero += w
    if not tall or not hero:
        appid = appid or steam_search(g.get("lookup") or g["name"])
        if appid:
            st = steam_art_urls(appid)
            if not tall:
                tall, wide = tall + st["tall"], wide + st["wide"]
            hero += st["hero"]
            logo += st["logo"]
    if not tall and not wide:
        w = wikipedia_art(g.get("lookup") or g["name"])
        if w:
            tall.append(w)
    return {"tall": tall, "wide": wide, "hero": hero, "logo": logo}


# ======================================================================= game details lookup
DETAILS_TTL = 30 * 86400
FEATURES_KEEP = {"Single-player", "Multi-player", "PvP", "Online PvP", "Shared/Split Screen PvP", "Co-op", "Online Co-op",
                 "Shared/Split Screen Co-op", "Shared/Split Screen", "Cross-Platform Multiplayer", "MMO",
                 "Full controller support", "Partial Controller Support", "VR Supported", "VR Only"}


def clean_text(s):
    s = re.sub(r"<br\s*/?>", "\n", s or "", flags=re.I)
    s = htmllib.unescape(re.sub(r"<[^>]+>", " ", s))
    return re.sub(r"[ \t\r\f\v]+", " ", s).replace(" \n", "\n").strip()


def steam_details(appid):
    d = http_json(f"https://store.steampowered.com/api/appdetails?appids={appid}&l=english&cc=us")
    try:
        if not d[str(appid)]["success"]:
            return None
        x = d[str(appid)]["data"]
    except (TypeError, KeyError):
        return None
    return {"desc": clean_text(x.get("short_description")), "dev": x.get("developers") or [],
            "pub": x.get("publishers") or [], "released": (x.get("release_date") or {}).get("date", ""),
            "genres": [g.get("description") for g in x.get("genres") or [] if g.get("description")],
            "features": [c["description"] for c in x.get("categories") or [] if c.get("description") in FEATURES_KEEP],
            "score": (x.get("metacritic") or {}).get("score"),
            "shots": [{"thumb": s.get("path_thumbnail"), "full": s.get("path_full")}
                      for s in (x.get("screenshots") or [])[:10] if s.get("path_thumbnail")],
            "url": f"https://store.steampowered.com/app/{appid}", "source": "Steam"}


def epic_details(g):
    epic_catalog()
    it = _epic_items.get(g.get("catalog")) or _epic_items.get(g["id"].split(":", 1)[1])
    if not it:
        return None
    released = (it.get("creationDate") or "")[:10]
    return {"desc": clean_text(it.get("description")), "dev": [it["developer"]] if it.get("developer") else [],
            "pub": [], "released": released, "genres": [], "features": [], "score": None, "shots": [],
            "url": "", "source": "Epic"}


def gog_details(product_id):
    d = http_json(f"https://api.gog.com/v2/games/{product_id}?locale=en-US")
    if not d:
        return None
    emb = d.get("_embedded") or {}
    names = lambda v: [x.get("name") for x in (v if isinstance(v, list) else [v]) if isinstance(x, dict) and x.get("name")]
    prod = emb.get("product") or {}
    return {"desc": clean_text(d.get("overview") or d.get("description") or "")[:900],
            "dev": names(emb.get("developers") or []), "pub": names(emb.get("publisher") or {}),
            "released": (prod.get("globalReleaseDate") or emb.get("product", {}).get("releaseDate") or "")[:10],
            "genres": names(emb.get("tags") or [])[:5], "features": names(emb.get("features") or [])[:6],
            "score": None, "shots": [], "url": f"https://www.gog.com/game/{prod.get('slug', product_id)}", "source": "GOG"}


def wikipedia_details(name):
    params = urlencode({"action": "query", "format": "json", "generator": "search", "gsrlimit": 5,
                        "gsrsearch": clean_name(name) + " video game", "prop": "extracts", "exintro": 1,
                        "explaintext": 1, "exsentences": 4, "redirects": 1})
    d = http_json("https://en.wikipedia.org/w/api.php?" + params)
    pages = sorted(((d or {}).get("query", {}).get("pages", {}) or {}).values(), key=lambda p: p.get("index", 99))
    for p in pages:
        title = p.get("title", "")
        if similar(name, re.sub(r"\s*\(.*?\)\s*$", "", title)) >= 0.8 and p.get("extract"):
            return {"desc": p["extract"].strip(), "dev": [], "pub": [], "released": "", "genres": [], "features": [],
                    "score": None, "shots": [], "url": "https://en.wikipedia.org/wiki/" + quote(title.replace(" ", "_")),
                    "source": "Wikipedia"}
    return None


def game_details(g):
    """Best available description/facts for a game, trying the richest source first."""
    gid = g["id"]
    appid = gid.split(":", 1)[1] if gid.startswith("steam:") else None
    epic = epic_details(g) if g["launcher"] == "Epic" else None
    appid = appid or steam_search(g.get("lookup") or g["name"])
    if appid:
        d = steam_details(appid)
        if d and (d["desc"] or d["genres"]):
            if epic and not d["desc"]:
                d["desc"] = epic["desc"]
            return d
    if epic and epic["desc"]:
        return epic
    if gid.startswith("gog:"):
        d = gog_details(gid.split(":", 1)[1])
        if d and d["desc"]:
            return d
    return wikipedia_details(g.get("lookup") or g["name"]) or epic or {}


def download_image(urls, dest_base):
    for url in urls:
        raw, ctype = http_get(url, timeout=15)
        if raw and len(raw) > 1500 and ctype.startswith("image"):
            ext = {"image/png": ".png", "image/webp": ".webp", "image/gif": ".gif"}.get(ctype.split(";")[0], ".jpg")
            path = dest_base + ext
            os.makedirs(ART_DIR, exist_ok=True)
            with open(path, "wb") as f:
                f.write(raw)
            return path
    return None


def safe_file(gid):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", gid)[:120]


# ======================================================================= play tracking
_win = None
_pid_paths = {}   # pid -> exe path ('' if it can't be read); only new pids get looked up


def _win_api():
    global _win
    if _win is None:
        import ctypes
        from ctypes import wintypes
        psapi, k32 = ctypes.WinDLL("psapi"), ctypes.WinDLL("kernel32")
        k32.OpenProcess.restype = wintypes.HANDLE
        k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        k32.QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR,
                                                   ctypes.POINTER(wintypes.DWORD)]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        _win = (ctypes, wintypes, psapi, k32, (wintypes.DWORD * 8192)(), ctypes.create_unicode_buffer(1024))
    return _win


def running_exe_paths():
    """Full paths of every running process (Windows, no extra installs)."""
    if os.name != "nt":
        return set()
    ctypes, wintypes, psapi, k32, pids, buf = _win_api()
    needed = wintypes.DWORD()
    if not psapi.EnumProcesses(ctypes.byref(pids), ctypes.sizeof(pids), ctypes.byref(needed)):
        return set()
    current = set(pids[:needed.value // ctypes.sizeof(wintypes.DWORD)])
    for pid in [p for p in _pid_paths if p not in current]:
        del _pid_paths[pid]
    for pid in current - _pid_paths.keys():
        path = ""
        h = k32.OpenProcess(0x1000, False, pid)  # PROCESS_QUERY_LIMITED_INFORMATION
        if h:
            size = wintypes.DWORD(len(buf))
            if k32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(size)):
                path = os.path.normcase(buf.value)
            k32.CloseHandle(h)
        _pid_paths[pid] = path
    return {p for p in _pid_paths.values() if p}


def lower_priority():
    """Run Game Hub below normal priority so games always come first."""
    if os.name == "nt":
        try:
            import ctypes
            k32 = ctypes.windll.kernel32
            k32.SetPriorityClass(k32.GetCurrentProcess(), 0x4000)  # BELOW_NORMAL_PRIORITY_CLASS
        except Exception:
            pass


def _broad_dirs():
    names = [os.environ.get(v) for v in ("ProgramFiles", "ProgramFiles(x86)", "ProgramW6432",
                                         "SystemRoot", "USERPROFILE", "PUBLIC", "LOCALAPPDATA", "APPDATA")]
    return {os.path.normcase(os.path.normpath(n)) for n in names if n}


def build_prefixes(games):
    """[(folder_prefix, game_id)] longest first, skipping folders too broad to mean one game."""
    broad, out = _broad_dirs(), []
    for g in games:
        p = g.get("path")
        if not p or not os.path.isdir(p):
            continue
        p = os.path.normcase(os.path.normpath(p)).rstrip("\\/")
        if len(p) <= 3 or p in broad:
            continue
        out.append((p + os.sep, g["id"]))
    out.sort(key=lambda x: -len(x[0]))
    return out


# ======================================================================= helpers
SIZES = {"tall": (600, 900), "wide": (920, 430), "hero": (1920, 900), "logo": (800, 320)}


def small_copy(path, kind):
    """A copy of the image no bigger than it is shown (cached on disk). Big banners shrink ~4x."""
    box = SIZES.get(kind)
    if not box:
        return path
    try:
        from PIL import Image as _Im
    except Exception:
        return path
    try:
        st = os.stat(path)
        who = re.sub(r"[^A-Za-z0-9_-]", "", os.path.splitext(os.path.basename(path))[0])[:40]
        who += "-" + hashlib.sha1(os.path.normcase(path).encode()).hexdigest()[:6] + "." + kind
        ver = hashlib.sha1(f"{st.st_mtime_ns}|{st.st_size}".encode()).hexdigest()[:8]
        out = os.path.join(ART_DIR, "small", f"{who}.{ver}.{'png' if kind == 'logo' else 'jpg'}")
        if os.path.isfile(out):
            return out
        for old in glob.glob(os.path.join(ART_DIR, "small", glob.escape(who) + ".*")):
            try:
                os.remove(old)                # the picture changed: drop the previous resized copy
            except OSError:
                pass
        with _Im.open(path) as im:
            if im.width <= box[0] and im.height <= box[1] and os.path.getsize(path) < 400_000:
                return path
            im.thumbnail(box)
            os.makedirs(os.path.dirname(out), exist_ok=True)
            if kind == "logo":
                im.save(out, "PNG", optimize=True)
            else:
                im.convert("RGB").save(out, "JPEG", quality=84, optimize=True, progressive=True)
        return out
    except Exception:
        return path


def data_uri(path, kind=None):
    if kind:
        path = small_copy(path, kind)
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError:
        return None
    mime = mimetypes.guess_type(path)[0] or "image/jpeg"
    return f"data:{mime};base64," + base64.b64encode(raw).decode("ascii")


def startup_file():
    return os.path.join(APPDATA, "Microsoft", "Windows", "Start Menu", "Programs", "Startup", "Game Hub.vbs")


def gui_python():
    """The windowless Python to start Game Hub with: pythonw.exe, or Game Hub.exe in the downloadable install."""
    here = os.path.dirname(sys.executable)
    for p in (os.path.join(sys.base_prefix, "pythonw.exe"), os.path.join(here, "Game Hub.exe"), os.path.join(here, "pythonw.exe")):
        if os.path.isfile(p):
            return p
    return sys.executable


def set_startup(on, script=None):
    path = startup_file()
    if not on:
        if os.path.exists(path):
            os.remove(path)
        return
    if getattr(sys, "frozen", False):
        cmd = f'"{sys.executable}" --minimized'
    else:
        cmd = f'"{gui_python()}" "{script or os.path.abspath(__file__)}" --minimized'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write('CreateObject("WScript.Shell").Run "' + cmd.replace('"', '""') + '", 0, False\n')


def open_path(target):
    if hasattr(os, "startfile"):
        os.startfile(target)
    else:
        subprocess.Popen(["xdg-open", target])


# ======================================================================= the app (JS API)
class App:
    """Public methods are callable from the UI; underscore attributes stay private."""

    def __init__(self):
        lower_priority()
        self._lock = threading.RLock()
        self._data = self._load()
        self._games, self._by_id, self._prefixes = [], {}, []
        self._launcher_stats = {}
        self._updates = {}
        self._uninstalled, self._un_by_id = [], {}
        self._app_update = None    # newer Game Hub found: {version, notes, source, path|text}
        self._friends, self._friends_t = None, 0
        self._scan_lock = threading.Lock()
        self._relaunch = None
        self._active = {}
        self._version = 0
        self._scanning = False
        self._window = None
        self._tray = None
        self._quitting = False
        self._covers = {}
        self._ready = False          # True once the first scan + covers + sizes are done
        self._post_running = self._post_again = False
        self._prog = {"art_done": 0, "art_total": 0, "art_name": "", "size_done": 0, "size_total": 0,
                      "det_done": 0, "det_total": 0}
        self._recover_sessions()
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(PID_FILE, "w") as f:
                f.write(str(os.getpid()))
        except OSError:
            pass
        threading.Thread(target=self._scan, daemon=True).start()
        threading.Thread(target=self._tracker, daemon=True).start()
        threading.Thread(target=self._quit_watch, daemon=True).start()

    # ---------- persistence
    def _load(self):
        d = {"favorites": [], "hidden": [], "collections": {}, "custom": [], "sizes": {}, "covers": {},
             "tracked": {}, "sessions": [], "active": {}, "art": {}, "details": {},
             "seen": {}, "forgotten": [], "names": {},
             "settings": {"tracking": True, "close_to_tray": True, "show_hidden": False, "hover_play": False,
                          "check_updates": True, "update_url": "", "find_standalone": True, "game_folders": []}}
        try:
            with open(DATA_FILE, encoding="utf-8") as f:
                saved = json.load(f)
            settings = {**d["settings"], **saved.get("settings", {})}
            d.update(saved)
            d["settings"] = settings
        except (OSError, ValueError):
            pass
        return d

    def _save(self):
        with self._lock:
            os.makedirs(DATA_DIR, exist_ok=True)
            tmp = DATA_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self._data, f)
            os.replace(tmp, DATA_FILE)

    def _bump(self, save=True):
        with self._lock:
            self._version += 1
            if save:
                self._save()

    # ---------- scanning
    def _scan(self, wait=False):
        # Background scans skip if one is already running; a manual rescan waits for it, then runs its own.
        if not self._scan_lock.acquire(blocking=wait):
            return
        with self._lock:
            self._scanning = True
            self._version += 1
        try:
            games = scan_all(self._data["custom"], self._data["settings"])
            gone = set(self._data["forgotten"])
            games = [g for g in games if not (g["id"].startswith("sa:") and g["id"] in gone)]
            stats = launcher_playtime()
            updates = update_states()
            prefixes = build_prefixes(games)
            with self._lock:
                for g in games:
                    if not g["size"]:
                        g["size"] = self._data["sizes"].get(g["id"])
                self._games, self._by_id = games, {g["id"]: g for g in games}
                self._prefixes, self._launcher_stats, self._updates = prefixes, stats, updates
                for g in games:  # remember every installed game, so it can be listed after an uninstall
                    self._data["seen"][g["id"]] = {"name": g["name"], "launcher": g["launcher"],
                                                   "catalog": g.get("catalog"), "ns": g.get("ns"), "lookup": g.get("lookup"),
                                                   "cover_url": g.get("cover_url")}
            self._build_uninstalled()
        finally:
            with self._lock:
                self._scanning = False
                self._version += 1
            self._scan_lock.release()
        threading.Thread(target=self._post_scan, daemon=True).start()

    def _post_scan(self):
        """Cover art and folder sizes, side by side. Marks the app ready when the first round finishes."""
        if not getattr(self, "_tidied", False):
            self._tidied = True
            try:
                tidy_caches()
            except Exception as e:
                log_problem("tidying old files", e)
        with self._lock:
            if self._post_running:
                self._post_again = True
                return
            self._post_running = True
        try:
            while True:
                self._post_again = False
                jobs = [threading.Thread(target=self._fetch_art, daemon=True),
                        threading.Thread(target=self._fetch_details, daemon=True),
                        threading.Thread(target=self._measure_sizes, daemon=True)]
                for j in jobs:
                    j.start()
                for j in jobs:
                    j.join()
                if not self._post_again:
                    break
        finally:
            with self._lock:
                self._post_running = False
                self._ready = True
                self._version += 1
            threading.Thread(target=self._fetch_art, args=(list(self._uninstalled), False), daemon=True).start()

    def _measure_sizes(self):
        todo = [g for g in list(self._games) if not g["size"] and g["path"] and os.path.isdir(g["path"])]
        self._prog.update(size_done=0, size_total=len(todo))
        for g in todo:
            if self._quitting:
                break
            g["size"] = folder_size(g["path"])
            with self._lock:
                self._data["sizes"][g["id"]] = g["size"]
                self._version += 1
            self._prog["size_done"] += 1
        if todo:
            self._save()

    # ---------- games that aren't installed
    def _build_uninstalled(self):
        installed = {g["id"] for g in self._games}
        custom = {c["id"] for c in self._data["custom"]}
        forgotten = set(self._data["forgotten"])
        found = {}

        def add(gid, name, launcher, extra=None):
            if gid in installed or gid in forgotten or gid in found or gid in custom or not name:
                return
            g = game(gid, name, launcher, None)
            g.update(installed=False, install=install_uri(gid, extra), art=extra or {})
            if extra:
                g["catalog"] = extra.get("catalog")
            found[gid] = g

        for gid, v in list(self._data["seen"].items()):
            add(gid, v.get("name"), v.get("launcher"), {"catalog": v.get("catalog"), "ns": v.get("ns")})
            if gid in found:
                for k in ("lookup", "cover_url"):
                    if v.get(k):
                        found[gid][k] = v[k]
        for source, launcher in ((galaxy_library, "GOG"), (epic_library, "Epic")):
            try:
                for gid, v in source().items():
                    add(gid, v["name"], launcher, v)
            except Exception as e:
                print(f"{source.__name__} failed: {e}")
        played = [k.split(":", 1)[1] for k in self._launcher_stats if k.startswith("steam:") and k not in installed
                  and k not in forgotten and k not in found]
        names = self._data["names"]
        missing = [a for a in played if "steam:" + a not in names
                   or (names["steam:" + a] is None and time.time() - names.get("_t", 0) > 7 * 86400)]
        if missing:
            try:
                for appid, name in steam_names(missing).items():
                    names["steam:" + appid] = name
                names["_t"] = time.time()
            except Exception as e:
                print("steam names:", e)
        for a in played:
            add("steam:" + a, names.get("steam:" + a), "Steam")
        with self._lock:
            self._uninstalled = sorted(found.values(), key=lambda g: g["name"].lower())
            self._un_by_id = {g["id"]: g for g in self._uninstalled}
            self._version += 1

    def install(self, gid):
        g = self._un_by_id.get(gid)
        if not g or not g.get("install"):
            return {"ok": False, "error": "This launcher can't be asked to install games from here."}
        try:
            open_path(g["install"])
        except Exception as e:
            return {"ok": False, "error": str(e)}
        return {"ok": True}

    def forget_game(self, gid):
        with self._lock:
            if gid not in self._data["forgotten"]:
                self._data["forgotten"].append(gid)
            self._data["seen"].pop(gid, None)
            self._uninstalled = [g for g in self._uninstalled if g["id"] != gid]
            self._un_by_id.pop(gid, None)
            if gid.startswith("sa:") and gid in self._by_id:
                self._games = [g for g in self._games if g["id"] != gid]
                self._by_id.pop(gid, None)
        self._bump()
        return self.get_state()

    # ---------- cover art
    def _needs_art(self, g, full=True):
        gid = g["id"]
        if self._data["covers"].get(gid):
            return False
        if gid.startswith("steam:") and local_steam_art(gid.split(":", 1)[1], "library_600x900"):
            return False
        a = self._data["art"].get(gid)
        if not a or a.get("v", 1) < ART_VERSION:
            return True
        if full and a.get("partial"):
            return True  # was fetched while uninstalled: now get the banner and logo too
        if a.get("src") and os.path.isfile(a["src"]):
            return False
        return time.time() - a.get("t", 0) > 3 * 86400  # nothing found last time: retry every few days

    def _fetch_art(self, games=None, installed=True):
        """Download cover art. Installed games also get banner + logo; not-installed games just covers."""
        flag = "_art_running" if installed else "_art_un_running"
        with self._lock:
            if getattr(self, flag, False):
                return
            setattr(self, flag, True)
        try:
            todo = [g for g in list(self._games if games is None else games) if self._needs_art(g, full=installed)]
            if installed:
                self._prog.update(art_done=0, art_total=len(todo), art_name="")
            for i, g in enumerate(todo):
                if self._quitting:
                    break
                if installed:
                    self._prog["art_name"] = g["name"]
                try:
                    c = art_candidates(g)
                    base = os.path.join(ART_DIR, safe_file(g["id"]))
                    src = download_image(c["tall"] or c["wide"], base + "_tall")
                    wsrc = download_image(c["wide"], base + "_wide") if c["wide"] and c["tall"] else None
                    hsrc = download_image(c["hero"], base + "_hero") if c["hero"] and installed else None
                    lsrc = download_image(c["logo"], base + "_logo") if c["logo"] and installed else None
                except Exception as e:
                    print("art:", g["name"], e)
                    src = wsrc = hsrc = lsrc = None
                with self._lock:
                    self._data["art"][g["id"]] = {"src": src, "wide": wsrc, "hero": hsrc, "logo": lsrc,
                                                  "t": time.time(), "v": ART_VERSION, "partial": not installed}
                    self._covers.pop(g["id"], None)
                    self._covers.pop("hero:" + g["id"], None)
                    self._version += 1
                if installed:
                    self._prog["art_done"] = i + 1
                if i % 10 == 9:
                    self._save()
                time.sleep(0.25)
            self._save()
        finally:
            setattr(self, flag, False)

    # ---------- game details
    def _needs_details(self, gid):
        d = self._data["details"].get(gid)
        if not d:
            return True
        age = time.time() - d.get("t", 0)
        return age > (DETAILS_TTL if d.get("desc") or d.get("genres") else 3 * 86400)

    def _lookup_details(self, g):
        try:
            d = game_details(g) or {}
        except Exception as e:
            print("details:", g["name"], e)
            d = {}
        d["t"] = time.time()
        with self._lock:
            self._data["details"][g["id"]] = d
        return d

    def _fetch_details(self):
        todo = [g for g in list(self._games) if self._needs_details(g["id"])]
        self._prog.update(det_done=0, det_total=len(todo))
        for i, g in enumerate(todo):
            if self._quitting:
                break
            self._lookup_details(g)
            self._prog["det_done"] = i + 1
            if i % 10 == 9:
                self._save()
            time.sleep(0.2)
        if todo:
            self._save()

    def _cover_rev(self, gid):
        a = self._data["art"].get(gid, {})
        return f'{self._data["covers"].get(gid, "")}|{a.get("t", 0)}'

    # ---------- tracking
    def _recover_sessions(self):
        """Close sessions left open by a crash or shutdown, ending at the last time they were seen."""
        for gid, v in list(self._data.get("active", {}).items()):
            self._active[gid] = v.get("start", 0)
            self._close_session(gid, v.get("seen", 0))
        self._data["active"] = {}

    def _close_session(self, gid, end):
        start = self._active.pop(gid, None)
        if start is None or end - start < MIN_SESSION:
            return
        t = self._data["tracked"].setdefault(gid, {"total": 0, "last": 0})
        t["total"] += end - start
        t["last"] = max(t["last"], end)
        cutoff = time.time() - 30 * 86400
        self._data["sessions"] = [s for s in self._data["sessions"] if s[2] > cutoff] + [[gid, start, end]]

    def _match(self, exe):
        for prefix, gid in self._prefixes:
            if exe.startswith(prefix):
                return gid
        return None

    def _tracker(self):
        last_save = last_refresh = last_upd = last_scan = last_sig_check = time.time()
        last_self, last_self_url = time.time() - 1800 + 20, 0   # first update check ~20 s after start
        lib_sig = library_signature()
        while not self._quitting:
            try:
                now = time.time()
                if self._data["settings"].get("tracking", True) and self._prefixes:
                    seen = {gid for gid in map(self._match, running_exe_paths()) if gid}
                    with self._lock:
                        started = seen - set(self._active)
                        ended = [gid for gid in self._active if gid not in seen]
                        for gid in started:
                            self._active[gid] = now
                        for gid in ended:
                            self._close_session(gid, now)
                        self._data["active"] = {g: {"start": s, "seen": now} for g, s in self._active.items()}
                        if started or ended:
                            self._version += 1
                    if ended or (self._active and now - last_save > 60):
                        self._save()
                        last_save = now
                    if ended:
                        time.sleep(5)  # give the launcher a moment to write its own playtime
                        last_refresh = 0
                if now - last_upd > 60:  # launchers change update state in the background
                    ups = update_states()
                    with self._lock:
                        if ups != self._updates:
                            self._updates = ups
                            self._version += 1
                    last_upd = time.time()
                if not self._active:  # never rescan in the middle of a game
                    sig = library_signature() if now - last_sig_check > 60 else lib_sig
                    if now - last_sig_check > 60:
                        last_sig_check = now
                    if sig != lib_sig or now - last_scan > 1800:
                        lib_sig = sig
                        threading.Thread(target=self._scan, daemon=True).start()
                        last_scan = time.time()
                if self._data["settings"].get("check_updates", True) and now - last_self > 1800:
                    use_url = now - last_self_url > 6 * 3600
                    threading.Thread(target=self._check_app_update, args=(use_url,), daemon=True).start()
                    last_self = now
                    if use_url:
                        last_self_url = now
                if now - last_refresh > 300:
                    stats = launcher_playtime()
                    with self._lock:
                        if stats != self._launcher_stats:
                            self._launcher_stats = stats
                            self._version += 1
                    last_refresh = time.time()
            except Exception as e:
                print("tracker:", e)
            time.sleep(POLL_SECONDS)

    def _stats(self, gid, now, recent_tracked):
        src = self._launcher_stats.get(gid)
        tr = self._data["tracked"].get(gid, {})
        live = now - self._active[gid] if gid in self._active else 0
        if src and src.get("total"):
            total = src["total"] + live
            recent = src["recent"] + live if src.get("recent") is not None else recent_tracked + live
            source = src["source"]
        elif tr.get("total") or live:
            total, recent, source = tr.get("total", 0) + live, recent_tracked + live, "Game Hub"
        else:
            total, recent, source = 0, 0, (src or {}).get("source")
        last = max((src or {}).get("last", 0), tr.get("last", 0), now if live else 0)
        if last < now - TWO_WEEKS:
            recent = 0  # launchers can keep stale "last 2 weeks" numbers
        return int(total), int(recent), int(last), source

    # ---------- API: state
    def get_state(self):
        with self._lock:
            now = time.time()
            recent = {}
            for gid, s, e in self._data["sessions"]:
                overlap = min(e, now) - max(s, now - TWO_WEEKS)
                if overlap > 0:
                    recent[gid] = recent.get(gid, 0) + overlap
            d, games = self._data, []
            custom_ids = {c["id"] for c in d["custom"]}
            for g in self._games:
                total, rec, last, source = self._stats(g["id"], now, recent.get(g["id"], 0))
                games.append({
                    "id": g["id"], "name": g["name"], "launcher": g["launcher"], "path": g["path"],
                    "size": g["size"] or 0, "fav": g["id"] in d["favorites"], "hidden": g["id"] in d["hidden"],
                    "collection": d["collections"].get(g["id"], ""), "custom": g["id"] in custom_ids,
                    "playing": g["id"] in self._active, "total": total, "recent": rec, "last": last,
                    "source": source, "cv": self._cover_rev(g["id"]), "update": self._updates.get(g["id"], ""),
                })
            uninstalled = []
            for g in self._uninstalled:
                total, rec, last, source = self._stats(g["id"], now, recent.get(g["id"], 0))
                uninstalled.append({
                    "id": g["id"], "name": g["name"], "launcher": g["launcher"], "path": None, "size": 0,
                    "fav": g["id"] in d["favorites"], "hidden": g["id"] in d["hidden"], "collection": d["collections"].get(g["id"], ""),
                    "custom": False, "playing": False, "total": total, "recent": rec, "last": last, "source": source,
                    "cv": self._cover_rev(g["id"]), "update": "", "installed": False, "canInstall": bool(g.get("install")),
                })
            settings = dict(d["settings"])
            settings["startup"] = os.path.exists(startup_file())
            k = settings.pop("steam_api_key", "")
            settings["steam_key_hint"] = ("••••" + k[-4:]) if k else ""   # the key itself never leaves Python
            for k in ("update_token", "update_url"):   # update source stays out of the window
                settings.pop(k, None)
            return {"games": games, "uninstalled": uninstalled, "version": self._version, "scanning": self._scanning,
                    "collections": sorted(set(d["collections"].values()), key=str.lower),
                    "settings": settings, "tray": bool(self._tray), "windows": os.name == "nt",
                    "app_version": VERSION,
                    "install": {"running_installed": running_installed(), "installed_version": installed_version()},
                    "app_update": {"version": self._app_update["version"], "notes": self._app_update["notes"],
                                   "source": "Downloads" if self._app_update["source"] == "Downloads" else ""} if self._app_update else None}

    def get_progress(self):
        with self._lock:
            return dict(self._prog, ready=self._ready, scanning=self._scanning, games=len(self._games))

    def get_live(self):
        with self._lock:
            return {"version": self._version, "playing": list(self._active)}

    def rescan(self):
        """Rescan button: every launcher and every folder, read fresh. Returns once it's finished."""
        before = {g["id"] for g in self._games}
        un_before = {g["id"] for g in self._uninstalled}
        with self._scan_lock:          # let any scan already running finish first
            clear_scan_caches()
            with self._lock:
                self._friends = None
        self._scan(wait=True)
        after = {g["id"] for g in self._games}
        st = self.get_state()
        st["rescan"] = {"total": len(after), "added": len(after - before), "removed": len(before - after),
                        "uninstalled": len(self._uninstalled), "new_uninstalled": len({g["id"] for g in self._uninstalled} - un_before),
                        "names": sorted(self._by_id[i]["name"] for i in after - before)[:3]}
        return st

    # ---------- API: actions
    def play(self, gid):
        g = self._by_id.get(gid)
        if not g:
            return {"ok": False, "error": "Game not found - try Rescan."}
        if g["launcher"] == "RSI" and not g["launch"]:
            g["launch"] = find_rsi_launcher()  # launcher may have been installed since the scan
            if not g["launch"]:
                return {"ok": False, "error": "The RSI Launcher wasn't found. Open it yourself to start Star Citizen."}
        target = g["launch"] or g["path"]
        try:
            if "://" in target or not os.path.isfile(target):
                open_path(target)
            else:
                try:
                    subprocess.Popen([target], cwd=os.path.dirname(target))
                except OSError:  # e.g. needs admin rights
                    open_path(target)
        except Exception as e:
            return {"ok": False, "error": str(e)}
        if g["launcher"] == "Xbox":
            return {"ok": True, "note": "Xbox games start from the Xbox app - opened the game folder."}
        if g["launcher"] == "RSI":
            return {"ok": True, "note": "Opening the RSI Launcher - press Launch Game there."}
        return {"ok": True}

    def open_folder(self, gid):
        g = self._by_id.get(gid)
        if g and g["path"]:
            open_path(g["path"] if os.path.isdir(g["path"]) else os.path.dirname(g["path"]))

    def _toggle(self, listname, gid):
        with self._lock:
            lst = self._data[listname]
            if gid in lst:
                lst.remove(gid)
            else:
                lst.append(gid)
        self._bump()
        return self.get_state()

    def toggle_favorite(self, gid):
        return self._toggle("favorites", gid)

    def toggle_hidden(self, gid):
        return self._toggle("hidden", gid)

    def set_collection(self, gid, name):
        with self._lock:
            name = (name or "").strip()
            if name:
                self._data["collections"][gid] = name
            else:
                self._data["collections"].pop(gid, None)
        self._bump()
        return self.get_state()

    def _open_dialog(self, types):
        if not self._window:
            return None
        kind = getattr(getattr(webview, "FileDialog", None), "OPEN", None) or webview.OPEN_DIALOG
        result = self._window.create_file_dialog(kind, file_types=types)
        return result[0] if result else None

    def pick_exe(self):
        path = self._open_dialog(("Programs (*.exe)", "All files (*.*)"))
        if not path:
            return None
        return {"path": path, "name": os.path.basename(os.path.dirname(path))}

    def add_custom(self, path, name):
        if not path or not os.path.isfile(path):
            return self.get_state()
        gid = f"custom:{os.path.normcase(path)}"
        with self._lock:
            self._data["custom"] = [c for c in self._data["custom"] if c["id"] != gid]
            self._data["custom"].append({"id": gid, "name": name.strip() or os.path.basename(path),
                                         "path": os.path.dirname(path), "launch": path})
        self._save()
        self._scan(wait=True)
        return self.get_state()

    def remove_custom(self, gid):
        with self._lock:
            self._data["custom"] = [c for c in self._data["custom"] if c["id"] != gid]
        self._save()
        self._scan(wait=True)
        return self.get_state()

    def pick_cover(self, gid):
        path = self._open_dialog(("Images (*.jpg;*.jpeg;*.png;*.webp)", "All files (*.*)"))
        if path:
            with self._lock:
                self._data["covers"][gid] = path
                self._covers.pop(gid, None)
                self._covers.pop("hero:" + gid, None)
                self._data["art"].pop(gid, None)
            self._bump()
        return bool(path)

    def clear_cover(self, gid):
        with self._lock:
            self._data["covers"].pop(gid, None)
            self._covers.pop(gid, None)
            self._covers.pop("hero:" + gid, None)
        self._bump()
        return True

    def get_cover(self, gid):
        # Not cached here on purpose: the window keeps its own copy, so a second one would just use memory.
        res = {}
        custom = self._data["covers"].get(gid)
        art = self._data["art"].get(gid) or {}
        steam_local = gid.startswith("steam:") and local_steam_art(gid.split(":", 1)[1], "library_600x900")
        if custom and os.path.isfile(custom):
            uri = data_uri(custom, "tall")
            res = {"src": uri, "wide": uri}
        elif not steam_local and art.get("src") and os.path.isfile(art["src"]):
            uri = data_uri(art["src"], "tall")
            wide = data_uri(art["wide"], "wide") if art.get("wide") and os.path.isfile(art["wide"]) else None
            res = {"src": uri, "wide": wide or uri}
        elif gid in self._un_by_id and (self._un_by_id[gid].get("art") or {}).get("tall"):
            a = self._un_by_id[gid]["art"]
            res = {"src": a["tall"], "wide": a.get("wide") or a["tall"]}
        elif gid.startswith("steam:"):
            appid = gid.split(":", 1)[1]
            cdn = f"https://cdn.cloudflare.steamstatic.com/steam/apps/{appid}/"
            portrait = local_steam_art(appid, "library_600x900")
            header = local_steam_art(appid, "header")
            header_src = (data_uri(header, "wide") if header else None) or cdn + "header.jpg"
            res = {"src": (data_uri(portrait, "tall") if portrait else None) or cdn + "library_600x900.jpg",
                   "fallback": header_src, "wide": header_src}
        res["cv"] = self._cover_rev(gid)
        return res

    def get_hero(self, gid):
        """Big banner art + logo for the Home hero. Loaded only for the few featured games."""
        res = {}
        art = self._data["art"].get(gid) or {}
        if self._data["covers"].get(gid):
            pass  # user picked a cover: use it everywhere, no separate banner
        else:
            for k in ("hero", "logo"):
                if art.get(k) and os.path.isfile(art[k]):
                    res[k] = data_uri(art[k], k)
            if gid.startswith("steam:"):
                appid = gid.split(":", 1)[1]
                cdn = f"https://cdn.cloudflare.steamstatic.com/steam/apps/{appid}/"
                if "hero" not in res:
                    p = local_steam_art(appid, "library_hero")
                    res["hero"] = (data_uri(p, "hero") if p else None) or cdn + "library_hero.jpg"
                if "logo" not in res:
                    p = local_steam_art(appid, "logo", "png")
                    res["logo"] = (data_uri(p, "logo") if p else None) or cdn + "logo.png"
        return res

    def get_details(self, gid):
        d = self._data["details"].get(gid)
        g = self._by_id.get(gid) or self._un_by_id.get(gid)
        if d is None and g:
            d = self._lookup_details(g)
            self._save()
        return {k: v for k, v in (d or {}).items() if k != "t"}

    # ---------- friends
    def get_friends(self, force=False):
        now = time.time()
        if self._friends and not force and now - self._friends_t < FRIEND_TTL:
            return self._friends
        sources = {}
        if find_steam_root():
            me, key = steam_login_user(), self._data["settings"].get("steam_api_key", "")
            src = {"signed_in": bool(me), "has_key": bool(key), "live": False, "error": None,
                   "me": (me or {}).get("name"), "friends": []}
            if me:
                saved = steam_saved_friends(me["account"])
                if key:
                    live, err = steam_live_friends(key, me["id64"], saved)
                    if live is not None:
                        src["friends"], src["live"] = live, True
                    else:
                        src["error"] = {401: "private", 403: "badkey"}.get(err, "network")
                if not src["live"]:
                    src["friends"] = [{"id": "steam:" + f["steamid"], "launcher": "Steam", "name": f["name"],
                                       "nick": f["nick"], "avatar": f["avatar"], "status": "unknown"} for f in saved]
            sources["steam"] = src
        rc = riot_client_path()
        if rc or riot_lockfile():
            fr = riot_friends()
            sources["riot"] = {"running": fr is not None, "client": bool(rc), "friends": fr or []}
        names = {_norm(g["name"]): g["id"] for g in self._games}
        for src in sources.values():
            for f in src["friends"]:
                lib = f.get("game_key") if f.get("game_key") in self._by_id else names.get(_norm(f.get("game") or ""))
                f["lib"] = lib
        self._friends, self._friends_t = {"sources": sources}, now
        return self._friends

    def friend_action(self, fid, action):
        plat, _, ident = fid.partition(":")
        f = next((x for s in ((self._friends or {}).get("sources") or {}).values() for x in s["friends"] if x["id"] == fid), {})
        try:
            if action == "copy":
                text = f"{f.get('name', '')}#{f['tag']}" if f.get("tag") else f.get("name", "")
                return {"ok": copy_text(text), "text": text}
            if plat == "steam":
                url = {"message": f"steam://friends/message/{ident}", "profile": f"steam://url/SteamIDPage/{ident}",
                       "join": f.get("join"), "friends": "steam://open/friends"}.get(action)
                if not url:
                    return {"ok": False, "error": "That isn't available right now."}
                open_path(url)
            elif plat == "riot" and action == "client":
                path = riot_client_path()
                if not path:
                    return {"ok": False, "error": "The Riot Client wasn't found."}
                subprocess.Popen([path])
        except Exception as e:
            return {"ok": False, "error": str(e)}
        return {"ok": True}

    def open_riot_client(self):
        return self.friend_action("riot:", "client")

    # ---------- updating Game Hub itself
    def _check_app_update(self, use_url=True):
        cur, best = parse_version(VERSION), None
        me = os.path.normcase(os.path.abspath(__file__))

        def better(h):
            return h and parse_version(h["version"]) > cur and (not best or parse_version(h["version"]) > parse_version(best["version"]))

        for f in glob.glob(os.path.join(downloads_dir(), "game_hub*.py")):
            if os.path.normcase(os.path.abspath(f)) == me:
                continue
            try:
                with open(f, encoding="utf-8", errors="ignore") as fh:
                    h = read_header(fh.read(16000))
                    if not better(h):
                        continue           # cheap: most checks stop here after reading the first few KB
                    fh.seek(0)
                    if not valid_update(fh.read()):
                        continue           # incomplete or broken copy: never offer it
            except OSError:
                continue
            best = dict(h, source="Downloads", path=f)
        url = self._data["settings"].get("update_url") or DEFAULT_UPDATE_URL
        if use_url and url:
            token = unseal(self._data["settings"].get("update_token", ""))
            cache = self._data.setdefault("update_cache", {})
            known = cache.get(url) or {}
            text, err, tag = fetch_update_link(url, token, known.get("etag") if known.get("version") else None)
            if err == "unchanged":
                h, text, err = {"version": known["version"], "notes": known.get("notes", "")}, None, None
                held = self._app_update if (self._app_update or {}).get("version") == h["version"] else None
                if better(h):
                    if held and held.get("text"):
                        text = held["text"]                    # already downloaded it this session
                    else:                                      # an update is waiting: download it this once
                        text, err, tag = fetch_update_link(url, token)
            h = read_header(text) if text else (None if err else h)
            if text and not h:
                err = "notgamehub"
            if text and h:
                cache[url] = {"etag": tag, "version": h["version"], "notes": h["notes"]}
                self._save()
            self._update_err = err
            if text and better(h) and valid_update(text):
                best = dict(h, source="update link", text=text)
        elif use_url:
            self._update_err = None
        with self._lock:
            if (best or {}).get("version") != (self._app_update or {}).get("version"):
                self._version += 1
            self._app_update = best
        return best

    def add_game_folder(self):
        if not self._window:
            return self.get_state()
        kind = getattr(getattr(webview, "FileDialog", None), "FOLDER", None) or webview.FOLDER_DIALOG
        res = self._window.create_file_dialog(kind)
        path = res[0] if res else None
        if path:
            with self._lock:
                folders = self._data["settings"].setdefault("game_folders", [])
                if path not in folders:
                    folders.append(path)
            self._save()
            self._scan(wait=True)
        return self.get_state()

    def remove_game_folder(self, path):
        with self._lock:
            self._data["settings"]["game_folders"] = [f for f in self._data["settings"].get("game_folders", []) if f != path]
        self._save()
        self._scan(wait=True)
        return self.get_state()

    def check_app_update(self):
        found = self._check_app_update(use_url=True)
        return {"found": bool(found), "error": getattr(self, "_update_err", None), "state": self.get_state()}

    def pick_update_file(self):
        path = self._open_dialog(("Game Hub (game_hub*.py)", "Python files (*.py)"))
        if not path:
            return None
        try:
            with open(path, encoding="utf-8", errors="ignore") as f:
                h = read_header(f.read(16000))
        except OSError as e:
            return {"error": str(e)}
        if not h:
            return {"error": "That file isn't a copy of Game Hub."}
        return dict(h, path=path, newer=parse_version(h["version"]) > parse_version(VERSION))

    def apply_app_update(self, path=None):
        u = self._app_update
        if path:
            u = {"path": path}
        if not u:
            return {"ok": False, "error": "No update is ready."}
        text = u.get("text")
        try:
            if text is None:
                with open(u["path"], encoding="utf-8", errors="ignore", newline="") as f:
                    text = f.read()
        except OSError as e:
            return {"ok": False, "error": str(e)}
        if not valid_update(text):
            return {"ok": False, "error": "That file isn't a working copy of Game Hub, so nothing was changed."}
        new = read_header(text)["version"]
        me = os.path.abspath(__file__)
        try:
            os.makedirs(os.path.join(DATA_DIR, "backup"), exist_ok=True)
            shutil.copy2(me, os.path.join(DATA_DIR, "backup", f"game_hub_{VERSION}.py"))
            prune_backups()
            tmp = me + ".new"
            with open(tmp, "w", encoding="utf-8", newline="") as f:
                f.write(text)
            os.replace(tmp, me)
        except OSError as e:
            return {"ok": False, "error": f"Couldn't replace Game Hub's file: {e}"}
        cmd = [sys.executable] if getattr(sys, "frozen", False) else [gui_python(), me]
        self._relaunch = cmd + ["--updated"]
        threading.Timer(0.6, self._quit).start()
        return {"ok": True, "version": new}

    # ---------- uninstall / repair / update
    def _find_uninstaller(self, path):
        """The Windows uninstall command registered for a game folder, if any."""
        if not winreg or not path:
            return None
        want = os.path.normcase(os.path.normpath(path)).rstrip("\\/")
        key = r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall"
        for root, view in ((winreg.HKEY_LOCAL_MACHINE, _view("KEY_WOW64_64KEY")),
                           (winreg.HKEY_LOCAL_MACHINE, _view("KEY_WOW64_32KEY")), (winreg.HKEY_CURRENT_USER, 0)):
            for _, v in reg_subkeys(root, key, view):
                loc = (v.get("InstallLocation") or "").strip().strip('"')
                cmd = v.get("UninstallString")
                if loc and cmd and os.path.normcase(os.path.normpath(loc)).rstrip("\\/") == want:
                    return cmd
        return None

    def _rescan_soon(self):
        for delay in (45, 180):
            t = threading.Timer(delay, lambda: self._quitting or self._scan())
            t.daemon = True   # never keeps Game Hub alive after you quit
            t.start()

    def uninstall_game(self, gid):
        g = self._by_id.get(gid)
        if not g:
            return {"ok": False, "error": "Game not found - try Rescan."}
        plat, _, ident = gid.partition(":")
        try:
            if plat == "steam":
                open_path(f"steam://uninstall/{ident}")
                how = "steam"
            elif plat == "epic":
                open_path("com.epicgames.launcher://library")
                how = "epic"
            elif plat == "xbox":
                open_path("ms-settings:appsfeatures")
                how = "settings"
            elif plat == "itch":
                open_path("itch://library")
                how = "itch"
            elif plat == "rsi":
                launcher = find_rsi_launcher()
                if not launcher:
                    return {"ok": False, "error": "The RSI Launcher wasn't found on this PC."}
                open_path(launcher)
                how = "rsi"
            else:
                cmd = self._find_uninstaller(g["path"])
                if not cmd and plat == "sa":
                    local = next((e.path for e in _entries(g["path"]) if re.match(r"unins\d*\.exe$", e.name, re.I)), None)
                    cmd = f'"{local}"' if local else None
                    if not cmd:
                        return {"ok": False, "error": "This game has no uninstaller. To remove it, delete its folder (⋯ → Open folder)."}
                if cmd:
                    subprocess.Popen(cmd, shell=True, cwd=g["path"] if os.path.isdir(g["path"] or "") else None)
                    how = "uninstaller"
                else:
                    open_path("ms-settings:appsfeatures")
                    how = "settings"
        except Exception as e:
            return {"ok": False, "error": str(e)}
        self._rescan_soon()
        return {"ok": True, "how": how}

    def repair_game(self, gid):
        plat, _, ident = gid.partition(":")
        try:
            if plat == "steam":
                open_path(f"steam://validate/{ident}")
            elif plat == "epic":
                open_path("com.epicgames.launcher://library")
            else:
                return {"ok": False, "error": "This launcher can't be asked to repair games from here."}
        except Exception as e:
            return {"ok": False, "error": str(e)}
        return {"ok": True}

    def open_launcher(self, which):
        target = {"steam": "steam://open/downloads", "epic": "com.epicgames.launcher://library"}.get(which)
        if target:
            try:
                open_path(target)
            except Exception as e:
                return {"error": str(e)}
        return {}

    def open_url(self, url):
        if isinstance(url, str) and url.startswith(("https://", "http://")):
            webbrowser.open(url)

    def set_setting(self, key, value):
        if key == "startup":
            try:
                set_startup(bool(value))
            except OSError as e:
                return {"error": str(e)}
        elif key == "steam_api_key":
            v = (value or "").strip()
            if v and not re.fullmatch(r"[0-9A-Fa-f]{32}", v):
                return {"error": "That doesn't look like a Steam Web API key. It should be 32 letters and numbers."}
            with self._lock:
                self._data["settings"]["steam_api_key"] = v.upper()
                self._friends = None
            self._bump()
        elif key == "update_url":
            with self._lock:
                self._data["settings"]["update_url"] = (value or "").strip()
            self._bump()
        elif key == "update_token":
            v = (value or "").strip()
            if v and not re.fullmatch(r"(github_pat_|ghp_)[A-Za-z0-9_]{20,}", v):
                return {"error": "That doesn't look like a GitHub token. It should start with github_pat_ or ghp_."}
            with self._lock:
                self._data["settings"]["update_token"] = seal(v)
            self._bump()
        elif key in ("tracking", "close_to_tray", "show_hidden", "hover_play", "check_updates", "find_standalone"):
            with self._lock:
                self._data["settings"][key] = bool(value)
            self._bump()
            if key == "find_standalone":
                threading.Thread(target=self._scan, daemon=True).start()
        return self.get_state()

    def _quit_watch(self):
        """The installer and uninstaller leave a note asking Game Hub to quit, so it can save first."""
        me = str(os.getpid())
        while not self._quitting:
            try:
                if os.path.exists(QUIT_FILE) and open(QUIT_FILE).read().strip() == me:
                    os.remove(QUIT_FILE)
                    self._quit()
                    return
            except OSError:
                pass
            time.sleep(1)

    def uninstall(self):
        # the uninstaller asks this window to close (saving first), so no need to quit here
        setup_uninstaller = os.path.join(INSTALL_DIR, "unins000.exe")
        if setup_installed() and os.path.isfile(setup_uninstaller):
            subprocess.Popen([setup_uninstaller])
        else:
            subprocess.Popen([gui_python(), os.path.abspath(__file__), "--uninstall"])
        return True

    def install_on_pc(self):
        subprocess.Popen([gui_python(), os.path.abspath(__file__), "--install"])
        return True

    # ---------- window / tray
    def _on_closing(self):
        # Windows waits for this answer before doing anything else, so answer at once and never touch
        # the window from in here (doing so made both sides wait for each other and froze the app).
        if self._tray and not self._quitting and self._data["settings"].get("close_to_tray", True):
            threading.Thread(target=self._to_tray, daemon=True).start()
            return False
        return True

    def _to_tray(self):
        time.sleep(0.15)          # let Windows finish handling the close first
        try:
            self._window.hide()
        except Exception as e:
            log_problem("hiding the window", e)
        self._sleep(True)

    def _sleep(self, on):
        """In the tray: let the window drop its pictures while nobody's looking."""
        try:
            self._window.evaluate_js(f"window.sleepMode&&sleepMode({'true' if on else 'false'})")
        except Exception:
            pass

    def _start_tray(self):
        if not pystray:
            return
        img = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
        d = ImageDraw.Draw(img)
        d.rounded_rectangle((2, 2, 62, 62), 16, fill=(124, 92, 255, 255))
        d.polygon([(25, 18), (25, 46), (47, 32)], fill=(255, 255, 255, 255))
        menu = pystray.Menu(pystray.MenuItem("Open Game Hub", lambda: self._show(), default=True),
                            pystray.MenuItem("Quit", lambda: self._quit()))
        self._tray = pystray.Icon("GameHub", img, APP_NAME, menu)
        threading.Thread(target=self._tray.run, daemon=True).start()

    def _show(self):
        if not self._window:
            return
        try:
            self._window.show()
            self._window.restore()
        except Exception as e:
            log_problem("showing the window", e)
        self._sleep(False)

    def _quit(self):
        self._quitting = True
        if self._window:
            try:
                self._window.destroy()
            except Exception as e:
                log_problem("closing the window", e)

    def _shutdown(self):
        self._quitting = True
        with self._lock:
            now = time.time()
            for gid in list(self._active):
                self._close_session(gid, now)
            self._data["active"] = {}
        self._save()
        try:
            os.remove(PID_FILE)
        except OSError:
            pass
        if self._tray:
            try:
                self._tray.stop()
            except Exception:
                pass


# ======================================================================= UI
HTML = r"""<!doctype html>
<html><head><meta charset="utf-8"><title>Game Hub</title>
<style>
:root{--bg:#0a0c11;--side:#0e1117;--surface:#141821;--surface2:#1b202b;--line:#222838;--text:#eceef4;
--muted:#8d95a9;--faint:#596178;--accent:#7c5cff;--accent2:#22d3ee;--good:#34d399;--r:14px}
*{box-sizing:border-box}
html,body{margin:0;height:100%;background:var(--bg);color:var(--text);overflow:hidden;
font:14px/1.4 "Segoe UI Variable Text","Segoe UI",system-ui,sans-serif;-webkit-font-smoothing:antialiased}
button{font:inherit;color:inherit}
svg.i{width:18px;height:18px;fill:none;stroke:currentColor;stroke-width:2;stroke-linecap:round;stroke-linejoin:round;flex:none}
::-webkit-scrollbar{width:12px;height:12px}::-webkit-scrollbar-thumb{background:#262c3b;border-radius:8px;border:3px solid transparent;background-clip:padding-box}
::-webkit-scrollbar-thumb:hover{background-color:#323a4d}::-webkit-scrollbar-track{background:transparent}
.app{display:grid;grid-template-columns:250px 1fr;grid-template-rows:minmax(0,1fr);height:100vh}

/* sidebar */
aside{min-height:0;background:var(--side);border-right:1px solid var(--line);display:flex;flex-direction:column;padding:20px 12px 14px;overflow:auto}
.brand{display:flex;align-items:center;gap:11px;padding:2px 10px 20px;font-weight:700;font-size:17px;letter-spacing:.2px}
.logo{width:34px;height:34px;border-radius:11px;background:linear-gradient(135deg,var(--accent),var(--accent2));display:grid;place-items:center;box-shadow:0 8px 24px -8px rgba(124,92,255,.8)}
.logo svg{width:16px;height:16px;fill:#fff;stroke:none}
.sec{font-size:10.5px;font-weight:700;letter-spacing:1.4px;color:var(--faint);padding:18px 12px 7px;text-transform:uppercase}
.nav{display:flex;align-items:center;gap:11px;padding:8px 12px;border-radius:10px;color:var(--muted);cursor:pointer;user-select:none;transition:background .15s,color .15s}
.nav:hover{background:var(--surface);color:var(--text)}
.nav.active{background:linear-gradient(90deg,rgba(124,92,255,.24),rgba(124,92,255,.04));color:#fff;box-shadow:inset 3px 0 0 var(--accent)}
.nav .n{margin-left:auto;font-size:12px;color:var(--faint);font-variant-numeric:tabular-nums}
.nav.active .n{color:#b9b0ff}
.dot{width:8px;height:8px;border-radius:50%;flex:none}
.nav .dot{margin:0 5px}
.side-foot{margin-top:auto;padding:14px 12px 2px;border-top:1px solid var(--line);display:flex;align-items:center;gap:8px;color:var(--muted);font-size:12px}
.pulse{width:8px;height:8px;border-radius:50%;background:var(--good)}
.pulse.off{background:var(--faint);animation:none}
@keyframes pulse{0%{box-shadow:0 0 0 0 rgba(52,211,153,.55)}70%{box-shadow:0 0 0 8px rgba(52,211,153,0)}100%{box-shadow:0 0 0 0 rgba(52,211,153,0)}}

/* top bar */
main{display:flex;flex-direction:column;min-width:0;min-height:0;position:relative}
.top{display:flex;align-items:center;gap:10px;padding:18px 30px;border-bottom:1px solid var(--line);background:rgba(10,12,17,.85);}
.title{font-size:23px;font-weight:700;margin-right:auto;letter-spacing:-.2px;white-space:nowrap}
.title small{font-size:13px;color:var(--muted);font-weight:500;margin-left:10px;letter-spacing:0}
.search{position:relative}
.search svg{position:absolute;left:12px;top:50%;transform:translateY(-50%);color:var(--faint);width:16px;height:16px}
.search input{width:260px;background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:9px 12px 9px 36px;color:var(--text);outline:none;font:inherit;transition:border-color .15s,box-shadow .15s}
.search input:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(124,92,255,.2)}
select{background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:8px 10px;color:var(--text);font:inherit;outline:none;cursor:pointer}
.btn{display:inline-flex;align-items:center;gap:8px;background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:8px 13px;cursor:pointer;transition:background .15s,border-color .15s,transform .1s;white-space:nowrap}
.btn:hover{background:var(--surface2);border-color:#2e3548}
.btn:active{transform:scale(.97)}
.btn.icon{padding:8px}
.btn.primary{background:linear-gradient(135deg,#8669ff,#6a48ff);border-color:transparent;color:#fff;box-shadow:0 8px 22px -10px rgba(124,92,255,.9)}
.btn.primary:hover{filter:brightness(1.08)}
.btn.danger:hover{border-color:#5b2a35;color:#ff8b9b}
.seg{display:flex;background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:3px}
.seg button{background:none;border:0;padding:5px 8px;border-radius:7px;cursor:pointer;color:var(--muted);display:grid;place-items:center}
.seg button.on{background:var(--surface2);color:#fff}
.spin svg{animation:spin 1s linear infinite}@keyframes spin{to{transform:rotate(360deg)}}

/* content */
.content{flex:1;min-height:0;overflow:auto;padding:26px 30px 50px}
.stats{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:14px;margin-bottom:30px}
.stat{background:linear-gradient(180deg,var(--surface),#11141c);border:1px solid var(--line);border-radius:var(--r);padding:16px 18px;position:relative;overflow:hidden}
.stat::after{content:"";position:absolute;right:-30px;top:-30px;width:90px;height:90px;border-radius:50%;background:radial-gradient(circle,rgba(124,92,255,.18),transparent 70%)}
.stat span{color:var(--muted);font-size:12px;font-weight:500}
.stat b{display:block;font-size:25px;font-weight:700;margin-top:4px;letter-spacing:-.3px;font-variant-numeric:tabular-nums}
.h3{font-size:15px;font-weight:650;margin:0 0 14px;display:flex;align-items:center;gap:8px}
.h3 em{font-style:normal;color:var(--faint);font-weight:500;font-size:13px}
.shead{display:flex;align-items:center;justify-content:space-between;margin:0 0 8px}
.h3link{display:inline-flex;align-items:center;gap:8px;background:none;border:0;padding:4px 8px 4px 0;font-size:15px;font-weight:650;cursor:pointer;color:var(--text);border-radius:8px}
.h3link em{font-style:normal;color:var(--faint);font-weight:500;font-size:13px}
.h3link svg{width:16px;height:16px;color:var(--faint);transition:transform .15s,color .15s}
.h3link:hover{color:#fff}.h3link:hover svg{transform:translateX(3px);color:#b9b0ff}
.arrows{display:flex;gap:6px}
.arr{width:34px;height:34px;border-radius:50%;border:1px solid var(--line);background:var(--surface);display:grid;place-items:center;cursor:pointer;transition:background .15s,opacity .15s}
.arr:hover{background:var(--surface2)}.arr:disabled{opacity:.3;cursor:default}
.arr svg{width:16px;height:16px}
.slider{display:grid;grid-auto-flow:column;grid-auto-columns:168px;gap:18px;overflow-x:auto;overflow-y:hidden;padding:10px 4px 14px;margin:0 -4px 22px;scroll-snap-type:x proximity;scrollbar-width:none;
  -webkit-mask-image:linear-gradient(90deg,#000 calc(100% - 40px),transparent);mask-image:linear-gradient(90deg,#000 calc(100% - 40px),transparent)}
.slider.end{-webkit-mask-image:none;mask-image:none}
.slider::-webkit-scrollbar{display:none}
.slider>*{scroll-snap-align:start}
.slider.wides{grid-auto-columns:minmax(290px,320px)}
.seeall{display:flex;flex-direction:column;align-items:center;justify-content:center;gap:10px;aspect-ratio:2/3;border-radius:12px;border:1.5px dashed #2e3548;color:var(--muted);cursor:pointer;font-weight:600;transition:border-color .15s,color .15s,background .15s;text-align:center;padding:10px}
.seeall:hover{border-color:var(--accent);color:#fff;background:rgba(124,92,255,.08)}
.wides .seeall{aspect-ratio:460/215;flex-direction:row}
.seeall span{width:44px;height:44px;border-radius:50%;background:var(--surface2);display:grid;place-items:center}
.wcard{cursor:pointer}
.wcard .cover{aspect-ratio:460/215}
.wcard .wmeta{display:flex;justify-content:space-between;gap:10px;padding:9px 2px 0;font-size:12px;color:var(--muted)}
.wcard .wmeta b{color:var(--text);font-size:13.5px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(158px,1fr));gap:24px 18px}
.card{cursor:pointer;min-width:0}
.cover{position:relative;aspect-ratio:2/3;border-radius:12px;overflow:hidden;background:var(--surface2);box-shadow:0 10px 26px -14px rgba(0,0,0,.9);transition:transform .22s cubic-bezier(.2,.8,.2,1),box-shadow .22s}
.card:hover .cover,.wcard:hover .cover{transform:translateY(-5px);box-shadow:0 22px 44px -18px rgba(124,92,255,.6),0 0 0 1.5px rgba(124,92,255,.55)}
.cover img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;opacity:0;transition:opacity .35s}
.cover img.on{opacity:1}.cover img.instant{transition:none}
.tile{position:absolute;inset:0;display:flex;flex-direction:column;justify-content:flex-end;padding:14px;overflow:hidden}
.tile .ini{position:absolute;inset:0;display:grid;place-items:center;font-size:46px;font-weight:800;color:rgba(255,255,255,.92);letter-spacing:-1px;text-shadow:0 4px 18px rgba(0,0,0,.35)}
.tile .tn{position:relative;font-size:12px;font-weight:600;color:rgba(255,255,255,.75);line-height:1.25}
.wcard .tile .ini{font-size:38px}
.cover::after{content:"";position:absolute;inset:0;background:linear-gradient(180deg,transparent 55%,rgba(0,0,0,.45));pointer-events:none}
.playbtn{position:absolute;left:50%;top:50%;z-index:2;transform:translate(-50%,-50%) scale(.7);width:56px;height:56px;border-radius:50%;border:0;background:rgba(124,92,255,.95);display:grid;place-items:center;opacity:0;transition:opacity .2s,transform .2s;cursor:pointer;box-shadow:0 10px 30px -6px rgba(124,92,255,.9)}
.playbtn svg{fill:#fff;stroke:none;width:22px;height:22px;margin-left:3px}
.card:hover .playbtn,.wcard:hover .playbtn{opacity:1;transform:translate(-50%,-50%) scale(1)}
.playbtn:hover{background:#8f74ff}
.live{position:absolute;top:9px;left:9px;z-index:2;background:rgba(52,211,153,.95);color:#04281b;font-size:11px;font-weight:700;padding:3px 9px 3px 7px;border-radius:99px;display:flex;align-items:center;gap:6px;box-shadow:0 4px 14px -4px rgba(52,211,153,.8)}
.live i{width:6px;height:6px;border-radius:50%;background:#04281b;animation:blink 1.3s infinite}
@keyframes blink{50%{opacity:.25}}
.star{position:absolute;top:8px;right:8px;z-index:3;width:30px;height:30px;border-radius:50%;border:0;background:rgba(10,12,17,.82);display:grid;place-items:center;color:#fff;cursor:pointer;opacity:0;transform:scale(.85);transition:opacity .15s,transform .15s,background .15s,color .15s}
.star svg{width:16px;height:16px}
.card:hover .star,.wcard:hover .star,.star.on{opacity:1;transform:none}
.star:hover{background:rgba(10,12,17,.9);color:#ffd166;transform:scale(1.1)}
.star.on{color:#ffd166}.star.on svg{fill:#ffd166}
.star.pop{animation:pop .35s}
@keyframes pop{40%{transform:scale(1.35)}}
.lstar{background:none;border:0;cursor:pointer;color:var(--faint);padding:4px;border-radius:6px;display:grid;place-items:center}
.lstar svg{width:17px;height:17px}.lstar:hover{color:#ffd166}.lstar.on{color:#ffd166}.lstar.on svg{fill:#ffd166}
#splash{position:fixed;inset:0;z-index:100;display:grid;place-items:center;background:radial-gradient(ellipse at 50% 35%,#1a1540 0%,#0a0c11 60%);transition:opacity .5s}
#splash.hide{opacity:0;pointer-events:none}
.sp-in{display:flex;flex-direction:column;align-items:center;gap:16px;width:360px;text-align:center}
.sp-logo{width:78px;height:78px;border-radius:24px;background:linear-gradient(135deg,var(--accent),var(--accent2));display:grid;place-items:center;box-shadow:0 20px 60px -15px rgba(124,92,255,.9);animation:float 2.4s ease-in-out infinite}
.sp-logo svg{width:32px;height:32px;fill:#fff;margin-left:5px}
@keyframes float{50%{transform:translateY(-8px)}}
.sp-title{font-size:26px;font-weight:700;letter-spacing:-.3px;margin-top:6px}
.sp-bar{width:100%;height:6px;border-radius:99px;background:#1c2130;overflow:hidden;margin-top:8px}
.sp-bar i{display:block;height:100%;width:0;border-radius:99px;background:linear-gradient(90deg,var(--accent),var(--accent2));transition:width .35s ease}
.sp-text{font-size:13px;color:var(--muted);min-height:20px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:100%}
.sp-skip{margin-top:4px;background:none;border:0;color:var(--faint);font:inherit;font-size:12px;cursor:pointer;text-decoration:underline;opacity:0;pointer-events:none;transition:opacity .3s}
.sp-skip.on{opacity:1;pointer-events:auto}.sp-skip:hover{color:var(--text)}
.meta{padding:10px 2px 0}
.name{font-weight:600;font-size:13.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sub{display:flex;align-items:center;gap:6px;color:var(--muted);font-size:12px;margin-top:3px;white-space:nowrap;overflow:hidden}
.sub .sep{color:var(--faint)}
.empty{display:flex;flex-direction:column;align-items:center;justify-content:center;text-align:center;color:var(--muted);padding:90px 20px}
.empty b{color:var(--text);font-size:17px;margin-bottom:6px}
.skel{aspect-ratio:2/3;border-radius:12px;background:linear-gradient(100deg,var(--surface) 30%,var(--surface2) 50%,var(--surface) 70%);background-size:300% 100%;animation:shimmer 1.4s infinite}
@keyframes shimmer{from{background-position:100% 0}to{background-position:0 0}}

/* list view */
table{width:100%;border-collapse:separate;border-spacing:0 6px}
th{text-align:left;font-size:11px;font-weight:700;letter-spacing:1px;text-transform:uppercase;color:var(--faint);padding:0 14px 4px;cursor:pointer;user-select:none;white-space:nowrap}
th:hover{color:var(--text)} th.on{color:#b9b0ff}
td{background:var(--surface);padding:8px 14px;white-space:nowrap;font-variant-numeric:tabular-nums;color:var(--muted)}
td:first-child{border-radius:10px 0 0 10px;width:56px;padding-right:0} td:last-child{border-radius:0 10px 10px 0}
tr.row{cursor:pointer} tr.row:hover td{background:var(--surface2)}
td.nm{color:var(--text);font-weight:600;max-width:340px;overflow:hidden;text-overflow:ellipsis}
td .cover{width:38px;border-radius:6px;box-shadow:none}
td .tile .ini{font-size:14px} td .tile .tn{display:none}
.r{text-align:right}
.lchip{display:inline-flex;align-items:center;gap:7px}
.livetxt{color:var(--good);font-weight:600}

/* drawer */
.scrim{position:fixed;inset:0;background:rgba(0,0,0,.45);opacity:0;pointer-events:none;transition:opacity .25s;z-index:20}
.scrim.on{opacity:1;pointer-events:auto}
.drawer{position:fixed;top:0;right:0;bottom:0;width:430px;max-width:92vw;background:#0f1219;border-left:1px solid var(--line);transform:translateX(102%);transition:transform .3s cubic-bezier(.2,.8,.2,1);z-index:21;overflow:auto;box-shadow:-30px 0 60px -20px rgba(0,0,0,.7)}
.drawer.open{transform:none}
.d-top{position:relative;padding:28px 26px 22px;overflow:hidden;min-height:240px;display:flex;align-items:flex-end}
.d-bg{position:absolute;inset:-40px;background-size:cover;background-position:center;filter:blur(38px) saturate(1.4);opacity:.55;transform:scale(1.1)}
.d-fade{position:absolute;inset:0;background:linear-gradient(180deg,rgba(15,18,25,.15),#0f1219 92%)}
.d-head{position:relative;display:flex;gap:18px;align-items:flex-end;width:100%}
.d-head .cover{width:118px;flex:none;box-shadow:0 18px 40px -12px rgba(0,0,0,.9)}
.d-head h2{margin:8px 0 0;font-size:22px;line-height:1.2;letter-spacing:-.3px;word-break:break-word}
.chip{display:inline-flex;align-items:center;gap:7px;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.08);padding:4px 10px;border-radius:99px;font-size:12px;color:#d6d9e3}
.x{position:absolute;top:14px;right:14px;z-index:3;width:34px;height:34px;border-radius:50%;border:0;background:rgba(10,12,17,.6);display:grid;place-items:center;cursor:pointer;color:#fff}
.x:hover{background:rgba(10,12,17,.9)}
.d-body{padding:4px 26px 30px}
.big{width:100%;justify-content:center;padding:13px;font-size:15px;font-weight:650;border-radius:12px}
.big svg{fill:#fff;stroke:none}
.d-stats{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin:18px 0 8px}
.ds{background:var(--surface);border:1px solid var(--line);border-radius:12px;padding:12px 14px}
.ds span{display:block;font-size:11.5px;color:var(--muted);font-weight:500}
.ds b{display:block;font-size:18px;margin-top:3px;font-variant-numeric:tabular-nums}
.note{font-size:12px;color:var(--faint);margin-bottom:20px;display:flex;gap:6px;align-items:center}
.lbl{display:block;font-size:11px;font-weight:700;letter-spacing:1.1px;text-transform:uppercase;color:var(--faint);margin:0 0 8px}
.inp{width:100%;background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:10px 12px;color:var(--text);font:inherit;outline:none}
.inp:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(124,92,255,.2)}
.pills{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0 22px}
.pill{background:var(--surface);border:1px solid var(--line);border-radius:99px;padding:4px 11px;font-size:12px;cursor:pointer;color:var(--muted)}
.pill:hover{color:var(--text)} .pill.on{border-color:var(--accent);color:#fff;background:rgba(124,92,255,.18)}
.d-actions{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.d-actions .btn{justify-content:center}
.path{margin-top:20px;font:11.5px/1.5 Consolas,monospace;color:var(--faint);word-break:break-all}

/* modal + toast */
.modal-wrap{position:fixed;inset:0;display:grid;place-items:center;background:rgba(0,0,0,.55);z-index:40;opacity:0;pointer-events:none;transition:opacity .2s}
.modal-wrap.on{opacity:1;pointer-events:auto}
.modal{width:440px;max-width:92vw;background:#121620;border:1px solid var(--line);border-radius:18px;padding:24px;box-shadow:0 30px 80px -20px rgba(0,0,0,.8);transform:translateY(10px) scale(.98);transition:transform .2s}
.modal-wrap.on .modal{transform:none}
.modal h3{margin:0 0 4px;font-size:18px}.modal p{margin:0 0 18px;color:var(--muted);font-size:13px}
.modal .acts{display:flex;justify-content:flex-end;gap:8px;margin-top:20px}
.set{display:flex;align-items:center;gap:14px;padding:14px 0;border-top:1px solid var(--line)}
.set:first-of-type{border-top:0}
.set div{flex:1}.set b{display:block;font-weight:600}.set small{color:var(--muted);font-size:12px}
.tog{width:42px;height:24px;border-radius:99px;background:#2a3040;position:relative;cursor:pointer;flex:none;transition:background .2s;border:0}
.tog::after{content:"";position:absolute;top:3px;left:3px;width:18px;height:18px;border-radius:50%;background:#fff;transition:transform .2s}
.tog.on{background:var(--accent)}.tog.on::after{transform:translateX(18px)}
.tog:disabled{opacity:.4;cursor:not-allowed}
.toast{position:fixed;bottom:24px;left:50%;transform:translate(-50%,20px);background:#1c2130;border:1px solid #2c3346;padding:11px 18px;border-radius:12px;box-shadow:0 20px 50px -15px rgba(0,0,0,.8);opacity:0;transition:.25s;z-index:50;pointer-events:none;font-size:13px}
.toast.on{opacity:1;transform:translate(-50%,0)}
@media (max-width:1100px){.search input{width:190px}}

/* ===== theme v2: the games set the mood ===== */
:root{--tint:#7c5cff;--tint-soft:rgba(124,92,255,.35);--game:var(--tint);--game-soft:var(--tint-soft);--display:"Bahnschrift","Segoe UI Variable Display","Segoe UI",sans-serif;--base:#07090e}
html,body{background:var(--base)}
#amb{position:fixed;inset:0;z-index:0;pointer-events:none;overflow:hidden;background:radial-gradient(1100px 700px at 85% -15%,rgba(124,92,255,.20),transparent 60%),radial-gradient(900px 600px at 0% 115%,rgba(34,211,238,.08),transparent 60%),var(--base)}
.amb-layer{position:absolute;inset:-15%;background-size:cover;background-position:center;filter:blur(80px) saturate(1.6) brightness(.5);opacity:0;transition:opacity 1.2s ease}
.amb-layer.on{opacity:1}

.app{position:relative;z-index:1}
aside{background:rgba(10,12,18,.94);border-right:1px solid rgba(255,255,255,.06)}
.brand{font-family:var(--display);font-stretch:condensed;font-size:20px;letter-spacing:.2px}
.logo{background:var(--tint);box-shadow:0 8px 26px -8px var(--tint-soft);transition:background 1s}
.sec{text-transform:none;letter-spacing:0;font-size:12px;font-weight:600;color:rgba(255,255,255,.38);padding:20px 12px 6px}
.nav{color:rgba(255,255,255,.62)}
.nav:hover{background:rgba(255,255,255,.06);color:#fff}
.nav.active{background:rgba(255,255,255,.09);color:#fff;box-shadow:inset 3px 0 0 var(--tint)}
.nav.active .n{color:rgba(255,255,255,.8)}
.side-bottom{margin-top:auto;padding-top:16px}
.side-stats{padding:0 12px 14px;display:grid;gap:8px}
.side-stats div{color:rgba(255,255,255,.45);font-size:12px;line-height:1.25}
.side-stats b{display:block;font-family:var(--display);font-stretch:condensed;color:#fff;font-weight:600;font-size:19px;letter-spacing:.2px}
.side-foot{margin-top:0;border-top:1px solid rgba(255,255,255,.07)}
.pulse{background:var(--good)}
main{position:relative}
.top{position:absolute;top:0;left:0;right:0;z-index:6;padding:20px 34px 30px;background:linear-gradient(180deg,rgba(7,9,14,.78) 0%,rgba(7,9,14,.35) 65%,rgba(7,9,14,0) 100%);border-bottom:0;}
.top{transition:background .25s}
.top.scrolled{background:rgba(9,11,17,.97);padding-bottom:20px;box-shadow:0 1px 0 rgba(255,255,255,.06)}
.title{font-family:var(--display);font-stretch:condensed;font-size:30px;font-weight:700;letter-spacing:.2px;text-shadow:0 2px 20px rgba(0,0,0,.4)}
.title small{font-family:"Segoe UI Variable Text","Segoe UI",sans-serif;font-stretch:normal}
.content{padding:100px 34px 70px}
.search input,select,.btn,.seg,.arr{background:rgba(255,255,255,.07);border-color:rgba(255,255,255,.09);}
.btn:hover,.arr:hover{background:rgba(255,255,255,.13);border-color:rgba(255,255,255,.14)}
.search input:focus,.inp:focus{border-color:var(--tint);box-shadow:0 0 0 3px var(--tint-soft)}
.seg button.on{background:rgba(255,255,255,.14)}
.btn.primary{background:var(--tint);box-shadow:0 12px 30px -12px var(--tint)}
.playbtn{background:var(--tint);box-shadow:0 10px 30px -6px var(--tint-soft)}
.playbtn:hover{background:var(--tint);filter:brightness(1.12)}
:focus-visible{outline:2px solid var(--tint);outline-offset:2px}
.cover{border-radius:14px;background:rgba(255,255,255,.06)}
.card:hover .cover,.wcard:hover .cover{transform:translateY(-4px);box-shadow:0 24px 48px -20px rgba(0,0,0,.95),0 0 0 2px var(--tint)}
.h3link{font-family:var(--display);font-stretch:condensed;font-size:23px;font-weight:600;letter-spacing:.2px}
.h3link em{font-family:"Segoe UI Variable Text","Segoe UI",sans-serif;font-size:13px;color:rgba(255,255,255,.4)}
.shead{margin-bottom:4px}
.wcard .wmeta b{font-size:14px}
.wcard .wmeta,.sub{color:rgba(255,255,255,.55)}
.seeall{border-color:rgba(255,255,255,.18)}
.seeall:hover{border-color:var(--tint);background:rgba(255,255,255,.05)}
th{text-transform:none;letter-spacing:0;font-size:12.5px;font-weight:600;color:rgba(255,255,255,.4)}
th.on{color:#fff}
td{background:rgba(255,255,255,.045);color:rgba(255,255,255,.62)}
tr.row:hover td{background:rgba(255,255,255,.09)}
.lbl{text-transform:none;letter-spacing:0;font-size:13px;font-weight:600;color:rgba(255,255,255,.5)}
.drawer{background:#0d1017;border-left:1px solid rgba(255,255,255,.07)}
.d-head h2{font-family:var(--display);font-stretch:condensed;font-size:30px;font-weight:700;letter-spacing:.2px;line-height:1}
.ds{background:rgba(255,255,255,.05);border-color:rgba(255,255,255,.07)}
.ds b{font-family:var(--display);font-stretch:condensed;font-size:22px;font-weight:600}
.pill.on{border-color:var(--tint);background:var(--tint-soft)}
.tog.on{background:var(--tint)}
.modal{background:#121620;}

/* friends */
.fbar{display:flex;align-items:center;justify-content:space-between;margin-bottom:18px}
.ftabs{display:flex;gap:6px;background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.08);border-radius:12px;padding:4px}
.ftab{border:0;background:none;color:rgba(255,255,255,.65);font:inherit;font-size:14px;font-weight:600;padding:7px 14px;border-radius:9px;cursor:pointer;display:flex;align-items:center;gap:7px}
.ftab:hover{color:#fff}.ftab.on{background:rgba(255,255,255,.12);color:#fff}
.ftab em{font-style:normal;font-size:12px;font-weight:600;color:var(--good)}
.fnote{padding:14px 16px;border-radius:12px;background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.1);margin-bottom:16px;max-width:760px}
.fnote.warn{background:rgba(245,166,35,.1);border-color:rgba(245,166,35,.35)}
.fnote b{display:block;font-size:14px}.fnote>span{display:block;color:rgba(255,255,255,.72);font-size:13px;line-height:1.5;margin-top:3px}
.fnote small{display:block;color:rgba(255,255,255,.5);font-size:12px;margin-top:8px;line-height:1.45}
.fkey{display:flex;gap:8px;margin-top:12px}.fkey .inp{flex:1;max-width:420px}
.fsec{margin-bottom:22px;max-width:980px}
.fsec-h{display:flex;align-items:center;gap:8px;font-family:var(--display);font-stretch:condensed;font-size:19px;font-weight:600;margin-bottom:8px}
.fsec-h em{font-style:normal;font-family:"Segoe UI Variable Text","Segoe UI",sans-serif;font-stretch:normal;font-size:13px;color:rgba(255,255,255,.4);font-weight:500}
.fsec-h .linkbtn{margin:0 0 0 6px;font-family:"Segoe UI Variable Text","Segoe UI",sans-serif;font-stretch:normal}
.flist{display:grid;grid-template-columns:repeat(auto-fill,minmax(330px,1fr));gap:8px}
.frow{display:flex;align-items:center;gap:12px;padding:10px 12px;border-radius:12px;background:rgba(255,255,255,.045);cursor:context-menu;min-width:0}
.frow:hover{background:rgba(255,255,255,.08)}
.frow:hover .more{opacity:1}
.fav{position:relative;width:42px;height:42px;flex:none}
.fav img,.fini{width:42px;height:42px;border-radius:50%;object-fit:cover;display:grid;place-items:center;font-weight:700;font-size:14px;color:#fff}
.fav i{position:absolute;right:-1px;bottom:-1px;width:13px;height:13px;border-radius:50%;border:2.5px solid #0f1219;background:#5b6275}
.fav.ingame i{background:var(--good)}.fav.online i{background:#60a5fa}.fav.away i{background:#f5a623}.fav.busy i{background:#f87171}
.fav.unknown i{display:none}.fav.offline img,.fav.offline .fini{filter:grayscale(1) brightness(.7)}
.finfo{flex:1;min-width:0}
.fname{font-weight:600;font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ftag{color:rgba(255,255,255,.45);font-weight:500;margin-left:2px}
.fnick{color:rgba(255,255,255,.45);font-weight:500;font-size:12.5px;margin-left:8px}
.fline{font-size:12.5px;color:rgba(255,255,255,.6);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin-top:2px}
.fline b{color:var(--good);font-weight:600}
.fright{display:flex;align-items:center;gap:8px;flex:none}
.fright .lchip{font-size:12px;color:rgba(255,255,255,.55)}
.btn.fjoin{padding:5px 12px;font-size:12.5px;background:var(--tint);border-color:transparent;color:#fff}
.fother{max-width:760px;color:rgba(255,255,255,.42);font-size:12.5px;line-height:1.5;margin-top:26px}

/* settings: folders */
.folders{display:grid;gap:6px;margin-top:4px}
.folder{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:8px 10px;border-radius:9px;background:rgba(255,255,255,.05);font-size:12.5px}
.folder span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;color:rgba(255,255,255,.8);font-family:Consolas,monospace}
.folder.none{color:rgba(255,255,255,.45)}.folder .linkbtn{margin:0;flex:none}

/* update notice + settings */
.appupd{margin:0 0 14px;padding:12px;border-radius:12px;background:rgba(124,92,255,.14);border:1px solid rgba(124,92,255,.4)}
.appupd b{display:block;font-size:13.5px}.appupd span{display:block;font-size:12.5px;color:rgba(255,255,255,.7);margin-top:2px}
.appupd-acts{display:flex;align-items:center;gap:12px;margin-top:10px}
.appupd .btn{padding:6px 12px;font-size:12.5px}.appupd .linkbtn{margin:0}
.sethead{display:flex;justify-content:space-between;align-items:baseline;font-weight:650;font-size:15px;margin:18px 0 2px;padding-top:16px;border-top:1px solid var(--line)}
.sethead span{font-weight:500;font-size:12.5px;color:var(--muted)}
.sethead + .set{border-top:0}
.updacts{display:flex;gap:8px;margin-top:10px}
.sethint{display:block;color:var(--muted);font-size:12px;margin-top:6px}.updacts .btn{font-size:13px}
.modal{max-height:88vh;overflow:auto}

/* render only what's on screen */
.grid>.card{content-visibility:auto;contain-intrinsic-size:auto 300px}
.slider>.wcard{content-visibility:auto;contain-intrinsic-size:auto 190px}
tbody>tr.row{content-visibility:auto;contain-intrinsic-size:auto 70px}

/* popup menu + ⋯ buttons */
#menu{position:fixed;z-index:70;min-width:220px;padding:6px;border-radius:12px;background:#151924;border:1px solid rgba(255,255,255,.1);box-shadow:0 24px 60px -12px rgba(0,0,0,.85);opacity:0;pointer-events:none;transform:translateY(-4px);transition:opacity .12s,transform .12s}
#menu.on{opacity:1;pointer-events:auto;transform:none}
.mi{display:flex;align-items:center;gap:10px;width:100%;padding:8px 10px;border:0;border-radius:8px;background:none;color:#e9ebf1;font:inherit;font-size:13.5px;text-align:left;cursor:pointer}
.mi:hover,.mi:focus-visible{background:rgba(255,255,255,.08);outline:none}
.mi svg{width:16px;height:16px;color:rgba(255,255,255,.6)}
.mi span{flex:1;white-space:nowrap}.mi .mi-pad{flex:0 0 0;width:0;margin-right:-10px}
.mi.on{color:#fff}.mi.on svg:last-child{color:var(--tint)}
.mi.danger{color:#ff8e8e}.mi.danger svg{color:#ff8e8e}
.mi.danger:hover{background:rgba(248,113,113,.12)}
.mi:disabled{opacity:.4;cursor:default}
.msep{height:1px;background:rgba(255,255,255,.08);margin:5px 4px}
.sortgrp{display:flex;gap:6px}
.dirbtn svg{width:17px;height:17px}
.sortbtn svg{width:16px;height:16px}.sortbtn svg:last-child{opacity:.6}
.sortbtn:disabled{opacity:.5;cursor:default}
.nrow{display:flex;align-items:center;gap:6px}.nrow .name{flex:1;min-width:0}
.more{flex:none;width:28px;height:24px;border:0;border-radius:7px;background:none;color:rgba(255,255,255,.4);display:grid;place-items:center;cursor:pointer;opacity:0;transition:opacity .15s,background .15s,color .15s}
.more svg{width:18px;height:18px;fill:currentColor;stroke:none}
.card:hover .more,.wcard:hover .more,tr.row:hover .more,.more:focus-visible{opacity:1}
.more:hover{background:rgba(255,255,255,.1);color:#fff}
.wr{display:flex;align-items:center;gap:6px}
tr.row .more{opacity:.5}
.more.hmore{width:48px;height:48px;border-radius:13px;opacity:1;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.1);color:#fff}
.more.hmore svg{width:20px;height:20px}
.btn.danger-fill{background:#d9443c;box-shadow:0 12px 30px -12px #d9443c}

/* not-installed games */
.card.off .cover img,.card.off .cover .tile{filter:grayscale(.9) brightness(.62);transition:filter .25s}
.card.off:hover .cover img,.card.off:hover .cover .tile{filter:none}
.noinst{position:absolute;top:9px;left:9px;z-index:2;font-size:11px;font-weight:600;padding:3px 9px;border-radius:99px;background:rgba(10,12,18,.86);color:rgba(255,255,255,.85);border:1px solid rgba(255,255,255,.12)}
.playbtn.inst svg{fill:none;stroke:#fff;stroke-width:2.4;margin-left:0}
.big svg.i{flex:none}
.btn.big[data-install] svg{fill:none;stroke:#fff}
.updbar.off{background:rgba(255,255,255,.05);border-color:rgba(255,255,255,.12)}

/* update badges */
.upd{position:absolute;top:9px;left:9px;z-index:2;display:flex;align-items:center;gap:6px;font-size:11px;font-weight:700;padding:3px 9px 3px 7px;border-radius:99px;background:rgba(245,166,35,.95);color:#2b1a00;box-shadow:0 4px 14px -4px rgba(245,166,35,.7)}
.upd i{width:6px;height:6px;border-radius:50%;background:currentColor}
.upd.updating i{animation:blink 1.1s infinite}
.upd.updating,.upd.paused{background:rgba(96,165,250,.95);color:#04203f;box-shadow:0 4px 14px -4px rgba(96,165,250,.7)}
.upd.repair{background:rgba(248,113,113,.95);color:#3b0606;box-shadow:0 4px 14px -4px rgba(248,113,113,.7)}
.upd.inline{position:static;display:inline-flex;vertical-align:middle;margin-left:6px;box-shadow:none}
.updbar{display:flex;align-items:center;gap:14px;padding:13px 14px;margin-bottom:12px;border-radius:12px;background:rgba(245,166,35,.12);border:1px solid rgba(245,166,35,.35)}
.updbar.updating,.updbar.paused{background:rgba(96,165,250,.12);border-color:rgba(96,165,250,.35)}
.updbar.repair{background:rgba(248,113,113,.12);border-color:rgba(248,113,113,.35)}
.updbar div{flex:1}.updbar b{display:block;font-size:13.5px}.updbar span{display:block;font-size:12.5px;color:rgba(255,255,255,.7);line-height:1.4;margin-top:2px}
.updbar .btn{flex:none;font-size:12.5px;padding:7px 11px}

/* about section */
#dAbout{margin:2px 0 22px}
.about-head{display:flex;align-items:center;justify-content:space-between;margin-bottom:8px}
.about-head .lbl{margin:0}
.desc{color:rgba(255,255,255,.8);line-height:1.6;margin:0 0 6px;font-size:13.5px;white-space:pre-line;display:-webkit-box;-webkit-line-clamp:5;-webkit-box-orient:vertical;overflow:hidden}
.desc.open{-webkit-line-clamp:unset;display:block}
.linkbtn{background:none;border:0;padding:0;color:rgba(255,255,255,.55);font:inherit;font-size:12.5px;cursor:pointer;text-decoration:underline;text-underline-offset:3px;margin-bottom:14px}
.linkbtn:hover{color:#fff}
.facts{display:grid;grid-template-columns:auto 1fr;gap:7px 16px;font-size:13px;margin:10px 0 14px}
.facts dt{color:rgba(255,255,255,.45)}.facts dd{margin:0;color:#fff}
.chips{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:16px}
.chipx{font-size:12px;padding:4px 10px;border-radius:99px;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.08);color:rgba(255,255,255,.82)}
.mc{display:inline-grid;place-items:center;min-width:36px;height:28px;padding:0 6px;border-radius:7px;font-family:var(--display);font-stretch:condensed;font-weight:700;font-size:16px;color:#fff}
.mc.hi{background:#2f9e4f}.mc.mid{background:#c7951a}.mc.lo{background:#c2413b}
.shots{display:grid;grid-auto-flow:column;grid-auto-columns:190px;gap:8px;overflow-x:auto;margin:0 -26px 12px;padding:0 26px 8px}
.shots img{width:100%;aspect-ratio:16/9;object-fit:cover;border-radius:9px;cursor:zoom-in;display:block;background:rgba(255,255,255,.05);transition:filter .15s}
.shots img:hover{filter:brightness(1.15)}
.about-loading{display:grid;gap:8px;margin:6px 0}
.about-loading span{height:11px;border-radius:6px;background:linear-gradient(100deg,rgba(255,255,255,.05) 30%,rgba(255,255,255,.12) 50%,rgba(255,255,255,.05) 70%);background-size:300% 100%;animation:shimmer 1.4s infinite}
.about-loading span:last-child{width:60%}
#lightbox{position:fixed;inset:0;z-index:60;background:rgba(0,0,0,.9);display:grid;place-items:center;opacity:0;pointer-events:none;transition:opacity .2s;cursor:zoom-out}
#lightbox.on{opacity:1;pointer-events:auto}
#lightbox img{max-width:90vw;max-height:86vh;border-radius:10px;box-shadow:0 30px 80px -20px #000}
.lb-nav{position:absolute;top:50%;transform:translateY(-50%);width:52px;height:52px;border-radius:50%;border:0;background:rgba(255,255,255,.1);color:#fff;font-size:30px;line-height:1;cursor:pointer}
.lb-nav:hover{background:rgba(255,255,255,.2)}.lb-nav.l{left:24px}.lb-nav.r{right:24px}

/* hero */
.hero{position:relative;margin:-100px -34px 30px;height:clamp(400px,60vh,640px);overflow:hidden}
.hero-art{position:absolute;inset:0;-webkit-mask-image:linear-gradient(180deg,#000 50%,transparent 100%);mask-image:linear-gradient(180deg,#000 50%,transparent 100%)}
.hero-art img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;object-position:center 30%;opacity:0;transition:opacity .8s ease}
.hero-art img.on{opacity:1}.hero-art img.instant{transition:none}
.hero-art.portrait img.bg{filter:blur(34px) brightness(.55) saturate(1.3);transform:scale(1.2)}
.hero-poster{position:absolute;right:7%;top:16%;height:68%;aspect-ratio:2/3;border-radius:16px;overflow:hidden;box-shadow:0 30px 70px -20px rgba(0,0,0,.9);opacity:0;transition:opacity .8s}
.hero-poster.on{opacity:1}.hero-poster img{width:100%;height:100%;object-fit:cover}
.hero-shade{position:absolute;inset:0;pointer-events:none;-webkit-mask-image:linear-gradient(180deg,#000 55%,transparent 100%);mask-image:linear-gradient(180deg,#000 55%,transparent 100%);background:
  linear-gradient(90deg,rgba(7,9,14,.86) 0%,rgba(7,9,14,.5) 34%,rgba(7,9,14,0) 64%),
  linear-gradient(0deg,rgba(7,9,14,.5) 0%,rgba(7,9,14,.25) 26%,rgba(7,9,14,0) 52%),
  linear-gradient(180deg,rgba(7,9,14,.55) 0%,rgba(7,9,14,0) 22%)}
.hero-body{position:absolute;left:34px;bottom:58px;width:min(600px,58%);z-index:2}
.hero-title{min-height:60px;display:flex;align-items:flex-end}
.hero-title h1{font-family:var(--display);font-stretch:condensed;font-weight:700;font-size:clamp(46px,5.4vw,82px);line-height:.9;margin:0;letter-spacing:-.3px;text-wrap:balance;text-shadow:0 6px 40px rgba(0,0,0,.55)}
.hero-title img{max-width:min(440px,100%);max-height:160px;object-fit:contain;object-position:left bottom;filter:drop-shadow(0 8px 30px rgba(0,0,0,.65))}
.hero-meta{display:flex;align-items:center;gap:20px;flex-wrap:wrap;margin:20px 0 24px;color:rgba(255,255,255,.8);font-size:14.5px}
.hero-meta b{font-family:var(--display);font-stretch:condensed;font-weight:600;font-size:17px;color:#fff;margin-right:4px}
.hero-acts{display:flex;gap:10px;align-items:center}
.btn.go{background:var(--game);border:0;color:#fff;font-weight:650;padding:13px 30px;font-size:15.5px;border-radius:13px;box-shadow:0 16px 40px -14px var(--game);transition:background-color .6s,box-shadow .6s,transform .1s}
.btn.go svg{fill:#fff;stroke:none}
.btn.go:hover{background:var(--game);filter:brightness(1.1)}
.btn.glass{padding:13px 22px;border-radius:13px;font-size:15px}
.star.hstar{position:static;opacity:1;transform:none;width:48px;height:48px;border-radius:13px;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.1)}
.star.hstar svg{width:19px;height:19px}
.hero-dots{position:absolute;right:34px;bottom:64px;display:flex;gap:7px;z-index:2}
.hdot{width:26px;height:4px;border-radius:4px;border:0;padding:0;background:rgba(255,255,255,.28);cursor:pointer;transition:width .25s,background .25s}
.hdot:hover{background:rgba(255,255,255,.55)}
.hdot.on{width:46px;background:#fff}
/* personality */
.title .greet{display:block;font-family:"Segoe UI Variable Text","Segoe UI",sans-serif;font-stretch:normal;font-size:13px;font-weight:500;color:rgba(255,255,255,.55);letter-spacing:0;text-shadow:none;margin-top:2px}
.title .greet b{color:#fff;font-weight:600}
.badges{display:flex;flex-wrap:wrap;gap:6px}
.badge{display:inline-flex;align-items:center;gap:5px;padding:4px 9px 4px 7px;border-radius:99px;font-size:11.5px;font-weight:600;letter-spacing:.2px;background:rgba(255,255,255,.08);color:#fff;border:1px solid rgba(255,255,255,.12);white-space:nowrap}
.badge i{font-style:normal;font-size:12px;line-height:1}
.badge.gold{background:linear-gradient(135deg,rgba(251,191,36,.28),rgba(245,158,11,.12));border-color:rgba(251,191,36,.45);color:#fde68a}
.badge.hot{background:linear-gradient(135deg,rgba(248,113,113,.28),rgba(244,63,94,.1));border-color:rgba(248,113,113,.45);color:#fecaca}
.badge.new{background:linear-gradient(135deg,rgba(52,211,153,.25),rgba(16,185,129,.08));border-color:rgba(52,211,153,.4);color:#a7f3d0}
.badge.dust{background:rgba(148,163,184,.14);border-color:rgba(148,163,184,.3);color:#cbd5e1}
.badge.owl{background:linear-gradient(135deg,rgba(124,92,255,.3),rgba(34,211,238,.1));border-color:rgba(124,92,255,.5);color:#ddd6fe}
.hero-badges{margin:-10px 0 22px}
.d-badges{margin:2px 0 16px}
.sp-quip{margin-top:8px;font-size:12.5px;color:rgba(255,255,255,.4);font-style:italic;min-height:18px;transition:opacity .35s}
.sp-quip.out{opacity:0}
.side-stats .fun{display:block;margin-top:2px;color:rgba(255,255,255,.3);font-size:11px;font-style:italic}
.empty .eic{width:74px;height:74px;border-radius:24px;display:grid;place-items:center;margin-bottom:18px;background:linear-gradient(135deg,rgba(124,92,255,.22),rgba(34,211,238,.08));border:1px solid rgba(124,92,255,.3);box-shadow:0 18px 50px -20px rgba(124,92,255,.8);transform:rotate(-6deg)}
.empty .eic svg{width:32px;height:32px;stroke:#c4b5fd}
.empty b{font-family:var(--display);font-stretch:condensed;font-size:22px}
.empty span{max-width:380px;line-height:1.5}
.burst{position:fixed;width:0;height:0;pointer-events:none;z-index:60}
.burst i{position:absolute;left:-3px;top:-3px;width:6px;height:6px;border-radius:50%;background:#fbbf24;animation:burst .6s cubic-bezier(.2,.7,.3,1) forwards}
.burst i:nth-child(even){background:#c4b5fd;width:5px;height:5px}
@keyframes burst{0%{transform:translate(0,0) scale(1);opacity:1}100%{transform:translate(var(--x),var(--y)) scale(.3);opacity:0}}
.btn.go{position:relative;overflow:hidden}
.btn.go::after{content:"";position:absolute;inset:0;background:linear-gradient(105deg,transparent 35%,rgba(255,255,255,.35) 50%,transparent 65%);transform:translateX(-120%);pointer-events:none}
.btn.go:hover::after{transform:translateX(120%);transition:transform .7s ease}
.btn.go:active{transform:scale(.97)}
.brand .logo{transition:transform .25s cubic-bezier(.3,1.6,.5,1),background 1s}
.brand:hover .logo{transform:rotate(-10deg) scale(1.08)}
.toast{display:flex;align-items:center;gap:9px}
.toast .ti{font-size:15px;line-height:1}
.toast.on{animation:toastin .38s cubic-bezier(.3,1.5,.5,1)}
@keyframes toastin{0%{transform:translate(-50%,24px) scale(.94)}100%{transform:translate(-50%,0) scale(1)}}
@media (prefers-reduced-motion:reduce){*,*::before,*::after{transition:none!important;animation:none!important}}
</style></head>
<body>
<div id="amb"></div>
<div class="app">
  <aside id="side"></aside>
  <main>
    <div class="top" id="top"></div>
    <div class="content" id="content"></div>
  </main>
</div>
<div class="scrim" id="scrim" data-act="close"></div>
<div class="drawer" id="drawer"></div>
<div class="modal-wrap" id="modalWrap"><div class="modal" id="modal"></div></div>
<div class="toast" id="toast"></div>
<div id="menu" role="menu"></div>
<div id="lightbox"><img id="lbImg" alt="Screenshot"><button class="lb-nav l" data-lb="-1">‹</button><button class="lb-nav r" data-lb="1">›</button></div>
<div id="splash"><div class="sp-in">
  <div class="sp-logo"><svg viewBox="0 0 24 24"><polygon points="6 4 20 12 6 20"/></svg></div>
  <div class="sp-title">Game Hub</div>
  <div class="sp-bar"><i id="spFill"></i></div>
  <div class="sp-text" id="spText">Starting up…</div>
  <div class="sp-quip" id="spQuip"></div>
  <button class="sp-skip" id="spSkip">Skip and open now</button>
</div></div>
<script>
const $ = s => document.querySelector(s);
const api = () => window.pywebview.api;
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const P = {
  play:'<polygon points="6 4 20 12 6 20 6 4"/>',
  pad:'<rect x="2" y="6" width="20" height="12" rx="5"/><path d="M7 12h4M9 10v4"/><path d="M15.5 11h.01M17.5 13h.01"/>',
  clock:'<circle cx="12" cy="12" r="9"/><polyline points="12 7 12 12 15.5 14"/>',
  star:'<polygon points="12 2.5 15 8.6 21.7 9.6 16.8 14.3 18 21 12 17.8 6 21 7.2 14.3 2.3 9.6 9 8.6 12 2.5"/>',
  eyeoff:'<path d="M3 3l18 18"/><path d="M10.6 5.1A9.7 9.7 0 0 1 12 5c6 0 10 7 10 7a17 17 0 0 1-3.2 4"/><path d="M6.6 6.6A17 17 0 0 0 2 12s4 7 10 7a9.6 9.6 0 0 0 5.4-1.6"/><path d="M9.9 9.9a3 3 0 0 0 4.2 4.2"/>',
  eye:'<path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/>',
  folder:'<path d="M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"/>',
  plus:'<path d="M12 5v14M5 12h14"/>',
  refresh:'<path d="M20.5 12a8.5 8.5 0 1 1-2.6-6.1L20.5 8.5"/><path d="M20.5 3.5v5h-5"/>',
  gear:'<circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.7 1.7 0 0 0 .3 1.8l.1.1a2 2 0 1 1-2.8 2.8l-.1-.1a1.7 1.7 0 0 0-1.8-.3 1.7 1.7 0 0 0-1 1.5V21a2 2 0 1 1-4 0v-.1a1.7 1.7 0 0 0-1.1-1.5 1.7 1.7 0 0 0-1.8.3l-.1.1a2 2 0 1 1-2.8-2.8l.1-.1a1.7 1.7 0 0 0 .3-1.8 1.7 1.7 0 0 0-1.5-1H3a2 2 0 1 1 0-4h.1a1.7 1.7 0 0 0 1.5-1.1 1.7 1.7 0 0 0-.3-1.8l-.1-.1a2 2 0 1 1 2.8-2.8l.1.1a1.7 1.7 0 0 0 1.8.3H9a1.7 1.7 0 0 0 1-1.5V3a2 2 0 1 1 4 0v.1a1.7 1.7 0 0 0 1 1.5 1.7 1.7 0 0 0 1.8-.3l.1-.1a2 2 0 1 1 2.8 2.8l-.1.1a1.7 1.7 0 0 0-.3 1.8V9a1.7 1.7 0 0 0 1.5 1H21a2 2 0 1 1 0 4h-.1a1.7 1.7 0 0 0-1.5 1z"/>',
  search:'<circle cx="11" cy="11" r="7"/><path d="M20 20l-3.8-3.8"/>',
  grid:'<rect x="3" y="3" width="7" height="7" rx="1.5"/><rect x="14" y="3" width="7" height="7" rx="1.5"/><rect x="3" y="14" width="7" height="7" rx="1.5"/><rect x="14" y="14" width="7" height="7" rx="1.5"/>',
  list:'<path d="M8 6h13M8 12h13M8 18h13M3.5 6h.01M3.5 12h.01M3.5 18h.01"/>',
  x:'<path d="M18 6L6 18M6 6l12 12"/>',
  layers:'<polygon points="12 2 2 7 12 12 22 7 12 2"/><polyline points="2 17 12 22 22 17"/><polyline points="2 12 12 17 22 12"/>',
  image:'<rect x="3" y="3" width="18" height="18" rx="3"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="M21 15l-5-5L5 21"/>',
  trash:'<path d="M3 6h18M8 6V4h8v2M19 6l-1 14H6L5 6"/>',
  left:'<polyline points="15 6 9 12 15 18"/>',
  right:'<polyline points="9 6 15 12 9 18"/>',
  starf:'<polygon points="12 2.5 15 8.6 21.7 9.6 16.8 14.3 18 21 12 17.8 6 21 7.2 14.3 2.3 9.6 9 8.6 12 2.5"/>',
  download:'<path d="M12 4v11M7 10l5 5 5-5M5 20h14"/>',
  archive:'<rect x="3" y="4" width="18" height="5" rx="1.5"/><path d="M5 9v9a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V9M10 13h4"/>',
  dots:'<circle cx="5" cy="12" r="1.6"/><circle cx="12" cy="12" r="1.6"/><circle cx="19" cy="12" r="1.6"/>',
  sort:'<path d="M4 7h11M4 12h8M4 17h5M18 6v12M15 15l3 3 3-3"/>',
  down:'<polyline points="7 10 12 15 17 10"/>',
  check:'<polyline points="5 12.5 10 17 19 7"/>',
  wrench:'<path d="M14.7 6.3a4 4 0 0 0-5.4 5.4L3.5 17.5a1.5 1.5 0 0 0 2.1 2.1l5.8-5.8a4 4 0 0 0 5.4-5.4l-2.6 2.6-2.1-.5-.5-2.1z"/>',
  sortdown:'<path d="M4 6h9M4 12h6M4 18h3M18 5v14M14.5 15.5 18 19l3.5-3.5"/>',
  sortup:'<path d="M4 6h3M4 12h6M4 18h9M18 19V5M14.5 8.5 18 5l3.5 3.5"/>',
  users:'<circle cx="9" cy="8" r="3.5"/><path d="M2.5 20a6.5 6.5 0 0 1 13 0"/><path d="M16 4.6a3.5 3.5 0 0 1 0 6.8M18 14.3a6.5 6.5 0 0 1 3.5 5.7"/>',
  chat:'<path d="M4 5h16v11H9l-5 4z"/>',
  user:'<circle cx="12" cy="8" r="4"/><path d="M4 21a8 8 0 0 1 16 0"/>',
  copy:'<rect x="8" y="8" width="12" height="12" rx="2"/><path d="M16 8V5a1 1 0 0 0-1-1H5a1 1 0 0 0-1 1v10a1 1 0 0 0 1 1h3"/>',
  info:'<circle cx="12" cy="12" r="9"/><path d="M12 11v5M12 8h.01"/>'
};
const ic = n => `<svg class="i" viewBox="0 0 24 24">${P[n]}</svg>`;
const LC = {Steam:'#66c0f4',Epic:'#e8e8e8',GOG:'#b06cff',Ubisoft:'#3d8bff','EA app':'#ff5a5a','Battle.net':'#1fb1ff',Riot:'#ff4655',Amazon:'#ff9900',Xbox:'#3fbf3f',RSI:'#4fc3f7',Rockstar:'#fcaf17','itch.io':'#fa5c5c',Wargaming:'#d9322e',Gaijin:'#e8603c',HoYoPlay:'#6ab7ff',Nexon:'#2fb5e8',Standalone:'#c9b79c',Custom:'#9aa3b5'};
const lc = l => LC[l] || '#9aa3b5';

function store(k, v){ try{ if(v===undefined) return localStorage.getItem(k); localStorage.setItem(k, v); }catch(e){ return null; } }
const S = {data:null, view:{k:'all'}, q:'', sort: store('sort') || 'name', rev: store('rev')==='1', ftab: store('ftab')||'all', mode: store('mode') || 'grid',
           open:null, version:-1, lastFull:0};
const COV = {}, PENDING = {};

// ---------- formatting
function fmtTime(s){ if(!s) return '—'; if(s<60) return '<1 min'; if(s<3600) return Math.round(s/60)+' min';
  const h=s/3600; return (h<100 ? h.toFixed(1) : Math.round(h).toLocaleString())+' h'; }
function fmtAgo(ts, playing){ if(playing) return 'Playing now'; if(!ts) return 'Never';
  const d=Date.now()/1000-ts; if(d<3600) return Math.max(1,Math.round(d/60))+' min ago'; if(d<86400) return Math.floor(d/3600)+' h ago';
  const days=Math.floor(d/86400); if(days===1) return 'Yesterday'; if(days<7) return days+' days ago';
  if(days<30){ const w=Math.floor(days/7); return w+(w===1?' week ago':' weeks ago'); }
  return new Date(ts*1000).toLocaleDateString(undefined,{month:'short',day:'numeric',year:'numeric'}); }
function fmtSize(n){ if(!n) return '—'; const u=['B','KB','MB','GB','TB']; let i=0; while(n>=1024&&i<4){n/=1024;i++;}
  return (i>=3 ? n.toFixed(1) : Math.round(n))+' '+u[i]; }
function hash(s){ let h=0; for(const c of s) h=(h*31+c.charCodeAt(0))|0; return Math.abs(h); }
function initials(n){ const w=n.replace(/[^\p{L}\p{N} ]/gu,'').split(/\s+/).filter(Boolean); return ((w[0]||'?')[0]+(w[1]?w[1][0]:'')).toUpperCase(); }
function tile(g){ const h=hash(g.name)%360;
  return `<div class="tile" style="background:linear-gradient(150deg,hsl(${h} 60% 34%),hsl(${(h+50)%360} 65% 16%))"><div class="ini">${esc(initials(g.name))}</div></div>`; }
const allGames=()=>S.data.games.concat(S.data.uninstalled||[]);
const gameById=id=>allGames().find(x=>x.id===id);
function actionBtn(g){  // play on installed games, install (when the launcher allows) on the rest
  if(!S.data.settings.hover_play) return '';   // off by default so covers can't be clicked into a game by accident
  if(g.installed===false) return g.canInstall?`<button class="playbtn inst" data-install="${esc(g.id)}" title="Install">${ic('download')}</button>`:'';
  return `<button class="playbtn" data-play="${esc(g.id)}" title="Play">${ic('play')}</button>`;
}
// Only Steam reliably knows a game was never played; elsewhere "no data" isn't "unplayed".
function lastLabel(g){ return (g.last||g.playing)?fmtAgo(g.last,g.playing):(g.launcher==='Steam'?'Never':'—'); }
function playLabel(g){ return g.total?fmtTime(g.total):(g.launcher==='Steam'?'Unplayed':''); }
const UPD={update:'Update required',updating:'Updating',paused:'Update paused',repair:'Needs repair'};
function updBadge(g){ return g.update&&!g.playing?`<span class="upd ${g.update}"><i></i>${UPD[g.update]||'Update'}</span>`:''; }
function updPanel(g){
  if(!g.update) return '';
  const steam=g.launcher==='Steam';
  const msg={update:steam?'Steam will download the update when you press Play, or you can start it now.':'This game needs an update before it can be played.',
    updating:'The update is downloading now. You can play once it finishes.',
    paused:'The update was paused. Resume it in Steam to play.',
    repair:steam?'Some game files are missing or damaged. Verify the files in Steam to fix it.':'Epic says this game needs to be verified. Open Epic Games to repair it.'}[g.update]||'';
  return `<div class="updbar ${g.update}"><div><b>${UPD[g.update]}</b><span>${msg}</span></div>
    <button class="btn" data-launcher="${steam?'steam':'epic'}">${steam?'Open Steam downloads':'Open Epic Games'}</button></div>`;
}
function sourceNote(g){
  if(g.source==='Steam') return 'Play time from Steam';
  if(g.source==='GOG Galaxy') return 'Play time from GOG Galaxy';
  if(g.source==='Game Hub') return 'Play time tracked by Game Hub while it runs';
  if(g.installed===false) return 'No play time recorded for this game';
  if(g.launcher==='Steam') return 'Not played yet';
  return 'No play time yet — Game Hub will track it from now on'; }

// ---------- filtering
function visible(){
  const {k,v}=S.view, q=S.q.trim().toLowerCase();
  const list=(k==='uninstalled'?(S.data.uninstalled||[]):k==='hidden'?allGames():S.data.games).filter(g=>{
    if((k==='hidden')!==!!g.hidden) return false;
    if(k==='fav'&&!g.fav) return false;
    if(k==='updates'&&!g.update) return false;
    if(k==='recent'&&!g.last&&!g.playing) return false;
    if(k==='launcher'&&g.launcher!==v) return false;
    if(k==='coll'&&g.collection!==v) return false;
    return !q || g.name.toLowerCase().includes(q);
  });
  const nm=(a,b)=>a.name.localeCompare(b.name);
  const by={name:nm, recent:(a,b)=>(b.playing-a.playing)||(b.last-a.last)||nm(a,b), most:(a,b)=>(b.total-a.total)||nm(a,b),
    fortnight:(a,b)=>(b.recent-a.recent)||(b.last-a.last)||nm(a,b), size:(a,b)=>(b.size-a.size)||nm(a,b),
    launcher:(a,b)=>a.launcher.localeCompare(b.launcher)||nm(a,b)};
  const cmp=by[k==='recent'?'recent':k==='all'?'name':S.sort]||nm;
  return list.sort(k!=='all'&&S.rev?(a,b)=>cmp(b,a):cmp);
}

// ---------- rendering
function render(){ if(!S.data) return; renderSide(); renderTop(); renderContent(); renderDrawer(); observeCovers(); }

function navItem(id, icon, label, n, extra=''){
  const [k,v]=id.split('|'); const on=S.view.k===k&&(S.view.v||'')===(v||'');
  return `<div class="nav ${on?'active':''}" data-nav="${esc(id)}">${icon}<span>${esc(label)}</span>${extra}<span class="n">${n}</span></div>`; }

function renderSide(){
  const gs=S.data.games, vis=gs.filter(g=>!g.hidden), counts={};
  vis.forEach(g=>counts[g.launcher]=(counts[g.launcher]||0)+1);
  let h=`<div class="brand"><div class="logo"><svg viewBox="0 0 24 24"><polygon points="7 4 20 12 7 20"/></svg></div>Game Hub</div>`;
  h+=navItem('all',ic('pad'),'Home','');
  h+=navItem('games',ic('grid'),'All games',vis.length);
  h+=navItem('recent',ic('clock'),'Recently played',vis.filter(g=>g.last||g.playing).length);
  h+=navItem('fav',ic('star'),'Favorites',vis.filter(g=>g.fav).length);
  if(FRIENDS_ON){ const fo=friendsOnline(); h+=navItem('friends',ic('users'),'Friends',fo===null?'':fo); }
  const nu=vis.filter(g=>g.update).length; if(nu) h+=navItem('updates',ic('download'),'Updates',nu);
  const ls=Object.keys(counts).sort();
  if(ls.length){ h+='<div class="sec">Launchers</div>'; ls.forEach(l=>h+=navItem('launcher|'+l,`<span class="dot" style="background:${lc(l)}"></span>`,l,counts[l])); }
  if(S.data.collections.length){ h+='<div class="sec">Collections</div>';
    S.data.collections.forEach(c=>h+=navItem('coll|'+c,ic('layers'),c,vis.filter(g=>g.collection===c).length)); }
  const nh=S.data.settings.show_hidden?allGames().filter(g=>g.hidden).length:0;
  const nun=(S.data.uninstalled||[]).filter(g=>!g.hidden).length;
  if(nh||nun){ h+='<div class="sec">Other</div>';
    if(nun) h+=navItem('uninstalled',ic('archive'),'Uninstalled',nun);
    if(nh) h+=navItem('hidden',ic('eyeoff'),'Hidden',nh); }
  const tracking=S.data.settings.tracking, playing=gs.filter(g=>g.playing);
  const sum=f=>vis.reduce((a,g)=>a+(g[f]||0),0);
  const au=S.data.app_update;
  const updNote=au&&S.updLater!==au.version?`<div class="appupd"><b>Update ready</b><span>Game Hub ${esc(au.version)} is ready to install.</span>
      <div class="appupd-acts"><button class="btn primary" data-act="appupdate">Update now</button><button class="linkbtn" data-act="appupdlater">Later</button></div></div>`:'';
  h+=`<div class="side-bottom">${updNote}<div class="side-stats">
      <div><b>${fmtSize(sum('size'))}</b>on disk</div>
      <div><b>${fmtTime(sum('recent'))}</b>played in the last 2 weeks</div>
      <div><b>${fmtTime(sum('total'))}</b>played in total${funTotal(sum('total'))?`<span class="fun">${funTotal(sum('total'))}</span>`:''}</div></div>`;
  h+=`<div class="side-foot"><span class="pulse ${tracking?'':'off'}"></span><span>${!tracking?'Tracking paused':playing.length?'Playing '+esc(playing[0].name):'Tracking play time'}</span></div></div>`;
  $('#side').innerHTML=h;
}

const SORTS=[['name','Name'],['recent','Recently played'],['most','Most played'],['fortnight','Played in the last 2 weeks'],['size','Size on disk'],['launcher','Launcher']];
const DIRS={name:['A to Z','Z to A'],recent:['Newest first','Oldest first'],most:['Most played first','Least played first'],
  fortnight:['Most played first','Least played first'],size:['Largest first','Smallest first'],launcher:['A to Z','Z to A']};
const curSort=()=>S.view.k==='recent'?'recent':S.sort;
function setSort(v){ if(v===S.sort) S.rev=!S.rev; else { S.sort=v; S.rev=false; } store('sort',S.sort); store('rev',S.rev?'1':'0'); render(); }
function renderTop(){
  const {k,v}=S.view;
  const title={all:'Home',friends:'Friends',games:'All games',updates:'Updates',uninstalled:'Uninstalled',recent:'Recently played',fav:'Favorites',hidden:'Hidden'}[k]||v;
  const n=visible().length;
  const sorts=SORTS; void [['name','Name A–Z'],['recent','Recently played'],['most','Most played'],['fortnight','Played in the last 2 weeks'],['size','Size on disk'],['launcher','Launcher']];
  const focused=document.activeElement&&document.activeElement.id==='q';
  const sub=k==='friends'?(friendsOnline()===null?'':`${friendsOnline()} online`):`${n} game${n===1?'':'s'}`;
  const homeTop=k==='all'&&!S.q.trim()&&S.data.games.length;
  const ttl=homeTop?`${esc(S.greet||(S.greet=greeting()))}<span class="greet">${homeLine(S.data.games.filter(g=>!g.hidden&&g.installed!==false))}</span>`:`${esc(title)}<small>${sub}</small>`;
  if(focused){ $('#ttl').innerHTML=ttl; return; }
  $('#top').innerHTML=`<div class="title" id="ttl">${ttl}</div>
    <div class="search">${ic('search')}<input id="q" placeholder="${k==='friends'?'Search friends…':'Search your games…'}  ( / )" value="${esc(S.q)}"></div>
    ${k==='all'||k==='friends'?'':`<div class="sortgrp"><button class="btn sortbtn" data-act="sortmenu" ${k==='recent'?'disabled':''}>${ic('sort')}<span>${esc((sorts.find(x=>x[0]===curSort())||sorts[0])[1])}</span>${ic('down')}</button><button class="btn icon dirbtn" data-act="sortdir" title="${esc(DIRS[curSort()][S.rev?1:0])} (click to flip)" aria-label="Sort direction: ${esc(DIRS[curSort()][S.rev?1:0])}">${ic(S.rev?'sortup':'sortdown')}</button></div>
    <div class="seg"><button data-mode="grid" class="${S.mode==='grid'?'on':''}" title="Grid">${ic('grid')}</button><button data-mode="list" class="${S.mode==='list'?'on':''}" title="List">${ic('list')}</button></div>`}
    <button class="btn" data-act="add">${ic('plus')}Add game</button>
    <button class="btn icon ${S.data.scanning||S.rescanning?'spin':''}" data-act="rescan" title="Rescan all launchers and folders" aria-label="Rescan all launchers and folders">${ic('refresh')}</button>
    <button class="btn icon" data-act="settings" title="Settings">${ic('gear')}</button>`;
}

function starBtn(g, cls='star'){
  return `<button class="${cls} ${g.fav?'on':''}" data-star="${esc(g.id)}" title="${g.fav?'Remove from favorites':'Add to favorites'}">${ic('starf')}</button>`; }

function coverBox(g, cls=''){
  return `<div class="cover ${cls}" data-cover="${esc(g.id)}">${tile(g)}</div>`; }

function card(g){
  return `<div class="card ${g.installed===false?'off':''}" data-open="${esc(g.id)}">
    <div class="cover" data-cover="${esc(g.id)}">${tile(g)}
      ${g.playing?'<span class="live"><i></i>Playing</span>':''}${updBadge(g)}${starBtn(g)}
      ${g.installed===false?'<span class="noinst">Not installed</span>':''}${actionBtn(g)}</div>
    <div class="meta"><div class="nrow"><div class="name" title="${esc(g.name)}">${esc(g.name)}</div>${moreBtn(g)}</div>
      <div class="sub"><span class="dot" style="background:${lc(g.launcher)}"></span>${esc(g.launcher)}${playLabel(g)?`<span class="sep">·</span>${playLabel(g)}`:''}</div></div></div>`; }

function wcard(g, info='ago'){
  const right = info==='ago' ? fmtAgo(g.last,g.playing) : info==='dust' ? longAgo(g.last)
    : `<span class="lchip"><span class="dot" style="background:${lc(g.launcher)}"></span>${esc(g.launcher)}${playLabel(g)?' · '+playLabel(g):''}</span>`;
  return `<div class="wcard" data-open="${esc(g.id)}">
    <div class="cover wide" data-cover="${esc(g.id)}">${tile(g)}${g.playing?'<span class="live"><i></i>Playing</span>':''}${updBadge(g)}${starBtn(g)}
      ${g.installed===false?'<span class="noinst">Not installed</span>':''}${actionBtn(g)}</div>
    <div class="wmeta"><b>${esc(g.name)}</b><span class="wr"><span style="white-space:nowrap">${right}</span>${moreBtn(g)}</span></div></div>`; }

function slider(title, nav, count, items, cls=''){
  return `<div class="shead"><button class="h3link" data-nav="${nav}" title="Open ${esc(title)}">${esc(title)}${count!=null?` <em>${count}</em>`:''}${ic('right')}</button>
    <div class="arrows"><button class="arr" data-scroll="-1" title="Back">${ic('left')}</button><button class="arr" data-scroll="1" title="More">${ic('right')}</button></div></div>
    <div class="slider ${cls}">${items}</div>`; }
function updArrows(sl){
  const head=sl.previousElementSibling; if(!head) return;
  const [l,r]=head.querySelectorAll('.arr'); const max=sl.scrollWidth-sl.clientWidth-2;
  if(l) l.disabled=sl.scrollLeft<=2; if(r) r.disabled=sl.scrollLeft>=max;
  sl.classList.toggle('end', sl.scrollLeft>=max);
}
function initSliders(){ document.querySelectorAll('.slider').forEach(sl=>{
  updArrows(sl);
  sl.addEventListener('scroll',()=>updArrows(sl),{passive:true});
}); }
window.addEventListener('resize',()=>document.querySelectorAll('.slider').forEach(updArrows));

function renderContent(){
  if(S.view.k==='friends'&&!FRIENDS_ON) S.view={k:'all'};
  if(S.view.k==='friends'){ $('#content').innerHTML=friendsHTML(); if(!S.friends) loadFriends(); return; }
  const list=visible(), home=S.view.k==='all'&&!S.q.trim(), d=S.data;
  let h='';
  if(d.scanning&&!d.games.length){
    h=`<div class="grid">${'<div class="skel"></div>'.repeat(14)}</div>`;
  } else {
    if(home&&d.games.length){
      const vis=d.games.filter(g=>!g.hidden);
      if(vis.length) h+=`<section class="hero" id="hero"><div class="hero-art" id="heroArt"></div><div class="hero-shade"></div>
        <div class="hero-body" id="heroBody"></div><div class="hero-dots" id="heroDots"></div></section>`;
      const rec=vis.filter(g=>g.last||g.playing).sort((a,b)=>(b.playing-a.playing)||(b.last-a.last)).slice(0,10);
      if(rec.length) h+=slider('Jump back in','recent',null,rec.map(g=>wcard(g,'ago')).join(''),'wides');
      const favs=list.filter(g=>g.fav);
      if(favs.length) h+=slider('Favorites','fav',favs.length,favs.slice(0,20).map(g=>wcard(g,'info')).join(''),'wides');
      const dust=vis.filter(g=>g.installed!==false&&!g.playing&&g.total>=3600&&daysSince(g.last)>=60).sort((a,b)=>b.total-a.total).slice(0,10);
      if(dust.length>=2) h+=slider('Miss these?','recent',null,dust.map(g=>wcard(g,'dust')).join(''),'wides');
      if(list.length){
        const shown=list.slice(0,30);
        const more=list.length>shown.length?`<div class="seeall" data-nav="games"><span>${ic('right')}</span>See all ${list.length} games</div>`:'';
        h+=slider('All games','games',list.length,shown.map(g=>wcard(g,'info')).join('')+more,'wides');
      }
      $('#content').innerHTML=h; initSliders(); renderHero(); return;
    }
    if(!list.length){
      const E=(icon,b,t)=>`<div class="empty"><div class="eic">${ic(icon)}</div><b>${b}</b><span>${t}</span></div>`, k=S.view.k;
      h+= !d.games.length ? E('pad','The shelf is empty','No installed games turned up. Click <i>Add game</i> to add one by hand, or Rescan after installing a launcher.')
        : S.q ? E('search',`No luck with “${esc(S.q.trim())}”`,'Check the spelling, or try part of the name.')
        : k==='recent' ? E('clock','Nothing played yet','Pick something and hit Play. It’ll show up here.')
        : k==='fav' ? E('star','No favorites yet','Tap the star on any game you love and it’ll live here.')
        : k==='updates' ? E('download','All caught up','Every game is up to date. Go play something.')
        : k==='uninstalled' ? E('trash','Nothing uninstalled','Games you remove from a launcher will show up here.')
        : k==='hidden' ? E('eyeoff','Nothing hidden','Hide a game from its ⋯ menu and it’ll wait here.')
        : E('grid','Nothing here yet','Try another view.');
    } else if(S.mode==='grid'){
      h+=`<div class="grid">${list.map(card).join('')}</div>`;
    } else {
      const cols=[['','',''],['','',''],['name','Name',''],['launcher','Launcher',''],['most','Total','r'],['fortnight','Last 2 wks','r'],['recent','Last played','r'],['size','Size','r'],['','','']];
      h+=`<table><thead><tr>${cols.map(([s,l,c])=>`<th class="${c} ${S.sort===s?'on':''}" ${s?`data-sort="${s}"`:''}>${l}</th>`).join('')}</tr></thead><tbody>
        ${list.map(g=>`<tr class="row" data-open="${esc(g.id)}"><td>${coverBox(g)}</td><td style="width:40px;padding:0 4px">${starBtn(g,'lstar')}</td><td class="nm">${esc(g.name)}${g.update?` <span class="upd inline ${g.update}"><i></i>${UPD[g.update]}</span>`:''}</td>
          <td><span class="lchip"><span class="dot" style="background:${lc(g.launcher)}"></span>${esc(g.launcher)}</span></td>
          <td class="r">${fmtTime(g.total)}</td><td class="r">${fmtTime(g.recent)}</td>
          <td class="r ${g.playing?'livetxt':''}">${lastLabel(g)}</td><td class="r">${g.installed===false?'Not installed':fmtSize(g.size)}</td><td style="width:44px;padding:0 8px">${moreBtn(g)}</td></tr>`).join('')}</tbody></table>`;
    }
  }
  $('#content').innerHTML=h;
}

function renderDrawer(){
  const g=S.open&&gameById(S.open), dr=$('#drawer');
  $('#scrim').classList.toggle('on',!!g); dr.classList.toggle('open',!!g);
  if(!g) return;
  if(document.activeElement&&document.activeElement.id==='coll'&&dr.dataset.id===g.id) return;
  dr.dataset.id=g.id;
  const pills=S.data.collections.map(c=>`<span class="pill ${g.collection===c?'on':''}" data-coll="${esc(c)}">${esc(c)}</span>`).join('');
  dr.innerHTML=`<button class="x" data-act="close">${ic('x')}</button>
    <div class="d-top"><div class="d-bg" id="dbg"></div><div class="d-fade"></div>
      <div class="d-head">${coverBox(g,'dcover')}<div>
        <span class="chip"><span class="dot" style="background:${lc(g.launcher)}"></span>${esc(g.launcher)}</span>
        <h2>${esc(g.name)}</h2>${g.playing?'<div class="livetxt" style="margin-top:6px">● Playing now</div>':''}</div></div></div>
    <div class="d-body">
      ${g.installed===false
        ? (g.canInstall?`<button class="btn primary big" data-install="${esc(g.id)}">${ic('download')}Install with ${esc(g.launcher)}</button>`
                       :`<div class="updbar off"><div><b>Not installed</b><span>Install it again from ${esc(g.launcher)} and it will move back to your library.</span></div></div>`)
        : `${updPanel(g)}<button class="btn primary big" data-play="${esc(g.id)}">${ic('play')}${g.update==='update'&&g.launcher==='Steam'?'Update and play':'Play'}</button>`}
      <div class="d-stats">
        <div class="ds"><span>Total played</span><b>${fmtTime(g.total)}</b></div>
        <div class="ds"><span>Last 2 weeks</span><b>${fmtTime(g.recent)}</b></div>
        <div class="ds"><span>Last played</span><b>${lastLabel(g)}</b></div>
        <div class="ds"><span>Size on disk</span><b>${g.installed===false?'—':fmtSize(g.size)}</b></div></div>
      ${badgesHTML(g,'d-badges')}<div class="note">${ic('info')}${sourceNote(g)}</div>
      <div id="dAbout">${aboutHTML(DET[g.id])}</div>
      <label class="lbl">Collection</label>
      <input class="inp" id="coll" placeholder="Type a name, e.g. Co-op or Backlog — Enter to save" value="${esc(g.collection)}">
      <div class="pills">${pills}${g.collection?`<span class="pill" data-coll="">Remove from collection</span>`:''}</div>
      <div class="d-actions">
        <button class="btn" data-act="fav">${ic('star')}${g.fav?'Unfavorite':'Favorite'}</button>
        ${g.installed===false?'':`<button class="btn" data-act="folder">${ic('folder')}Open folder</button>`}
        <button class="btn" data-act="cover">${ic('image')}Change cover</button>
        ${g.installed===false?`<button class="btn danger" data-act="forget">${ic('trash')}Remove from list</button>`
          :`<button class="btn" data-act="hide">${ic(g.hidden?'eye':'eyeoff')}${g.hidden?'Unhide':'Hide'}</button>`}
        ${g.custom?`<button class="btn danger" data-act="remove" style="grid-column:span 2">${ic('trash')}Remove from Game Hub</button>`:''}
      </div>
      <div class="path">${esc(g.path||'')}</div></div>`;
  requestAnimationFrame(fitAbout);
}

// ---------- game details (About section)
const DET={};
async function loadDetails(id){
  if(DET[id]===undefined){ DET[id]=null; try{ DET[id]=await api().get_details(id)||{}; }catch(e){ DET[id]={}; } }
  return DET[id];
}
function aboutHTML(d){
  if(!d) return `<label class="lbl">About</label><div class="about-loading"><span></span><span></span><span></span></div>`;
  const has=d.desc||(d.dev&&d.dev.length)||(d.genres&&d.genres.length)||(d.shots&&d.shots.length);
  if(!has) return '';
  const facts=[]; const add=(k,v)=>{ if(v) facts.push(`<dt>${k}</dt><dd>${esc(v)}</dd>`); };
  add('Developer',(d.dev||[]).join(', '));
  if((d.pub||[]).join()!==(d.dev||[]).join()) add('Publisher',(d.pub||[]).join(', '));
  add('Released',d.released); add('Genres',(d.genres||[]).join(', '));
  const sc=d.score?`<span class="mc ${d.score>=75?'hi':d.score>=50?'mid':'lo'}" title="Metacritic score">${d.score}</span>`:'';
  const shots=(d.shots||[]).map((x,i)=>`<img src="${esc(x.thumb)}" data-shot="${i}" alt="Screenshot ${i+1}" loading="lazy">`).join('');
  return `<div class="about-head"><label class="lbl">About</label>${sc}</div>
    ${d.desc?`<p class="desc" id="dDesc">${esc(d.desc)}</p><button class="linkbtn" data-more="1" hidden>Show more</button>`:''}
    ${facts.length?`<dl class="facts">${facts.join('')}</dl>`:''}
    ${(d.features||[]).length?`<div class="chips">${d.features.map(f=>`<span class="chipx">${esc(f)}</span>`).join('')}</div>`:''}
    ${shots?`<div class="shots">${shots}</div>`:''}
    ${d.url?`<button class="linkbtn" data-url="${esc(d.url)}">Open on ${esc(d.source||'the web')}</button>`:''}`;
}
function fitAbout(){  // show "Show more" only when the description really overflows
  const p=$('#dDesc'), b=document.querySelector('[data-more]'); if(!p||!b) return;
  b.hidden=!(p.classList.contains('open')||p.scrollHeight>p.clientHeight+2);
}
async function fillAbout(id){
  if(!DET[id]){
    await loadDetails(id);
    if(S.open===id){ const el=$('#dAbout'); if(el) el.innerHTML=aboutHTML(DET[id]); }
  }
  requestAnimationFrame(fitAbout);
}
let lbList=[], lbIdx=0;
function openLightbox(list, i){ lbList=list; lbIdx=i; $('#lbImg').src=list[i]; $('#lightbox').classList.add('on'); }
function stepLightbox(n){ if(!lbList.length) return; lbIdx=(lbIdx+n+lbList.length)%lbList.length; $('#lbImg').src=lbList[lbIdx]; }
function closeLightbox(){ $('#lightbox').classList.remove('on'); }

// ---------- covers (lazy)
const io=new IntersectionObserver(es=>es.forEach(e=>{ if(e.isIntersecting){ io.unobserve(e.target); loadCover(e.target.dataset.cover); } }),{rootMargin:'400px'});
function observeCovers(){ document.querySelectorAll('[data-cover]').forEach(el=>{
  if(el.querySelector('img')) return; if(COV[el.dataset.cover]!==undefined) applyCover(el); else io.observe(el); }); }
const BLOBS=new Set();
function blobify(o){  // turn data: strings into blob: URLs so the text copies can be freed
  for(const k of ['src','wide','fallback','hero','logo']){
    const v=o[k]; if(typeof v!=='string'||!v.startsWith('data:')) continue;
    try{ const i=v.indexOf(','), mime=v.slice(5,v.indexOf(';')), bin=atob(v.slice(i+1)), arr=new Uint8Array(bin.length);
      for(let j=0;j<bin.length;j++) arr[j]=bin.charCodeAt(j);
      const u=URL.createObjectURL(new Blob([arr],{type:mime})); BLOBS.add(u);
      for(const k2 of ['src','wide','fallback','hero','logo']) if(o[k2]===v) o[k2]=u;
    }catch(e){}
  }
  return o;
}
async function coverData(id){
  if(COV[id]===undefined){
    if(!PENDING[id]) PENDING[id]=api().get_cover(id).then(r=>{COV[id]=blobify(Object.assign({bad:[],ok:[]},r||{}));}).catch(()=>{COV[id]={bad:[],ok:[]};});
    await PENDING[id];
  }
  return COV[id];
}
async function loadCover(id){
  await coverData(id);
  document.querySelectorAll('[data-cover]').forEach(el=>{ if(el.dataset.cover===id) applyCover(el); });
}
const pickSrc=(c,wide)=>(wide?[c.wide,c.src,c.fallback]:[c.src,c.fallback,c.wide]).find(s=>s&&!c.bad.includes(s));
function warm(c, wide){  // download an image ahead of time; bad links are remembered so cards never flash
  return new Promise(res=>{
    const next=()=>{ const src=pickSrc(c,wide); if(!src||c.ok.includes(src)) return res();
      const im=new Image(); let t=setTimeout(()=>{ im.onload=im.onerror=null; c.bad.push(src); next(); }, 9000);
      im.onload=()=>{ clearTimeout(t); c.ok.push(src); res(); };
      im.onerror=()=>{ clearTimeout(t); c.bad.push(src); next(); };
      im.src=src; };
    next();
  });
}
async function preloadCovers(onProgress, cancelled){
  const list=S.data.games.filter(g=>!g.hidden); let i=0, done=0;
  const worker=async()=>{ while(i<list.length&&!cancelled()){ const g=list[i++]; const c=await coverData(g.id);
    await Promise.all([warm(c,false),warm(c,true)]); onProgress(++done,list.length); } };
  await Promise.all(Array.from({length:6},worker));
}
function applyCover(el){
  if(el.querySelector('img')) return;
  const c=COV[el.dataset.cover]; if(!c) return;
  const wide=el.classList.contains('wide');
  const pick=()=>pickSrc(c,wide);
  const src=pick(); if(!src) return;
  const img=new Image();
  const done=()=>{ img.classList.add('on'); const s=img.getAttribute('src'); if(!c.ok.includes(s)) c.ok.push(s);
    if(el.classList.contains('dcover')){ const bg=$('#dbg'); if(bg) bg.style.backgroundImage=`url("${img.src}")`; } };
  img.onload=done;
  img.onerror=()=>{ c.bad.push(img.getAttribute('src')); const next=pick(); if(next) img.src=next; else img.remove(); };
  if(c.ok.includes(src)) img.className='instant on';  // already loaded once: show immediately, no fade
  img.src=src; el.appendChild(img);
}

// ---------- hero, ambient background, game-colored accents
const HERO={}; let heroIdx=0, heroShown=null, heroHover=false;
function heroList(){
  const vis=S.data.games.filter(g=>!g.hidden);
  let l=vis.filter(g=>g.playing||g.last).sort((a,b)=>(b.playing-a.playing)||(b.last-a.last));
  for(const g of vis.filter(g=>g.fav)) if(l.length<5&&!l.includes(g)) l.push(g);
  for(const g of [...vis].sort((a,b)=>b.total-a.total)) if(l.length<5&&!l.includes(g)) l.push(g);
  return l.slice(0,5);
}
function agoPhrase(g){
  if(g.playing) return '<b>Playing now</b>';
  if(!g.last) return g.launcher==='Steam'?'Not played yet':'';
  const a=fmtAgo(g.last); return 'Last played '+(/^[A-Z][a-z]{2} \d/.test(a)?'on '+a:a.charAt(0).toLowerCase()+a.slice(1));
}
async function heroData(id){
  if(!HERO[id]){ try{ HERO[id]=blobify(Object.assign({bad:[]}, await api().get_hero(id))); }catch(e){ HERO[id]={bad:[]}; } }
  return HERO[id];
}
function loadImg(src){ return new Promise(res=>{ const im=new Image(); im.onload=()=>res(im); im.onerror=()=>res(null); im.src=src; }); }
async function firstGood(list, bad){
  for(const s of list){ if(!s||bad.includes(s)) continue; const im=await loadImg(s); if(im) return im; bad.push(s); }
  return null;
}
async function renderHero(){
  const box=$('#hero'); if(!box) return;
  const list=heroList(); if(!list.length) return box.remove();
  heroIdx=((heroIdx%list.length)+list.length)%list.length;
  const g=list[heroIdx], id=g.id, same=heroShown===id;
  $('#heroDots').innerHTML=list.length>1?list.map((x,i)=>`<button class="hdot ${i===heroIdx?'on':''}" data-hero="${i}" title="${esc(x.name)}"></button>`).join(''):'';
  $('#heroBody').innerHTML=`<div class="hero-title" id="heroTitle"><h1>${esc(g.name)}</h1></div>
    <div class="hero-meta"><span class="lchip"><span class="dot" style="background:${lc(g.launcher)}"></span>${esc(g.launcher)}</span>
      ${agoPhrase(g)?`<span>${agoPhrase(g)}</span>`:''}${g.total?`<span><b>${fmtTime(g.total)}</b>played</span>`:''}${g.update?`<span class="upd inline ${g.update}"><i></i>${UPD[g.update]}</span>`:''}</div>
    ${badgesHTML(g,'hero-badges')}<div class="hero-acts"><button class="btn go" data-play="${esc(id)}">${ic('play')}${g.last?'Continue':'Play'}</button>
      <button class="btn glass" data-open="${esc(id)}">Details</button>${starBtn(g,'star hstar')}${moreBtn(g,'more hmore')}</div>`;
  heroShown=id;
  applyGameColor(GC[id]);
  const [h,c]=await Promise.all([heroData(id),coverData(id)]);
  if(heroShown!==id||!$('#hero')) return;
  const art=$('#heroArt');
  const im=await firstGood([h.hero,c.wide,c.src,c.fallback], h.bad);
  if(heroShown!==id) return;
  if(im){
    const portrait=im.naturalWidth/im.naturalHeight<1.25;
    im.className=(portrait?'bg ':'')+(same?'instant':'');
    const old=[...art.children];
    art.classList.toggle('portrait',portrait); art.appendChild(im);
    requestAnimationFrame(()=>im.classList.add('on'));
    if(portrait){ const p=document.createElement('div'); p.className='hero-poster'; p.appendChild(im.cloneNode()); p.firstChild.className='';
      art.appendChild(p); requestAnimationFrame(()=>p.classList.add('on')); }
    setTimeout(()=>old.forEach(o=>o.remove()), 900);
  }
  if(h.logo&&!h.bad.includes(h.logo)){
    const lg=await loadImg(h.logo);
    if(heroShown!==id) return;
    if(lg&&lg.naturalWidth>40){ lg.alt=g.name; const t=$('#heroTitle'); if(t){ t.innerHTML=''; t.appendChild(lg); } } else h.bad.push(h.logo);
  }
  if(!GC[id]) gameColor([h.hero,c.wide,c.src,c.fallback].find(s=>s&&/^(data|blob):/.test(s)), id);
}
document.addEventListener('mouseover',e=>{ heroHover=!!e.target.closest('#hero'); });
setInterval(()=>{ if(S.data&&!S.sleeping&&!document.hidden&&S.view.k==='all'&&!S.q&&!heroHover&&!S.open&&$('#hero')&&document.hasFocus()){ heroIdx++; renderHero(); } }, 9000);

const GC={};  // game id -> its color
function applyGameColor(col){
  const el=$('#hero'); if(!el) return;
  if(!col){ el.style.removeProperty('--game'); el.style.removeProperty('--game-soft'); return; }
  el.style.setProperty('--game',col); el.style.setProperty('--game-soft',col.replace(')',' / .35)'));
}
function gameColor(src, id){  // colors the hero's Continue button after the featured game; the app theme never changes
  if(!src) return;
  const im=new Image();
  im.onload=()=>{ try{
    const cv=document.createElement('canvas'); cv.width=cv.height=24; const x=cv.getContext('2d'); x.drawImage(im,0,0,24,24);
    const d=x.getImageData(0,0,24,24).data; let r=0,g=0,b=0,w=0;
    for(let i=0;i<d.length;i+=4){ const mx=Math.max(d[i],d[i+1],d[i+2]), mn=Math.min(d[i],d[i+1],d[i+2]);
      const wt=(mx-mn)/255+0.04; r+=d[i]*wt; g+=d[i+1]*wt; b+=d[i+2]*wt; w+=wt; }
    let [h,s,l]=rgb2hsl(r/w,g/w,b/w); s=Math.max(s,0.5); l=Math.min(Math.max(l,0.5),0.6);
    GC[id]=`hsl(${h} ${Math.round(s*100)}% ${Math.round(l*100)}%)`;
    if(heroShown===id) applyGameColor(GC[id]);
  }catch(e){} };
  im.src=src;
}
function rgb2hsl(r,g,b){ r/=255; g/=255; b/=255; const mx=Math.max(r,g,b), mn=Math.min(r,g,b); let h=0,s=0; const l=(mx+mn)/2;
  if(mx!==mn){ const d=mx-mn; s=l>0.5?d/(2-mx-mn):d/(mx+mn);
    h=mx===r?(g-b)/d+(g<b?6:0):mx===g?(b-r)/d+2:(r-g)/d+4; h*=60; }
  return [Math.round(h),s,l]; }


// ---------- data
async function load(state){
  S.data=state||await api().get_state(); S.version=S.data.version; S.lastFull=Date.now();
  const au=S.data.app_update; if(au&&S.updSeen!==au.version){ S.updSeen=au.version; setTimeout(()=>toast(`Game Hub ${au.version} is ready to install — see the sidebar`), 1500); }
  for(const g of allGames()){ const c=COV[g.id]; if(c&&c.cv!==undefined&&c.cv!==g.cv){
    for(const k of ['src','wide','fallback']) if(typeof c[k]==='string'&&c[k].startsWith('blob:')){ URL.revokeObjectURL(c[k]); BLOBS.delete(c[k]); }
    delete COV[g.id]; delete PENDING[g.id];
    document.querySelectorAll('[data-cover] img').forEach(i=>{ if(i.parentElement.dataset.cover===g.id) i.remove(); }); } }
  render(); }
function toast(msg, ms=2600, icon=''){ const t=$('#toast'); t.innerHTML=(icon?`<span class="ti">${icon}</span>`:'')+`<span>${esc(msg)}</span>`;
  t.classList.remove('on'); void t.offsetWidth; t.classList.add('on'); clearTimeout(t._h); t._h=setTimeout(()=>t.classList.remove('on'),ms); }
const pick=a=>a[Math.floor(Math.random()*a.length)];
const DAY=86400;
function daysSince(ts){ return ts?Math.floor((Date.now()/1000-ts)/DAY):null; }
// Small earned labels, worked out from play time only
function badges(g){
  const b=[], h=(g.total||0)/3600, r=(g.recent||0)/3600, d=daysSince(g.last);
  if(h>=1000) b.push(['gold','👑','1,000-hour legend']);
  else if(h>=500) b.push(['gold','🏆','500-hour club']);
  else if(h>=100) b.push(['gold','🏅','100-hour club']);
  if(r>=20) b.push(['hot','🔥','Can’t put it down']);
  else if(r>=8) b.push(['hot','🔥','On a roll']);
  if(g.last){ const hr=new Date(g.last*1000).getHours(); if(hr>=0&&hr<5&&d!==null&&d<30) b.push(['owl','🌙','Night owl']); }
  if(g.installed!==false&&!g.playing){
    if(!g.total&&!g.last&&g.launcher==='Steam') b.push(['new','✨','Still in the wrapper']);
    else if(d!==null&&d>=365) b.push(['dust','🕸️','A year untouched']);
    else if(d!==null&&d>=90) b.push(['dust','🕸️','Gathering dust']);
  }
  return b; }
function badgesHTML(g, cls){ const b=badges(g); return b.length?`<div class="badges ${cls}">${b.map(([c,i,t])=>`<span class="badge ${c}"><i>${i}</i>${t}</span>`).join('')}</div>`:''; }
function greeting(){
  const hr=new Date().getHours();
  if(hr<5) return pick(['Still up?','Late-night session?','One more run?']);
  if(hr<12) return 'Good morning'; if(hr<18) return 'Good afternoon'; return 'Good evening'; }
function homeLine(vis){
  const on=vis.find(g=>g.playing); if(on) return `Have fun in <b>${esc(on.name)}</b>`;
  const rec=vis.filter(g=>g.recent>0).sort((a,b)=>b.recent-a.recent);
  const tot=rec.reduce((a,g)=>a+g.recent,0);
  if(rec.length&&tot>=3600) return `<b>${fmtTime(tot)}</b> played these last two weeks — mostly <b>${esc(rec[0].name)}</b>`;
  const last=vis.filter(g=>g.last).sort((a,b)=>b.last-a.last)[0];
  if(last&&daysSince(last.last)>=14) return `It’s been a while. <b>${esc(last.name)}</b> is right where you left it`;
  if(last) return `Last time it was <b>${esc(last.name)}</b>. Pick up where you left off?`;
  return `${vis.length} game${vis.length===1?'':'s'} ready to play`; }
function longAgo(ts){ const d=daysSince(ts); if(d===null) return '';
  if(d>=730) return `${Math.floor(d/365)} years ago`; if(d>=365) return 'Over a year ago';
  if(d>=60) return `${Math.floor(d/30)} months ago`; return `${Math.floor(d/7)} weeks ago`; }
function funTotal(sec){ const h=sec/3600; if(h<48) return '';
  const days=Math.round(h/24); return days>=365?`that’s ${(days/365).toFixed(1)} years nonstop`:`that’s ${days} days nonstop`; }
function burst(el){
  const r=el.getBoundingClientRect(), b=document.createElement('div'); b.className='burst';
  b.style.left=(r.left+r.width/2)+'px'; b.style.top=(r.top+r.height/2)+'px';
  for(let i=0;i<10;i++){ const a=i/10*Math.PI*2, d=22+Math.random()*12, s=document.createElement('i');
    s.style.setProperty('--x',Math.cos(a)*d+'px'); s.style.setProperty('--y',Math.sin(a)*d+'px'); b.appendChild(s); }
  document.body.appendChild(b); setTimeout(()=>b.remove(),700); }
const QUIPS=['Blowing on the cartridges…','Asking every launcher nicely…','Counting your hours. No judgment.','Dusting off the backlog…','Lining up the shelf…','Finding the good cover art…','Untangling the controller cables…','Checking under the couch for games…'];
async function play(id){
  const g=gameById(id); const r=await api().play(id);
  if(!r.ok) return toast('Couldn’t launch: '+r.error);
  if(g&&g.update==='update'&&g.launcher==='Steam') return toast(`Steam will update ${g.name} before it starts`);
  if(g&&(g.update==='updating'||g.update==='paused')) return toast(`${g.name} is still updating — Steam will start it when it's done`);
  const n=g?g.name:'your game';
  toast(r.note||pick([`Launching ${n}. Have fun!`,`${n} is starting. Good luck out there.`,`Loading ${n}… grab a drink.`,`Here we go: ${n}`]), 2600, r.note?'':'🎮'); }

async function toggleStar(id, btn){
  const g=gameById(id); if(!g) return;
  g.fav=!g.fav;                                   // instant feedback
  document.querySelectorAll('[data-star]').forEach(b=>{ if(b.dataset.star===id){ b.classList.toggle('on',g.fav);
    b.title=g.fav?'Remove from favorites':'Add to favorites'; } });
  if(btn){ btn.classList.remove('pop'); void btn.offsetWidth; btn.classList.add('pop'); if(g.fav) burst(btn); }
  toast(g.fav?`${g.name} is a favorite now`:`${g.name} left your favorites`, 2600, g.fav?'⭐':'');
  const st=await api().toggle_favorite(id);
  setTimeout(()=>load(st), 380);                  // let the pop animation finish, then refresh rows
}

// ---------- popup menus (sort menu, ⋯ game menu)
let MENU=[];
let menuOwner=null;
function openMenu(items, x, y, anchor, owner=null){
  MENU=items; menuOwner=owner; const m=$('#menu');
  m.innerHTML=items.map((it,i)=>it==='-'?'<div class="msep"></div>'
    :`<button class="mi ${it.danger?'danger':''} ${it.check?'on':''}" data-mi="${i}" ${it.disabled?'disabled':''}>${it.icon?ic(it.icon):'<span class="mi-pad"></span>'}<span>${esc(it.label)}</span>${it.check?ic('check'):''}</button>`).join('');
  m.classList.add('on');
  const r=m.getBoundingClientRect(), W=innerWidth, H=innerHeight;
  let left=anchor?anchor.right-r.width:x, top=anchor?anchor.bottom+6:y;
  if(anchor&&top+r.height>H-10) top=anchor.top-r.height-6;
  left=Math.max(10,Math.min(left,W-r.width-10)); top=Math.max(10,Math.min(top,H-r.height-10));
  m.style.left=left+'px'; m.style.top=top+'px';
}
function closeMenu(){ $('#menu').classList.remove('on'); MENU=[]; menuOwner=null; }
function moreBtn(g, cls='more'){ return `<button class="${cls}" data-menu="${esc(g.id)}" title="More options" aria-label="More options for ${esc(g.name)}">${ic('dots')}</button>`; }
function sortMenu(btn){
  const items=SORTS.map(([v,l])=>({label:l, check:S.sort===v, run:()=>setSort(v)}));
  items.push('-');
  DIRS[S.sort].forEach((d,i)=>items.push({label:d, icon:i?'sortup':'sortdown', check:S.rev===!!i,
    run:()=>{ S.rev=!!i; store('rev',S.rev?'1':'0'); render(); }}));
  openMenu(items, 0, 0, btn.getBoundingClientRect(), 'sort');
}
function gameMenu(g, x, y, anchor){
  const owner=anchor?'menu:'+g.id:null;
  const items=[];
  if(g.installed===false){
    if(g.canInstall) items.push({label:`Install with ${g.launcher}`, icon:'download', run:()=>installGame(g.id)});
  } else {
    items.push({label:g.update==='update'&&g.launcher==='Steam'?'Update and play':'Play', icon:'play', run:()=>play(g.id)});
    if(g.update==='update'||g.update==='paused') items.push({label:g.update==='paused'?'Resume update':'Update now', icon:'download', run:()=>api().open_launcher('steam')});
    if(g.update==='updating') items.push({label:'View download progress', icon:'download', run:()=>api().open_launcher('steam')});
    if(g.update==='repair') items.push({label:g.launcher==='Steam'?'Verify game files':'Repair in Epic Games', icon:'wrench', run:()=>repairGame(g)});
    if(g.path) items.push({label:'Open folder', icon:'folder', run:()=>api().open_folder(g.id)});
  }
  items.push({label:'Details', icon:'info', run:()=>{ S.open=g.id; renderDrawer(); observeCovers(); fillAbout(g.id); }});
  items.push('-');
  items.push({label:g.fav?'Remove from favorites':'Add to favorites', icon:'star', run:()=>toggleStar(g.id)});
  items.push({label:'Change cover', icon:'image', run:async()=>{ if(await api().pick_cover(g.id)){ delete COV[g.id]; delete PENDING[g.id]; await load(); } }});
  items.push({label:g.hidden?'Unhide':'Hide', icon:g.hidden?'eye':'eyeoff', run:()=>hideGame(g.id)});
  items.push('-');
  if(g.installed===false) items.push({label:'Remove from list', icon:'trash', danger:true, run:async()=>{ toast(`Removed ${g.name} from the Uninstalled list`); if(S.open===g.id) S.open=null; load(await api().forget_game(g.id)); }});
  else if(g.custom) items.push({label:'Remove from Game Hub', icon:'trash', danger:true, run:async()=>{ if(S.open===g.id) S.open=null; load(await api().remove_custom(g.id)); }});
  else if(g.launcher==='Standalone'){
    items.push({label:'Uninstall', icon:'trash', danger:true, run:()=>uninstallGame(g)});
    items.push({label:'Not a game? Remove from Game Hub', icon:'eyeoff', run:async()=>{ if(S.open===g.id) S.open=null; toast(`${g.name} won't be listed again`); load(await api().forget_game(g.id)); }});
  }
  else items.push({label:g.launcher==='Epic'?'Uninstall in Epic Games':g.launcher==='RSI'?'Uninstall in RSI Launcher':'Uninstall', icon:'trash', danger:true, run:()=>uninstallGame(g)});
  openMenu(items, x, y, anchor, owner);
}
async function hideGame(id){
  const st=await api().toggle_hidden(id); const g=(st.games.concat(st.uninstalled||[])).find(x=>x.id===id);
  if(g&&g.hidden){ if(S.open===id&&!st.settings.show_hidden) S.open=null;
    toast(st.settings.show_hidden?`${g.name} hidden — it's under Hidden in the sidebar`:`${g.name} hidden. Turn on “Show hidden games” in Settings to see it again.`); }
  else toast('Unhidden');
  load(st);
}
async function installGame(id){
  const g=gameById(id); const r=await api().install(id);
  toast(r.ok?`Opening ${g?g.launcher:'the launcher'} to install ${g?g.name:'the game'}`:'Couldn’t start the install: '+r.error);
}
async function repairGame(g){
  const r=await api().repair_game(g.id);
  toast(r.ok?(g.launcher==='Steam'?`Steam is verifying ${g.name}'s files`:'Opening Epic Games — choose Verify from the game’s menu'):r.error);
}
async function uninstallGame(g){
  const how={Steam:'Steam will ask you to confirm before anything is removed.',
    Epic:'Epic doesn’t let other apps uninstall its games, so Game Hub will open your Epic library. Open the game’s menu there and choose Uninstall.',
    Xbox:'Xbox games are removed in Windows Settings. Game Hub will open Installed apps for you.',
    Standalone:`This runs ${g.name}'s own uninstaller if it has one. Games without one can be removed by deleting their folder.`,
    'itch.io':'itch.io games are removed in the itch app. Game Hub will open your itch library.',
    RSI:'Star Citizen is removed from inside the RSI Launcher. Game Hub will open it — use the uninstall option in the launcher’s game settings.'}[g.launcher]
    ||`This opens ${g.name}'s own uninstaller, which will ask you to confirm.`;
  const ok=await confirmBox(`Uninstall ${g.name}?`, how, g.launcher==='Epic'?'Open Epic Games':g.launcher==='Xbox'?'Open Settings':g.launcher==='RSI'?'Open RSI Launcher':g.launcher==='itch.io'?'Open itch':'Uninstall');
  if(!ok) return;
  const r=await api().uninstall_game(g.id);
  if(!r.ok) return toast('Couldn’t start the uninstall: '+r.error);
  toast(r.how==='settings'&&g.launcher!=='Xbox'?'No uninstaller was found for this game, so Windows Installed apps was opened instead.'
    :'Once it’s removed, the game will move to Uninstalled.');
}
function confirmBox(title, text, okLabel){ return new Promise(res=>{
  modal(`<h3>${esc(title)}</h3><p style="white-space:pre-line">${esc(text)}</p><div class="acts"><button class="btn" id="cfNo">Cancel</button><button class="btn primary ${okLabel==='Uninstall'?'danger-fill':''}" id="cfOk">${esc(okLabel)}</button></div>`);
  const fin=v=>{ closeModal(); res(v); };
  $('#cfOk').onclick=()=>fin(true); $('#cfNo').onclick=()=>fin(false); setTimeout(()=>$('#cfOk').focus(),50);
}); }

// ---------- friends
const FRIENDS_ON=false;   // Friends page parked for a later update
const FST={ingame:'Playing',online:'Online',away:'Away',busy:'Busy',offline:'Offline',unknown:''};
const LIVE_ST=['ingame','online','away','busy'];
const isLive=s=>!!(s.live||s.running);   // a source with real online status (not just saved names)
function friendsOnline(){ if(!S.friends) return null;
  const live=Object.values(S.friends.sources).filter(isLive); if(!live.length) return null;
  return live.reduce((a,s)=>a+s.friends.filter(f=>LIVE_ST.includes(f.status)).length,0); }
let friendsBusy=false;
async function loadFriends(force){
  if(friendsBusy) return; friendsBusy=true;
  try{ S.friends=await api().get_friends(!!force); }catch(e){ S.friends=S.friends||{sources:{}}; }
  friendsBusy=false;
  renderSide();
  if(S.view.k==='friends'&&!(document.activeElement&&['steamKey','q'].includes(document.activeElement.id))){ renderTop(); $('#content').innerHTML=friendsHTML(); }
}
function agoLower(ts){ const a=fmtAgo(ts); return /^[A-Z][a-z]{2} \d/.test(a)?'on '+a:a.charAt(0).toLowerCase()+a.slice(1); }
function friendLine(f){
  const extra=f.detail?` · ${esc(f.detail)}`:'';
  if(f.status==='ingame') return `Playing <b>${esc(f.game||'a game')}</b>${extra}`;
  if(f.status==='offline') return f.last_online?`Last online ${agoLower(f.last_online)}`:'Offline';
  if(f.status==='unknown') return 'Saved by Steam on this PC';
  return `${FST[f.status]}${f.game?` in ${esc(f.game)}`:''}${extra}`;
}
function avatarHTML(f){
  if(f.avatar) return `<img src="${esc(f.avatar)}" alt="" loading="lazy">`;
  const h=hash(f.name||'?')%360; return `<span class="fini" style="background:hsl(${h} 45% 30%)">${esc(initials(f.name||'?'))}</span>`;
}
function friendRow(f, showLauncher){
  return `<div class="frow" data-friend="${esc(f.id)}">
    <div class="fav ${f.status}">${avatarHTML(f)}<i></i></div>
    <div class="finfo"><div class="fname">${esc(f.name)}${f.tag?`<span class="ftag">#${esc(f.tag)}</span>`:''}${f.nick&&f.nick!==f.name?`<span class="fnick">${esc(f.nick)}</span>`:''}</div>
      <div class="fline">${friendLine(f)}</div></div>
    <div class="fright">${f.group?`<span class="chipx">${esc(f.group)}</span>`:''}${showLauncher?`<span class="lchip"><span class="dot" style="background:${lc(f.launcher)}"></span>${esc(f.launcher)}</span>`:''}
      ${f.join?`<button class="btn fjoin" data-fact="join" data-fid="${esc(f.id)}">Join</button>`:''}
      <button class="more" data-fmenu="${esc(f.id)}" title="More options" aria-label="More options for ${esc(f.name)}">${ic('dots')}</button></div></div>`;
}
function friendNote(k,s){
  const keyBox=`<div class="fkey"><input class="inp" id="steamKey" type="password" placeholder="Paste your Steam Web API key" autocomplete="off">
      <button class="btn" data-url="https://steamcommunity.com/dev/apikey">Get a key</button></div>
    <small>Steam asks for a domain name when you create a key. Any name works, for example <i>localhost</i>. The key stays on this PC.</small>`;
  if(k==='steam'){
    if(!s.signed_in) return `<div class="fnote"><b>Sign in to Steam</b><span>Sign in to Steam on this PC to see your Steam friends here.</span></div>`;
    if(!s.has_key) return `<div class="fnote"><b>See who's online on Steam</b><span>Steam shares who's online and what they're playing with apps that have a free Steam Web API key. Until you add one, Game Hub shows the friends Steam has saved on this PC.</span>${keyBox}</div>`;
    if(s.error==='private') return `<div class="fnote warn"><b>Steam didn't share your friends list</b><span>In Steam, open your profile, choose Edit Profile, then Privacy Settings, and set Friends List to Public. Then refresh.</span></div>`;
    if(s.error==='badkey') return `<div class="fnote warn"><b>Steam didn't accept your key</b><span>Check the key and paste it again.</span>${keyBox}</div>`;
    if(s.error==='network') return `<div class="fnote warn"><b>Couldn't reach Steam</b><span>Showing the friends saved on this PC for now. Game Hub will try again in a minute.</span></div>`;
  }
  if(k==='riot'&&!s.running) return `<div class="fnote"><b>Open the Riot Client</b><span>Riot friends appear while the Riot Client is running, including who's in Valorant or League.</span>
      ${s.client?`<div class="fkey"><button class="btn" data-act="riotclient">Open Riot Client</button></div>`:''}</div>`;
  return '';
}
function friendsHTML(){
  const F=S.friends;
  if(!F) return `<div class="empty"><b>Loading friends…</b></div>`;
  const other=`<p class="fother">Epic, Battle.net, EA, Ubisoft, GOG and Xbox don't share friends lists with other apps on your PC. Getting them would mean signing in to each service through Game Hub with your password, so Game Hub leaves them out.</p>`;
  const srcs=Object.entries(F.sources);
  if(!srcs.length) return `<div class="empty"><b>No friends to show yet</b>Friends work with Steam and the Riot Client. Install or sign in to one of them.</div>${other}`;
  const names={steam:'Steam',riot:'Riot'};
  if(S.ftab!=='all'&&!F.sources[S.ftab]) S.ftab='all';
  const cnt=s=>s.friends.filter(f=>LIVE_ST.includes(f.status)).length;
  let h=`<div class="fbar"><div class="ftabs">${[['all','All']].concat(srcs.map(([k])=>[k,names[k]])).map(([k,l])=>
      `<button class="ftab ${S.ftab===k?'on':''}" data-ftab="${k}">${l}${k==='all'||!isLive(F.sources[k])?'':`<em>${cnt(F.sources[k])}</em>`}</button>`).join('')}</div>
    <button class="btn icon ${friendsBusy?'spin':''}" data-act="frefresh" title="Refresh friends">${ic('refresh')}</button></div>`;
  const shown=S.ftab==='all'?srcs:srcs.filter(([k])=>k===S.ftab);
  h+=shown.map(([k,s])=>friendNote(k,s)).join('');
  let list=[].concat(...shown.map(([,s])=>s.friends));
  const q=S.q.trim().toLowerCase();
  if(q) list=list.filter(f=>[f.name,f.tag,f.nick,f.game].some(x=>(x||'').toLowerCase().includes(q)));
  const by=(a,b)=>(a.name||'').localeCompare(b.name||'');
  const sections=[['ingame','Playing'],['online','Online'],['away','Away or busy'],['offline','Offline'],['unknown','Saved on this PC']];
  const multi=S.ftab==='all'&&shown.length>1;
  let any=false;
  for(const [st,label] of sections){
    let rows=list.filter(f=>st==='away'?(f.status==='away'||f.status==='busy'):f.status===st);
    if(!rows.length) continue; any=true;
    rows.sort(st==='offline'?(a,b)=>(b.last_online||0)-(a.last_online||0)||by(a,b):st==='ingame'?(a,b)=>(a.game||'').localeCompare(b.game||'')||by(a,b):by);
    const collapsed=st==='offline'&&!S.showOffline&&!q;
    h+=`<div class="fsec"><div class="fsec-h">${label}<em>${rows.length}</em>${st==='offline'?`<button class="linkbtn" data-act="toggleoff">${collapsed?'Show':'Hide'}</button>`:''}</div>
      ${collapsed?'':`<div class="flist">${rows.map(f=>friendRow(f,multi)).join('')}</div>`}</div>`;
  }
  if(!any) h+=`<div class="empty"><b>${q?'No friends match your search':'No friends here yet'}</b></div>`;
  if(S.ftab==='all') h+=other;
  return h;
}
function friendById(id){ if(!S.friends) return null; for(const s of Object.values(S.friends.sources)) for(const f of s.friends) if(f.id===id) return f; return null; }
async function friendDo(id, action){
  const r=await api().friend_action(id, action);
  if(!r.ok) return toast(r.error||'That didn’t work');
  if(action==='copy') toast(`Copied ${r.text}`);
  else if(action==='join') toast('Asking Steam to join…');
}
function friendMenu(f, x, y, anchor){
  const items=[];
  if(f.launcher==='Steam'){
    items.push({label:'Send message', icon:'chat', run:()=>friendDo(f.id,'message')});
    if(f.join) items.push({label:`Join ${f.game||'game'}`, icon:'play', run:()=>friendDo(f.id,'join')});
    items.push({label:'View Steam profile', icon:'user', run:()=>friendDo(f.id,'profile')});
  } else {
    items.push({label:'Open Riot Client', icon:'chat', run:()=>friendDo(f.id,'client')});
  }
  if(f.lib){ const g=gameById(f.lib); if(g) items.push({label:`Open ${g.name} in Game Hub`, icon:'pad', run:()=>{ S.open=g.id; renderDrawer(); observeCovers(); fillAbout(g.id); }}); }
  items.push('-');
  items.push({label:f.tag?'Copy Riot ID':'Copy name', icon:'copy', run:()=>friendDo(f.id,'copy')});
  openMenu(items, x, y, anchor, anchor?'fmenu:'+f.id:null);
}
setInterval(()=>{  // fresh while you're looking; occasional otherwise so the sidebar count stays close
  if(!FRIENDS_ON||!S.data||S.sleeping||document.hidden) return;
  const age=Date.now()-(S.friendsAt||0);
  if((S.view.k==='friends'&&age>60000)||age>300000){ S.friendsAt=Date.now(); loadFriends(true); }
}, 15000);

// ---------- updating Game Hub itself
async function appUpdateDialog(){
  const u=S.data.app_update; if(!u) return toast(`You're up to date (version ${S.data.app_version})`);
  const ok=await confirmBox(`Update to Game Hub ${u.version}?`,
    `${u.notes?`What's new: ${u.notes}\n\n`:''}${u.source==='Downloads'?'Found in your Downloads folder. ':''}Game Hub will save a backup of your current version (${S.data.app_version}), then restart.`,
    'Update and restart');
  if(ok) runAppUpdate();
}
async function runAppUpdate(path){
  const r=await api().apply_app_update(path||null);
  if(!r.ok) return toast(r.error);
  toast(`Updating to ${r.version}. Game Hub will reopen in a moment…`);
}

// ---------- modals
function modal(html){ $('#modal').innerHTML=html; $('#modalWrap').classList.add('on'); }
function closeModal(){ $('#modalWrap').classList.remove('on'); }
function ask(title, text, value){ return new Promise(res=>{
  modal(`<h3>${esc(title)}</h3><p>${esc(text)}</p><input class="inp" id="askIn" value="${esc(value||'')}">
    <div class="acts"><button class="btn" id="askNo">Cancel</button><button class="btn primary" id="askOk">Save</button></div>`);
  const inp=$('#askIn'); setTimeout(()=>{inp.focus();inp.select();},50);
  const fin=v=>{closeModal();res(v);};
  $('#askOk').onclick=()=>fin(inp.value); $('#askNo').onclick=()=>fin(null);
  inp.onkeydown=e=>{ if(e.key==='Enter') fin(inp.value); if(e.key==='Escape') fin(null); };
}); }
function settings(){
  const s=S.data.settings, tray=S.data.tray;
  const row=(k,t,d,on,dis)=>`<div class="set"><div><b>${t}</b><small>${d}</small></div><button class="tog ${on?'on':''}" data-set="${k}" ${dis?'disabled':''}></button></div>`;
  modal(`<h3>Settings</h3><p>Play time for non-Steam games is only counted while Game Hub is running.</p>
    ${row('tracking','Track play time','Watch which installed games are running and log sessions.',s.tracking)}
    ${row('close_to_tray','Keep running in the tray',tray?'Closing the window keeps Game Hub tracking in the system tray.':'Install pystray + pillow to enable (pip install pystray pillow).',s.close_to_tray&&tray,!tray)}
    ${row('startup','Start with Windows','Launch quietly in the tray when you sign in, so no session is missed.',s.startup,!S.data.windows)}
    ${row('hover_play','Play button on hover','Shows a play button over a game’s cover when you point at it. Off, games start only from Play or Continue.',s.hover_play)}
    ${row('show_hidden','Show hidden games','Adds a Hidden section to the sidebar with the games you’ve hidden.',s.show_hidden)}
    ${FRIENDS_ON?`<div class="sethead">Friends</div>
    <label class="lbl" for="steamKeySet" style="margin-top:8px">Steam Web API key</label>
    <div class="fkey" style="margin:0"><input class="inp" id="steamKeySet" type="password" autocomplete="off" placeholder="${s.steam_key_hint?`Saved (${esc(s.steam_key_hint)}). Paste a new key to replace it.`:'Paste your key to see who’s online on Steam'}">
      <button class="btn" data-url="https://steamcommunity.com/dev/apikey">Get a key</button></div>
    ${s.steam_key_hint?`<button class="linkbtn" data-act="clearkey" style="margin-top:8px">Remove key</button>`:''}`:''}
    <div class="sethead">Games without a launcher</div>
    ${row('find_standalone','Find games without a launcher','Looks for portable and self-installed games in Games folders, Program Files and the folders below.',s.find_standalone!==false)}
    <div class="folders">${(s.game_folders||[]).map(f=>`<div class="folder"><span title="${esc(f)}">${esc(f)}</span><button class="linkbtn" data-rmfolder="${esc(f)}">Remove</button></div>`).join('')||'<div class="folder none">No extra folders yet</div>'}</div>
    <div class="updacts"><button class="btn" data-act="addfolder">${ic('plus')}Add a folder to search</button></div>
    <div class="sethead">Updates <span>Version ${esc(S.data.app_version)}</span></div>
    ${row('check_updates','Check for updates','Game Hub checks for new versions on its own and lets you know when one is ready.',s.check_updates)}
    <div class="updacts"><button class="btn" data-act="checkupd">${ic('refresh')}Check now</button><button class="btn" data-act="updfile">${ic('folder')}Install from a file…</button></div>
    <div class="sethead">This PC</div>
    ${(()=>{ const ins=S.data.install||{};
      if(ins.running_installed) return `<div class="set"><div><b>Installed</b><small>In your Start menu and in Windows Settings → Apps. It updates itself.</small></div></div>`;
      if(ins.installed_version) return `<div class="set"><div><b>Running a separate copy</b><small>Game Hub ${esc(ins.installed_version)} is also installed on this PC. Install this version to replace it.</small></div><button class="btn" data-act="installpc">${ic('download')}Install this version</button></div>`;
      return `<div class="set"><div><b>Not installed</b><small>Install Game Hub to get Start menu and desktop shortcuts, and an entry in Windows Settings → Apps.</small></div><button class="btn" data-act="installpc">${ic('download')}Install Game Hub…</button></div>`; })()}
    <div class="acts" style="justify-content:space-between">${(S.data.install||{}).running_installed?`<button class="btn danger" data-act="uninstall">${ic('trash')}Uninstall Game Hub…</button>`:'<span></span>'}
    <button class="btn primary" data-act="closemodal">Done</button></div>`);
}

// ---------- events
document.addEventListener('click', async e=>{
  const prevOwner=menuOwner;
  if(!e.target.closest('#menu')) closeMenu();
  const t=e.target.closest('[data-rmfolder],[data-ftab],[data-fmenu],[data-fact],[data-friend],[data-mi],[data-menu],[data-install],[data-launcher],[data-shot],[data-more],[data-url],[data-hero],[data-star],[data-scroll],[data-play],[data-act],[data-nav],[data-mode],[data-sort],[data-open],[data-coll],[data-set]');
  if(!t) return;
  const ds=t.dataset;
  if(ds.shot!==undefined){ const d=DET[S.open]; if(d&&d.shots) openLightbox(d.shots.map(x=>x.full||x.thumb), Number(ds.shot)); return; }
  if(ds.more){ const p=$('#dDesc'); if(p){ const open=p.classList.toggle('open'); t.textContent=open?'Show less':'Show more'; } return; }
  if(ds.url){ return api().open_url(ds.url); }
  if(ds.launcher){ const r=await api().open_launcher(ds.launcher); if(r&&r.error) toast('Couldn’t open the launcher: '+r.error); return; }
  if(ds.hero!==undefined){ heroIdx=Number(ds.hero); return renderHero(); }
  if(ds.star){ e.stopPropagation(); return toggleStar(ds.star, t); }
  if(ds.scroll){ const sl=t.closest('.shead').nextElementSibling; sl.scrollBy({left:Number(ds.scroll)*sl.clientWidth*0.85,behavior:'smooth'}); return; }
  if(ds.mi!==undefined){ const it=MENU[Number(ds.mi)]; closeMenu(); if(it&&it.run) it.run(); return; }
  if(ds.menu){ e.stopPropagation(); if(prevOwner==='menu:'+ds.menu) return; const g=gameById(ds.menu); if(g) gameMenu(g,0,0,t.getBoundingClientRect()); return; }
  if(ds.play){ e.stopPropagation(); return play(ds.play); }
  if(ds.install){ e.stopPropagation(); const g=gameById(ds.install); const r=await api().install(ds.install);
    return toast(r.ok?`Opening ${g?g.launcher:'the launcher'} to install ${g?g.name:'the game'}`:'Couldn’t start the install: '+r.error); }
  if(ds.nav){ const [k,v]=ds.nav.split('|'); S.view={k,v}; S.open=null; $('#content').scrollTop=0; return render(); }
  if(ds.mode){ if(S.mode===ds.mode) return; S.mode=ds.mode; store('mode',S.mode); return render(); }
  if(ds.sort){ if(S.view.k==='recent'){ S.view={k:'games'}; } return setSort(ds.sort); }
  if(ds.set!==undefined && ds.set){ const on=!t.classList.contains('on'); const r=await api().set_setting(ds.set,on);
    if(r.error) toast(r.error); else { if(ds.set==='show_hidden'&&!on&&S.view.k==='hidden') S.view={k:'all'}; await load(r); settings(); } return; }
  if(ds.coll!==undefined){ return load(await api().set_collection(S.open, ds.coll)); }
  if(ds.open){ S.open=ds.open; renderDrawer(); observeCovers(); fillAbout(ds.open); return; }
  const id=S.open;
  if(ds.rmfolder){ const st=await api().remove_game_folder(ds.rmfolder); await load(st); settings(); return toast('Folder removed'); }
  if(ds.act==='addfolder'){ toast('Choose a folder that holds games'); const st=await api().add_game_folder(); await load(st); settings();
    const n=(S.data.games||[]).filter(g=>g.launcher==='Standalone').length; return toast(`Searching… ${n} game${n===1?'':'s'} without a launcher so far`); }
  if(ds.ftab){ S.ftab=ds.ftab; store('ftab',ds.ftab); return renderContent(); }
  if(ds.fmenu){ e.stopPropagation(); if(prevOwner==='fmenu:'+ds.fmenu) return; const f=friendById(ds.fmenu); if(f) friendMenu(f,0,0,t.getBoundingClientRect()); return; }
  if(ds.fact){ return friendDo(ds.fid, ds.fact); }
  if(ds.friend){ const f=friendById(ds.friend); const r=t.getBoundingClientRect(); if(f) friendMenu(f, Math.min(e.clientX+4, r.right-10), e.clientY+4); return; }
  if(ds.act==='clearkey'){ const r=await api().set_setting('steam_api_key',''); await load(r); settings(); S.friends=null; return toast('Steam key removed'); }
  if(ds.act==='frefresh'){ S.friendsAt=Date.now(); renderContent(); return loadFriends(true); }
  if(ds.act==='toggleoff'){ S.showOffline=!S.showOffline; return renderContent(); }
  if(ds.act==='riotclient'){ const r=await api().open_riot_client(); return toast(r.ok?'Opening the Riot Client. Friends will appear once it’s signed in.':r.error); }
  if(ds.act==='appupdate') return appUpdateDialog();
  if(ds.act==='appupdlater'){ S.updLater=(S.data.app_update||{}).version; return renderSide(); }
  if(ds.act==='checkupd'){ toast('Checking for updates…'); const r=await api().check_app_update(); await load(r.state);
    if(r.found){ closeModal(); return appUpdateDialog(); }
    const why=r.error==='network'?'Couldn’t check for updates. Check your internet connection and try again.'
      :r.error?'Couldn’t check for updates right now. Please try again later.':'';
    return toast(why?why:`You're up to date (version ${S.data.app_version})`, why?7000:2600); }
  if(ds.act==='updfile'){ const f=await api().pick_update_file(); if(!f) return; if(f.error) return toast(f.error);
    closeModal();
    const ok=await confirmBox(f.newer?`Update to Game Hub ${f.version}?`:`Install Game Hub ${f.version}?`,
      (f.newer?'':`This is not newer than the version you have (${S.data.app_version}). `)+'Game Hub will save a backup of your current version, then restart.'+(f.notes?`\n\nWhat's new: ${f.notes}`:''),
      f.newer?'Update and restart':'Install anyway');
    if(ok) return runAppUpdate(f.path); return; }
  if(ds.act==='sortmenu'){ if(prevOwner==='sort') return; return sortMenu(t); }
  if(ds.act==='sortdir'){ S.rev=!S.rev; store('rev',S.rev?'1':'0'); render(); return toast(DIRS[curSort()][S.rev?1:0]); }
  switch(ds.act){
    case 'close': S.open=null; return renderDrawer();
    case 'closemodal': return closeModal();
    case 'settings': return settings();
    case 'rescan': {
      if(S.rescanning) return toast('Already rescanning…');
      S.rescanning=true; renderTop(); toast('Rescanning all launchers and folders…');
      try{
        const st=await api().rescan(); await load(st); const r=st.rescan||{};
        const parts=[`${r.total} game${r.total===1?'':'s'} installed`];
        if(r.added) parts.push(`${r.added} new${r.names&&r.names.length?' ('+r.names.join(', ')+(r.added>r.names.length?', …':'')+')':''}`);
        if(r.removed) parts.push(`${r.removed} no longer installed`);
        toast(`Rescan finished: ${parts.join(' · ')}`, 6000);
      }catch(e){ toast('Rescan didn’t finish. Please try again.'); }
      finally{ S.rescanning=false; renderTop(); }
      return; }
    case 'add': { const p=await api().pick_exe(); if(!p) return; const name=await ask('Add a game','What should this game be called?',p.name);
      if(name===null) return; await load(await api().add_custom(p.path,name)); return toast('Added '+name); }
    case 'fav': return load(await api().toggle_favorite(id));
    case 'hide': return hideGame(id);
    case 'folder': return api().open_folder(id);
    case 'cover': { if(await api().pick_cover(id)){ delete COV[id]; delete PENDING[id]; document.querySelectorAll('[data-cover] img').forEach(i=>{ if(i.parentElement.dataset.cover===id) i.remove(); }); await load(); } return; }
    case 'remove': S.open=null; return load(await api().remove_custom(id));
    case 'forget': { const g=gameById(id); S.open=null; toast(g&&g.installed!==false?`${g.name} won't be listed again`:`Removed ${g?g.name:'game'} from the Uninstalled list`); return load(await api().forget_game(id)); }
    case 'uninstall': closeModal(); return api().uninstall();
    case 'installpc': closeModal(); toast('Opening the installer…'); return api().install_on_pc();
  }
});
document.addEventListener('input', e=>{ if(e.target.id==='q'){ S.q=e.target.value; renderContent(); renderTop(); observeCovers(); } });

document.addEventListener('keydown', async e=>{
  if(e.target.id==='coll'&&e.key==='Enter'){ e.target.blur(); return load(await api().set_collection(S.open, e.target.value)); }
  if($('#lightbox').classList.contains('on')){ if(e.key==='Escape') return closeLightbox(); if(e.key==='ArrowRight') return stepLightbox(1); if(e.key==='ArrowLeft') return stepLightbox(-1); }
  if(e.key==='Escape'&&$('#menu').classList.contains('on')) return closeMenu();
  if(e.key==='Escape'){ if($('#modalWrap').classList.contains('on')) return closeModal(); if(S.open){ S.open=null; renderDrawer(); } return; }
  if((e.key==='/'||(e.ctrlKey&&e.key.toLowerCase()==='f'))&&!['INPUT','TEXTAREA'].includes(document.activeElement.tagName)){ e.preventDefault(); $('#q').focus(); }
});
$('#modalWrap').addEventListener('click', e=>{ if(e.target.id==='modalWrap') closeModal(); });
$('#lightbox').addEventListener('click', e=>{ const n=e.target.closest('[data-lb]'); if(n) return stepLightbox(Number(n.dataset.lb)); closeLightbox(); });

// ---------- live updates
setInterval(async()=>{
  if(!S.data||S.sleeping||document.hidden) return;
  try{ const l=await api().get_live();
    if(l.version!==S.version || (l.playing.length && Date.now()-S.lastFull>60000)) await load(); }catch(e){}
}, 4000);

document.addEventListener('contextmenu', e=>{
  const fr=e.target.closest('[data-friend]');
  if(fr){ const f=friendById(fr.dataset.friend); if(f){ e.preventDefault(); friendMenu(f, e.clientX, e.clientY); } return; }
  const el=e.target.closest('[data-open]'); if(!el||e.target.closest('input,textarea')) return;
  const g=gameById(el.dataset.open); if(!g) return;
  e.preventDefault(); gameMenu(g, e.clientX, e.clientY);
});
window.addEventListener('resize', closeMenu);
document.addEventListener('change', async e=>{
  if(e.target.id==='steamKey'||e.target.id==='steamKeySet'){
    const v=e.target.value.trim(); if(!v&&e.target.id==='steamKey') return;
    const r=await api().set_setting('steam_api_key', v); if(r.error) return toast(r.error);
    await load(r); if(e.target.id==='steamKeySet') settings();
    toast(v?'Steam key saved. Loading your friends…':'Steam key removed'); S.friendsAt=Date.now(); return loadFriends(true); }
});
document.addEventListener('scroll', closeMenu, true);
$('#content').addEventListener('scroll',e=>$('#top').classList.toggle('scrolled',e.target.scrollTop>12),{passive:true});
// In the tray (or minimised for a while): drop pictures and pause; rebuild when shown again.
let hiddenTimer=null;
window.sleepMode=function(on){
  if(on===!!S.sleeping) return;
  S.sleeping=on;
  if(on){
    closeMenu(); $('#content').innerHTML=''; $('#drawer').innerHTML=''; S.open=null;
    for(const u of BLOBS) URL.revokeObjectURL(u); BLOBS.clear();
    for(const k in COV) delete COV[k]; for(const k in PENDING) delete PENDING[k]; for(const k in HERO) delete HERO[k];
    heroShown=null;
  } else if(S.data){ load(); }
};
document.addEventListener('visibilitychange',()=>{
  clearTimeout(hiddenTimer);
  if(document.hidden) hiddenTimer=setTimeout(()=>sleepMode(true), 90000);
  else if(S.sleeping) sleepMode(false);
});
let started=false;
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
let quipT=null;
function startQuips(){ const q=$('#spQuip'); if(!q) return; let i=Math.floor(Math.random()*QUIPS.length); q.textContent=QUIPS[i];
  quipT=setInterval(()=>{ if(!$('#spQuip')) return clearInterval(quipT); q.classList.add('out');
    setTimeout(()=>{ i=(i+1)%QUIPS.length; q.textContent=QUIPS[i]; q.classList.remove('out'); },350); },2200); }
function setSplash(pct, text){ if(!$('#spFill')) return; $('#spFill').style.width=Math.max(3,Math.min(100,pct))+'%'; if(text!==undefined) $('#spText').textContent=text; }
async function init(){
  if(started) return; started=true;
  startQuips();
  let skipped=false;
  $('#spSkip').onclick=()=>{ skipped=true; };
  const skipTimer=setTimeout(()=>{ const b=$('#spSkip'); if(b) b.classList.add('on'); }, 8000);
  // 1) wait for the scan, cover art downloads and size measuring
  while(!skipped){
    let p; try{ p=await api().get_progress(); }catch(e){ await sleep(300); continue; }
    if(p.scanning||(!p.ready&&!p.games)) setSplash(6,'Looking for your installed games…');
    else {
      const tot=p.art_total+p.size_total+p.det_total, done=p.art_done+p.size_done+p.det_done;
      const txt = p.art_done<p.art_total ? `Finding cover art · ${p.art_done+1} of ${p.art_total}${p.art_name?' · '+p.art_name:''}`
        : p.det_done<p.det_total ? `Getting game details · ${p.det_done+1} of ${p.det_total}`
        : p.size_done<p.size_total ? `Measuring game sizes · ${p.size_done+1} of ${p.size_total}` : 'Getting everything ready…';
      setSplash(12+(tot?58*done/tot:58), txt);
    }
    if(p.ready) break;
    await sleep(300);
  }
  // 2) pull the library and pre-load every picture
  await load();
  if(!skipped){
    setSplash(70,'Loading pictures…');
    await preloadCovers((d,t)=>setSplash(70+30*d/t,`Loading pictures · ${d} of ${t}`), ()=>skipped);
    render();
  }
  setSplash(100,'Ready');
  await sleep(skipped?0:250);
  clearTimeout(skipTimer);
  clearInterval(quipT); $('#splash').classList.add('hide');
  setTimeout(()=>{ const sp=$('#splash'); if(sp) sp.remove(); }, 700);  // gone for good, nothing left animating
}
window.addEventListener('pywebviewready', init);
if(window.pywebview&&window.pywebview.api) init();
</script></body></html>
"""


PACKAGES = ["pywebview", "pystray", "pillow"]


def _console_python():
    """The python.exe that belongs to whatever interpreter is running us (pip needs the console one)."""
    base = os.path.join(sys.base_prefix, "python.exe")
    if in_runtime() and os.path.isfile(base):
        return base                 # install packages into the real Python, not Game Hub's process copy
    exe = sys.executable
    if exe.lower().endswith("pythonw.exe"):
        alt = exe[:-len("pythonw.exe")] + "python.exe"
        if os.path.isfile(alt):
            return alt
    return exe


def _pip(args):
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    r = subprocess.run([_console_python(), "-m", "pip", "install", "--disable-pip-version-check"] + args,
                       capture_output=True, text=True, creationflags=flags)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def install_packages():
    """Install the helper packages into THIS Python, with a small progress window. Returns (ok, log)."""
    import tkinter as tk
    from tkinter import ttk
    root = tk.Tk()
    root.title(APP_NAME)
    root.geometry("380x120")
    root.resizable(False, False)
    root.configure(bg="#0e1117")
    tk.Label(root, text="Installing Game Hub's helper packages…\nThis takes about a minute.",
             bg="#0e1117", fg="#eceef4", font=("Segoe UI", 10)).pack(pady=(18, 10))
    bar = ttk.Progressbar(root, mode="indeterminate", length=300)
    bar.pack()
    bar.start(12)
    result = {}

    def work():
        code, log = _pip(PACKAGES)
        if code != 0 and "No module named pip" in log:  # pip itself missing
            subprocess.run([_console_python(), "-m", "ensurepip", "--upgrade"],
                           capture_output=True, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            code, log = _pip(PACKAGES)
        if code != 0 and ("Permission" in log or "Access is denied" in log):
            code, log = _pip(["--user"] + PACKAGES)
        result["code"], result["log"] = code, log

    t = threading.Thread(target=work, daemon=True)
    t.start()
    while t.is_alive():
        root.update()
        time.sleep(0.03)
    root.destroy()
    return result.get("code") == 0, result.get("log", "")


def show_install_error(log):
    import tkinter as tk
    ver = "{}.{}".format(*sys.version_info[:2])
    hint = (f"Game Hub is running on Python {ver} at:\n{sys.executable}\n\n"
            "The most common fix: install Python 3.12 from python.org (tick \"Add python.exe to PATH\"), "
            "then double-click Start Game Hub.bat again. Very new Python versions sometimes aren't "
            "supported by pywebview yet.\n\nDetails from the installer:")
    root = tk.Tk()
    root.title(APP_NAME + " - setup problem")
    root.geometry("640x460")
    tk.Label(root, text=hint, justify="left", wraplength=600, font=("Segoe UI", 10)).pack(padx=16, pady=(14, 8), anchor="w")
    box = tk.Text(root, wrap="word", font=("Consolas", 9), height=14)
    box.insert("1.0", log[-6000:] or "(no output)")
    box.pack(fill="both", expand=True, padx=16)
    tk.Button(root, text="Close", width=12, command=root.destroy).pack(pady=12)
    root.mainloop()


def ensure_packages():
    global webview, pystray, Image, ImageDraw
    if webview is not None:
        return True
    import importlib
    from tkinter import messagebox
    import tkinter as tk
    r = tk.Tk()
    r.withdraw()
    go = messagebox.askyesno(APP_NAME, "Game Hub needs a few free helper packages "
                                       "(pywebview, pystray, pillow).\n\nInstall them now?")
    r.destroy()
    if not go:
        return False
    ok, log = install_packages()
    importlib.invalidate_caches()
    try:
        import webview as _wv
        webview = _wv
    except Exception as e:
        show_install_error(log + f"\n\nImport error after install: {e}")
        return False
    try:
        import pystray as _ps
        from PIL import Image as _im, ImageDraw as _dr
        pystray, Image, ImageDraw = _ps, _im, _dr
    except Exception:
        pystray = None  # tray is optional
    return True


def prune_backups(keep=2):
    """Keep only the newest few backups of earlier versions."""
    folder = os.path.join(DATA_DIR, "backup")
    try:
        files = sorted((os.path.join(folder, f) for f in os.listdir(folder) if f.endswith(".py")),
                       key=os.path.getmtime, reverse=True)
    except OSError:
        return
    for f in files[keep:]:
        try:
            os.remove(f)
        except OSError:
            pass


def tidy_caches():
    """Remove leftovers so Game Hub's folder doesn't grow over time."""
    prune_backups()
    small = os.path.join(ART_DIR, "small")
    try:
        for f in os.listdir(small):
            if f.count(".") < 2:          # resized pictures saved by older versions (unnamed, never cleaned)
                os.remove(os.path.join(small, f))
    except OSError:
        pass
    for f in glob.glob(os.path.join(ART_DIR, "*.building")) + glob.glob(os.path.join(RUNTIME_ROOT, "*.building")):
        shutil.rmtree(f, ignore_errors=True)


def clear_scan_caches():
    """Forget every remembered folder/launcher result so the next scan reads everything fresh."""
    global _steam_root, _epic_cat
    _mt_cache.clear()
    _steam_root = None
    _epic_cat = None
    _epic_items.clear()


# ======================================================================= Game Hub's own process
# Windows shows a program by its file's name and icon. Game Hub runs on Python, so it showed as "Python".
# Game Hub makes its own copy of Python's pythonw.exe named "Game Hub.exe", gives it Game Hub's name and icon,
# and runs through it. It still uses your installed Python and packages (pyvenv.cfg points back to them).
RUNTIME_ROOT = os.path.join(os.environ.get("LOCALAPPDATA", DATA_DIR), "GameHub", "runtime")
RUNTIME_REV = 1          # bump to rebuild everyone's copy


def in_runtime():
    """Already running as "Game Hub.exe" (our own copy, or the one in the downloadable install)."""
    return os.path.basename(os.path.normcase(sys.executable)) == "game hub.exe"


def _vs_node(key, value=b"", wtype=1, vlen=0, children=()):
    """One VS_VERSIONINFO block: header, key, padding, value, padding, children (each 32-bit aligned)."""
    out = bytearray(struct.pack("<HHH", 0, vlen, wtype) + (key + "\0").encode("utf-16-le"))
    out += b"\0" * (-len(out) % 4)
    out += value
    out += b"\0" * (-len(out) % 4)
    for c in children:
        out += c
        out += b"\0" * (-len(out) % 4)
    struct.pack_into("<H", out, 0, len(out))
    return bytes(out)


def version_resource(name="Game Hub", version="1.0.0.0"):
    nums = ([int(x) for x in re.findall(r"\d+", version)] + [0, 0, 0, 0])[:4]
    ms, ls = (nums[0] << 16) | nums[1], (nums[2] << 16) | nums[3]
    fixed = struct.pack("<13I", 0xFEEF04BD, 0x00010000, ms, ls, ms, ls, 0x3F, 0, 0x00040004, 1, 0, 0, 0)
    strings = [("CompanyName", name), ("FileDescription", name), ("FileVersion", version), ("InternalName", name),
               ("LegalCopyright", ""), ("OriginalFilename", name + ".exe"), ("ProductName", name),
               ("ProductVersion", version)]
    table = _vs_node("040904B0", children=[_vs_node(k, (v + "\0").encode("utf-16-le"), 1, len(v) + 1) for k, v in strings])
    return _vs_node("VS_VERSION_INFO", fixed, 0, len(fixed), [
        _vs_node("StringFileInfo", children=[table]),
        _vs_node("VarFileInfo", children=[_vs_node("Translation", struct.pack("<HH", 0x0409, 0x04B0), 0, 4)])])


def icon_resources(ico):
    """(group bytes, [(id, image bytes)]) for an .ico file, in the layout Windows programs store icons."""
    _, kind, count = struct.unpack_from("<HHH", ico, 0)
    if kind != 1 or not count:
        raise ValueError("not an icon file")
    entries, images = [], []
    for i in range(count):
        w, h, colors, res, planes, bits, size, offset = struct.unpack_from("<BBBBHHII", ico, 6 + 16 * i)
        images.append((i + 1, ico[offset:offset + size]))
        entries.append(struct.pack("<BBBBHHIH", w, h, colors, res, planes or 1, bits or 32, size, i + 1))
    return struct.pack("<HHH", 0, 1, count) + b"".join(entries), images


def strip_signature(path):
    """Drop the publisher signature (it no longer matches once the name and icon are changed)."""
    with open(path, "r+b") as f:
        data = bytearray(f.read())
        pe = struct.unpack_from("<I", data, 0x3C)[0]
        opt = pe + 24
        dirs = opt + (112 if struct.unpack_from("<H", data, opt)[0] == 0x20B else 96)
        off, size = struct.unpack_from("<II", data, dirs + 4 * 8)
        if off and size and off + size <= len(data):
            struct.pack_into("<II", data, dirs + 4 * 8, 0, 0)
            if off + size >= len(data) - 8:
                del data[off:]
            f.seek(0)
            f.write(data)
            f.truncate()


def set_exe_resources(path, version_blob, group, images):
    """Replace a program's icon and name using Windows' own resource-editing functions."""
    from ctypes import wintypes
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.LoadLibraryExW.restype = ctypes.c_void_p
    k32.BeginUpdateResourceW.restype = ctypes.c_void_p
    k32.FreeLibrary.argtypes = [ctypes.c_void_p]
    rid = lambda n: ctypes.c_void_p(n) if isinstance(n, int) else ctypes.c_wchar_p(n)
    NAMES = ctypes.WINFUNCTYPE(wintypes.BOOL, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p)
    LANGS = ctypes.WINFUNCTYPE(wintypes.BOOL, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, wintypes.WORD, ctypes.c_void_p)
    old = []
    h = k32.LoadLibraryExW(path, None, 0x2 | 0x20)   # as data / as image resource: nothing is run
    if h:
        try:
            for rtype in (3, 14, 16):                  # icons, icon groups, version info
                names = []
                cbn = NAMES(lambda hm, t, n, p: names.append(n if (n or 0) >> 16 == 0 else ctypes.wstring_at(n)) or True)
                k32.EnumResourceNamesW(ctypes.c_void_p(h), ctypes.c_void_p(rtype), cbn, None)
                for n in names:
                    langs = []
                    cbl = LANGS(lambda hm, t, nn, lang, p: langs.append(lang) or True)
                    k32.EnumResourceLanguagesW(ctypes.c_void_p(h), ctypes.c_void_p(rtype), rid(n), cbl, None)
                    old += [(rtype, n, l) for l in langs]
        finally:
            k32.FreeLibrary(h)
    hu = k32.BeginUpdateResourceW(path, False)
    if not hu:
        raise OSError(f"Windows couldn't open the file for editing ({ctypes.get_last_error()})")
    ok = True

    def put(rtype, name, lang, data):
        nonlocal ok
        buf = ctypes.create_string_buffer(data, len(data)) if data else None
        ok &= bool(k32.UpdateResourceW(ctypes.c_void_p(hu), ctypes.c_void_p(rtype), rid(name), wintypes.WORD(lang),
                                       buf, wintypes.DWORD(len(data) if data else 0)))
    for rtype, n, lang in old:
        put(rtype, n, lang, None)                      # remove Python's icon and name
    for i, img in images:
        put(3, i, 0x0409, img)
    if group:
        put(14, 1, 0x0409, group)
    put(16, 1, 0x0409, version_blob)
    if not k32.EndUpdateResourceW(ctypes.c_void_p(hu), not ok):
        raise OSError(f"Windows couldn't save the new icon and name ({ctypes.get_last_error()})")
    if not ok:
        raise OSError("Windows refused part of the icon and name change")


def _runtime_stamp():
    home = sys.base_prefix
    src = os.path.join(home, "pythonw.exe")
    dll = os.path.join(home, f"python{sys.version_info[0]}{sys.version_info[1]}.dll")
    if not (os.path.isfile(src) and os.path.isfile(dll)):
        return None
    return {"rev": RUNTIME_REV, "home": os.path.normcase(home), "exe": os.path.getmtime(src), "dll": os.path.getmtime(dll)}


def ensure_runtime():
    """Path to Game Hub's own process file, building it if needed. None if this PC can't use one."""
    if os.name != "nt":
        return None
    stamp = _runtime_stamp()
    if not stamp:
        return None                     # e.g. Python from the Microsoft Store: can't be copied
    tag = hashlib.sha1(json.dumps(stamp, sort_keys=True).encode()).hexdigest()[:10]
    folder = os.path.join(RUNTIME_ROOT, tag)
    exe = os.path.join(folder, "Game Hub.exe")
    marker = os.path.join(folder, "runtime.json")
    try:
        info = json.load(open(marker))
        if os.path.isfile(exe):
            return None if info.get("broken") else exe
    except (OSError, ValueError):
        pass
    home = sys.base_prefix
    tmp = folder + ".building"
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)
    dll = f"python{sys.version_info[0]}{sys.version_info[1]}.dll"
    for name in ("python3.dll", dll, "vcruntime140.dll", "vcruntime140_1.dll"):
        if os.path.isfile(os.path.join(home, name)):
            shutil.copy2(os.path.join(home, name), tmp)
    new = os.path.join(tmp, "Game Hub.exe")
    shutil.copy2(os.path.join(home, "pythonw.exe"), new)
    strip_signature(new)
    ico = make_icon(os.path.join(tmp, "game_hub.ico"))
    group, images = icon_resources(open(ico, "rb").read()) if ico else (None, [])
    set_exe_resources(new, version_resource(), group, images)
    with open(os.path.join(tmp, "pyvenv.cfg"), "w") as f:
        f.write(f"home = {home}\ninclude-system-site-packages = true\nversion = {platform.python_version()}\n")
    with open(os.path.join(tmp, "runtime.json"), "w") as f:
        json.dump({"stamp": stamp}, f)
    os.replace(tmp, folder)
    for old in os.listdir(RUNTIME_ROOT):   # older copies (a previous Python); skipped if still in use
        if old != tag and not old.endswith(".building"):
            shutil.rmtree(os.path.join(RUNTIME_ROOT, old), ignore_errors=True)
    return exe


def handoff_to_runtime():
    """Start Game Hub inside its own process copy. True if that took over (this process should exit)."""
    if os.name != "nt" or in_runtime() or os.environ.get("GAMEHUB_PLAIN_PYTHON"):
        return False
    try:
        exe = ensure_runtime()
    except Exception as e:
        log_problem("preparing Game Hub's own process", e)
        return False
    if not exe:
        return False
    try:
        child = subprocess.Popen([exe, os.path.abspath(__file__)] + sys.argv[1:],
                                 cwd=os.path.dirname(os.path.abspath(__file__)))
        code = child.wait(timeout=3)        # a broken copy fails straight away
    except subprocess.TimeoutExpired:
        return True                         # it's running: hand over
    except Exception as e:
        log_problem("starting Game Hub's own process", e)
        return False
    if code == 0:
        return True
    log_problem(f"Game Hub's own process exited with code {code}; using plain Python from now on")
    try:
        marker = os.path.join(os.path.dirname(exe), "runtime.json")
        info = json.load(open(marker))
        info["broken"] = True
        json.dump(info, open(marker, "w"))
    except Exception:
        pass
    return False


def set_app_id():
    """Group Game Hub's taskbar button as its own app (with its own icon), not as Python."""
    if os.name == "nt":
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("GameHub.App")
        except Exception:
            pass


# ======================================================================= friends
STEAM64 = 76561197960265728
FRIEND_TTL = 45
STEAM_STATES = {0: "offline", 1: "online", 2: "busy", 3: "away", 4: "away", 5: "online", 6: "online"}
RIOT_GAMES = {"league_of_legends": "League of Legends", "valorant": "VALORANT", "bacon": "Legends of Runeterra"}
RIOT_DEFAULT_GROUPS = {"", "general", "**default", "offline", "online"}


def steam_login_user():
    """The Steam account most recently signed in on this PC: {id64, account, name}."""
    steam = find_steam_root()
    if not steam:
        return None
    p = os.path.join(steam, "config", "loginusers.vdf")
    try:
        with open(p, encoding="utf-8", errors="ignore") as f:
            users = ci_get(parse_vdf(f.read()), "users") or {}
    except OSError:
        return None
    best = None
    for sid, u in users.items():
        if not sid.isdigit() or not isinstance(u, dict):
            continue
        key = (str(ci_get(u, "MostRecent")) == "1", num(ci_get(u, "Timestamp")))
        if best is None or key > best[0]:
            best = (key, sid, u)
    if not best:
        return None
    return {"id64": best[1], "account": int(best[1]) - STEAM64, "name": ci_get(best[2], "PersonaName")}


def steam_saved_friends(account):
    """Friends Steam keeps on this PC (names, avatars, nicknames). No online status."""
    steam = find_steam_root()
    cfg = os.path.join(steam or "", "userdata", str(account), "config", "localconfig.vdf")
    if not steam or not os.path.isfile(cfg):
        return []

    def read():
        try:
            with open(cfg, encoding="utf-8", errors="ignore") as f:
                fr = ci_get(parse_vdf(f.read()), "UserLocalConfigStore", "friends") or {}
        except OSError:
            return []
        out = []
        for k, v in fr.items():
            if not k.isdigit() or not isinstance(v, dict) or int(k) == account:
                continue
            name = ci_get(v, "name")
            if not name:
                continue
            av = ci_get(v, "avatar") or ""
            out.append({"steamid": str(STEAM64 + int(k)), "name": name, "nick": ci_get(v, "tag") or "",
                        "avatar": f"https://avatars.steamstatic.com/{av}_medium.jpg" if av.strip("0") else None})
        return out
    return by_mtime("steamfriends:" + cfg, [cfg], read)


def steam_api(method, params):
    """(json, None) or (None, http status / 'network')."""
    try:
        with urlopen(Request(f"https://api.steampowered.com/{method}/?" + urlencode(params),
                             headers={"User-Agent": UA}), timeout=12) as r:
            return json.loads(r.read().decode("utf-8")), None
    except HTTPError as e:
        return None, e.code
    except Exception:
        return None, "network"


def steam_live_friends(key, id64, saved):
    """Full friends list with presence, via the Steam Web API."""
    d, err = steam_api("ISteamUser/GetFriendList/v1", {"key": key, "steamid": id64, "relationship": "friend"})
    if err:
        return None, err
    rows = (d.get("friendslist") or {}).get("friends") or []
    since = {r["steamid"]: r.get("friend_since") for r in rows if r.get("steamid")}
    ids, people = list(since), []
    for i in range(0, len(ids), 100):
        d, err = steam_api("ISteamUser/GetPlayerSummaries/v2", {"key": key, "steamids": ",".join(ids[i:i + 100])})
        if err:
            return None, err
        people += (d.get("response") or {}).get("players") or []
    nick = {f["steamid"]: f.get("nick") for f in saved}
    out = []
    for p in people:
        sid, gid = p.get("steamid"), p.get("gameid")
        status = STEAM_STATES.get(p.get("personastate", 0), "online")
        game = p.get("gameextrainfo")
        if game:
            status = "ingame"
        join = None
        if gid and p.get("lobbysteamid"):
            join = f"steam://joinlobby/{gid}/{p['lobbysteamid']}/{sid}"
        elif p.get("gameserverip") and not str(p["gameserverip"]).startswith("0.0.0.0"):
            join = f"steam://connect/{p['gameserverip']}"
        out.append({"id": "steam:" + sid, "launcher": "Steam", "name": p.get("personaname") or "Steam user",
                    "nick": nick.get(sid) or "", "avatar": p.get("avatarmedium"), "status": status, "game": game,
                    "game_key": f"steam:{gid}" if gid else None, "last_online": p.get("lastlogoff"),
                    "since": since.get(sid), "join": join})
    return out, None


def riot_lockfile():
    p = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Riot Games", "Riot Client", "Config", "lockfile")
    try:
        with open(p, encoding="utf-8", errors="ignore") as f:
            parts = f.read().strip().split(":")
        return parts[2], parts[3]
    except (OSError, IndexError):
        return None


def riot_client_path():
    p = os.path.join(PROGRAMDATA, "Riot Games", "RiotClientInstalls.json")
    try:
        with open(p, encoding="utf-8", errors="ignore") as f:
            d = json.load(f)
    except (OSError, ValueError):
        return None
    for k in ("rc_default", "rc_live", "rc_beta"):
        if d.get(k) and os.path.isfile(d[k]):
            return d[k]
    return None


def riot_local(path, lf):
    """Ask the Riot Client running on this PC (its own local web server, self-signed certificate)."""
    import ssl
    ctx = ssl.create_default_context()
    ctx.check_hostname, ctx.verify_mode = False, ssl.CERT_NONE   # only ever used for 127.0.0.1
    opener = build_opener(ProxyHandler({}), HTTPSHandler(context=ctx))
    auth = base64.b64encode(f"riot:{lf[1]}".encode()).decode()
    req = Request(f"https://127.0.0.1:{lf[0]}{path}", headers={"Authorization": "Basic " + auth, "Accept": "application/json"})
    with opener.open(req, timeout=4) as r:
        return json.loads(r.read().decode("utf-8"))


def riot_friends():
    lf = riot_lockfile()
    if not lf:
        return None
    try:
        friends = riot_local("/chat/v4/friends", lf).get("friends") or []
        pres = {p.get("puuid"): p for p in riot_local("/chat/v4/presences", lf).get("presences") or []}
    except Exception:
        return None  # client closed (old lockfile) or chat not ready yet
    out = []
    for f in friends:
        p = pres.get(f.get("puuid")) or {}
        state, product = p.get("state") or "offline", p.get("product")
        game, detail = RIOT_GAMES.get(product), None
        if product == "valorant" and p.get("private"):
            try:
                priv = json.loads(base64.b64decode(p["private"]))
                loop = priv.get("sessionLoopState") or (priv.get("matchPresenceData") or {}).get("sessionLoopState")
                detail = {"INGAME": "In a match", "PREGAME": "Agent select", "MENUS": "In the menus"}.get(loop)
            except Exception:
                pass
        if state == "offline" or not p:
            status = "offline"
        elif state == "mobile":
            status, detail = "online", "On mobile"
        elif game:
            status = "ingame" if state == "dnd" or detail == "In a match" else ("away" if state == "away" else "online")
        else:
            status = {"chat": "online", "away": "away", "dnd": "busy"}.get(state, "online")
        group = f.get("group") or ""
        out.append({"id": "riot:" + (f.get("puuid") or f.get("pid") or ""), "launcher": "Riot",
                    "name": f.get("game_name") or f.get("name") or "Riot player", "tag": f.get("game_tag") or "",
                    "nick": f.get("note") or "", "group": "" if group.lower() in RIOT_DEFAULT_GROUPS else group,
                    "avatar": None, "status": status, "game": game, "detail": detail})
    return out


def copy_text(text):
    """Put text on the Windows clipboard."""
    if os.name != "nt":
        return False
    import ctypes
    from ctypes import wintypes
    u32, k32 = ctypes.windll.user32, ctypes.windll.kernel32
    k32.GlobalAlloc.restype, k32.GlobalAlloc.argtypes = wintypes.HGLOBAL, [wintypes.UINT, ctypes.c_size_t]
    k32.GlobalLock.restype, k32.GlobalLock.argtypes = ctypes.c_void_p, [wintypes.HGLOBAL]
    k32.GlobalUnlock.argtypes = [wintypes.HGLOBAL]
    u32.SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
    data = (text + "\0").encode("utf-16-le")
    if not u32.OpenClipboard(None):
        return False
    try:
        u32.EmptyClipboard()
        h = k32.GlobalAlloc(0x0002, len(data))
        ptr = k32.GlobalLock(h)
        ctypes.memmove(ptr, data, len(data))
        k32.GlobalUnlock(h)
        u32.SetClipboardData(13, h)  # CF_UNICODETEXT
    finally:
        u32.CloseClipboard()
    return True


# ======================================================================= self-update
_VER_RE = re.compile(r'^VERSION\s*=\s*"([\d.]+)"', re.M)
_NEW_RE = re.compile(r'^WHATS_NEW\s*=\s*"((?:\\.|[^"\\])*)"', re.M)


def parse_version(v):
    """Comparable version. Numbering is 0.019, 0.020, ... (three digits) until 1.0.0.
    The early builds were numbered 1.0-1.9; those count as older than 0.019."""
    parts = str(v).split(".")
    try:
        nums = tuple(int(x) for x in parts)
    except ValueError:
        return (0,)
    if len(parts) == 2 and nums[0] == 1 and len(parts[1]) == 1:   # old 1.0-1.9 numbering
        return (0, nums[1])
    return nums


def read_header(text):
    """{version, notes} from the top of a game_hub.py, or None if it isn't one."""
    m = _VER_RE.search(text or "")
    if not m:
        return None
    n = _NEW_RE.search(text)
    notes = ""
    if n:
        try:
            notes = json.loads('"' + n.group(1) + '"')
        except ValueError:
            notes = n.group(1)
    return {"version": m.group(1), "notes": notes}


def valid_update(text):
    """A real, working copy of Game Hub: the right markers and no syntax errors."""
    if "class App" not in text or "def main()" not in text or not _VER_RE.search(text):
        return False
    try:
        compile(text, "game_hub.py", "exec")
        return True
    except (SyntaxError, ValueError):
        return False


def downloads_dir():
    if winreg:
        v = reg_get(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Explorer\User Shell Folders",
                    "{374DE290-123F-4565-9164-39C4925E467B}")
        if v and os.path.isdir(os.path.expandvars(v)):
            return os.path.expandvars(v)
    return os.path.join(os.path.expanduser("~"), "Downloads")


def raw_url(u):
    """Accept a normal GitHub file link and turn it into the raw-file link."""
    u = (u or "").strip()
    m = re.match(r"https://github\.com/([^/]+)/([^/]+)/blob/(.+)", u)
    return f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}/{m.group(3)}" if m else u


def github_parts(u):
    """(owner, repo, branch or None, path) from any GitHub link to the file or the repository."""
    u = (u or "").strip().rstrip("/")
    m = re.match(r"https://github\.com/([^/]+)/([^/#?]+)/(?:blob|raw)/([^/]+)/(.+)", u)
    if m:
        return m.group(1), m.group(2), m.group(3), m.group(4)
    m = re.match(r"https://raw\.githubusercontent\.com/([^/]+)/([^/]+)/(?:refs/heads/)?([^/]+)/(.+)", u)
    if m:
        return m.group(1), m.group(2), m.group(3), m.group(4)
    m = re.match(r"https://github\.com/([^/]+)/([^/#?]+?)(?:\.git)?$", u)
    if m:
        return m.group(1), m.group(2), None, "game_hub.py"
    return None


def _fetch(req, etag=None):
    """(text, etag, error). Asks for a compressed copy, and for nothing at all if it hasn't changed (etag)."""
    import gzip
    req.add_header("Accept-Encoding", "gzip")
    if etag:
        req.add_header("If-None-Match", etag)
    try:
        with urlopen(req, timeout=15) as r:
            raw = r.read()
            if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
                raw = gzip.decompress(raw)
            return raw.decode("utf-8", "ignore"), r.headers.get("ETag"), None
    except HTTPError as e:
        if e.code == 304:
            return None, etag, "unchanged"       # nothing new: GitHub sent no file at all
        return None, None, e.code
    except Exception:
        return None, None, "network"


def fetch_update_link(url, token=None, etag=None):
    """(text, error, etag). error is "unchanged" when the file is the same as last time (nothing downloaded)."""
    parts = github_parts(url)
    if parts:
        owner, repo, ref, path = parts
        api = f"https://api.github.com/repos/{owner}/{repo}/contents/{quote(path)}" + (f"?ref={quote(ref)}" if ref else "")
        headers = {"User-Agent": UA, "Accept": "application/vnd.github.raw", "X-GitHub-Api-Version": "2022-11-28"}
        if token:
            headers["Authorization"] = f"Bearer {token}"
        # GitHub's API always has the newest file (the plain file server can lag ~5 minutes behind)
        text, tag, err = _fetch(Request(api, headers=headers), etag)
        if text is not None or err == "unchanged" or token:
            if err == 401:
                return None, "token", None
            if err in (403, 404):
                return None, "access" if token else "private", None
            return text, (None if text is not None else (err if err == "unchanged" else "network")), tag
        # e.g. the API's hourly limit: use the file server, skipping its saved copy with ?t=
        req = Request(f"https://raw.githubusercontent.com/{owner}/{repo}/{ref or 'HEAD'}/{path}?t={int(time.time())}",
                      headers={"User-Agent": UA, "Cache-Control": "no-cache"})
    else:
        req = Request(url, headers={"User-Agent": UA})
    text, tag, err = _fetch(req, etag)
    if text is not None or err == "unchanged":
        return text, err, tag
    return None, "private" if err in (403, 404) else "network", None


class _Blob(ctypes.Structure):   # DATA_BLOB for Windows' CryptProtectData
    _fields_ = [("cbData", ctypes.c_uint32), ("pbData", ctypes.POINTER(ctypes.c_char))]


def _dpapi(data, protect):
    crypt32, k32 = ctypes.windll.crypt32, ctypes.windll.kernel32
    buf = ctypes.create_string_buffer(data, len(data))
    inb = _Blob(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
    out = _Blob()
    fn = crypt32.CryptProtectData if protect else crypt32.CryptUnprotectData
    if not fn(ctypes.byref(inb), None, None, None, None, 0x1, ctypes.byref(out)):  # CRYPTPROTECT_UI_FORBIDDEN
        raise OSError("Windows couldn't encrypt or decrypt the token")
    try:
        return ctypes.string_at(out.pbData, out.cbData)
    finally:
        k32.LocalFree(out.pbData)


def seal(secret):
    """Encrypt with the signed-in Windows account (DPAPI); only this user on this PC can read it back."""
    if not secret:
        return ""
    if os.name == "nt":
        try:
            return "dpapi:" + base64.b64encode(_dpapi(secret.encode(), True)).decode()
        except Exception:
            pass
    return "plain:" + base64.b64encode(secret.encode()).decode()


def unseal(stored):
    if not stored:
        return ""
    kind, _, data = stored.partition(":")
    try:
        raw = base64.b64decode(data)
        return (_dpapi(raw, False) if kind == "dpapi" else raw).decode()
    except Exception:
        return ""


# ======================================================================= install / uninstall
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def _ps(script):
    r = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", script],
                       capture_output=True, text=True, creationflags=NO_WINDOW)
    return (r.stdout or "").strip()


def desktop_dir():
    return _ps("[Environment]::GetFolderPath('Desktop')") or os.path.join(os.path.expanduser("~"), "Desktop")


def start_menu_lnk():
    return os.path.join(APPDATA, "Microsoft", "Windows", "Start Menu", "Programs", "Game Hub.lnk")


def make_shortcut(lnk, target, args, workdir, icon):
    q = lambda v: v.replace("'", "''")
    _ps(f"$s=(New-Object -ComObject WScript.Shell).CreateShortcut('{q(lnk)}');$s.TargetPath='{q(target)}';"
        f"$s.Arguments='{q(args)}';$s.WorkingDirectory='{q(workdir)}';$s.IconLocation='{q(icon)}';"
        "$s.Description='Game Hub';$s.Save()")


def make_icon(path):
    try:
        from PIL import Image as _Im, ImageDraw as _Dr
        img = _Im.new("RGBA", (256, 256), (0, 0, 0, 0))
        d = _Dr.Draw(img)
        d.rounded_rectangle((8, 8, 248, 248), 60, fill=(124, 92, 255, 255))
        d.polygon([(98, 70), (98, 186), (190, 128)], fill=(255, 255, 255, 255))
        sizes = [(16, 16), (24, 24), (32, 32), (48, 48), (64, 64), (128, 128), (256, 256)]
        try:
            img.save(path, sizes=sizes, bitmap_format="bmp")   # classic format: works everywhere in Windows
        except (TypeError, ValueError, OSError):
            img.save(path, sizes=sizes)
        return path
    except Exception:
        return ""


def _tk_root():
    import tkinter as tk
    root = tk.Tk()
    root.withdraw()
    return root


# ---------- closing a running Game Hub safely (so play time in progress is saved)
QUIT_FILE = os.path.join(DATA_DIR, "quit.request")


def _pid_alive(pid):
    if os.name != "nt":
        try:
            os.kill(pid, 0)
            return True
        except OSError:
            return False
    k32 = ctypes.windll.kernel32
    h = k32.OpenProcess(0x1000, False, pid)  # PROCESS_QUERY_LIMITED_INFORMATION
    if not h:
        return False
    code = ctypes.c_ulong()
    k32.GetExitCodeProcess(h, ctypes.byref(code))
    k32.CloseHandle(h)
    return code.value == 259  # STILL_ACTIVE


def close_running_game_hub(timeout=12):
    """Ask a running Game Hub to quit (it saves first); force it only if it doesn't respond."""
    try:
        pid = int(open(PID_FILE).read().strip())
    except (OSError, ValueError):
        return
    if pid == os.getpid() or not _pid_alive(pid):
        return
    try:
        with open(QUIT_FILE, "w") as f:
            f.write(str(pid))
    except OSError:
        pass
    end = time.time() + timeout
    while time.time() < end and _pid_alive(pid):
        time.sleep(0.25)
    if _pid_alive(pid):
        subprocess.run(["taskkill", "/PID", str(pid), "/F"], capture_output=True, creationflags=NO_WINDOW)
        time.sleep(0.5)
    try:
        os.remove(QUIT_FILE)
    except OSError:
        pass


def setup_installed():
    """Installed with the downloadable installer (GameHubSetup.exe)."""
    return bool(winreg and reg_get(winreg.HKEY_CURRENT_USER, SETUP_KEY, "DisplayName"))


def installed_version():
    """Version of the installed copy (from Windows' Apps list), or None."""
    if not winreg:
        return None
    return reg_get(winreg.HKEY_CURRENT_USER, SETUP_KEY, "DisplayVersion") or reg_get(winreg.HKEY_CURRENT_USER, UNINSTALL_KEY, "DisplayVersion")


def running_installed():
    return os.path.normcase(os.path.dirname(os.path.abspath(__file__))) == os.path.normcase(INSTALL_DIR)


def refresh_install_record():
    """Keep Windows' Apps list showing the version you actually have, after Game Hub updates itself."""
    if not (winreg and running_installed()):
        return
    for key in (SETUP_KEY, UNINSTALL_KEY):
        try:
            if reg_get(winreg.HKEY_CURRENT_USER, key, "DisplayName") and reg_get(winreg.HKEY_CURRENT_USER, key, "DisplayVersion") != VERSION:
                with winreg.OpenKey(winreg.HKEY_CURRENT_USER, key, 0, winreg.KEY_WRITE) as k:
                    winreg.SetValueEx(k, "DisplayVersion", 0, winreg.REG_SZ, VERSION)
        except OSError:
            pass


# ---------- small themed window for the installer and uninstaller
class _Wizard:
    BG, PANEL, FG, MUTED, ACCENT, LINE = "#0f1117", "#171a23", "#eceef4", "#8d95a9", "#7c5cff", "#262b38"

    def __init__(self, title, height=380):
        import tkinter as tk
        from tkinter import ttk
        self.tk, self.ttk = tk, ttk
        self.root = tk.Tk()
        self.root.title(title)
        self.root.geometry(f"500x{height}")
        self.root.resizable(False, False)
        self.root.configure(bg=self.BG)
        try:
            ico = os.path.join(INSTALL_DIR, "game_hub.ico")
            if os.path.isfile(ico):
                self.root.iconbitmap(ico)
        except Exception:
            pass
        st = ttk.Style(self.root)
        st.theme_use("clam")
        st.configure("G.Horizontal.TProgressbar", troughcolor=self.LINE, background=self.ACCENT,
                     bordercolor=self.BG, lightcolor=self.ACCENT, darkcolor=self.ACCENT, thickness=8)
        self.body = tk.Frame(self.root, bg=self.BG)
        self.body.pack(fill="both", expand=True, padx=28, pady=(24, 0))
        self.bar = tk.Frame(self.root, bg=self.BG)
        self.bar.pack(fill="x", padx=28, pady=22)

    def clear(self):
        for w in list(self.body.winfo_children()) + list(self.bar.winfo_children()):
            w.destroy()

    def heading(self, text, sub=None):
        self.tk.Label(self.body, text=text, bg=self.BG, fg=self.FG, font=("Segoe UI Semibold", 16), anchor="w",
                      justify="left").pack(fill="x")
        if sub:
            self.tk.Label(self.body, text=sub, bg=self.BG, fg=self.MUTED, font=("Segoe UI", 10), anchor="w",
                          justify="left", wraplength=440).pack(fill="x", pady=(6, 0))

    def text(self, t, muted=False, pady=(10, 0)):
        lbl = self.tk.Label(self.body, text=t, bg=self.BG, fg=self.MUTED if muted else self.FG, font=("Segoe UI", 10),
                            anchor="w", justify="left", wraplength=440)
        lbl.pack(fill="x", pady=pady)
        return lbl

    def check(self, label, value):
        var = self.tk.BooleanVar(value=value)
        self.tk.Checkbutton(self.body, text=label, variable=var, bg=self.BG, fg=self.FG, activebackground=self.BG,
                            activeforeground=self.FG, selectcolor=self.PANEL, font=("Segoe UI", 10), anchor="w",
                            highlightthickness=0, bd=0).pack(fill="x", pady=(8, 0))
        return var

    def button(self, label, cmd, primary=False):
        b = self.tk.Button(self.bar, text=label, command=cmd, font=("Segoe UI Semibold" if primary else "Segoe UI", 10),
                           bg=self.ACCENT if primary else self.PANEL, fg="#ffffff" if primary else self.FG,
                           activebackground="#6a48ff" if primary else self.LINE, activeforeground="#ffffff",
                           relief="flat", bd=0, padx=18, pady=7, cursor="hand2")
        b.pack(side="right", padx=(8, 0))
        return b

    def progress(self):
        pb = self.ttk.Progressbar(self.body, style="G.Horizontal.TProgressbar", mode="determinate", maximum=100)
        pb.pack(fill="x", pady=(22, 0))
        status = self.text("", muted=True)
        return pb, status

    def run_steps(self, steps, on_done):
        """Run (label, fn) steps on a worker thread, showing progress; on_done(error_or_None)."""
        pb, status = self.progress()
        state = {"i": 0, "label": "", "err": None, "done": False}

        def work():
            for i, (label, fn) in enumerate(steps):
                state["i"], state["label"] = i, label
                try:
                    fn()
                except Exception as e:
                    state["err"] = f"{label} failed: {e}"
                    break
            state["done"] = True

        def tick():
            pb["value"] = 100 * (state["i"] + (1 if state["done"] else 0.5)) / len(steps)
            status.configure(text=state["label"] + "…")
            if state["done"]:
                pb["value"] = 100
                on_done(state["err"])
            else:
                self.root.after(120, tick)
        threading.Thread(target=work, daemon=True).start()
        tick()


def install():
    if os.name != "nt" or not winreg:
        print("The installer only runs on Windows.")
        return
    if not ensure_packages():
        return
    src, dest = os.path.abspath(__file__), os.path.join(INSTALL_DIR, "game_hub.py")
    have = installed_version() if os.path.isfile(dest) else None
    w = _Wizard("Install Game Hub")
    opts = {}

    def welcome():
        w.clear()
        if have and parse_version(have) == parse_version(VERSION):
            w.heading(f"Reinstall Game Hub {VERSION}", "Game Hub is already installed. Reinstalling repairs its shortcuts and its entry in Windows.")
        elif have:
            w.heading(f"Install Game Hub {VERSION}", f"This replaces the installed version ({have}).")
        else:
            w.heading(f"Install Game Hub {VERSION}", "Installs Game Hub for your Windows account. No administrator rights needed.")
        w.text("Your library, play time and settings are kept.", muted=True, pady=(4, 6))
        opts["desktop"] = w.check("Add a desktop shortcut", True)
        opts["startup"] = w.check("Start with Windows (so play time is always tracked)", os.path.exists(startup_file()))
        opts["launch"] = w.check("Open Game Hub when finished", True)
        w.button("Cancel", w.root.destroy)
        w.button("Reinstall" if have and parse_version(have) == parse_version(VERSION) else "Install", go, primary=True)

    def go():
        o = {k: v.get() for k, v in opts.items()}
        w.clear()
        w.heading("Installing Game Hub…")
        pyw = gui_python()
        paths = {}

        def copy_files():
            os.makedirs(INSTALL_DIR, exist_ok=True)
            if os.path.normcase(src) != os.path.normcase(dest):
                tmp = dest + ".new"
                shutil.copy2(src, tmp)
                os.replace(tmp, dest)
            paths["icon"] = make_icon(os.path.join(INSTALL_DIR, "game_hub.ico")) or pyw
            with open(os.path.join(INSTALL_DIR, "Uninstall Game Hub.bat"), "w") as f:
                f.write(f'@echo off\r\nstart "" "{pyw}" "{dest}" --uninstall\r\n')

        def shortcuts():
            make_shortcut(start_menu_lnk(), pyw, f'"{dest}"', INSTALL_DIR, paths["icon"])
            desk = os.path.join(desktop_dir(), "Game Hub.lnk")
            if o["desktop"]:
                make_shortcut(desk, pyw, f'"{dest}"', INSTALL_DIR, paths["icon"])
            elif os.path.exists(desk):
                os.remove(desk)
            set_startup(o["startup"], dest)

        def register():
            with winreg.CreateKeyEx(winreg.HKEY_CURRENT_USER, UNINSTALL_KEY, 0, winreg.KEY_WRITE) as k:
                for name, val in (("DisplayName", "Game Hub"), ("DisplayVersion", VERSION), ("Publisher", "Game Hub"),
                                  ("DisplayIcon", paths["icon"]), ("InstallLocation", INSTALL_DIR),
                                  ("UninstallString", f'"{pyw}" "{dest}" --uninstall'),
                                  ("InstallDate", time.strftime("%Y%m%d"))):
                    winreg.SetValueEx(k, name, 0, winreg.REG_SZ, val)
                for name, val in (("NoModify", 1), ("NoRepair", 1), ("EstimatedSize", max(1, os.path.getsize(dest) // 1024))):
                    winreg.SetValueEx(k, name, 0, winreg.REG_DWORD, val)

        def finished(err):
            w.clear()
            if err:
                w.heading("Game Hub couldn't be installed", err)
                w.text("Nothing you had before was removed. Close any open Game Hub windows and try again.", muted=True)
                w.button("Close", w.root.destroy, primary=True)
                return
            w.heading("Game Hub is installed")
            w.text("Find it in your Start menu" + (" and on your desktop." if o["desktop"] else "."))
            w.text("It updates itself. To remove it later, use Windows Settings → Apps → Installed apps → Game Hub.", muted=True)

            def close():
                w.root.destroy()
                if o["launch"]:
                    subprocess.Popen([pyw, dest], cwd=INSTALL_DIR)
            w.button("Finish", close, primary=True)

        steps = [("Closing Game Hub", close_running_game_hub), ("Copying Game Hub", copy_files)]
        if not setup_installed():
            steps += [("Creating shortcuts", shortcuts), ("Adding Game Hub to Windows' Apps list", register)]
        w.run_steps(steps, finished)

    welcome()
    w.root.mainloop()


def uninstall():
    w = _Wizard("Uninstall Game Hub", height=330)
    wipe = {}

    def ask():
        w.clear()
        w.heading("Uninstall Game Hub?", "Removes Game Hub, its shortcuts and its entry in Windows. Your games are never touched.")
        wipe["v"] = w.check("Also delete my Game Hub data (favorites, collections, play time history and covers)", False)
        w.text("Keep your data if you might reinstall later.", muted=True, pady=(4, 0))
        w.button("Cancel", w.root.destroy)
        w.button("Uninstall", go, primary=True)

    def go():
        delete_data = wipe["v"].get()
        w.clear()
        w.heading("Uninstalling Game Hub…")

        def shortcuts():
            try:
                set_startup(False)
            except OSError:
                pass
            for lnk in (start_menu_lnk(), os.path.join(desktop_dir(), "Game Hub.lnk")):
                try:
                    os.remove(lnk)
                except OSError:
                    pass

        def unregister():
            if winreg:
                try:
                    winreg.DeleteKey(winreg.HKEY_CURRENT_USER, UNINSTALL_KEY)
                except OSError:
                    pass

        def data():
            if delete_data:
                shutil.rmtree(DATA_DIR, ignore_errors=True)
            else:
                for f in (PID_FILE, QUIT_FILE):
                    try:
                        os.remove(f)
                    except OSError:
                        pass

        def finished(err):
            w.clear()
            w.heading("Game Hub has been removed" if not err else "Game Hub was only partly removed", err or None)
            if not err and not delete_data:
                w.text("Your library data was kept, in case you reinstall later.", muted=True)

            def close():
                w.root.destroy()
                # remove the program folder (only the installed copy) a moment after this window closes
                if os.name == "nt" and running_installed():
                    os.chdir(os.environ.get("TEMP", os.path.expanduser("~")))
                    subprocess.Popen(f'cmd /c "ping 127.0.0.1 -n 3 >nul & rmdir /s /q "{INSTALL_DIR}""',
                                     creationflags=NO_WINDOW | getattr(subprocess, "DETACHED_PROCESS", 0))
            w.button("Close", close, primary=True)

        w.run_steps([("Closing Game Hub", close_running_game_hub), ("Removing shortcuts", shortcuts),
                     ("Removing Game Hub from Windows' Apps list", unregister), ("Tidying up", data)], finished)

    ask()
    w.root.mainloop()


CRASH_LOG = os.path.join(DATA_DIR, "crash.log")
_crash_file = None


def log_problem(what, exc=None):
    try:
        import traceback
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(CRASH_LOG, "a", encoding="utf-8") as f:
            f.write(f"\n[{time.strftime('%Y-%m-%d %H:%M:%S')}] Game Hub {VERSION}: problem {what}\n")
            if exc is not None:
                f.write("".join(traceback.format_exception(type(exc), exc, exc.__traceback__)))
    except Exception:
        pass


def setup_crash_log():
    """Record crashes and errors in %APPDATA%\\GameHub\\crash.log (kept small)."""
    global _crash_file
    try:
        import faulthandler
        os.makedirs(DATA_DIR, exist_ok=True)
        if os.path.isfile(CRASH_LOG) and os.path.getsize(CRASH_LOG) > 256_000:
            os.replace(CRASH_LOG, CRASH_LOG + ".old")
        _crash_file = open(CRASH_LOG, "a", encoding="utf-8")
        faulthandler.enable(file=_crash_file, all_threads=True)   # hard crashes inside Windows code too
    except Exception:
        pass
    sys.excepthook = lambda t, e, tb: log_problem("that wasn't handled", e)
    threading.excepthook = lambda a: log_problem(f"in background task {getattr(a.thread, 'name', '')}", a.exc_value)


def main():
    setup_crash_log()
    if "--enable-startup" in sys.argv:          # used by GameHubSetup.exe
        return set_startup(True, os.path.abspath(__file__))
    refresh_install_record()
    if "--install" in sys.argv:
        return install()
    if "--uninstall" in sys.argv:
        return uninstall()
    if in_runtime() and webview is None:
        sys.exit(3)                 # can't see the packages from here: let the normal start use plain Python
    if not ensure_packages():
        return
    if handoff_to_runtime():
        return                      # Game Hub is now running as "Game Hub" in Task Manager
    set_app_id()
    app = App()
    app._start_tray()
    minimized = "--minimized" in sys.argv and app._tray is not None
    window = webview.create_window(APP_NAME, html=HTML, js_api=app, width=1320, height=840,
                                   min_size=(980, 620), background_color="#0a0c11", hidden=minimized)
    app._window = window
    window.events.closing += app._on_closing
    try:
        webview.start()
    except Exception as e:
        log_problem("running the window", e)
    try:
        app._shutdown()
    except Exception as e:
        log_problem("saving on exit", e)
    if app._relaunch:  # finished updating: start the new version
        subprocess.Popen(app._relaunch, cwd=os.path.dirname(os.path.abspath(__file__)),
                         creationflags=getattr(subprocess, "DETACHED_PROCESS", 0) | NO_WINDOW)


if __name__ == "__main__":
    main()

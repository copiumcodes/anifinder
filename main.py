#!/usr/bin/env python3
"""anifinder: find downloaded anime you have not watched yet, using AniList.

Scans a directory for video files, works out the series, season and episode
number of each file from its name, looks the series up on AniList, and removes
the shows on your AniList list. The interactive list starts with Planning, Watching
and Not on list shown; you can filter by any AniList status (Completed, Dropped, ...),
format or tag, change the sort,
change the sort, see which episodes you have, and play them.

Understands folders sorted by season ("2024-winter", "2023-fall", "2022-movies",
including misspellings such as "2026-sping"). Files directly inside those
folders are named by their file name; a series folder inside them is named by
the folder.

If a name still cannot be matched, add it to the aliases file
(default ~/.config/anifinder/aliases.json) as {"local name": "AniList title"}
or {"local name": 12345} with an AniList media ID. For one season of a show,
use the season in the key, e.g. {"Aharen Is Indecipherable S2": 179979}; a key
without a season applies to every season.

Keys in the list: j/k or arrows move, f formats, t tags, s sort, r reverse,
l list status, c clear filters, x random pick, Enter details, q quit.
In details: j/k pick a file, Enter plays it, o opens the folder, any other key goes back.

Playback uses mpv, then vlc, then xdg-open, whichever is installed. Set
ANIFINDER_PLAYER to use another program (its arguments are allowed).

Progress: with a login, playing episode N sets your AniList progress to N (never
lower than it already is) and asks for a score. Log in with --login. The token
is read from ANILIST_TOKEN if set, otherwise from ~/.config/anifinder/token.
Progress is saved when the episode starts playing, not when it finishes.

Caching: AniList results are cached (default 7 days, see --cache-days) and the
watched list for an hour, so repeated runs make few requests. Several searches
are sent in one request. Use --refresh to ignore the cache.

Only the standard library is used. Without a login, the AniList profile list must
be public, since AniList only returns a private list to the account that owns it.
"""

from __future__ import annotations

import argparse
import difflib
import getpass
import json
import os
import random
import re
import shlex
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

ANILIST_URL = "https://graphql.anilist.co"
USER_AGENT = "anifinder/0.1"
VIDEO_EXTENSIONS = {".mkv", ".mp4", ".avi", ".m4v", ".webm", ".mov", ".wmv", ".ts"}
# Your AniList list statuses that the status filter selects when the program starts.
# Every status can be filtered in the TUI (press l).
DEFAULT_LIST_STATUSES = {"NOT_ON_LIST", "PLANNING", "CURRENT"}
STATUS_LABELS = {
    "NOT_ON_LIST": "Not on list", "PLANNING": "Planning", "CURRENT": "Watching",
    "PAUSED": "Paused", "REPEATING": "Rewatching", "DROPPED": "Dropped", "COMPLETED": "Completed",
}
STATUS_ORDER = ["NOT_ON_LIST", "PLANNING", "CURRENT", "PAUSED", "REPEATING", "DROPPED", "COMPLETED"]
MATCH_THRESHOLD = 0.6
FORMAT_BONUS = {"TV": 0.1, "TV_SHORT": 0.1, "ONA": 0.05}
YEAR_BONUS = 0.05        # AniList air year equals a season folder's year
SEASON_MATCH_BONUS = 0.1
SEASON_MISMATCH_PENALTY = 0.15
SEASON_ONE_BONUS = 0.02  # when the name has no season, prefer season 1 among similar entries
MAX_QUERIES = 6          # search variants tried per series
BATCH_SIZE = 5           # searches sent in one AniList request
REQUEST_DELAY = 0.8      # AniList allows ~90 requests/minute
CACHE_VERSION = "v5"     # bump when the cache layout or the fields requested change
DEFAULT_CACHE_DAYS = 7   # how long search and media results are reused
WATCHED_MAX_AGE = 3600   # the watched list is re-fetched after an hour
CACHE_KEEP_DAYS = 30     # entries older than this are dropped when the cache is saved
TAG_MIN_RANK = 60        # ignore AniList tags ranked below this (they are often noise)
PLAYERS = ["mpv", "vlc", "xdg-open"]

FORMAT_ORDER = ["TV", "TV_SHORT", "MOVIE", "SPECIAL", "OVA", "ONA", "MUSIC"]

SEASON_WORDS = ["winter", "spring", "summer", "fall", "autumn", "movies", "movie", "films", "film"]
SEASON_FOLDER_RE = re.compile(r"^(?P<year>\d{4})[\s._-]*(?P<word>[A-Za-z]+)$")
# Season numbers in names: "Season 2", "Season3", "2nd Season", "S02"
SEASON_RE = re.compile(
    r"\bseason\s*(\d{1,2})\b|\b(\d{1,2})(?:st|nd|rd|th)\s+season\b|\bs(\d{1,2})\b",
    re.IGNORECASE,
)
# Common English words that get glued onto the end of a word in filenames ("Behindthe")
GLUED_WORDS = ["the", "with", "from", "into", "and", "for"]

CONFIG_DIR = Path.home() / ".config" / "anifinder"
DEFAULT_CACHE = Path.home() / ".cache" / "anifinder" / "search.json"
DEFAULT_ALIASES = CONFIG_DIR / "aliases.json"
DEFAULT_TOKEN_FILE = CONFIG_DIR / "token"


# ---------------------------------------------------------------- names

def norm_key(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


def similarity(a: str, b: str) -> float:
    return difflib.SequenceMatcher(None, norm_key(a), norm_key(b)).ratio()


def clean_title(raw: str) -> str:
    """Strip release-group and quality tags, and episode numbers, from a release name."""
    s = re.sub(r"\[[^\]]*\]|\([^)]*\)|\{[^}]*\}", " ", raw)
    s = s.replace("_", " ").replace(".", " ")
    cut = re.search(
        r"\s[-–]\s*\d+"                       # ' - 05'
        r"|\bS\d{1,2}E\d{1,3}\b"              # S01E05
        r"|\bE[Pp]?\s*\d{1,4}\b"              # E05 / EP05
        r"|\bEpisode\s*\d+"                   # Episode 5
        r"|\b(480|720|1080|2160)p\b"          # 1080p
        r"|\b(x264|x265|hevc|h ?264|h ?265|10bit|hi10p|bdrip|bd|web-?dl|webrip|remux|aac|flac)\b",
        s,
        re.IGNORECASE,
    )
    if cut:
        s = s[: cut.start()]
    return re.sub(r"\s+", " ", s).strip(" -–")


def split_words(s: str) -> str:
    """Split CamelCase ('ChainsmokerCat' -> 'Chainsmoker Cat', 'FXSenshi' -> 'FX Senshi')
    and glued common words ('Behindthe' -> 'Behind the')."""
    s = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", s)
    s = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", s)
    out = []
    for tok in s.split():
        low = tok.lower()
        for w in GLUED_WORDS:
            if len(tok) >= 8 and low.endswith(w):
                tok = tok[: -len(w)] + " " + tok[-len(w):]
                break
        out.append(tok)
    return " ".join(out)


def parse_name(raw: str) -> tuple[str, int | None]:
    """Return (series name, season number or None) for a file or folder name."""
    s = split_words(clean_title(raw))
    season = None
    m = SEASON_RE.search(s)
    if m:
        season = int(next(g for g in m.groups() if g))
        s = s[: m.start()] + " " + s[m.end():]
    s = re.sub(r"[-–_]+", " ", s)
    name = re.sub(r"\s+", " ", s).strip()
    return (name or clean_title(raw) or raw.strip()), season


def parse_episode(stem: str) -> int | None:
    """Episode number from a file name (without extension), or None if there is none.

    Tries the common release patterns in order of how reliable they are:
    S01E05, E05 / EP05 / Episode 5, ' - 05', '[05]', then a bare number left over.
    Season markers and resolutions are ignored, so 'Show S02' is not episode 2."""
    m = re.search(r"S\d{1,2}E(\d{1,4})", stem, re.IGNORECASE)
    if m:
        return int(m.group(1))
    m = re.search(r"\b(?:E|EP|Episode)\s*(\d{1,4})\b", stem, re.IGNORECASE)
    if m:
        return int(m.group(1))
    m = re.search(r"\s[-–]\s*(\d{1,4})(?:v\d+)?(?=\s|\[|\(|\.|$)", stem)
    if m:
        return int(m.group(1))
    m = re.search(r"\[(\d{1,4})(?:v\d+)?\]", stem)
    if m:
        return int(m.group(1))
    # Last resort: a bare 1-3 digit number once tags, resolutions and season markers are removed.
    cleaned = re.sub(r"\[[^\]]*\]|\([^)]*\)|\{[^}]*\}", " ", stem)
    cleaned = re.sub(r"\b(480|720|1080|2160)p\b", " ", cleaned, flags=re.IGNORECASE)
    cleaned = SEASON_RE.sub(" ", cleaned)
    numbers = re.findall(r"(?<![\w.])\d{1,3}(?![\w])", cleaned)
    return int(numbers[-1]) if numbers else None


def season_folder_year(part: str) -> int | None:
    """'2024-winter' -> 2024. Tolerates small typos in the season word ('2026-sping')."""
    m = SEASON_FOLDER_RE.match(part)
    if not m:
        return None
    if difflib.get_close_matches(m["word"].lower(), SEASON_WORDS, n=1, cutoff=0.8):
        return int(m["year"])
    return None


def classify(rel_parts: tuple[str, ...]) -> tuple[str | None, int | None, str, int]:
    """Return (season folder, season year, raw series name, series folder depth) for a file path
    relative to the root. The depth is how many leading parts form the series folder; 0 means the
    file's own folder."""
    dirs, filename = rel_parts[:-1], rel_parts[-1]
    stem = Path(filename).stem
    for i, part in enumerate(dirs):
        year = season_folder_year(part)
        if year is not None:
            if i + 1 < len(dirs):
                return part, year, dirs[i + 1], i + 2
            return part, year, stem, 0
    if dirs:
        return None, None, dirs[0], 1
    return None, None, stem, 0


def compress_numbers(nums: list[int]) -> str:
    """[1, 2, 3, 5, 7, 8] -> '1-3, 5, 7-8'."""
    parts: list[str] = []
    for n in sorted(set(nums)):
        if parts and "-" not in parts[-1] and int(parts[-1]) == n - 1:
            parts[-1] = f"{parts[-1]}-{n}"
        elif parts and "-" in parts[-1] and int(parts[-1].split("-")[1]) == n - 1:
            parts[-1] = f"{parts[-1].split('-')[0]}-{n}"
        else:
            parts.append(str(n))
    return ", ".join(parts)


# ---------------------------------------------------------------- scanning

@dataclass
class EpisodeFile:
    path: Path
    episode: int | None  # None when the name has no episode number (e.g. a movie)


@dataclass
class Series:
    name: str
    season: int | None = None
    years: set[int] = field(default_factory=set)
    labels: set[str] = field(default_factory=set)
    folders: set[Path] = field(default_factory=set)  # where the files are on disk
    episode_files: list[EpisodeFile] = field(default_factory=list)
    query: str = ""  # what is actually searched on AniList (may come from an alias)

    def __post_init__(self) -> None:
        self.query = self.query or self.name

    @property
    def label(self) -> str:
        return f"{self.name} S{self.season}" if self.season else self.name

    @property
    def files(self) -> int:
        return len(self.episode_files)


def open_folder(s: Series) -> str:
    """Open a series' folder in the desktop file manager. Returns a status message."""
    if not s.folders:
        return "no folder known for this entry"
    folder = sorted(s.folders)[0]
    opener = shutil.which("xdg-open")
    if opener is None:
        return f"xdg-open not found. Path: {folder}"
    try:
        subprocess.Popen([opener, str(folder)], stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    except OSError as e:
        return f"could not open {folder}: {e}"
    extra = f" ({len(s.folders)} folders, opened the first)" if len(s.folders) > 1 else ""
    return f"opened {folder}{extra}"


def play_file(path: Path) -> str:
    """Start a video in an external player without waiting for it. Returns a status message."""
    custom = os.environ.get("ANIFINDER_PLAYER", "").strip()
    if custom:
        argv = shlex.split(custom)
        if not argv or shutil.which(argv[0]) is None:
            return f"ANIFINDER_PLAYER not found: {custom}"
    else:
        exe = next((p for p in PLAYERS if shutil.which(p)), None)
        if exe is None:
            return "no player found: install mpv or vlc, or set ANIFINDER_PLAYER"
        argv = [exe]
    try:
        subprocess.Popen([*argv, str(path)], stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    except OSError as e:
        return f"could not start {argv[0]}: {e}"
    return f"playing {path.name} with {argv[0]}"


def scan_directory(root: Path) -> dict[tuple[str, int | None], Series]:
    series: dict[tuple[str, int | None], Series] = {}
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix.lower() not in VIDEO_EXTENSIONS:
            continue
        rel = path.relative_to(root)
        label, year, raw, depth = classify(rel.parts)
        name, season = parse_name(raw)
        entry = series.setdefault((norm_key(name), season), Series(name, season))
        entry.episode_files.append(EpisodeFile(path, parse_episode(path.stem)))
        entry.folders.add(root.joinpath(*rel.parts[:depth]) if depth else path.parent)
        if label:
            entry.labels.add(label)
        if year:
            entry.years.add(year)
    for entry in series.values():
        entry.episode_files.sort(key=lambda f: (f.episode is None, f.episode or 0, f.path.name.lower()))
    return series


# ---------------------------------------------------------------- AniList

class AniListError(RuntimeError):
    pass


def graphql(query: str, variables: dict[str, Any], retries: int = 4, token: str | None = None) -> dict[str, Any]:
    body = json.dumps({"query": query, "variables": variables}).encode()
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "User-Agent": USER_AGENT,
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    for attempt in range(retries):
        req = urllib.request.Request(ANILIST_URL, data=body, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                payload = json.loads(resp.read().decode())
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < retries - 1:
                wait = int(e.headers.get("Retry-After") or 60)
                print(f"  rate limited by AniList, waiting {wait}s...", file=sys.stderr)
                time.sleep(wait)
                continue
            if e.code == 401:
                raise AniListError("AniList rejected the token (expired or wrong). Run --login again.")
            if e.code == 404:
                raise AniListError("AniList user not found")
            raise AniListError(f"AniList HTTP error {e.code}") from e
        except urllib.error.URLError as e:
            raise AniListError(f"could not reach AniList: {e.reason}") from e

        if payload.get("errors"):
            msg = payload["errors"][0].get("message", "unknown error")
            raise AniListError(f"AniList error: {msg}")
        return payload["data"]
    raise AniListError("AniList request failed after retries")


MEDIA_FIELDS = """
  id
  title { romaji english native }
  episodes
  averageScore
  format
  seasonYear
  startDate { year }
  genres
  tags { name rank }
"""

MEDIA_BY_ID_QUERY = f"""
query ($id: Int) {{
  Media(id: $id, type: ANIME) {{ {MEDIA_FIELDS} }}
}}
"""

WATCHED_QUERY = """
query ($name: String) {
  MediaListCollection(userName: $name, type: ANIME) {
    lists {
      status
      entries { status media { id } }
    }
  }
}
"""

VIEWER_QUERY = """
query {
  Viewer { id name mediaListOptions { scoreFormat } }
}
"""

# Your own list entry for one anime (needs a token).
ENTRY_QUERY = """
query ($id: Int) {
  Media(id: $id, type: ANIME) {
    episodes
    mediaListEntry { status progress score }
  }
}
"""

SAVE_ENTRY_MUTATION = """
mutation ($mediaId: Int, $progress: Int, $status: MediaListStatus, $score: Float) {
  SaveMediaListEntry(mediaId: $mediaId, progress: $progress, status: $status, score: $score) {
    id progress status score
  }
}
"""

# How to read and check a score for each of AniList's score formats.
SCORE_FORMATS: dict[str, tuple[str, float, float, bool]] = {
    # format: (hint, min, max, whole numbers only)
    "POINT_100": ("0-100", 0, 100, True),
    "POINT_10_DECIMAL": ("0-10, decimals allowed", 0, 10, False),
    "POINT_10": ("0-10", 0, 10, True),
    "POINT_5": ("0-5 stars", 0, 5, True),
    "POINT_3": ("1-3 (1 sad, 2 ok, 3 happy), 0 clears", 0, 3, True),
}


def build_batch_search(n: int) -> str:
    """One GraphQL request that runs n searches, as aliased fields s0..s{n-1}."""
    variables = ", ".join(f"$s{i}: String" for i in range(n))
    fields = "\n".join(
        f"s{i}: Page(perPage: 8) {{ media(search: $s{i}, type: ANIME, sort: SEARCH_MATCH) {{ {MEDIA_FIELDS} }} }}"
        for i in range(n)
    )
    return f"query ({variables}) {{\n{fields}\n}}"


def fetch_list_statuses(user: str) -> dict[int, str]:
    """Your list status for every anime on the user's public list: {media id: status}."""
    data = graphql(WATCHED_QUERY, {"name": user})
    collection = data.get("MediaListCollection") or {}
    statuses: dict[int, str] = {}
    for lst in collection.get("lists", []):
        for entry in lst.get("entries", []):
            status = entry.get("status") or lst.get("status")
            if status:
                statuses[entry["media"]["id"]] = status
    return statuses


def media_year(media: dict[str, Any]) -> int | None:
    return media.get("seasonYear") or (media.get("startDate") or {}).get("year")


def titles_of(media: dict[str, Any]) -> list[str]:
    """All titles of an entry, plus the part before any ':' or ' - ' (long English titles often
    add a subtitle to the name people use, e.g. 'Rich Girl Caretaker: I'm Secretly...')."""
    titles: list[str] = []
    for t in media["title"].values():
        if not t:
            continue
        titles.append(t)
        for sep in (":", " - "):
            if sep in t:
                titles.append(t.split(sep, 1)[0])
    return titles


def candidate_season(media: dict[str, Any]) -> int:
    """The season an AniList entry is, from its titles. Entries with no marker are season 1."""
    for t in titles_of(media):
        m = SEASON_RE.search(t)
        if m:
            return int(next(g for g in m.groups() if g))
    return 1


def best_match(series: Series, candidates: list[dict[str, Any]]) -> dict[str, Any] | None:
    best, best_score = None, 0.0
    for media in candidates:
        names = titles_of(media)
        score = max((similarity(series.query, n) for n in names), default=0.0)
        # Also try the query without its first word, for names with a stray prefix ("FX Senshi ...").
        words = series.query.split()
        if len(words) > 1:
            score = max(score, max((similarity(" ".join(words[1:]), n) for n in names), default=0.0))
        score += FORMAT_BONUS.get(media.get("format"), 0.0)
        if series.years and media_year(media) in series.years:
            score += YEAR_BONUS
        cand = candidate_season(media)
        if series.season is not None:
            score += SEASON_MATCH_BONUS if cand == series.season else -SEASON_MISMATCH_PENALTY
        elif cand == 1:
            score += SEASON_ONE_BONUS
        if score > best_score:
            best, best_score = media, score
    return best if best_score >= MATCH_THRESHOLD else None


def query_variants(name: str) -> list[str]:
    """Search strings to try, longest first. AniList returns nothing for long queries,
    and a stray leading word ('FX', a group tag) can stop a search working."""
    words = name.split()
    variants: list[tuple[int, str]] = []
    for start in (0, 1):
        for end in range(len(words), start, -1):
            cand = " ".join(words[start:end])
            if len(cand) >= 3 and cand not in [v for _, v in variants]:
                variants.append((len(cand), cand))
    variants.sort(key=lambda v: -v[0])
    return [v for _, v in variants][:MAX_QUERIES] or [name]


def is_strong_hit(query: str, results: list[dict[str, Any]]) -> bool:
    """True when one of the results is clearly the title that was searched for."""
    return any(similarity(query, t) >= 0.9 for m in results for t in titles_of(m))


# ---------------------------------------------------------------- login and progress

def token_source() -> tuple[str | None, str]:
    """(token, where it came from). The environment variable wins over the saved file."""
    env = os.environ.get("ANILIST_TOKEN", "").strip()
    if env:
        return env, "ANILIST_TOKEN"
    try:
        saved = DEFAULT_TOKEN_FILE.read_text().strip()
        if saved:
            return saved, str(DEFAULT_TOKEN_FILE)
    except OSError:
        pass
    return None, ""


def save_token(token: str) -> None:
    DEFAULT_TOKEN_FILE.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(DEFAULT_TOKEN_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as f:
        f.write(token + "\n")
    os.chmod(DEFAULT_TOKEN_FILE, 0o600)


@dataclass
class Session:
    """A logged-in AniList account."""
    token: str
    name: str
    score_format: str  # e.g. POINT_10, as set in the account's settings

    def get_entry(self, media_id: int) -> tuple[dict[str, Any] | None, int | None]:
        """(your list entry or None, total episodes)."""
        data = graphql(ENTRY_QUERY, {"id": media_id}, token=self.token)["Media"]
        return data.get("mediaListEntry"), data.get("episodes")

    def save_entry(self, media_id: int, **fields: Any) -> dict[str, Any]:
        """Create or update your list entry. Only the given fields are changed."""
        variables = {"mediaId": media_id, **{k: v for k, v in fields.items() if v is not None}}
        return graphql(SAVE_ENTRY_MUTATION, variables, token=self.token)["SaveMediaListEntry"]

    def set_progress(self, media: dict[str, Any], episode: int) -> str:
        """Move your progress up to the episode you just started. Never moves it back."""
        entry, total = self.get_entry(media["id"])
        total = total or media.get("episodes")
        current = (entry or {}).get("progress") or 0
        if episode <= current:
            return f"progress stays at {current}"
        if total and episode >= total:
            status = "COMPLETED"
        elif entry and entry.get("status") in ("REPEATING", "PAUSED", "DROPPED"):
            status = entry["status"]
        else:
            status = "CURRENT"
        self.save_entry(media["id"], progress=episode, status=status)
        return f"progress {current} -> {episode}"

    def set_score(self, media_id: int, score: float) -> None:
        self.save_entry(media_id, score=score)


def load_session() -> tuple[Session | None, str]:
    """Log in with the stored token. Returns (session or None, message for the user)."""
    token, source = token_source()
    if not token:
        return None, "not logged in: progress will not be saved (run --login)"
    try:
        viewer = graphql(VIEWER_QUERY, {}, token=token)["Viewer"]
    except AniListError as e:
        return None, f"login failed: {e}"
    fmt = (viewer.get("mediaListOptions") or {}).get("scoreFormat") or "POINT_10"
    return Session(token, viewer["name"], fmt), f"logged in as {viewer['name']} (token from {source})"


def login() -> int:
    print("To log in you need an AniList access token:")
    print("  1. Create an API client at https://anilist.co/settings/developer")
    print("     with the redirect URL https://anilist.co/api/v2/oauth/pin")
    print("  2. Open https://anilist.co/api/v2/oauth/authorize?client_id=YOUR_CLIENT_ID&response_type=token")
    print("     approve it, and copy the access token AniList shows you.")
    token = getpass.getpass("Access token (input is hidden): ").strip()
    if not token:
        print("No token entered.", file=sys.stderr)
        return 1
    try:
        viewer = graphql(VIEWER_QUERY, {}, token=token)["Viewer"]
    except AniListError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    save_token(token)
    print(f"Logged in as {viewer['name']}. Token saved to {DEFAULT_TOKEN_FILE} (readable by you only).")
    return 0


def logout() -> int:
    try:
        DEFAULT_TOKEN_FILE.unlink()
        print(f"Removed {DEFAULT_TOKEN_FILE}.")
    except FileNotFoundError:
        print("No saved token.")
    return 0


# ---------------------------------------------------------------- cache

def load_cache(path: Path) -> dict[str, Any]:
    data = load_json(path)
    return data if isinstance(data, dict) else {}


def save_cache(path: Path, cache: dict[str, Any]) -> None:
    """Write the cache atomically, dropping entries older than CACHE_KEEP_DAYS."""
    cutoff = time.time() - CACHE_KEEP_DAYS * 86400
    for key in [k for k, v in cache.items() if not isinstance(v, dict) or v.get("t", 0) < cutoff]:
        del cache[key]
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(".tmp")
        tmp.write_text(json.dumps(cache, indent=1))
        os.replace(tmp, path)
    except OSError as e:
        print(f"warning: could not write cache: {e}", file=sys.stderr)


def is_fresh(cache: dict[str, Any], key: str, max_age: float) -> bool:
    entry = cache.get(key)
    return isinstance(entry, dict) and time.time() - entry.get("t", 0) < max_age


def put_cache(cache: dict[str, Any], key: str, value: Any) -> None:
    cache[key] = {"t": time.time(), "v": value}


def fetch_statuses_cached(user: str, cache: dict[str, Any], use_cache: bool) -> dict[int, str]:
    key = f"{CACHE_VERSION}|statuses|{user.lower()}"
    if use_cache and is_fresh(cache, key, WATCHED_MAX_AGE):
        return {int(k): v for k, v in cache[key]["v"].items()}
    statuses = fetch_list_statuses(user)
    put_cache(cache, key, {str(k): v for k, v in statuses.items()})
    return statuses


def media_by_id_cached(media_id: int, cache: dict[str, Any], use_cache: bool, max_age: float) -> dict[str, Any]:
    key = f"{CACHE_VERSION}|media|{media_id}"
    if use_cache and is_fresh(cache, key, max_age):
        return cache[key]["v"]
    media = graphql(MEDIA_BY_ID_QUERY, {"id": media_id})["Media"]
    put_cache(cache, key, media)
    time.sleep(REQUEST_DELAY)
    return media


def fetch_search_results(names: list[str], cache: dict[str, Any], use_cache: bool, max_age: float,
                         save: Callable[[], None]) -> dict[str, list[dict[str, Any]]]:
    """Search AniList for each name. Uncached names are searched in batches, several per request.
    Each name tries its query variants in turn until one clearly matches. The cache is saved after
    every batch, so an interrupted run keeps its progress."""
    results: dict[str, list[dict[str, Any]]] = {}
    plans: dict[str, list[str]] = {}
    for name in dict.fromkeys(names):
        key = f"{CACHE_VERSION}|search|{name}"
        if use_cache and is_fresh(cache, key, max_age):
            results[name] = cache[key]["v"]
        else:
            plans[name] = query_variants(name)
    print(f"  {len(results)} searches from cache, {len(plans)} to fetch from AniList")
    if not plans:
        return results

    found: dict[str, dict[int, dict[str, Any]]] = {n: {} for n in plans}
    active = list(plans)
    depth = 0
    while active:
        # The query for each active name at this depth; each batch is one request.
        todo = [(n, plans[n][depth]) for n in active if depth < len(plans[n])]
        hits: set[str] = set()
        finished: set[str] = set()
        for start in range(0, len(todo), BATCH_SIZE):
            chunk = todo[start:start + BATCH_SIZE]
            variables = {f"s{i}": query for i, (_, query) in enumerate(chunk)}
            data = graphql(build_batch_search(len(chunk)), variables)
            for i, (name, query) in enumerate(chunk):
                media = data[f"s{i}"]["media"]
                for m in media:
                    found[name].setdefault(m["id"], m)
                if is_strong_hit(query, media):
                    hits.add(name)
            # Save each batch as it arrives, so a failure later keeps what is already fetched.
            for name, _ in chunk:
                if name in hits:
                    results[name] = list(found[name].values())
                    put_cache(cache, f"{CACHE_VERSION}|search|{name}", results[name])
                    finished.add(name)
            save()
            time.sleep(REQUEST_DELAY)

        for name in active:
            if name not in finished and depth + 1 >= len(plans[name]):
                results[name] = list(found[name].values())
                put_cache(cache, f"{CACHE_VERSION}|search|{name}", results[name])
                finished.add(name)
        active = [n for n in active if n not in finished]
        depth += 1
        save()
    return results


# ---------------------------------------------------------------- filtering and sorting

def display_name(media: dict[str, Any]) -> str:
    t = media["title"]
    return t.get("english") or t.get("romaji") or t.get("native") or "?"


def row_tags(media: dict[str, Any]) -> set[str]:
    """Genres plus tags ranked high enough to be meaningful."""
    tags = {t["name"] for t in media.get("tags") or [] if (t.get("rank") or 0) >= TAG_MIN_RANK}
    return tags | set(media.get("genres") or [])


SORT_OPTIONS: dict[str, tuple[str, Callable[[tuple[Series, dict[str, Any]]], Any], bool]] = {
    # key: (label, sort key function, default descending)
    "score":    ("Score",       lambda r: r[1].get("averageScore") or 0, True),
    "title":    ("AniList name", lambda r: display_name(r[1]).lower(), False),
    "local":    ("Local name",  lambda r: r[0].label.lower(), False),
    "year":     ("Year",        lambda r: media_year(r[1]) or 0, True),
    "episodes": ("Episodes",    lambda r: r[1].get("episodes") or float("inf"), False),  # unknown last
    "files":    ("Local files", lambda r: r[0].files, True),
    "format":   ("Format",      lambda r: r[1].get("format") or "", False),
}


@dataclass
class ViewState:
    formats: set[str] = field(default_factory=set)   # empty = all formats
    tags: set[str] = field(default_factory=set)      # empty = all tags
    tag_mode: str = "any"                            # "any": match one selected tag, "all": match every one
    sort_key: str = "score"
    desc: bool = True
    statuses: set[str] = field(default_factory=lambda: set(DEFAULT_LIST_STATUSES))  # empty = all statuses

    def reset_sort(self, key: str) -> None:
        self.sort_key = key
        self.desc = SORT_OPTIONS[key][2]

    def clear_filters(self) -> None:
        self.formats.clear()
        self.tags.clear()
        self.tag_mode = "any"
        self.statuses = set(DEFAULT_LIST_STATUSES)


def list_status(statuses: dict[int, str], media: dict[str, Any]) -> str:
    return statuses.get(media["id"], "NOT_ON_LIST")


def apply_view(rows: list[tuple[Series, dict[str, Any]]], state: ViewState,
               statuses: dict[int, str]) -> list[tuple[Series, dict[str, Any]]]:
    out = []
    for s, media in rows:
        if state.formats and (media.get("format") or "") not in state.formats:
            continue
        if state.statuses and list_status(statuses, media) not in state.statuses:
            continue
        if state.tags:
            tags = row_tags(media)
            ok = state.tags <= tags if state.tag_mode == "all" else bool(state.tags & tags)
            if not ok:
                continue
        out.append((s, media))
    _, keyfn, _ = SORT_OPTIONS[state.sort_key]
    # sorted() is stable, so ties keep the order they were in before.
    return sorted(out, key=keyfn, reverse=state.desc)


def available_formats(rows: list[tuple[Series, dict[str, Any]]]) -> list[tuple[str, int]]:
    counts = Counter(m.get("format") or "?" for _, m in rows)
    order = {f: i for i, f in enumerate(FORMAT_ORDER)}
    return sorted(counts.items(), key=lambda kv: (order.get(kv[0], len(order)), kv[0]))


def available_tags(rows: list[tuple[Series, dict[str, Any]]], limit: int = 80) -> list[tuple[str, int]]:
    counts = Counter(t for _, m in rows for t in row_tags(m))
    return sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:limit]


def available_statuses(rows: list[tuple[Series, dict[str, Any]]],
                       statuses: dict[int, str]) -> list[tuple[str, int]]:
    """Every AniList status, with how many of these rows have it."""
    counts = Counter(list_status(statuses, m) for _, m in rows)
    return [(st, counts[st]) for st in STATUS_ORDER]


def episode_coverage(s: Series, total: int | None) -> tuple[str, str]:
    """(episodes you have, episodes missing) as text, using the AniList episode count when known."""
    have = sorted({f.episode for f in s.episode_files if f.episode is not None})
    unnumbered = sum(1 for f in s.episode_files if f.episode is None)
    have_text = compress_numbers(have) or "none numbered"
    if unnumbered:
        have_text += f" (+{unnumbered} without a number)"
    if total:
        missing = [n for n in range(1, total + 1) if n not in have]
        missing_text = compress_numbers(missing) or "none"
    else:
        missing_text = "unknown (AniList episode count not known)"
    return have_text, missing_text


# ---------------------------------------------------------------- output

def print_table(rows: list[tuple[Series, dict[str, Any]]], statuses: dict[int, str]) -> None:
    if not rows:
        print("  (none)")
        return
    header = (f"  {'Local name':<34} {'Folder':<12} {'AniList name':<40} {'Status':<12} "
              f"{'Score':>5} {'Eps':>5} {'Files':>5}  Format")
    print(header)
    print("  " + "-" * (len(header) - 2))
    for s, media in rows:
        score = media.get("averageScore")
        eps = media.get("episodes")
        folder = ",".join(sorted(s.labels))[:12] or "-"
        status = STATUS_LABELS[list_status(statuses, media)]
        print(
            f"  {s.label[:34]:<34} "
            f"{folder:<12} "
            f"{display_name(media)[:40]:<40} "
            f"{status:<12} "
            f"{(str(score) if score else '-'):>5} "
            f"{(str(eps) if eps else '?'):>5} "
            f"{s.files:>5}  {media.get('format') or '-'}"
        )


# ---------------------------------------------------------------- TUI

def run_tui(rows: list[tuple[Series, dict[str, Any]]], statuses: dict[int, str],
            session: Session | None, login_note: str = "") -> None:
    import curses  # imported here so the rest of the tool does not need a terminal

    def app(stdscr: "curses.window") -> None:
        curses.curs_set(0)
        state = ViewState()
        cursor = top = 0
        message = login_note

        def put(y: int, x: int, text: str, attr: int = 0) -> None:
            h, w = stdscr.getmaxyx()
            if 0 <= y < h and x < w:
                try:
                    stdscr.addnstr(y, x, text, max(0, w - x - 1), attr)
                except curses.error:
                    pass

        def ask_text(prompt: str) -> str | None:
            """Read one line at the bottom of the screen. Returns None if cancelled with Esc."""
            buf = ""
            while True:
                h, _ = stdscr.getmaxyx()
                put(h - 1, 0, " " * (stdscr.getmaxyx()[1] - 1))
                put(h - 1, 0, f"{prompt}{buf}")
                stdscr.refresh()
                key = stdscr.getch()
                if key == 27:
                    return None
                if key in (10, 13, curses.KEY_ENTER):
                    return buf
                if key in (curses.KEY_BACKSPACE, 127, 8):
                    buf = buf[:-1]
                elif 32 <= key < 127:
                    buf += chr(key)

        def checklist(title: Callable[[], str], items: list[tuple[str, str]], selected: set[str],
                      single: bool = False, extra: dict[int, Callable[[], None]] | None = None) -> set[str] | None:
            """Pick from a list. Returns the new selection, or None if cancelled."""
            sel = set(selected)
            idx = 0
            off = 0
            extra = extra or {}
            while True:
                stdscr.erase()
                h, _ = stdscr.getmaxyx()
                put(0, 0, title(), curses.A_BOLD)
                if not items:
                    put(2, 2, "Nothing to choose from. Press any key.")
                    stdscr.refresh()
                    stdscr.getch()
                    return None
                body = h - 3
                if idx < off:
                    off = idx
                if idx >= off + body:
                    off = idx - body + 1
                for row, (value, label) in enumerate(items[off: off + body]):
                    mark = "(*)" if value in sel and single else "[x]" if value in sel else "[ ]"
                    attr = curses.A_REVERSE if off + row == idx else 0
                    put(2 + row, 2, f"{mark} {label}", attr)
                put(h - 1, 0, "space toggle  enter apply  esc cancel" + ("  |  " + "  ".join(
                    f"{chr(k)} {fn.__name__}" for k, fn in extra.items()) if extra else ""))
                stdscr.refresh()
                key = stdscr.getch()
                if key == 27:
                    return None
                if key in (10, 13, curses.KEY_ENTER):
                    return {items[idx][0]} if single else sel
                if key == ord(" "):
                    value = items[idx][0]
                    if single:
                        sel = {value}
                    elif value in sel:
                        sel.discard(value)
                    else:
                        sel.add(value)
                elif key in (curses.KEY_DOWN, ord("j")):
                    idx = min(idx + 1, len(items) - 1)
                elif key in (curses.KEY_UP, ord("k")):
                    idx = max(idx - 1, 0)
                elif key == curses.KEY_NPAGE:
                    idx = min(idx + body, len(items) - 1)
                elif key == curses.KEY_PPAGE:
                    idx = max(idx - body, 0)
                elif key in extra:
                    extra[key]()

        def pick_formats() -> None:
            choices = available_formats(rows)
            items = [(f, f"{f} ({n})") for f, n in choices]
            result = checklist(lambda: "Filter by format (space to toggle, enter to apply)",
                               items, state.formats)
            if result is not None:
                state.formats = result

        def pick_tags() -> None:
            choices = available_tags(rows)
            items = [(t, f"{t} ({n})") for t, n in choices]

            def toggle_mode() -> None:
                state.tag_mode = "all" if state.tag_mode == "any" else "any"

            toggle_mode.__name__ = "mode"
            result = checklist(
                lambda: f"Filter by tag/genre, mode: {state.tag_mode} "
                        f"({'match any selected' if state.tag_mode == 'any' else 'match all selected'})",
                items, state.tags, extra={ord("m"): toggle_mode},
            )
            if result is not None:
                state.tags = result

        def pick_statuses() -> None:
            items = [(st, f"{STATUS_LABELS[st]} ({n})") for st, n in available_statuses(rows, statuses)]
            result = checklist(lambda: "Filter by your list status (space to toggle, enter to apply; "
                                       "none selected = all)", items, state.statuses)
            if result is not None:
                state.statuses = result

        def pick_sort() -> None:
            items = [(k, label) for k, (label, _, _) in SORT_OPTIONS.items()]
            result = checklist(lambda: "Sort by (enter to choose)", items, {state.sort_key}, single=True)
            if result:
                state.reset_sort(next(iter(result)))

        def ask_score(current: Any, fmt: str) -> float | None:
            """Ask for a score in the account's format. Returns None to keep the current score."""
            hint, lo, hi, whole = SCORE_FORMATS.get(fmt, SCORE_FORMATS["POINT_10"])
            cur_text = f"{current:g}" if current else "none"
            prompt = f"Score ({hint}), now {cur_text}, enter keeps it: "
            while True:
                text = ask_text(prompt)
                if not text:  # Esc or empty: keep the current score
                    return None
                try:
                    value = float(text)
                except ValueError:
                    prompt = f"Not a number. Score ({hint}): "
                    continue
                if not (lo <= value <= hi) or (whole and value != int(value)):
                    prompt = f"Out of range ({hint}): "
                    continue
                return value

        def play_and_track(media: dict[str, Any], f: EpisodeFile, entry_info: list[str]) -> str:
            """Play an episode, then update progress on AniList and ask for a score."""
            note = play_file(f.path)
            if f.episode is None or session is None:
                if session is None and f.episode is not None:
                    note += " | not logged in: progress not saved"
                return note
            try:
                note += " | " + session.set_progress(media, f.episode)
                entry, _ = session.get_entry(media["id"])
                current = (entry or {}).get("score")
                score = ask_score(current, session.score_format)
                if score is not None:
                    session.set_score(media["id"], score)
                    note += f" | score {score:g} saved"
                entry_info[0] = describe_entry(media, session)
            except AniListError as e:
                note += f" | AniList: {e}"
            return note

        def describe_entry(media: dict[str, Any], sess: Session | None) -> str:
            if sess is None:
                return "not logged in (run --login)"
            try:
                entry, total = sess.get_entry(media["id"])
            except AniListError as e:
                return f"unavailable: {e}"
            if not entry:
                return f"not on your list (episodes on AniList: {total or '?'})"
            return (f"{entry.get('status') or '-'}, progress {entry.get('progress') or 0}"
                    f"/{total or '?'}, score {entry.get('score') or '-'}")

        def details(media: dict[str, Any], s: Series) -> None:
            t = media["title"]
            total = media.get("episodes")
            have_text, missing_text = episode_coverage(s, total)
            entry_info = [describe_entry(media, session)]
            file_cursor = 0
            file_top = 0
            note = ""
            while True:
                info = [
                    ("AniList", display_name(media)),
                    ("Romaji", t.get("romaji") or "-"),
                    ("Native", t.get("native") or "-"),
                    ("Local name", s.label),
                    ("Local files", str(s.files)),
                    ("Folder", ", ".join(sorted(s.labels)) or "-"),
                    ("Path", ", ".join(str(p) for p in sorted(s.folders)) or "-"),
                    ("Format", media.get("format") or "-"),
                    ("Episodes", f"{total or '?'} on AniList"),
                    ("Have", have_text),
                    ("Missing", missing_text),
                    ("Your list", entry_info[0]),
                    ("Score", str(media.get("averageScore") or "-")),
                    ("Year", str(media_year(media) or "-")),
                    ("Genres", ", ".join(media.get("genres") or []) or "-"),
                ]
                tags = sorted((t for t in media.get("tags") or [] if (t.get("rank") or 0) >= TAG_MIN_RANK),
                              key=lambda t: -(t.get("rank") or 0))
                info.append(("Tags", ", ".join(f"{t['name']} ({t['rank']})" for t in tags[:15]) or "-"))
                info.append(("AniList", f"https://anilist.co/anime/{media['id']}"))

                stdscr.erase()
                h, w = stdscr.getmaxyx()
                put(0, 0, "Details", curses.A_BOLD)
                for i, (k, v) in enumerate(info):
                    put(2 + i, 2, f"{k}:", curses.A_BOLD)
                    put(2 + i, 16, v)
                list_top = 2 + len(info) + 1
                put(list_top, 2, "Files (enter plays the selected file and updates your progress):", curses.A_BOLD)
                first_row = list_top + 1
                visible = max(1, h - 2 - first_row)
                if file_cursor < file_top:
                    file_top = file_cursor
                if file_cursor >= file_top + visible:
                    file_top = file_cursor - visible + 1
                if not s.episode_files:
                    put(first_row, 4, "(no files)")
                for i, f in enumerate(s.episode_files[file_top: file_top + visible]):
                    pos = file_top + i
                    ep = f"E{f.episode:02d}" if f.episode is not None else "  -"
                    attr = curses.A_REVERSE if pos == file_cursor else 0
                    put(first_row + i, 4, f"{ep:>4}  {f.path.name}", attr)
                put(h - 2, 0, note)
                put(h - 1, 0, "j/k select  enter play  o open folder  any other key: back")
                stdscr.refresh()

                key = stdscr.getch()
                if key in (curses.KEY_DOWN, ord("j")):
                    file_cursor = min(file_cursor + 1, max(0, len(s.episode_files) - 1))
                elif key in (curses.KEY_UP, ord("k")):
                    file_cursor = max(file_cursor - 1, 0)
                elif key in (10, 13, curses.KEY_ENTER) and s.episode_files:
                    note = play_and_track(media, s.episode_files[file_cursor], entry_info)
                elif key == ord("o"):
                    note = open_folder(s)
                else:
                    return

        while True:
            view = apply_view(rows, state, statuses)
            h, w = stdscr.getmaxyx()
            body = max(1, h - 4)
            cursor = min(cursor, max(0, len(view) - 1))
            if cursor < top:
                top = cursor
            if cursor >= top + body:
                top = cursor - body + 1

            stdscr.erase()
            fmt_f = ",".join(sorted(state.formats)) or "all"
            tag_f = (f"{','.join(sorted(state.tags))} ({state.tag_mode})" if state.tags else "all")
            label = SORT_OPTIONS[state.sort_key][0]
            put(0, 0, f"anifinder: {len(view)} of {len(rows)} not watched", curses.A_BOLD)
            status_f = ", ".join(STATUS_LABELS[st] for st in STATUS_ORDER if st in state.statuses) or "all"
            put(1, 0, f"format: {fmt_f} | tags: {tag_f} | list: {status_f} | sort: {label} "
                      f"{'desc' if state.desc else 'asc'}")

            aw = max(8, w - 80)
            put(2, 0, f"{'#':>4}  {'Local name':<28}  {'AniList name':<{aw}}  {'Status':<12}  "
                      f"{'Scr':>3}  {'Eps':>3}  {'Year':>4}  Format", curses.A_UNDERLINE)
            if not view:
                put(4, 2, "No entries match the current filters. Press c to clear them.")
            for i, (s, media) in enumerate(view[top: top + body]):
                pos = top + i
                score = media.get("averageScore") or "-"
                eps = media.get("episodes") or "?"
                year = media_year(media) or "-"
                status = STATUS_LABELS[list_status(statuses, media)]
                line = (f"{pos + 1:>4}  {s.label[:28]:<28}  {display_name(media)[:aw]:<{aw}}  {status:<12}  "
                        f"{str(score):>3}  {str(eps):>3}  {str(year):>4}  {media.get('format') or '-'}")
                put(3 + i, 0, line, curses.A_REVERSE if pos == cursor else 0)
            put(h - 2, 0, message)
            put(h - 1, 0, "j/k move  f formats  t tags  l status  s sort  r reverse  c clear  x random  enter details  q quit")
            stdscr.refresh()
            message = ""

            key = stdscr.getch()
            if key in (ord("q"), 27):
                return
            if key in (curses.KEY_DOWN, ord("j")):
                cursor = min(cursor + 1, max(0, len(view) - 1))
            elif key in (curses.KEY_UP, ord("k")):
                cursor = max(cursor - 1, 0)
            elif key == curses.KEY_NPAGE:
                cursor = min(cursor + body, max(0, len(view) - 1))
            elif key == curses.KEY_PPAGE:
                cursor = max(cursor - body, 0)
            elif key in (ord("g"), curses.KEY_HOME):
                cursor = 0
            elif key in (ord("G"), curses.KEY_END):
                cursor = max(0, len(view) - 1)
            elif key == ord("f"):
                pick_formats()
                cursor = 0
            elif key == ord("t"):
                pick_tags()
                cursor = 0
            elif key == ord("l"):
                pick_statuses()
                cursor = 0
            elif key == ord("s"):
                pick_sort()
            elif key == ord("r"):
                state.desc = not state.desc
            elif key == ord("c"):
                state.clear_filters()
                cursor = 0
            elif key == ord("x") and view:
                cursor = random.randrange(len(view))
                message = f"Random pick: {display_name(view[cursor][1])}  (enter for details)"
            elif key in (10, 13, curses.KEY_ENTER) and view:
                s, media = view[cursor]
                details(media, s)

    curses.wrapper(app)


# ---------------------------------------------------------------- main

def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return None


def load_aliases(path: Path) -> dict[str, str | int]:
    data = load_json(path)
    if not isinstance(data, dict):
        return {}
    return {norm_key(k): v for k, v in data.items() if isinstance(v, (str, int))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, nargs="?", help="directory containing your downloaded anime")
    parser.add_argument("-u", "--user", default=os.environ.get("ANILIST_USER"),
                        help="your AniList username (or set ANILIST_USER)")
    parser.add_argument("-n", "--limit", type=int, default=0,
                        help="without the TUI, only print the top N suggestions (default: all)")
    parser.add_argument("--no-tui", action="store_true", help="print a plain table instead of the interactive list")
    parser.add_argument("--refresh", action="store_true", help="ignore cached AniList results and the watched list")
    parser.add_argument("--cache-days", type=float, default=DEFAULT_CACHE_DAYS,
                        help=f"how many days AniList results are reused (default: {DEFAULT_CACHE_DAYS})")
    parser.add_argument("--cache", type=Path, default=DEFAULT_CACHE, help="cache file")
    parser.add_argument("--aliases", type=Path, default=DEFAULT_ALIASES,
                        help="JSON file mapping local names to AniList titles or IDs")
    parser.add_argument("--login", action="store_true", help="save an AniList access token to track progress")
    parser.add_argument("--logout", action="store_true", help="delete the saved AniList access token")
    args = parser.parse_args()

    if args.login:
        return login()
    if args.logout:
        return logout()
    if not args.directory:
        parser.error("a directory is required")
    if not args.user:
        parser.error("an AniList username is required (--user or ANILIST_USER)")
    if not args.directory.is_dir():
        parser.error(f"not a directory: {args.directory}")

    series = scan_directory(args.directory)
    if not series:
        print("No video files found.")
        return 0
    print(f"Found {len(series)} series in {args.directory}")

    use_cache = not args.refresh
    max_age = args.cache_days * 86400
    cache = load_cache(args.cache)

    def save() -> None:
        save_cache(args.cache, cache)

    try:
        print(f"Fetching list for '{args.user}'...")
        statuses = fetch_statuses_cached(args.user, cache, use_cache)
        print(f"  {len(statuses)} entries on AniList")

        # Work out how each series is looked up: by alias ID, by alias title, or by its own name.
        aliases = load_aliases(args.aliases)
        by_id: dict[int, int] = {}  # keyed by id(series): Series is not hashable
        for s in series.values():
            # A season-specific key ("Name S2") wins over a name-only key, which applies to every season.
            alias = aliases.get(norm_key(s.label))
            if alias is None:
                alias = aliases.get(norm_key(s.name))
            if isinstance(alias, int):
                by_id[id(s)] = alias
            elif isinstance(alias, str):
                s.query = alias

        names = [s.query for s in series.values() if id(s) not in by_id]
        print(f"Looking up {len(series)} series on AniList...")
        results = fetch_search_results(names, cache, use_cache, max_age, save)

        to_watch: list[tuple[Series, dict[str, Any]]] = []
        unmatched: list[Series] = []
        for s in sorted(series.values(), key=lambda s: (s.name.lower(), s.season or 0)):
            if id(s) in by_id:
                media = media_by_id_cached(by_id[id(s)], cache, use_cache, max_age)
            else:
                media = best_match(s, results.get(s.query, []))
            if media is None:
                unmatched.append(s)
            else:
                to_watch.append((s, media))
    except AniListError as e:
        print(f"error: {e}", file=sys.stderr)
        save()
        return 1
    save()

    to_watch.sort(key=lambda r: (-(r[1].get("averageScore") or 0), r[0].label.lower()))
    shown_default = [r for r in to_watch if list_status(statuses, r[1]) in DEFAULT_LIST_STATUSES]
    print(f"\nOn your list: {len(to_watch)} matched; {len(shown_default)} shown by default "
          f"(Planning, Watching, Not on list). The rest are in the status filter.")

    print(f"\nCould not match on AniList ({len(unmatched)}), check the names:")
    print("  " + ", ".join(s.label for s in unmatched) if unmatched else "  (none)")
    if unmatched:
        print(f"  Add them to {args.aliases} as {{\"name\": \"AniList title\"}} or {{\"name\": <AniList ID>}}.")

    interactive = sys.stdin.isatty() and sys.stdout.isatty() and not args.no_tui
    if not to_watch:
        print("\nNothing matched.")
    elif interactive:
        session, login_note = load_session()
        run_tui(to_watch, statuses, session, login_note)
    elif not shown_default:
        print("\nNothing to show by default. Run in a terminal and press l to pick other statuses.")
    else:
        shown = shown_default[: args.limit] if args.limit else shown_default
        print(f"\nShown by default ({len(shown_default)}), best rated first:")
        print_table(shown, statuses)
        if args.limit and len(shown_default) > args.limit:
            print(f"  ... {len(shown_default) - args.limit} more (use without --limit to see all)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)

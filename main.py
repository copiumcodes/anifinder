#!/usr/bin/env python3
"""anifinder: find downloaded anime you have not watched yet, using AniList.

Scans a directory for video files, works out the series and season of each
one from its name, looks it up on AniList, and removes everything that appears
in your AniList list with a watched status. What is left is shown in an
interactive list where you can filter by format or tag and change the sort.

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
c clear filters, x random pick, Enter details (o in details opens the folder), q quit.

Only the standard library is used. The AniList profile list must be public
(AniList's GraphQL API does not return private lists without an auth token).
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import random
import re
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
# AniList list statuses that count as "already watched"
WATCHED_STATUSES = {"COMPLETED", "CURRENT", "REPEATING", "PAUSED", "DROPPED"}
MATCH_THRESHOLD = 0.6
FORMAT_BONUS = {"TV": 0.1, "TV_SHORT": 0.1, "ONA": 0.05}
YEAR_BONUS = 0.05        # AniList air year equals a season folder's year
SEASON_MATCH_BONUS = 0.1
SEASON_MISMATCH_PENALTY = 0.15
SEASON_ONE_BONUS = 0.02  # when the name has no season, prefer season 1 among similar entries
MAX_QUERIES = 6          # AniList searches per series
REQUEST_DELAY = 0.8      # AniList allows ~90 requests/minute
CACHE_VERSION = "v4"     # bump when the fields requested from AniList change
TAG_MIN_RANK = 60        # ignore AniList tags ranked below this (they are often noise)

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

DEFAULT_CACHE = Path.home() / ".cache" / "anifinder" / "search.json"
DEFAULT_ALIASES = Path.home() / ".config" / "anifinder" / "aliases.json"


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


# ---------------------------------------------------------------- scanning

@dataclass
class Series:
    name: str
    season: int | None = None
    files: int = 0
    years: set[int] = field(default_factory=set)
    labels: set[str] = field(default_factory=set)
    folders: set[Path] = field(default_factory=set)  # where the files are on disk
    query: str = ""  # what is actually searched on AniList (may come from an alias)

    def __post_init__(self) -> None:
        self.query = self.query or self.name

    @property
    def label(self) -> str:
        return f"{self.name} S{self.season}" if self.season else self.name


def scan_directory(root: Path) -> dict[tuple[str, int | None], Series]:
    series: dict[tuple[str, int | None], Series] = {}
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix.lower() not in VIDEO_EXTENSIONS:
            continue
        rel = path.relative_to(root)
        label, year, raw, depth = classify(rel.parts)
        name, season = parse_name(raw)
        entry = series.setdefault((norm_key(name), season), Series(name, season))
        entry.files += 1
        entry.folders.add(root.joinpath(*rel.parts[:depth]) if depth else path.parent)
        if label:
            entry.labels.add(label)
        if year:
            entry.years.add(year)
    return series


# ---------------------------------------------------------------- AniList

class AniListError(RuntimeError):
    pass


def graphql(query: str, variables: dict[str, Any], retries: int = 4) -> dict[str, Any]:
    body = json.dumps({"query": query, "variables": variables}).encode()
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "User-Agent": USER_AGENT,
    }
    for attempt in range(retries):
        req = urllib.request.Request(ANILIST_URL, data=body, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                payload = json.loads(resp.read().decode())
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < retries - 1:
                wait = int(e.headers.get("Retry-After", "60"))
                print(f"  rate limited by AniList, waiting {wait}s...", file=sys.stderr)
                time.sleep(wait)
                continue
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

SEARCH_QUERY = f"""
query ($search: String) {{
  Page(perPage: 8) {{
    media(search: $search, type: ANIME, sort: SEARCH_MATCH) {{ {MEDIA_FIELDS} }}
  }}
}}
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


def fetch_watched_ids(user: str) -> set[int]:
    data = graphql(WATCHED_QUERY, {"name": user})
    collection = data.get("MediaListCollection") or {}
    watched: set[int] = set()
    for lst in collection.get("lists", []):
        for entry in lst.get("entries", []):
            status = entry.get("status") or lst.get("status")
            if status in WATCHED_STATUSES:
                watched.add(entry["media"]["id"])
    return watched


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
    return [v for _, v in variants][:MAX_QUERIES]


def search(name: str, cache: dict[str, Any], use_cache: bool) -> list[dict[str, Any]]:
    key = f"{CACHE_VERSION}|{name}"
    if use_cache and key in cache:
        return cache[key]
    seen: dict[int, dict[str, Any]] = {}
    for query in query_variants(name):
        results = graphql(SEARCH_QUERY, {"search": query})["Page"]["media"]
        time.sleep(REQUEST_DELAY)
        for media in results:
            seen.setdefault(media["id"], media)
        # Stop early once a result is clearly the right title.
        if any(similarity(query, t) >= 0.9 for m in results for t in titles_of(m)):
            break
    merged = list(seen.values())
    cache[key] = merged
    return merged


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return None


def load_cache(path: Path) -> dict[str, Any]:
    return load_json(path) or {}


def save_cache(path: Path, cache: dict[str, Any]) -> None:
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(cache, indent=1))
    except OSError as e:
        print(f"warning: could not write cache: {e}", file=sys.stderr)


def load_aliases(path: Path) -> dict[str, str | int]:
    data = load_json(path)
    if not isinstance(data, dict):
        return {}
    return {norm_key(k): v for k, v in data.items() if isinstance(v, (str, int))}


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

    def reset_sort(self, key: str) -> None:
        self.sort_key = key
        self.desc = SORT_OPTIONS[key][2]

    def clear_filters(self) -> None:
        self.formats.clear()
        self.tags.clear()
        self.tag_mode = "any"


def apply_view(rows: list[tuple[Series, dict[str, Any]]], state: ViewState) -> list[tuple[Series, dict[str, Any]]]:
    out = []
    for s, media in rows:
        if state.formats and (media.get("format") or "") not in state.formats:
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


# ---------------------------------------------------------------- output

def print_table(rows: list[tuple[Series, dict[str, Any]]]) -> None:
    if not rows:
        print("  (none)")
        return
    header = f"  {'Local name':<34} {'Folder':<12} {'AniList name':<40} {'Score':>5} {'Eps':>5} {'Files':>5}  Format"
    print(header)
    print("  " + "-" * (len(header) - 2))
    for s, media in rows:
        score = media.get("averageScore")
        eps = media.get("episodes")
        folder = ",".join(sorted(s.labels))[:12] or "-"
        print(
            f"  {s.label[:34]:<34} "
            f"{folder:<12} "
            f"{display_name(media)[:40]:<40} "
            f"{(str(score) if score else '-'):>5} "
            f"{(str(eps) if eps else '?'):>5} "
            f"{s.files:>5}  {media.get('format') or '-'}"
        )


# ---------------------------------------------------------------- TUI

def run_tui(rows: list[tuple[Series, dict[str, Any]]]) -> None:
    import curses  # imported here so the rest of the tool does not need a terminal

    def app(stdscr: "curses.window") -> None:
        curses.curs_set(0)
        state = ViewState()
        cursor = top = 0
        message = ""

        def put(y: int, x: int, text: str, attr: int = 0) -> None:
            h, w = stdscr.getmaxyx()
            if 0 <= y < h and x < w:
                try:
                    stdscr.addnstr(y, x, text, max(0, w - x - 1), attr)
                except curses.error:
                    pass

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

        def pick_sort() -> None:
            items = [(k, label) for k, (label, _, _) in SORT_OPTIONS.items()]
            result = checklist(lambda: "Sort by (enter to choose)", items, {state.sort_key}, single=True)
            if result:
                state.reset_sort(next(iter(result)))

        def details(media: dict[str, Any], s: Series) -> None:
            stdscr.erase()
            t = media["title"]
            lines = [
                ("AniList", display_name(media)),
                ("Romaji", t.get("romaji") or "-"),
                ("Native", t.get("native") or "-"),
                ("Local name", s.label),
                ("Local files", str(s.files)),
                ("Folder", ", ".join(sorted(s.labels)) or "-"),
                ("Path", ", ".join(str(p) for p in sorted(s.folders)) or "-"),
                ("Format", media.get("format") or "-"),
                ("Episodes", str(media.get("episodes") or "?")),
                ("Score", str(media.get("averageScore") or "-")),
                ("Year", str(media_year(media) or "-")),
                ("Genres", ", ".join(media.get("genres") or []) or "-"),
            ]
            tags = sorted((t for t in media.get("tags") or [] if (t.get("rank") or 0) >= TAG_MIN_RANK),
                          key=lambda t: -(t.get("rank") or 0))
            lines.append(("Tags", ", ".join(f"{t['name']} ({t['rank']})" for t in tags[:15]) or "-"))
            lines.append(("AniList", f"https://anilist.co/anime/{media['id']}"))
            note = ""
            while True:
                stdscr.erase()
                put(0, 0, "Details", curses.A_BOLD)
                for i, (k, v) in enumerate(lines):
                    put(2 + i, 2, f"{k}:", curses.A_BOLD)
                    put(2 + i, 16, v)
                h, _ = stdscr.getmaxyx()
                put(h - 2, 0, note)
                put(h - 1, 0, "o open folder  |  any other key: back")
                stdscr.refresh()
                if stdscr.getch() != ord("o"):
                    return
                note = open_folder(s)

        while True:
            view = apply_view(rows, state)
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
            put(1, 0, f"format: {fmt_f} | tags: {tag_f} | sort: {label} {'desc' if state.desc else 'asc'}")

            aw = max(8, w - 66)
            put(2, 0, f"{'#':>4}  {'Local name':<28}  {'AniList name':<{aw}}  {'Scr':>3}  {'Eps':>3}  {'Year':>4}  Format",
                curses.A_UNDERLINE)
            if not view:
                put(4, 2, "No entries match the current filters. Press c to clear them.")
            for i, (s, media) in enumerate(view[top: top + body]):
                pos = top + i
                score = media.get("averageScore") or "-"
                eps = media.get("episodes") or "?"
                year = media_year(media) or "-"
                line = (f"{pos + 1:>4}  {s.label[:28]:<28}  {display_name(media)[:aw]:<{aw}}  "
                        f"{str(score):>3}  {str(eps):>3}  {str(year):>4}  {media.get('format') or '-'}")
                put(3 + i, 0, line, curses.A_REVERSE if pos == cursor else 0)
            put(h - 2, 0, message)
            put(h - 1, 0, "j/k move  f formats  t tags  s sort  r reverse  c clear  x random  enter details  q quit")
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

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, help="directory containing your downloaded anime")
    parser.add_argument("-u", "--user", default=os.environ.get("ANILIST_USER"),
                        help="your AniList username (or set ANILIST_USER)")
    parser.add_argument("-n", "--limit", type=int, default=0,
                        help="without the TUI, only print the top N suggestions (default: all)")
    parser.add_argument("--no-tui", action="store_true", help="print a plain table instead of the interactive list")
    parser.add_argument("--refresh", action="store_true", help="ignore cached AniList search results")
    parser.add_argument("--cache", type=Path, default=DEFAULT_CACHE, help="search cache file")
    parser.add_argument("--aliases", type=Path, default=DEFAULT_ALIASES,
                        help="JSON file mapping local names to AniList titles or IDs")
    args = parser.parse_args()

    if not args.user:
        parser.error("an AniList username is required (--user or ANILIST_USER)")
    if not args.directory.is_dir():
        parser.error(f"not a directory: {args.directory}")

    series = scan_directory(args.directory)
    if not series:
        print("No video files found.")
        return 0
    print(f"Found {len(series)} series in {args.directory}")

    try:
        print(f"Fetching watched list for '{args.user}'...")
        watched = fetch_watched_ids(args.user)
        print(f"  {len(watched)} watched entries on AniList")
    except AniListError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    aliases = load_aliases(args.aliases)
    cache = load_cache(args.cache)
    to_watch: list[tuple[Series, dict[str, Any]]] = []
    already: list[tuple[Series, dict[str, Any]]] = []
    unmatched: list[Series] = []

    try:
        ordered = sorted(series.values(), key=lambda s: (s.name.lower(), s.season or 0))
        for i, s in enumerate(ordered, 1):
            print(f"\r  matching {i}/{len(ordered)}: {s.label[:40]:<40}", end="", flush=True)
            # A season-specific key ("Name S2") wins over a name-only key, which applies to every season.
            alias = aliases.get(norm_key(s.label))
            if alias is None:
                alias = aliases.get(norm_key(s.name))
            if isinstance(alias, int):
                media = graphql(MEDIA_BY_ID_QUERY, {"id": alias})["Media"]
            else:
                if isinstance(alias, str):
                    s.query = alias
                media = best_match(s, search(s.query, cache, use_cache=not args.refresh))
            if media is None:
                unmatched.append(s)
            elif media["id"] in watched:
                already.append((s, media))
            else:
                to_watch.append((s, media))
    except AniListError as e:
        print(f"\nerror: {e}", file=sys.stderr)
        save_cache(args.cache, cache)
        return 1
    print()
    save_cache(args.cache, cache)

    to_watch.sort(key=lambda r: (-(r[1].get("averageScore") or 0), r[0].label.lower()))
    already.sort(key=lambda r: r[0].label.lower())

    print(f"\nAlready watched, skipped ({len(already)}):")
    print("  " + ", ".join(f"{s.label} = {display_name(m)}" for s, m in already) if already else "  (none)")

    print(f"\nCould not match on AniList ({len(unmatched)}), check the names:")
    print("  " + ", ".join(s.label for s in unmatched) if unmatched else "  (none)")
    if unmatched:
        print(f"  Add them to {args.aliases} as {{\"name\": \"AniList title\"}} or {{\"name\": <AniList ID>}}.")

    interactive = sys.stdin.isatty() and sys.stdout.isatty() and not args.no_tui
    if not to_watch:
        print("\nNothing left to watch.")
    elif interactive:
        run_tui(to_watch)
    else:
        shown = to_watch[: args.limit] if args.limit else to_watch
        print(f"\nNot watched yet ({len(to_watch)}), best rated first:")
        print_table(shown)
        if args.limit and len(to_watch) > args.limit:
            print(f"  ... {len(to_watch) - args.limit} more (use without --limit to see all)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)

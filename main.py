#!/usr/bin/env python3
"""anifinder: find downloaded anime you have not watched yet, using AniList.

Scans a directory for video files, works out the series and season of each
one from its name, looks it up on AniList, and removes everything that appears
in your AniList list with a watched status. What is left is what you can pick
from.

Understands folders sorted by season ("2024-winter", "2023-fall", "2022-movies",
including misspellings such as "2026-sping"). Files directly inside those
folders are named by their file name; a series folder inside them is named by
the folder.

If a name still cannot be matched, add it to the aliases file
(default ~/.config/anifinder/aliases.json) as {"local name": "AniList title"}
or {"local name": 12345} with an AniList media ID. For one season of a show,
use the season in the key, e.g. {"Aharen Is Indecipherable S2": 179979}; a key
without a season applies to every season.

Only the standard library is used. The AniList profile list must be public
(AniList's GraphQL API does not return private lists without an auth token).
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

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
CACHE_VERSION = "v3"     # bump when the fields requested from AniList change

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


def classify(rel_parts: tuple[str, ...]) -> tuple[str | None, int | None, str]:
    """Return (season folder, season year, raw series name) for a file path relative to the root."""
    dirs, filename = rel_parts[:-1], rel_parts[-1]
    stem = Path(filename).stem
    for i, part in enumerate(dirs):
        year = season_folder_year(part)
        if year is not None:
            raw = dirs[i + 1] if i + 1 < len(dirs) else stem
            return part, year, raw
    return None, None, dirs[0] if dirs else stem


# ---------------------------------------------------------------- scanning

@dataclass
class Series:
    name: str
    season: int | None = None
    files: int = 0
    years: set[int] = field(default_factory=set)
    labels: set[str] = field(default_factory=set)
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
        label, year, raw = classify(path.relative_to(root).parts)
        name, season = parse_name(raw)
        entry = series.setdefault((norm_key(name), season), Series(name, season))
        entry.files += 1
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


# ---------------------------------------------------------------- output

def display_name(media: dict[str, Any]) -> str:
    t = media["title"]
    return t.get("english") or t.get("romaji") or t.get("native") or "?"


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


# ---------------------------------------------------------------- main

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, help="directory containing your downloaded anime")
    parser.add_argument("-u", "--user", default=os.environ.get("ANILIST_USER"),
                        help="your AniList username (or set ANILIST_USER)")
    parser.add_argument("-n", "--limit", type=int, default=0,
                        help="only show the top N suggestions (default: all)")
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

    def sort_key(row):
        s, media = row
        return (-(media.get("averageScore") or 0), s.name.lower(), s.season or 0)

    to_watch.sort(key=sort_key)
    already.sort(key=sort_key)

    shown = to_watch[: args.limit] if args.limit else to_watch
    print(f"\nNot watched yet ({len(to_watch)}), best rated first:")
    print_table(shown)
    if args.limit and len(to_watch) > args.limit:
        print(f"  ... {len(to_watch) - args.limit} more (use without --limit to see all)")

    print(f"\nAlready watched, skipped ({len(already)}):")
    print("  " + ", ".join(f"{s.label} = {display_name(m)}" for s, m in already) if already else "  (none)")

    print(f"\nCould not match on AniList ({len(unmatched)}), check the names:")
    print("  " + ", ".join(s.label for s in unmatched) if unmatched else "  (none)")
    if unmatched:
        print(f"  Add them to {args.aliases} as {{\"name\": \"AniList title\"}} or {{\"name\": <AniList ID>}}.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)

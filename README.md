# anifinder

Finds the anime you have downloaded but not watched yet. It reads your video
files, matches them to [AniList](https://anilist.co), and shows what is left in
an interactive list. You can filter and sort the list, see which episodes you
have, play episodes, and update your AniList progress and score.

## Requirements

- Python 3 (tested with 3.14). Only the standard library is used.
- Linux or macOS for the interactive list (it uses `curses`).
- Optional: `mpv` or `vlc` for playback, and `xdg-open` to open folders.
  Set `ANIFINDER_PLAYER` to use a different player.

## Quick start

```
python main.py ~/Videos/Anime -u YOUR_ANILIST_USERNAME
```

Your AniList list must be public, unless you log in (see below).

## Folder layout

The script works with any layout, but it understands folders sorted by season:

```
Anime/
  2024-winter/
    Frieren/
      [Group] Frieren - 01.mkv
  2023-fall/
    [SubsPlease] Mob Psycho 100 - 05 (1080p).mkv
  2022-movies/
    Your Name (2016).mkv
```

- `yyyy-season` and `yyyy-movies` folders are recognised, including small typos
  such as `2026-sping`.
- A series folder inside a season folder gives the series name.
- Without a series folder, the file name gives the series name.
- Episode numbers come from the file name (`S01E05`, `E05`, ` - 05`, `[05]`, ...).

## Options

| Option | Meaning |
| --- | --- |
| `-u`, `--user` | AniList username (or set `ANILIST_USER`) |
| `--no-tui` | Print a plain table instead of the interactive list |
| `-n`, `--limit N` | With `--no-tui`, show only the first N entries |
| `--include-missing` | Start with entries you have no files for included |
| `--refresh` | Ignore the cache and fetch everything again |
| `--cache-days N` | How long AniList search results are reused (default 7) |
| `--cache FILE` | Cache file (default `~/.cache/anifinder/search.json`) |
| `--aliases FILE` | Aliases file (default `~/.config/anifinder/aliases.json`) |
| `--login` | Save an AniList access token, so progress can be updated |
| `--logout` | Delete the saved token |

## Interactive list

| Key | Action |
| --- | --- |
| `j` / `k`, arrows | Move |
| `Enter` | Open the details view |
| `f` | Filter by format |
| `t` | Filter by tag or genre (`m` switches between "any" and "all") |
| `l` | Filter by your AniList status (Planning, Watching, Not on list by default) |
| `d` | Include or hide entries you have no files for |
| `s` | Choose the sort order |
| `r` | Reverse the sort |
| `x` | Pick a random entry |
| `c` | Clear filters |
| `q` | Quit |

In the details view, `j`/`k` select an episode file, `Enter` plays it, and
`o` opens the series folder. Any other key goes back.

## Logging in (progress and scores)

Logging in lets the script update your progress when you play an episode.

```
python main.py --login
```

You will need an AniList access token. The login prompt explains how to get one.
The token is saved to `~/.config/anifinder/token`, readable only by you. You can
also set `ANILIST_TOKEN` instead. Run `python main.py --logout` to remove the
saved token.

When you play episode N:

- your progress is set to N, but never lowered;
- the show is marked Completed when you play its last episode;
- you are asked for a score. Press Enter to keep your current score.

Progress is saved when the episode starts, not when it finishes.

## Aliases

If a series is not matched to the right AniList entry, add it to the aliases file:

```json
{
  "Kaiko sareta Ankoku Geishi no Slow na Second Life": 152523,
  "Aharen Is Indecipherable S2": 179979,
  "Rich Girl Caretaker": "Rich Girl Caretaker"
}
```

Values can be an AniList ID (a number) or a title to search for. A key with a
season (`S2`) applies to that season only. A key without one applies to every season.

## Caching

AniList results are cached in `~/.cache/anifinder/search.json`. Search results
are reused for 7 days, and your list for one hour. Several searches are sent in
one request. Use `--refresh` to skip the cache for one run.

## Limitations

- Matching is by name, so unusual names may match the wrong entry. Check the
  "Could not match" output and use aliases for those.
- Matching is per series and season. Each season is its own entry in the list.
- Episode numbers are read from file names. Files without a number are listed
  without one.
- Your AniList list must be public unless you log in.
- The login steps and the way progress is saved have not been tested against
  the live AniList service.

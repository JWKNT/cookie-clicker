# Cookie Monster+ patcher

This patcher installs Cookie Monster+ in the Steam version of *Cookie Clicker*.
Cookie Monster+ is a version of the Cookie Monster mod with mathematically
optimal autoplay. The guide at <https://jehlp.net/cookie-clicker/> explains
the rules that it plays by.

## Before you start

- Subscribe to Cookie Monster in the Steam Workshop. Start the game once, so
  that Steam downloads it.
- Install Python 3.9 or newer.
- Keep a copy of your save.

## Install

1. Extract the archive.
2. On macOS, double-click `Install Cookie Monster Plus.command`. On Windows,
   double-click `Install Cookie Monster Plus.bat`. On Linux, run
   `python3 install_cookie_monster_plus.py`.
3. If the patcher does not find the game, drag the Cookie Clicker folder into
   the window and press Return.
4. Restart Cookie Clicker. The autoplay settings are in Options, under
   Cookie Monster.

If macOS blocks the `.command` file, Control-click it and select Open.

## Command line

```sh
python3 install_cookie_monster_plus.py ["/path/to/Cookie Clicker"]
python3 install_cookie_monster_plus.py --verify
python3 install_cookie_monster_plus.py --uninstall
```

| Option | Effect |
| --- | --- |
| `--verify` | Check the installed files against the release. |
| `--uninstall` | Remove Cookie Monster+. Its files move to the backup folder. |
| `--offline` | Install the files in this archive. Do not download. |
| `--version 2.053.13` | Install this release instead of the latest one. |
| `--force` | Install even if Cookie Monster is not installed. |

## What the patcher changes

- It writes `mods/local/Cookie Monster Plus` in the game folder: `info.txt`,
  `main.js`, `thumbnail.png` and the license files.
- It moves an earlier, different copy to `mods/.cookie-monster-plus-backups`.
  The game does not load mods from that folder.
- It does not change the Workshop copy of Cookie Monster, because Steam
  replaces Workshop files when the game starts. If both mods are on, only
  Cookie Monster+ runs.
- It does not change your save.

## Verification

The patcher downloads `mod/manifest.json` from
<https://github.com/JWKNT/cookie-clicker> and checks the SHA-256 digest of
every file before it changes the game. If the download fails, it uses the
files in this archive after the same check. The patcher writes the files to a
temporary folder first and moves them into place only after they verify.

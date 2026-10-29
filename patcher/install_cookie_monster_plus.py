#!/usr/bin/env python3
"""Install, verify or remove Cookie Monster+ in the Steam version of Cookie Clicker.

Cookie Monster+ extends the Cookie Monster mod. Install Cookie Monster from the
Steam Workshop first. This patcher then downloads the current Cookie Monster+
build, checks every file against its published SHA-256 digest and installs the
build as a local mod. It never changes the Workshop copy of Cookie Monster,
because Steam replaces Workshop files when the game starts.

Python 3.9 or newer is the only requirement.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path

VERSION = "2.053.12"
REPOSITORY = "JWKNT/cookie-clicker"
RAW_BASE = f"https://raw.githubusercontent.com/{REPOSITORY}"
PAGE = "https://jehlp.net/cookie-clicker/"
MOD_FOLDER = "Cookie Monster Plus"
MOD_ID = "cookie monster plus"
BASE_MOD_ID = "cookie monster"
BACKUP_FOLDER = ".cookie-monster-plus-backups"
GAME_VERSION = "2.053"
PATCHER = Path(__file__).resolve().parent


class PatchError(Exception):
    """A problem that stops the installation before the game files change."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalized_id(info: dict) -> str:
    """Mod ID as the game compares it: each run of non-word characters becomes one space."""
    return re.sub(r"\W+", " ", str(info.get("ID", ""))).strip().lower()


def read_info(path: Path) -> dict | None:
    try:
        info = json.loads(path.read_text(encoding="utf-8-sig"))
    except (OSError, ValueError):
        return None
    return info if isinstance(info, dict) and info.get("Name") and info.get("ID") else None


def parse_dragged_path(value: str, system: str | None = None) -> str:
    """Read a folder path typed or dragged into the terminal."""
    value = value.strip()
    if not value:
        raise PatchError("No game folder was supplied.")
    if (system or platform.system()) == "Windows":
        return value.strip('"').strip("'")
    try:
        values = shlex.split(value)
    except ValueError as error:
        raise PatchError(f"Could not read the dragged path: {error}") from error
    if len(values) != 1:
        raise PatchError("Drag exactly one folder into the window.")
    return values[0]


def app_folder(path: Path) -> Path | None:
    """Return the folder that holds the game's mods folder, from any folder near it."""
    path = Path(path).expanduser()
    if path.is_file():
        path = path.parent
    candidates = [
        path,
        path / "resources" / "app",
        path / "Cookie Clicker.app" / "Contents" / "Resources" / "app",
        path / "Contents" / "Resources" / "app",
        path / "Resources" / "app",
    ]
    if path.name == "mods":
        candidates.insert(0, path.parent)
    if path.name in ("local", "workshop") and path.parent.name == "mods":
        candidates.insert(0, path.parent.parent)
    for candidate in candidates:
        if (candidate / "mods").is_dir() and (
            (candidate / "start.js").is_file() or (candidate / "mods" / "local").is_dir()
        ):
            return candidate.resolve()
    return None


def steam_libraries() -> list[Path]:
    """Steam library folders: the default install and those listed in libraryfolders.vdf."""
    home = Path.home()
    system = platform.system()
    if system == "Darwin":
        roots = [home / "Library" / "Application Support" / "Steam"]
    elif system == "Windows":
        roots = [Path(os.environ[name]) / "Steam" for name in ("PROGRAMFILES(X86)", "PROGRAMFILES")
                 if os.environ.get(name)]
        roots.append(Path("C:/Program Files (x86)/Steam"))
    else:
        roots = [
            home / ".steam" / "steam",
            home / ".local" / "share" / "Steam",
            home / ".var" / "app" / "com.valvesoftware.Steam" / ".local" / "share" / "Steam",
        ]
    libraries: list[Path] = []
    for root in roots:
        libraries.append(root)
        vdf = root / "steamapps" / "libraryfolders.vdf"
        try:
            text = vdf.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for match in re.finditer(r'"path"\s+"([^"]+)"', text):
            libraries.append(Path(match.group(1).replace("\\\\", "\\")))
    unique: list[Path] = []
    for library in libraries:
        if library not in unique:
            unique.append(library)
    return unique


def find_game() -> Path | None:
    for library in steam_libraries():
        app = app_folder(library / "steamapps" / "common" / "Cookie Clicker")
        if app:
            return app
    return None


def installed_mods(app: Path) -> list[tuple[Path, dict]]:
    mods = []
    for kind in ("workshop", "local"):
        folder = app / "mods" / kind
        if not folder.is_dir():
            continue
        for child in sorted(folder.iterdir()):
            info = read_info(child / "info.txt") if child.is_dir() else None
            if info:
                mods.append((child, info))
    return mods


def find_cookie_monster(app: Path) -> Path | None:
    for folder, info in installed_mods(app):
        if normalized_id(info) == BASE_MOD_ID:
            return folder
    return None


def game_version(app: Path) -> str | None:
    try:
        text = (app / "src" / "main.js").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    match = re.search(r"Game\.version\s*=\s*([0-9.]+)", text)
    return match.group(1) if match else None


def fetch(url: str) -> bytes:
    """Download a file. Use curl when Python has no certificate store (common on macOS)."""
    request = urllib.request.Request(url, headers={"User-Agent": f"cookie-monster-plus-patcher/{VERSION}"})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            return response.read()
    except (urllib.error.URLError, OSError) as error:
        curl = shutil.which("curl")
        if not curl:
            raise PatchError(f"Could not download {url}: {error}") from error
        result = subprocess.run([curl, "-fsSL", "--max-time", "120", url], capture_output=True, check=False)
        if result.returncode != 0:
            raise PatchError(f"Could not download {url}: {error}") from error
        return result.stdout


def check_manifest(manifest: object) -> dict:
    if not isinstance(manifest, dict) or not isinstance(manifest.get("files"), dict) or not manifest["files"]:
        raise PatchError("The release manifest is not valid.")
    for name, entry in manifest["files"].items():
        if "/" in name or "\\" in name or name.startswith(".") or not isinstance(entry, dict):
            raise PatchError(f"The release manifest lists a file that is not valid: {name}")
        if not re.fullmatch(r"[0-9a-f]{64}", str(entry.get("sha256", ""))):
            raise PatchError(f"The release manifest has no valid digest for {name}.")
    return manifest


def verified_files(manifest: dict, read) -> dict[str, bytes]:
    """Read every file in the manifest and check its SHA-256 digest."""
    files = {}
    for name, entry in manifest["files"].items():
        data = read(name)
        if sha256(data) != entry["sha256"]:
            raise PatchError(f"{name} does not match its published SHA-256 digest.")
        files[name] = data
    return files


def bundled_folder() -> Path | None:
    for folder in (PATCHER / "mod", PATCHER.parent / "mod"):
        if (folder / "manifest.json").is_file():
            return folder
    return None


def load_bundled() -> tuple[dict, dict[str, bytes]]:
    folder = bundled_folder()
    if folder is None:
        raise PatchError("This copy of the patcher has no bundled mod files.")
    manifest = check_manifest(json.loads((folder / "manifest.json").read_text(encoding="utf-8")))
    return manifest, verified_files(manifest, lambda name: (folder / name).read_bytes())


def load_download(ref: str) -> tuple[dict, dict[str, bytes]]:
    base = f"{RAW_BASE}/{ref}/mod"
    try:
        manifest = check_manifest(json.loads(fetch(f"{base}/manifest.json").decode("utf-8")))
    except ValueError as error:
        raise PatchError(f"The release manifest could not be read: {error}") from error
    return manifest, verified_files(manifest, lambda name: fetch(f"{base}/{name}"))


def load_release(offline: bool, version: str | None) -> tuple[dict, dict[str, bytes], str]:
    if offline:
        manifest, files = load_bundled()
        return manifest, files, "the bundled files"
    ref = f"v{version}" if version else "main"
    try:
        manifest, files = load_download(ref)
        return manifest, files, f"github.com/{REPOSITORY} ({ref})"
    except PatchError as error:
        if version or bundled_folder() is None:
            raise
        print(f"Download failed: {error}")
        print("Using the files bundled with this patcher instead.")
        manifest, files = load_bundled()
        return manifest, files, "the bundled files"


def matches(folder: Path, manifest: dict) -> bool:
    for name, entry in manifest["files"].items():
        path = folder / name
        if not path.is_file() or sha256(path.read_bytes()) != entry["sha256"]:
            return False
    return True


def move_to_backup(app: Path, folder: Path) -> Path:
    backups = app / "mods" / BACKUP_FOLDER
    backups.mkdir(parents=True, exist_ok=True)
    target = backups / f"{folder.name} {time.strftime('%Y-%m-%d %H%M%S')}"
    suffix = 1
    while target.exists():
        suffix += 1
        target = backups / f"{folder.name} {time.strftime('%Y-%m-%d %H%M%S')} {suffix}"
    shutil.move(str(folder), str(target))
    return target


def install(app: Path, manifest: dict, files: dict[str, bytes]) -> tuple[Path, Path | None]:
    """Write the mod into mods/local. A different earlier copy moves to the backup folder."""
    target = app / "mods" / "local" / MOD_FOLDER
    if target.is_dir() and matches(target, manifest) and not (set(p.name for p in target.iterdir()) - set(files)):
        return target, None
    target.parent.mkdir(parents=True, exist_ok=True)
    # Stage beside the local folder (the game only loads mods inside it), then move into place
    staging = Path(tempfile.mkdtemp(prefix=".cookie-monster-plus-", dir=app / "mods"))
    try:
        for name, data in files.items():
            (staging / name).write_bytes(data)
        if not matches(staging, manifest):
            raise PatchError("The staged files did not verify. The game was not changed.")
        backup = move_to_backup(app, target) if target.exists() else None
        shutil.move(str(staging), str(target))
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    return target, backup


def uninstall(app: Path) -> Path | None:
    target = app / "mods" / "local" / MOD_FOLDER
    return move_to_backup(app, target) if target.exists() else None


def choose_game(argument: str | None) -> Path:
    if argument:
        app = app_folder(Path(argument))
        if app is None:
            raise PatchError(f"No Cookie Clicker mods folder was found in {argument}.")
        return app
    app = find_game()
    if app:
        print(f"Found Cookie Clicker: {app}")
        return app
    if not sys.stdin.isatty():
        raise PatchError("Cookie Clicker was not found. Give the game folder as an argument.")
    print("Cookie Clicker was not found in the default Steam library.")
    print("Drag the Cookie Clicker game folder into this window, then press Return:")
    path = parse_dragged_path(input("> "))
    app = app_folder(Path(path))
    if app is None:
        raise PatchError(f"No Cookie Clicker mods folder was found in {path}.")
    return app


def run(arguments: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Install Cookie Monster+ for the Steam version of Cookie Clicker.")
    parser.add_argument("game", nargs="?", help="Cookie Clicker game folder (found automatically when omitted)")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--verify", action="store_true", help="check the installed files against the release")
    action.add_argument("--uninstall", action="store_true", help="remove Cookie Monster+ (moved to a backup folder)")
    parser.add_argument("--offline", action="store_true", help="install the files bundled with this patcher")
    parser.add_argument("--version", help="install this release instead of the latest one, for example 2.053.12")
    parser.add_argument("--force", action="store_true", help="install even if Cookie Monster is not installed")
    options = parser.parse_args(arguments)

    if sys.version_info < (3, 9):
        raise PatchError("Python 3.9 or newer is necessary.")
    print(f"Cookie Monster+ patcher {VERSION}")
    app = choose_game(options.game)

    if options.uninstall:
        backup = uninstall(app)
        if backup is None:
            print("Cookie Monster+ is not installed.")
        else:
            print(f"Removed Cookie Monster+. Its files are in {backup}")
            print("Turn the Workshop Cookie Monster back on in Options > Manage mods if it is off.")
        return 0

    base = find_cookie_monster(app)
    if base is None and not options.force:
        raise PatchError(
            "Cookie Monster is not installed. Subscribe to Cookie Monster in the Steam Workshop, "
            "start the game once, then run this patcher again."
        )
    if base is not None:
        print(f"Found Cookie Monster: {base}")
    installed_game = game_version(app)
    if installed_game and installed_game != GAME_VERSION:
        print(f"Warning: this build is tested with Cookie Clicker {GAME_VERSION}. The game reports {installed_game}.")

    manifest, files, source = load_release(options.offline, options.version)
    if options.verify:
        target = app / "mods" / "local" / MOD_FOLDER
        if matches(target, manifest):
            print(f"Cookie Monster+ {manifest.get('version', '')} is installed and every file is correct.")
            return 0
        print(f"The installed files differ from Cookie Monster+ {manifest.get('version', '')}.")
        print("Run the patcher again without --verify to install it.")
        return 1

    target, backup = install(app, manifest, files)
    print(f"Cookie Monster+ {manifest.get('version', '')} from {source} is installed in {target}")
    if backup is not None:
        print(f"The earlier copy is in {backup}")
    print("Restart Cookie Clicker. Cookie Monster+ starts as a local mod.")
    print("If the Workshop Cookie Monster is also on, Cookie Monster+ runs alone.")
    print(f"The settings are under Options > Cookie Monster > Autoplay. Guide: {PAGE}")
    return 0


def main() -> int:
    try:
        return run()
    except PatchError as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("Stopped. The game was not changed.", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

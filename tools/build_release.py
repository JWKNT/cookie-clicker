#!/usr/bin/env python3
"""Write mod/manifest.json and build the patcher release archive.

Run from any directory after replacing mod/main.js with a new Cookie Monster+ build:

    python3 tools/build_release.py

The archive goes to dist/ (not tracked). The script prints its SHA-256 digest for the
download guide in index.html and checks that the versions in the patcher, the manifest
and mod/info.txt agree.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MOD = ROOT / "mod"
PATCHER = ROOT / "patcher"
MOD_FILES = ("info.txt", "main.js", "thumbnail.png", "LICENSE.md")
PATCHER_FILES = (
    "install_cookie_monster_plus.py",
    "Install Cookie Monster Plus.command",
    "Install Cookie Monster Plus.bat",
    "README.md",
)
EXECUTABLE = {"install_cookie_monster_plus.py", "Install Cookie Monster Plus.command"}


def patcher_version() -> str:
    text = (PATCHER / "install_cookie_monster_plus.py").read_text(encoding="utf-8")
    match = re.search(r'^VERSION = "([^"]+)"', text, re.MULTILINE)
    if match is None:
        raise SystemExit("The patcher has no VERSION line.")
    return match.group(1)


def main() -> int:
    version = patcher_version()
    info = json.loads((MOD / "info.txt").read_text(encoding="utf-8"))
    major, minor, patch = version.split(".")
    if float(info["ModVersion"]) != float(f"{major}.{minor}{int(patch):02d}"):
        print(f"mod/info.txt ModVersion {info['ModVersion']} does not match patcher version {version}")
        return 1
    files = {}
    for name in MOD_FILES:
        data = (MOD / name).read_bytes()
        files[name] = {"sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}
    manifest = {
        "name": "Cookie Monster+",
        "version": version,
        "gameVersion": str(info["GameVersion"]),
        "requires": "cookie monster",
        "files": files,
    }
    (MOD / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    dist = ROOT / "dist"
    dist.mkdir(exist_ok=True)
    archive = dist / f"Cookie-Monster-Plus-Patcher-v{version}.zip"
    folder = f"Cookie Monster Plus Patcher v{version}"
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
        entries = [(PATCHER / name, f"{folder}/{name}") for name in PATCHER_FILES]
        entries += [(MOD / name, f"{folder}/mod/{name}") for name in (*MOD_FILES, "manifest.json")]
        for source, target in entries:
            item = zipfile.ZipInfo(target, date_time=(2026, 10, 29, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = (0o755 if source.name in EXECUTABLE else 0o644) << 16
            bundle.writestr(item, source.read_bytes())
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    print(f"Wrote mod/manifest.json for {version}")
    print(f"{archive.relative_to(ROOT)}  {archive.stat().st_size / 1024:.1f} KB")
    print(f"SHA-256 {digest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

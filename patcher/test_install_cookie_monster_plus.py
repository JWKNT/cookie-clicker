"""Tests for the Cookie Monster+ patcher, run against a fake game folder."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import install_cookie_monster_plus as patcher  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


def make_game(base: Path, layout: str = "windows", with_cookie_monster: bool = True) -> tuple[Path, Path]:
    """Create a game folder; return (folder the player sees, app folder with mods)."""
    game = base / "Cookie Clicker"
    app = game / "Cookie Clicker.app" / "Contents" / "Resources" / "app" if layout == "mac" else game / "resources" / "app"
    (app / "mods" / "local").mkdir(parents=True)
    (app / "src").mkdir(parents=True)
    (app / "start.js").write_text("// launcher\n")
    (app / "src" / "main.js").write_text("Game.version=2.053;\n")
    if with_cookie_monster:
        workshop = app / "mods" / "workshop" / "Cookie Monster"
        workshop.mkdir(parents=True)
        (workshop / "info.txt").write_text(json.dumps({"Name": "Cookie Monster", "ID": "cookie monster"}))
    return game, app.resolve()


def run_quiet(arguments: list[str]) -> int:
    with contextlib.redirect_stdout(io.StringIO()):
        return patcher.run(arguments)


class PatcherTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_finds_the_mods_folder_from_any_nearby_folder(self) -> None:
        for layout in ("windows", "mac"):
            game, app = make_game(self.base / layout, layout)
            self.assertEqual(patcher.app_folder(game), app)
            self.assertEqual(patcher.app_folder(app / "mods"), app)
            self.assertEqual(patcher.app_folder(app / "mods" / "local"), app)
        self.assertIsNone(patcher.app_folder(self.base / "missing"))

    def test_reads_dragged_paths(self) -> None:
        self.assertEqual(patcher.parse_dragged_path("/Games/Cookie\\ Clicker ", "Darwin"), "/Games/Cookie Clicker")
        self.assertEqual(patcher.parse_dragged_path("'/Games/Cookie Clicker'", "Linux"), "/Games/Cookie Clicker")
        self.assertEqual(patcher.parse_dragged_path('"C:\\Games\\Cookie Clicker"', "Windows"), "C:\\Games\\Cookie Clicker")
        with self.assertRaises(patcher.PatchError):
            patcher.parse_dragged_path("  ", "Darwin")

    def test_ids_are_normalized_like_the_game(self) -> None:
        self.assertEqual(patcher.normalized_id({"ID": "Cookie-Monster"}), "cookie monster")
        self.assertEqual(patcher.normalized_id({"ID": "cookie monster plus"}), "cookie monster plus")

    def test_refuses_without_cookie_monster_unless_forced(self) -> None:
        game, app = make_game(self.base, with_cookie_monster=False)
        with self.assertRaises(patcher.PatchError):
            run_quiet([str(game), "--offline"])
        self.assertEqual(run_quiet([str(game), "--offline", "--force"]), 0)
        self.assertTrue((app / "mods" / "local" / patcher.MOD_FOLDER / "main.js").is_file())

    def test_installs_verifies_updates_and_removes(self) -> None:
        game, app = make_game(self.base, "mac")
        target = app / "mods" / "local" / patcher.MOD_FOLDER
        self.assertEqual(run_quiet([str(game), "--offline"]), 0)
        manifest = json.loads((ROOT / "mod" / "manifest.json").read_text())
        for name in manifest["files"]:
            self.assertEqual((target / name).read_bytes(), (ROOT / "mod" / name).read_bytes())
        self.assertEqual(run_quiet([str(game), "--offline", "--verify"]), 0)
        # A second run leaves a verified install alone
        self.assertEqual(run_quiet([str(game), "--offline"]), 0)
        self.assertFalse((app / "mods" / patcher.BACKUP_FOLDER).exists())
        # A changed file fails verification; reinstalling keeps the old copy outside mods/local
        (target / "main.js").write_text("changed")
        self.assertEqual(run_quiet([str(game), "--offline", "--verify"]), 1)
        self.assertEqual(run_quiet([str(game), "--offline"]), 0)
        backups = list((app / "mods" / patcher.BACKUP_FOLDER).iterdir())
        self.assertEqual(len(backups), 1)
        self.assertEqual((backups[0] / "main.js").read_text(), "changed")
        self.assertEqual([p.name for p in (app / "mods" / "local").iterdir()], [patcher.MOD_FOLDER])
        self.assertEqual(run_quiet([str(game), "--uninstall"]), 0)
        self.assertFalse(target.exists())
        self.assertEqual(len(list((app / "mods" / patcher.BACKUP_FOLDER).iterdir())), 2)

    def test_rejects_files_that_do_not_match_the_manifest(self) -> None:
        manifest = {"files": {"main.js": {"sha256": "0" * 64}}}
        with self.assertRaises(patcher.PatchError):
            patcher.verified_files(manifest, lambda name: b"other")
        with self.assertRaises(patcher.PatchError):
            patcher.check_manifest({"files": {"../main.js": {"sha256": "0" * 64}}})

    def test_bundled_manifest_matches_the_patcher_version(self) -> None:
        manifest = json.loads((ROOT / "mod" / "manifest.json").read_text())
        self.assertEqual(manifest["version"], patcher.VERSION)
        info = json.loads((ROOT / "mod" / "info.txt").read_text())
        self.assertEqual(patcher.normalized_id(info), patcher.MOD_ID)


if __name__ == "__main__":
    unittest.main()

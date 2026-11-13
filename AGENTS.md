# Cookie Clicker guide and patcher

Read `../site-theme/PHILOSOPHY.md`, `../site-theme/docs/DESIGN-SYSTEM.md` and
`../site-theme/docs/WRITING-STYLE.md` before a change to the page.

## Original technical writing

Use ASD-STE100 Issue 9 for original explanations, instructions, and interface text.
Preserve formulas, rules, numerical values, identifiers, the paper, and license text.
Describe the style as ASD-STE100-guided. Do not claim full compliance without a dictionary and rule review.

## Build and checks

- Edit `src/index.html`, not `index.html`. Run `node build.mjs`. The build changes the TeX formulas to MathML
  and puts in the figures and tables of `src/figures.mjs`, which `assets/cookie-math.mjs` calculates.
- The guide has one text column and a margin column. A section has one margin item (`class="side"`) beside
  the paragraph that it shows, and a reference to pages of the paper (`{{in-paper: ...}}`). Read
  `../site-theme/skills/jehlp-math-explainer/SKILL.md` before a change to the text.
- Run `npm test`. It checks that `index.html` is current, runs the page, mathematics and paper tests, and
  runs the patcher tests. Each number that the page or the paper quotes has a test.
- `tools.html` is hand-written. It holds the download card and follows the shared tools pattern of
  `../site-theme/v2/reader.css`.
- After a paper change, build `paper/four-decisions.tex` with `tectonic`, copy the PDF to `paper.pdf` and
  inspect it. The site serves the paper at `/cookie-clicker/paper.pdf`. If the pages move, correct the
  references in `src/index.html`. The design is in `paper/style/preamble.tex`.
- The paper states what Lean has checked. After a change to `paper/lean/`, run `lake build` there and read
  its exit code.
- A new mod build follows `source/README.md`. The Tools page, the manifest and the release must name the same
  version.

## The audit folders

`lean/`, `model/`, `tools/`, most files of `tests/`, `paper/AUDIT.md` and the report
`paper/cookie-clicker-optimal-play.tex` are the audit of October 2026. Read `lean/README.md` and
`model/README.md` before a change there.

- Every committed file is public at `jehlp.net/cookie-clicker/`. Do not commit a file of the game: no script,
  page, style sheet, image or sound, and no complete parsed form of them. `.gitignore` names two such
  records. `THIRD-PARTY.md` says what the repository holds from the game and from other projects.
- A witness file must not hold the home folder of a machine. `tests/publication.test.mjs` checks this.
  `model/native-engine.mjs` writes the engine path with `~`.
- Many records hold SHA-256 digests of other files. After a change to a file, look for its old digest in
  `model/`, `lean/` and `tests/`. For the veil records, run `node tools/audit-veil-cover.mjs --check`.
- A test that needs an installed copy of Cookie Clicker 2.053 for Steam must skip itself on a machine without
  the game. `npm test` must pass there.
- `python3 lean/check.py --engine` needs the game. `lake build` in `lean/` does not.

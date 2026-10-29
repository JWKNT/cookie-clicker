# Cookie Clicker guide and patcher

Read `../site-theme/PHILOSOPHY.md`, `../site-theme/docs/DESIGN-SYSTEM.md` and
`../site-theme/docs/WRITING-STYLE.md` before a change to the page.

## Original technical writing

Use ASD-STE100 Issue 9 for original explanations, instructions, and interface text.
Preserve formulas, rules, numerical values, identifiers, the paper, and license text.
Describe the style as ASD-STE100-guided. Do not claim full compliance without a dictionary and rule review.

## Build and checks

- Edit `src/index.html`, not `index.html`. Run `node build.mjs` to render the TeX formulas as MathML.
- Run `npm test`. It checks that `index.html` is current, runs the page and mathematics tests, and runs the
  patcher tests.
- `tools.html` is hand-written. It holds the download card and follows the shared tools pattern of
  `../site-theme/v2/reader.css`.
- After a paper change, build `paper/cookie-clicker-optimal-play.tex` with `tectonic`, copy the PDF to `paper.pdf`
  and inspect it. The site serves the paper at `/cookie-clicker/paper.pdf`.
- A new mod build follows `source/README.md`. The Tools page, the manifest and the release must name the same
  version.

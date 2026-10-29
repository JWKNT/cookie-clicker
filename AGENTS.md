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
- After a paper change, rebuild `paper/cookie-clicker-optimal-play.pdf` from its `.tex` source and inspect it.
- A new mod build follows `source/README.md`. The page, the manifest and the release must name the same version.

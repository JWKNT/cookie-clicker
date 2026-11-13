# Cookie Clicker: four rules and the Cookie Monster+ patcher

[Guide](https://jehlp.net/cookie-clicker/) · [Paper (PDF)](https://jehlp.net/cookie-clicker/paper.pdf) · [Download the patcher](https://jehlp.net/cookie-clicker/tools.html)

This repository contains a guide to four decisions in *Cookie Clicker*, the paper with the proofs, and a
patcher. Each decision has a rule that is exact in a small model of the game. No rule is proved for the whole
game. The patcher installs Cookie Monster+, a version of the Cookie Monster mod that plays by these rules, in
the Steam version of the game.

| Folder | Contents |
| --- | --- |
| `index.html`, `src/`, `assets/` | The guide at <https://jehlp.net/cookie-clicker/>, with calculated figures and tables. |
| `tools.html` | The download page at <https://jehlp.net/cookie-clicker/tools.html>. |
| `paper.pdf`, `paper/` | The paper at <https://jehlp.net/cookie-clicker/paper.pdf> and its LaTeX source. |
| `paper/lean/` | Lean 4 proofs of three statements of the paper. |
| `patcher/` | The patcher and its double-click launchers for macOS and Windows. |
| `mod/` | The Cookie Monster+ build that the patcher installs, with its SHA-256 manifest. |
| `source/` | The full, readable Cookie Monster+ source and the build steps. |

## Install Cookie Monster+

1. Subscribe to Cookie Monster in the Steam Workshop. Start Cookie Clicker once.
2. Download the patcher from the [latest release](https://github.com/JWKNT/cookie-clicker/releases/latest)
   and extract the archive.
3. On macOS, double-click `Install Cookie Monster Plus.command`. On Windows, double-click
   `Install Cookie Monster Plus.bat`. On Linux, run `python3 install_cookie_monster_plus.py`.
4. Restart Cookie Clicker. The autoplay settings are in Options, under Cookie Monster.

The patcher needs Python 3.9 or newer. It installs Cookie Monster+ as a local mod beside Cookie Monster and
checks every file against its published SHA-256 digest. It does not change the Workshop copy of Cookie Monster
or your save. See [patcher/README.md](patcher/README.md) for the options.

In the browser version of the game, enter this line in the developer console:

```js
Game.LoadMod('https://jehlp.net/cookie-clicker/mod/main.js')
```

## What Cookie Monster+ does

Cookie Monster+ keeps every Cookie Monster feature and adds autoplay. Each system has a switch in the settings.

- It clicks the big cookie and every golden cookie and reindeer.
- It keeps the game at full speed while its window is hidden.
- It buys the item with the smallest payback period and keeps a "Lucky!" bank only when the bank pays back faster.
- It sells and buys back buildings every frame for Godzamok's click buff.
- It chooses the Grandmapocalypse stage by income, and it bursts wrinklers when that pays.
- It trains the dragon, plays the seasons, spends sugar lumps and runs the Pantheon, Grimoire, Garden and
  Stock Market.
- It takes achievements when they are worth their cost, including one Born again run.
- It spends heavenly chips by the ratio rule and plans its ascensions with a dynamic program.

## The rules

The guide explains each rule. The paper, *Four decisions in Cookie Clicker*, proves each rule in a model and
gives two examples in which a rule loses time outside its model.

1. **Purchase order.** For two items that the bank cannot pay, buy first the item with the smaller
   $p/c + p/\Delta$: the time to save for it plus its payback time. With three items this rule can lose time.
2. **The Lucky bank.** Up to the cap of the Lucky payout, a purchase increases the expected income when it
   pays back faster than $\theta = 1/(0.15\,g\,\lambda)$, about 1,915 seconds with the two frequency upgrades.
3. **Heavenly chips.** If each chip costs the same effort, buy upgrades in decreasing order of $(1 - 1/m)/p$.
4. **Ascension.** Late in the game, each run multiplies all-time cookies by the one root above 1 of
   $\tfrac{\beta}{3}(1 - 1/v) = (1 - v^{-\gamma/3})/\gamma$, where $\gamma = 3/\beta - 1$.
5. **Achievements.** An action that stops production for $D$ and then multiplies it by $M$ saves time when
   $D < H(1 - 1/M)$, where $H$ is the time to the goal.

Lean 4 has checked the method for a fixed list of purchases, the example with three items and the inequality
of rule 5. The files are in [paper/lean](paper/lean).

## Development

```sh
npm ci
npm test
```

Edit `src/index.html` and run `node build.mjs`. The build changes the TeX formulas to MathML and calculates
the figures and tables of `src/figures.mjs` with `assets/cookie-math.mjs`. The page needs no script of its own.
The site uses the shared jehlp.net theme. GitHub Pages publishes the repository root from `main`. To publish a
new mod build, follow [source/README.md](source/README.md).

The tests calculate each number that the page and the paper quote. With `pdftotext` installed, they also check
that each reference of the page is on the named page of `paper.pdf`.

To build the paper, run `tectonic four-decisions.tex` in `paper/` and copy the PDF to `paper.pdf`. To check the
Lean proofs, run `lake build` in `paper/lean/` with Lean 4.33.1.

## Licenses

`mod/main.js` is a modified build of Cookie Monster by the Cookie Monster Team. Cookie Monster, its framework and
the Cookie Monster+ changes in `source/` are under the MIT License. The build also includes jscolor 2.5.2, which
is under the GPL 3.0 or later, so `mod/main.js` as a whole is under the GPL 3.0 or later.
[mod/LICENSE.md](mod/LICENSE.md) lists each part. The Latin Modern Math font has its own license in
`assets/fonts/`. No new license is granted for the other files.

# Cookie Clicker: optimal play and the Cookie Monster+ patcher

[Guide](https://jehlp.net/cookie-clicker/) · [Paper (PDF)](paper/cookie-clicker-optimal-play.pdf) · [Download the patcher](https://github.com/JWKNT/cookie-clicker/releases/latest)

This repository contains a guide to the mathematics of optimal play in *Cookie Clicker*, the paper with the
complete proofs, and a patcher. The patcher installs Cookie Monster+, a version of the Cookie Monster mod that
plays by these rules, in the Steam version of the game.

| Folder | Contents |
| --- | --- |
| `index.html`, `src/`, `assets/` | The guide at <https://jehlp.net/cookie-clicker/>, with interactive examples. |
| `paper/` | The paper: LaTeX source and PDF. |
| `patcher/` | The patcher and its double-click launchers for macOS and Windows. |
| `mod/` | The Cookie Monster+ build that the patcher installs, with its SHA-256 manifest. |
| `source/` | The Cookie Monster+ changes, as one patch over upstream Cookie Monster. |

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
- It buys the item with the smallest payback period and keeps a "Lucky!" bank only when the bank pays back faster.
- It sells and buys back buildings every frame for Godzamok's click buff.
- It chooses the Grandmapocalypse stage by income, and it bursts wrinklers when that pays.
- It trains the dragon, plays the seasons, spends sugar lumps and runs the Pantheon, Grimoire, Garden and
  Stock Market.
- It takes achievements when they are worth their cost, including one Born again run.
- It spends heavenly chips by the ratio rule and ascends when a dynamic program says that ascension is optimal.

## The rules

The guide explains each rule. The paper proves them.

1. **Purchase order.** Buy the item with the smallest $p/c + p/\Delta$: the time to save for it plus its
   payback time.
2. **The "Lucky!" bank.** Spend a cookie when the purchase pays back faster than
   $\theta = 1/(0.15\,g\,\lambda_L)$, about 1,900 seconds with both frequency upgrades.
3. **Heavenly chips.** Buy upgrades in decreasing order of $(1 - 1/m)/p$.
4. **Ascension.** Late in the game, each run multiplies all-time cookies by the root of
   $\tfrac{\beta}{3}(1 - 1/v) = (1 - v^{-\gamma/3})/\gamma$, where $\gamma = 3/\beta - 1$.
5. **Achievements.** An action that delays play by $D$ pays when $D$ is less than the share of income
   that its achievements add, multiplied by the remaining play time.

## Development

```sh
npm ci
npm test
```

Edit `src/index.html` and run `node build.mjs` to render its TeX formulas as MathML in `index.html`. The site
uses the shared jehlp.net theme. GitHub Pages publishes the repository root from `main`. To publish a new mod
build, follow [source/README.md](source/README.md).

## Licenses

`mod/main.js` is a modified build of Cookie Monster by the Cookie Monster Team. It and the changes in
`source/` are under the MIT License in [mod/LICENSE.md](mod/LICENSE.md). The Latin Modern Math font has its own
license in `assets/fonts/`. No new license is granted for the other files.

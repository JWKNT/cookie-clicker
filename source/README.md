# Cookie Monster+ source

Cookie Monster+ is a set of changes to [Cookie Monster](https://github.com/CookieMonsterTeam/CookieMonster).
`cookie-monster-plus.patch` contains all of them, as one Git patch against upstream commit
`7f06fd383a280747200aff8e76280abc5d505ddc`. The patch excludes the built files in `dist/`.
The build uses the unchanged [Cookie Monster Framework](https://github.com/CookieMonsterTeam/CookieMonsterFramework)
at commit `e5ec8e4da7635d5c7055ed14c9d08f1b3e065ce2` (version 0.2.4), from a checkout beside Cookie Monster.

## Build `mod/main.js`

Install Node.js 22 or newer and Git. Then run these commands from the folder that contains this repository:

```sh
git clone https://github.com/CookieMonsterTeam/CookieMonsterFramework.git
git -C CookieMonsterFramework checkout e5ec8e4da7635d5c7055ed14c9d08f1b3e065ce2
git clone https://github.com/CookieMonsterTeam/CookieMonster.git
cd CookieMonster
git checkout 7f06fd383a280747200aff8e76280abc5d505ddc
git apply ../cookie-clicker/source/cookie-monster-plus.patch
npm ci
npx mocha
npx webpack --env minimize --env finalfile
cp dist/CookieMonster.js ../cookie-clicker/mod/main.js
```

The result is byte-identical to the published `mod/main.js`. The 124 unit tests cover the mathematics.

## Where the changes are

- `src/Main/Autoplay/`: the autoplay systems (purchases, golden cookies, Godzamok, the Grandmapocalypse,
  the dragon, seasons, sugar lumps, the Pantheon, Grimoire, Garden, Stock Market, achievements, the Born again
  challenge and ascension).
- `src/Cache/PP/`: the long-run income model, golden cookie outcomes, wrinklers and the Godzamok round trip.
- `src/Cache/Stats/AscensionMath.js`, `Ascension.js` and `HeavenlyPlan.js`: the ascension planner and the order
  of heavenly upgrades.
- `test/t_Cache/`: unit tests for the mathematics.

## Release a new build

1. Build `mod/main.js` as above.
2. Set `VERSION` in `patcher/install_cookie_monster_plus.py` and `ModVersion` in `mod/info.txt`.
3. Run `python3 tools/build_release.py`. It writes `mod/manifest.json`, builds the patcher archive in `dist/`
   and prints its SHA-256 digest.
4. Put the digest, size and version in the download card of `src/index.html`. Run `npm test`.
5. Commit, tag the commit `v<version>` and attach the archive to a GitHub release with that tag.

# Cookie Monster+ source

[`cookie-monster-plus/`](cookie-monster-plus/) is the complete source of Cookie Monster+. It is a fork of
[Cookie Monster](https://github.com/CookieMonsterTeam/CookieMonster) at upstream commit
`7f06fd383a280747200aff8e76280abc5d505ddc`. It uses the unchanged
[Cookie Monster Framework](https://github.com/CookieMonsterTeam/CookieMonsterFramework) 0.2.4 at upstream
commit `e5ec8e4da7635d5c7055ed14c9d08f1b3e065ce2`, which npm installs from GitHub.

## Build `mod/main.js`

Install Node.js 22 or newer. Then run these commands from the repository root:

```sh
cd source/cookie-monster-plus
npm ci
npm test
npx eslint src test
npm run build:mod
```

`npm run build:mod` writes `mod/main.js`. The build is not minified and has no source map, so the published
file is readable. The 124 unit tests cover the mathematics.

## Where the changes are

| Folder | Contents |
| --- | --- |
| [`src/Main/Autoplay/`](cookie-monster-plus/src/Main/Autoplay/) | The autoplay systems: purchases, golden cookies, Godzamok, the Grandmapocalypse, the dragon, seasons, sugar lumps, the Pantheon, Grimoire, Garden, Stock Market, achievements, the Born again challenge and ascension. |
| [`src/Cache/PP/`](cookie-monster-plus/src/Cache/PP/) | The long-run income model, golden cookie outcomes, wrinklers and the Godzamok round trip. |
| [`src/Cache/Stats/`](cookie-monster-plus/src/Cache/Stats/) | The ascension planner (`AscensionMath.js`, `Ascension.js`) and the order of heavenly upgrades (`HeavenlyPlan.js`). |
| [`test/t_Cache/`](cookie-monster-plus/test/t_Cache/) | Unit tests for the mathematics. |

## Release a new build

1. Change the source. Build `mod/main.js` as above.
2. Set `VersionMinor` in `src/Data/Moddata.js`, `VERSION` in `patcher/install_cookie_monster_plus.py` and
   `ModVersion` in `mod/info.txt`.
3. Run `python3 tools/build_release.py` from the repository root. It writes `mod/manifest.json`, builds the
   patcher archive in `dist/` and prints its size and SHA-256 digest.
4. Put the version, size and digest in the download card of `tools.html`. Run `npm test`.
5. Commit, tag the commit `v<version>` and attach the archive to a GitHub release with that tag.

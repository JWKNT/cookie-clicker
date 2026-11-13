# First ripe lump and funding: archived diagnostic prefix

The original fixed controller started from a new save. Its first archived periodic checkpoint after lump acquisition has Temple level 1, an active Devastation multiplier 16386, and a bank of about 6.25×10^21 cookies at 95,400,678ms (26.5 game hours). It has no ascension and is not complete. The original run continues separately.

The runner writes a public checkpoint every 30 minutes of game time. This record therefore does not give the exact first harvest or funding time. It contains no resumable game state and no full random/action replay tape. It is one Node/LCG sample, not an IID53 expected-time estimate, a source refinement proof, or an optimality certificate.

`evaluated-policy.js` has 179,221 bytes. The original runner appends one LF when it writes that file. The file hash is `cd2564269468ed45a8dfc203a19917722ced9a4d69f53634df78c385f06bb477`. Removing only that final LF gives the 179,220-byte VM input, whose hash is `fad0bf030fe6c2d881341cb4e3cff1cebe3da8042ea1c45e22ea74d93477188c`.

`original-runner.mjs`, `original-start.json`, `original-receipt.json`, the public checkpoint and the log prefix retain their original bytes. `snapshot/model` contains the frozen local adapter, completion data and policy generator import closure. The game itself is an external dependency: supply a read-only Steam 2.053 source directory. Its eight files must match the SHA-256 values in `snapshot/model/game-source.mjs`. The checker never reads a player save. The recorded execution environment is Node 23.6.0/V8 12.9.202.28-node.12 on macOS arm64; the adapter's game clock starts at 2026-10-29 12:00 UTC and uses UTC calendar fields. The adapter supplies its documented browser/asset approximation; it is not the pinned Chromium native interpreter.

Check the archive and the installed source without starting another game run:

```sh
node reproduce.mjs --check --source /path/to/CookieClicker/src
```

To reproduce the observed prefix in a new, empty output directory:

```sh
node reproduce.mjs --run /path/to/new-output --source /path/to/CookieClicker/src
```

The reproduced runner preserves the original 365-day horizon for action censoring. Its sole change is a diagnostic stop after the first periodic progress write at or beyond 95,400,678ms. It does not change the policy or any earlier game action. The wrapper checks the final public observation and controller memory; wall time and process memory are excluded from that comparison. Reproduction can require substantial CPU time. Only the integrity/policy/source check was run when this archive was prepared; the original prefix was not rerun.

These explanations are ASD-STE100-guided. Full dictionary and rule compliance was not checked.

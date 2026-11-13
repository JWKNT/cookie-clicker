# Reproduce the accepted one-Cursor source cycle

This archive contains the exact diagnostic request, its source inputs, the local Lean inspector, and the accepted receipt. It does not contain a player save. It does not start the installed game or the Steam wrapper.

The accepted request runs configured-English initialization, then two explicit fixture stages. The fixture writes `Game.volume=0`, a bank and earned-cookie total of 2^60, one Cursor, one level-1 Temple, the two already-unlocked Cursor upgrades, and the already-won Click achievement. It calls the intact `Game.LoadMinigames` and allows three native tasks. It then assigns diamond Godzamok, creates an existing Devastation buff through source, and calls the intact Cursor refresh. These assignments prepare a funded test. They are not certified player actions or a route from a new save.

The inspector then executes these source programs in order:

```javascript
Game.storeBulkButton(1);
Game.ClickProduct(0);
Game.storeBulkButton(0);
Game.ClickProduct(0);
```

The result retains the actual buy, sell, pricing, refresh, rebuild, callback, DOM and sound-selection effects. No helper or intermediate state is replaced. The request uses 4,096 fixed admissible 53-bit draw indices for a finite diagnostic. It is not an expectation calculation.

## Check and regenerate the request

Use a checkout with the source hashes in `dependency-sources.json`, its npm dependencies, and the selected Lean toolchain. `COOKIE_CLICKER_SOURCE` can point to a read-only installation of the pinned Cookie Clicker 2.053 source. The source loader checks all eight game files. `source-units.json` also checks every inline and fixture program. `request-template.json` retains the captured browser, CSS and diagnostic-budget inputs.

```sh
node /path/to/archive/generate-request.mjs /path/to/cookie-clicker /tmp/cursor-cycle-request.json
```

This command compiles the actual source and compares the result, byte for byte, with `request.json.gz`. It does not run the game. The accepted request hash is:

```text
52fb65af37571ac769cdc90d8d3841917250d47f0af4fe4e3c6c3edec906a5aa
```

The archive keeps Python's original ASCII JSON escaping to reproduce the exact accepted bytes. A different frontend result is an error; the script will not relabel it as the accepted input. `generation-check.json` records a successful exact match.

## Build and run

First build the repository's normal driver, in `REPOSITORY/lean`:

```sh
LEAN_NUM_THREADS=2 lake build jsastcheck
```

Then build the three archived inspector modules against those compiled dependencies. The script checks the source snapshot first. It writes only its output directory and uses one Lean worker.

```sh
python3 /path/to/archive/build.py /path/to/cookie-clicker /tmp/cursor-cycle-build
python3 /path/to/archive/run.py /tmp/cursor-cycle-build/cycle-driver /tmp/cursor-cycle-rerun
```

The invocation is `cycle-driver --execute`, with the request supplied through a regular input file. Decoder mode without `--execute` is a different operation. The default process limit is 600 seconds. A limit or process error produces a censored receipt with no final-state claim. Build paths can affect the executable hash; each new run records its actual binary hash. Do not overwrite the historical receipt with a new run.

## Accepted result and proof limit

The historical run returned in 93.384 seconds. It preserved the bank and earned-cookie bits, elapsed time, one Cursor, total building count, Cursor free/highest counts, and Devastation time/maxTime/arg1. Cursor bought increased from 1 to 2. The multiplier increased from native 1.01 to native 1.02. It consumed exactly two free draws and retained 239 new objects and 191 new environments. All startup and fixture stages completed; the final continuation is empty.

The inspector definitions and generic run-equation constructor are Lean-checked. The recorded acceptance is finite executable evidence. It is not a closed kernel evaluation of the whole serialized startup state. The flags `physicalInputRefined=false` and `universalAcceptanceProved=false` are deliberate. The result does not prove physical targeting, acceptance for every initialized entry, repetition for N cycles, new-save funding, 2^90 funding, or a globally optimal policy. Full correspondence to the native browser and the source parser remains a separate obligation.

Earlier harness errors are not native game failures. A proof-only finite-state list was initially evaluated during compiled startup; that eager initialization was removed without changing the theorem. A later invocation omitted `--execute` and selected decoder mode. The accepted run used the unchanged request after both harness issues were corrected.

Original archive instructions are ASD-STE100-guided. Full compliance has not been assessed.

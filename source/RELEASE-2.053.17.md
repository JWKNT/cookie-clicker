# Cookie Monster+ 2.053.17

This local candidate corrects Godzamok trade costs at the current bank value.
The GitHub release has not been published. Use `--offline` to install the bundled candidate.
The default installer downloads the build on `main`.

## Changes

- Apply each sale credit and buyback debit in native order when projecting the bank.
- Account for floating-point bank rounding, including trades with zero bank loss.
- Allow sale refunds to fund a complete buyback.
- Check every purchase for affordability. Reject a cycle that would restore only some buildings.
- Recheck the projected return and buyback immediately before each sale.

The projection requires unchanged price modifiers during the cycle. The existing three-millisecond budget and four-pass limit remain.
These practical limits are not restrictions on the zero-input-latency mathematical strategy class.
This release does not certify full-game optimality.

## Validation

- Mod `npm test`: 148 tests passed.
- Mod `npx eslint src test`: passed.
- Repository `npm test`: 244 Node tests and seven patcher tests passed.
- Native store-control regressions compare bank projections across eight cases, including free copies, discounts, rounding boundaries, and incomplete buybacks.
- A native regression confirms that selling the last Temple retains slotted Godzamok and grants Devastation.
- The readable webpack build completed with advisory size warnings.

Diagnostic fixtures do not establish a new-save route. Release text is ASD-STE100-guided.
A complete dictionary review has not been performed.

## Local archive

`dist/Cookie-Monster-Plus-Patcher-v2.053.17.zip`

Size: 271,378 bytes (265.0 KiB).

SHA-256: `17da24b0262321731aa9f0a20da1f3cf804852a3af0f63dabf93f47b0efce2a4`

`mod/main.js` SHA-256: `d4bd9c3ee68e12373c38d19aef0b9b941586acca2890b2c5c7e7675e24eee492`

The source, package files, patcher, mod metadata, manifest, and Tools page name version `2.053.17`.
No release was published and no commit was created.

# Cookie Monster+ 2.053.21

> Version 2.053.21 was published on 13 November 2026 as the release `v2.053.21`. The published archive has
> another `README.md` of the patcher, so its size is 279,286 bytes and its SHA-256 is
> `2ff91611596da4032f1dcffaed209b0ab1805520b5da16790876777fb949b7a7`. The text below is the note of the
> local candidate of 31 October 2026. The files `RELEASE-2.053.14.md` to `RELEASE-2.053.20.md` are the
> notes of earlier candidates, which were not published.

This local candidate corrects the immediate Godzamok return estimate.
The GitHub release has not been published. Use `--offline` to install the bundled
candidate. The default installer downloads the build on `main`.

## Change

The estimate now uses the actual rounded multiplier increase from a sale.
It follows native operation order and uses the stored binary64 slot constant.
An increase that rounds away contributes no click benefit. A cycle can still
qualify if the native bank updates produce a net gain.

Zero multiplier gain remains zero when estimated click income is infinite.
The future-average forecast starts each proposed buff at multiplier one.
That forecast remains a heuristic. The change does not prove minimum completion
time.

## Validation

- All 385 repository tests and seven patcher tests pass.
- All 197 mod tests pass.
- Three source-runtime tests compare 21 supplied sale/buyback boundary cases
  across all Pantheon slots. These are not new-save reachability tests.
- Unit tests cover halfway ties, absorbed increases, bank gains, infinite
  estimated income and future-buff forecasts.
- Full source and test ESLint passes.
- The readable webpack build succeeds with three bundle-size advisory warnings.
- The archive, manifest, metadata, source versions and Tools card agree.

The bundle has 689,663 bytes and SHA-256
`2d0b2336f9163f537b6a0a7a5032958d06864d24da1200319dfd64412b16add5`.
The patcher archive has 279,293 bytes and SHA-256
`6c1694209205253f9dd96062d9fe8c3ff6ef09617dc4cd530881372f02d1389a`.

The updated paper and Lean files retain their explicit proof limits.
Full-game optimality remains unproved. Release text is ASD-STE100-guided.
A complete dictionary review has not been performed.

# Cookie Monster+ 2.053.14

This local release candidate corrects planner and execution defects found in the strategy audit.
The GitHub release has not been published. Use `--offline` to install this candidate's bundled files.
The default installer still downloads the build on `main`.

## Changes

- Compare an ascension with reaching the model's goal without another reset.
- Use the combined milk gain and the exact completion-time saving `H*x/(1+x)`.
- Rank heavenly parent blocks by discounted internal cost. Apply affordable prefixes in both planning and execution.
- Use rounded building prices and check funds before every Godzamok sale and buyback.
- Pause spending while wrinklers pay out. Buy the Chocolate egg after their payout.
- Include Dragon Guts, shiny wrinklers, and other payout modifiers in the cash-in forecast.
- Describe ascension advice as a recommendation. Full-game expected-completion optimality remains unproved.

The revised paper includes a strict counterexample to greedy purchasing.
The Lean project proves finite purchase completion optimality and finite-depth stochastic certificate results.
It does not verify the whole game or the JavaScript implementation.

## Validation

- Root `npm test`: 21 Node tests and 7 patcher tests passed.
- Mod `npm test`: 133 tests passed.
- Mod `npx eslint src test`: passed.
- `npm run test:lean`: build, source checks, and 12 theorem axiom reports passed.
- Paper: Tectonic build and visual inspection of the 26-page PDF passed. No overfull boxes or unresolved references were reported.
- Browser: the achievement calculator, narrow layout, and light/dark rendering were checked. No console errors were reported.
- Archive: CRCs, every bundled file, manifest digests, version fields, and the Tools-page digest were verified.

The readable webpack bundle exceeds the default advisory size limit.
Tectonic reports an encoding warning in its external `algorithm.sty` package. The rendered algorithms were inspected.
Original explanatory revisions are ASD-STE100-guided. They have not had a complete dictionary review.

## Local archive

`dist/Cookie-Monster-Plus-Patcher-v2.053.14.zip`

SHA-256: `aacd156acb3e529e48b988047e575b5cfd791b012621d0d829b1c5290f512374`

The manifest, source version, mod metadata, patcher, and Tools page all name version `2.053.14`.

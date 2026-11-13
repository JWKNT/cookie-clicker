# Cookie Monster+ 2.053.19

This local candidate uses magic that a planned ordinary ascension would discard
to advance the spell-count achievements. The GitHub release has not been
published. Use `--offline` to install the bundled candidate. The default
installer downloads the build on `main`.

## Change

After cash-in, loans and the Lucky prestige wait are complete, cast the cheaper
affordable spell from Haggler's Charm and Diminish Ineptitude. Stop when
"A wizard is you" is won or no listed spell is affordable. Then perform the
already-planned ascension.

Both native outcomes advance the spell count without changing cookies or sugar
lumps. The reset clears their temporary buffs and retains their count and
achievements. The helper respects the Grimoire switch and skips challenges,
prompts and active ascension transitions. It neither waits for regeneration nor
requests another reset. A loop bound and progress checks also stop altered
callbacks from holding the browser in a loop.

The spell sequence still changes seeded state and future observations. This
change is not a proof that every full-game continuation becomes faster. The
paper now states the fixed-capacity, continuous-regeneration scope of the
full-magic frequency rule and proves its bound for nonperiodic schedules.

## Validation

- 190 mod tests pass, including 11 new cases.
- Four source branch tests cover both outcomes of both spells, cookies and
  lumps, the 999-cast award, and the effects of Reset.
- Integration tests check the order of cash-in, loans, the Lucky wait, casting
  and ascension. They also check blocked and disabled cases.
- Full source and test ESLint passes. The readable webpack build succeeds with
  its three bundle-size advisory warnings.
- The repository suite passes 330 tests and seven patcher tests. The full
  pinned-engine Lean check passes; it does not prove this mod globally optimal.

The bundle has 688,914 bytes and SHA-256
`b27ca5e295a0670806a41ff8becd291727c73cda3f0be299297cfb8bae866073`.
The patcher archive has 278,986 bytes and SHA-256
`f22dcaadef57c5184c014c95ca280b5a5d5d1da197160b020918f3b60ec71e6f`.

Full-game optimality remains unproved. Release text is ASD-STE100-guided; a
complete dictionary review has not been performed.

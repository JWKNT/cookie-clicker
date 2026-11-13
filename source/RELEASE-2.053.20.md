# Cookie Monster+ 2.053.20

This local candidate fixes native random bookkeeping during muted auto-clicks.
The GitHub release has not been published. Use `--offline` to install the bundled
candidate. The default installer downloads the build on `main`.

## Change

Auto-click now calls the native click-sound function with sound volume temporarily
set to zero. The function retains its random draw and sound-index update.
The earlier replacement callback skipped both operations.

The mod restores the previous volume and pointer fields after the click, including
when the click throws. The native 20 ms click guard and challenge restrictions
remain in force. This change preserves bookkeeping. It does not establish an
optimal completion strategy.

## Validation

- All 370 repository tests and seven patcher tests pass.
- All 193 mod tests pass. Three new tests cover the callback, restoration and blocked states.
- Paired source tests compare economic fields, sound indices and subsequent random
  outputs under free and seeded generators. A repeated same-time click remains rejected.
- Full source and test ESLint passes.
- The readable webpack build succeeds with its three bundle-size advisory warnings.

The bundle has 689,150 bytes and SHA-256
`de19c2fa58020e339dcba55728ea4741e3d87d65634775debee0bfc07ec0a02d`.
The patcher archive has 279,107 bytes and SHA-256
`c455ea77c8cbff6f574fe8cf01bfb2da8aae759d4024f4ac9d11e6779d0f9747`.

Full-game optimality remains unproved. Release text is ASD-STE100-guided.
A complete dictionary review has not been performed.

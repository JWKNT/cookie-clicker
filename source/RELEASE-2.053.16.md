# Cookie Monster+ 2.053.16

This local candidate removes the fixed one-minute wait between dragon-petting batches.
The GitHub release has not been published. Use `--offline` to install the bundled candidate.
The default installer downloads the build on `main`.

## Changes

- Make at most 20 ordinary pet calls per autoplay turn. Stop when a new drop becomes visible.
- Learn each quarter-hour's drop from observed unlocks. Skip a quarter when its known drop is already available.
- Use a short retry interval when existing drops have unknown quarter-hour mappings.
- Clear that learning on a new run, including a zero-prestige reset.
- Preserve the open menu and volume, including when a native call fails. Wait when an unrelated prompt is open.

The native two-second pet check limits a sound. It does not limit drop attempts.
The mod does not inspect a seed or predict a hidden drop. Bounded batches keep the interface responsive.
Lean checks a zero-delay local minimum for the mathematical case in which the current quarter's drop is known to be missing.
This is not a full-game optimality certificate for the mod.

## Validation

- Mod `npm test`: 144 tests passed.
- Mod `npx eslint src test`: passed.
- Eight new regressions cover observed drop learning, repeated calls at one timestamp, partial ownership, zero-gain resets, menu and volume restoration, and unrelated prompts.
- Native fixtures check both a missing drop and an already-owned quarter's item.
- The readable webpack build completed with its existing advisory size warnings.

The fixtures are diagnostic states. They do not establish optimal reachability from a new save.
Release text is ASD-STE100-guided; a complete dictionary review has not been performed.

## Local archive

`dist/Cookie-Monster-Plus-Patcher-v2.053.16.zip`

Size: 270,716 bytes (264.4 KiB).

SHA-256: `a30337361a454bca49a014dfb9162c16f964efb469777dfb707e7968e8a289f2`

`mod/main.js` SHA-256: `e5b73582d8f2b180aa9a3c99a77bbaad8dab65d433021fc0c22913d52d5c880a`

The source, package files, patcher, mod metadata, manifest, and Tools page name version `2.053.16`.
No release was published and no commit was created.

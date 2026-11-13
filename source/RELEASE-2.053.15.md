# Cookie Monster+ 2.053.15

This local candidate removes avoidable delays from automatic ascension.
The GitHub release has not been published. Use `--offline` to install the candidate's bundled files.
The default installer still downloads the build on `main`.

## Changes

- Dispatch the game's native Escape key event after autoplay starts an ascent. This skips the five-second ascent animation.
- Replace the fixed two-second cash-in delay with the actual pending-wrinkler check.
- Request newly stored wrinkler payouts before buying the Chocolate egg. Keep other autoplay spending paused during cash-in.
- Remove the fixed 1.5-second wait before heavenly purchases and reincarnation.
- Wait when an unrelated prompt is open. Cancel cash-in if a manual ascent or reincarnation has started.
- Stop heavenly-screen automation if the user disables automatic ascension.

The mod does not assign the ascent timer. The game handles the Escape event.
The native reincarnation animation remains unchanged.
These changes improve execution time. They do not establish full-game strategy optimality.

## Validation

- Mod `npm test`: 136 tests passed.
- Mod `npx eslint src test`: passed.
- Root `npm test`: 89 Node tests and 7 patcher tests passed.
- Native-engine integration: production `Autoplay`, `AutoAscend`, and cash-in functions ran against the pinned Steam 2.053 game.
- The integration fixture confirmed a shiny wrinkler payout before the Chocolate egg purchase.
- It confirmed the native 150-frame ascent duration and the Escape transition. Reincarnation was requested less than 200 milliseconds after ascent started.
- Guard tests confirmed that unrelated prompts stay open and manual ascent retains control.
- Archive CRCs, bundled file contents, manifest digests, version fields, and the Tools-page digest passed verification.

The integration test uses synthetic readiness and unlock fixtures. It does not prove that a new-save policy reaches those fixtures optimally.
The readable webpack bundle exceeds its advisory size limit.
Original release text is ASD-STE100-guided. It has not had a complete dictionary review.

## Local archive

`dist/Cookie-Monster-Plus-Patcher-v2.053.15.zip`

Size: 269,874 bytes (263.5 KiB).

SHA-256: `2dcdf02761720435b985143ab0d663598d77a1ec2ea2a1426a8c54d2c367d1d0`

`mod/main.js` SHA-256: `692073ae547ec8ab17870f6903aa72c009bf80e54cebfd31be718f0ded3614a5`

The source, package files, patcher, mod metadata, manifest, and Tools page name version `2.053.15`.
No release was published and no commit was created.

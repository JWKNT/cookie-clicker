# Cookie Monster+ 2.053.18

This local candidate removes the purchase delay at the start of each run.
The GitHub release has not been published. Use `--offline` to install the bundled candidate.
The default installer downloads the build on `main`.

## Changes

- Run the buyer on every frame. Version 2.053.17 bought at most one item in every ten frames.
- Price each candidate once per frame with Cookie Monster's values from the start of that frame. Buy in payback order for at most four milliseconds.
- Buy consecutive copies of a building in one native call. Every copy must pay back no slower than the runner-up and need the same reserve.
- Stop the frame after an upgrade and before a second purchase that needs a reserve. Wait one frame for new values.
- Keep the turn of each other system at one frame in every ten.
- Stay in Valentine's day until the last heart biscuit. Wait in Christmas until the hearts are cheap, instead of a round trip through Easter.
- Keep cookies for a seasonal action only from purchases that pay back in more than 60 seconds.
- Ignore a plan check scheduled in an earlier run. `Game.Reset()` sets `Game.T` to 0 at each ascension.
- Keep the game at full speed while its window is hidden. The browser throttles timers in a hidden window, for example one behind a full-screen app. The game then makes up at most five seconds per run of its loop.
- Start a worker whose timer the browser does not throttle. When the game's loop has not run for 250 ms, each tick runs the missed logic frames with the game's own catch-up.
- Click on those ticks when the auto-clicker's timer is throttled. Missed clicks are not made up in a burst.
- Add the setting "Full speed when hidden" (on by default).
- Open the Bank panel before market actions. Use an office, loan or goods control only when the control and its parents are visible.
- Take loans through the native loan button. During ascension cash-in, wait for that button when a loan is planned.
- Value the 34 "Unshackled" heavenly upgrades together. Each building contributes its share of CpS times the gain of its unshackled tiers. "Unshackled cursors" multiplies the Thousand fingers gain by 25.
- Value Aura gloves and Luminous gloves by cursor level and click share, Cat ladies and Milkhelp by the grandma share, and Fortune cookies and Pet the dragon by what autoplay does with them. Give estimates to Kitten wages, Chimera and Sucralosia Inutilis.
- Do not buy Sugar craving or Sugar aging process. With Sugar craving, autoplay spends each lump on the sugar frenzy before cursor levels and "Sugar baking".
- After the planned purchases, buy the cheapest available upgrades still missing for "All the stars in heaven" (100 heavenly upgrades) when together they cost at most 1% of the chips held at ascension. The shimmering veil and Sugar craving are not used for the count.
- Before ascending, wait up to 60 seconds for a prestige level that contains four 7s. Only then does the ascension screen sell "Lucky payout". The game earns no cookies during the ascension animation, so the frame that starts the ascension fixes the prestige level.

The first 2.053.18 archive did not have the change for frame numbers across an ascension. After an ascension, its buyer stayed idle until the new run reached the last frame number of the previous run.
The game showed this in run 72. A second archive fixed it.
The third archive added full speed in a hidden window, after the game ran at about 1/8 speed behind a full-screen app.
The fourth archive added the market controls. This fifth archive adds the heavenly purchases above. In the user's save, the earlier archives left 1.41 × 10^14 chips unspent, because no upgrade that they valued was left to buy.
The version number is unchanged because the candidate was not published.

More copies of a building only increase the value of other purchases. Values from the start of a frame therefore do not overrate a purchase.
The "Lucky!" bank and the season reserve increase with CpS, so a frame does not make a second purchase that needs one of them.
These changes improve execution time. They do not establish full-game strategy optimality.

## Measurements

A local browser harness ran the Steam 2.053 game files with a copy of the user's save.
The save was 6.6 minutes into run 70 at prestige 2.9 × 10^10. Each build started from the same bank and run age.

- 2.053.17: 447 buildings and 6.5 × 10^19 CpS after 125 seconds. The bank stayed above the next purchase price for most of that time.
- 2.053.17 also made five season switches in that time. The run reached 14 switches, and each switch costs 1.5 times the one before.
- 2.053.18: 9,259 buildings and 4.7 × 10^38 CpS after 30 seconds. The run stayed at 10 switches.
- The game kept 29 to 31 frames per second during the purchases.

In the game, the first minute after installing bought 3,802 buildings, from 5,645 to 9,447, 55 minutes into run 70.
The two minutes before the restart had added 358 buildings.

A forced ascension in the harness checked the frame-counter fix. With the first archive, the new run kept its 15 starting buildings for 20 seconds.
With the fix, the new run had 747 buildings after 5 seconds and 3,874 after 20 seconds.

A harness test delayed the game's loop timer to 40 seconds and the page's intervals to one second, as in a hidden window.
The previous archive then ran 3.1 logic frames per second. This archive ran 30.0 frames and 19.7 clicks per second, and it continued to buy.
The test does not show how Electron throttles a worker. The game itself is the check for that.

The heavenly purchases used a save from run 84 at prestige 1.43 × 10^14, with 63 of 129 heavenly upgrades and 1.41 × 10^14 chips.
Cursors made 34% of CpS from the Thousand fingers gain of 11,491 other buildings.

- "Unshackled cursors" with its four parents costs 3.3 × 10^7 chips. In the game's own CpS calculation it multiplied CpS and clicks by 9.27.
- All 34 Unshackled upgrades together multiplied CpS by 14.1.
- The harness ascension bought 38 heavenly upgrades, 16 of them Unshackled, and kept 8.9 × 10^11 chips. It earned "All the stars in heaven".
- 73 seconds into the next run, the Unshackled upgrades multiplied CpS by 9.5.
- A second harness ascension waited 0.2 seconds for the prestige level 142,723,231,777,917 and bought Lucky payout.
- With 34 Unshackled candidates, the planner refresh every five seconds took at most about 30 ms. Other frames had a median of 3.3 ms.

These are single runs on one save. They are not committed traces.

## Validation

- Mod `npm test`: 179 tests passed, including four market-control regressions and nine heavenly regressions.
- Mod `npx eslint src test`: passed.
- Repository `npm test`: 305 Node tests and seven patcher tests passed.
- One earlier full run had a timing failure in the policy evaluator's 50 ms timeout test. That test passed three times alone and in the next full run.
- Nine new buyer regressions cover payback ranking, reserve rules, consecutive copies, affordability, the copy limit, and plan checks across an ascension.
- Four new season regressions cover the Valentine's day visit and the order of seasons.
- Five new regressions cover the hidden-window catch-up, its five-second limit, frame accounting with the game's own loop, and the click schedule.
- The scheduler regression now expects the buyer on the first frame after cash-in.
- Nine new heavenly regressions cover the Unshackled value against owned upgrades, its marginal steps in the order, the purchases for "All the stars in heaven", and the wait for Lucky payout.
- The readable webpack build completed with advisory size warnings.

Release text is ASD-STE100-guided. A complete dictionary review has not been performed.

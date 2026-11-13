# Full-game audit model

This directory supplies the Steam 2.053 completion contract and an executable
adapter around the installed game. It does not yet supply an exhaustive control
model or an optimal completion policy.

The user allows scheduled maintenance reloads that save the current state.
The user also allows reading and decoding the current save shown by native
Export save, including its startup seed. Native export bookkeeping still applies.
This permission does not allow import, editing, restoration or outcome retries.
The user excludes reloads that retry random outcomes and deliberate manipulation
of random outcomes through native UI actions. The user also forbids timing chosen
to change seeded outcomes. This includes searching harvest timestamps with the
publicly exported seed. Native export inspection remains allowed. Compliance
requires an audit of the decision rule; the timestamp alone cannot show why the
strategy selected it. Save editing and clock changes are also
outside the model. Diagnostic fixtures that reproduce the clone-hover RNG leak
are not admissible strategy traces. The policy interface exposes observations
without future tape values or direct private generator access. Native export
is a permitted public observation. The full admissible
observation and action class is still an open modeling obligation.

`mathematical-assumptions.json` records the user's selected probability and clock
model: independent uniform 53-bit free draws, the native explicitly seeded
generators unchanged, and an unbounded monotone clock. The user also selected
total timestamp string processing beyond native string limits. It preserves
native seeded results for ordinary timestamps and uses exact traversal indices
for extended timestamp text. The source machine now carries this text through
the retained seed library and native save-codec helpers. It changes only the
captured mixkey activation's index initializer; the remaining source statements
and seeded draws still execute. The captured tagged-loop path has a composed
BrowserRuntime proof through ARC4 initialization, entropy mixing and installation
of the native random closure. A checked constructor reads that returned heap and
derives the retained draw frame. The complete source draw has a conditional
termination proof: its exact ARC4 orbit must contain a nonzero output byte.
Universal seed termination, initialized-frame preservation and full source
propagation remain open. Ordinary economic Numbers remain binary64. A no-argument
`Math.seedrandom()` restores the free draw law in this model. This is an explicit
idealization of the environment. It is not a claim about a browser entropy pool.
A path that never completes has infinite hitting time, including an infinite
sequence of zero-time inputs. Diagnostic decision caps do not restrict the
strategies in the requested optimum.

## Run the audit

```sh
npm run audit:game
npm test
npm run test:lean
```

The adapter reads the local Steam `src` directory. Set `COOKIE_CLICKER_SOURCE`
to another copy of the pinned version if needed. Eight source files must match
the hashes in `game-source.mjs`. The source files are not redistributed here.
The adapter does not read the player's save. Storage is private to each instance.

`audit:game` checks the installed constructors against `catalogue.json`, checks
the generated completion requirements, and evaluates a new save. Engine tests
are skipped when the game source is absent. The audit command fails in that case;
it cannot report a successful engine check without the game.

To regenerate the identities and completion requirements:

```sh
node model/runtime.mjs catalogue model/catalogue.json
node tools/generate-completion-requirements.mjs
```

## Completion

`completion-profile.json` fixes the target. `completion-requirements.json` lists
the selected identities and thresholds. `completion.mjs` reads a normalized game
observation and returns each missing condition.

- Win 598 specified normal achievements. The 24 named sugar exceptions remove
  individual achievement requirements. Shadow achievements do not count.
- Own 845 ordinary and heavenly upgrades in the current state. Cosmetic and
  offline upgrades count. The Steam-only cookie counts; the web-only cookie does not.
- Access all 17 toggles and selectors. Recorded access can satisfy mutually
  exclusive states. History must have the matching version and edition.
- Unlock all 34 Garden seeds, all minigames, soils, plots, spells, gods, goods,
  loans, dragon levels, Santa levels, and offices.
- Unlock every milk choice. The final milk requires 600 normal achievements.
  Both the won-flag count and the actual native `AchievementsOwned` counter
  must reach 600. The native counter is required explicitly; it is not inferred
  from flags. Thus a sugar exception can help satisfy a separate required unlock.
- Finish outside ascension and reincarnation transitions, in a normal run.

Current ownership matters. An earlier seed log followed by a Garden sacrifice
does not complete the target. Nor does an ordinary upgrade bought before an
ascension. The predicate does not require unbounded building levels or quantities.
It retains finite dependencies such as cursor level 12 and farm level 9.

Input validation is not a reachability proof. A synthetic fixture can satisfy
the predicate without being reachable from a new save. Upgrade access history
also needs a valid trace; a supplied list is not evidence of acquisition.

## Direct veil phase

The candidate makes one planned final normal-run reset after the prior growth,
heavenly-upgrade and spell phases. This decision does not use the startup seed,
veil outcomes or the Thick-skinned flag. It can reuse the spell controller's
actual final reincarnation. It does not reset after an unsuccessful veil trial.

The phase sells the starter buildings and checks zero production and the native
zero-price veil offer. It then makes consecutive accepted clicks from counter
zero. The quoted normal upgrade `"egg"` adds 9 CpS without buildings, so final
preparation excludes it from permanent slots. Final collection still buys it.
A nonzero production effect is an explicit unresolved boundary.

`veil-cover-witness.json` records an exhaustive finite scan of all 11,881,376
five-letter startup seeds. Each seed has a sufficient counter at most 34.
The compressed certificate is in `certificates/veil-first-counter.bin.gz`.
The policy reads neither the seed nor this certificate.

Run `node tools/audit-veil-cover.mjs --check` from the repository root to check
archive hashes, the certificate histogram, 6,192 native seeded outputs and the
conditional worst-seed source fixture. This command does not recompute every
seed predicate. Use `--scan` for that separate exhaustive computation.
Both commands use native diagnostic computations; neither runs a Lean proof
of the certificate. The original source and receipts remain in
`experiments/veil-seed-cover/`. Entry reachability, complete source/input
correspondence, finite expected completion and optimality remain open.

## Executable transitions

`createRuntime()` loads the unmodified game and its four minigames in an isolated
Node VM. `act(action)` invokes a permitted native operation. Timers run in order
when simulated time advances. Rendering has an inert DOM/canvas adapter.
`snapshot()` returns an observation for the completion test. It is not a complete
Markov state: the engine also holds callbacks, transient objects, PRNG state,
timers, and UI state.

Reproduction uses the initial environment, random tape, and complete action
history. The default environment is a Steam adapter, 100 heralds, UTC calendar,
English, zero asset latency, and a fixed start at 29 October 2026, 12:00 UTC. These are simulation fixtures,
not measurements of the user's Steam environment.

Startup executes the three active inline page scripts and the pinned external
page scripts in source order. The Steam IPC and audio wrapper is supplied by
the isolated environment. The native `window.onload` handler loads English,
calls `Game.Launch`, selects its console greeting, and invokes `Game.Load`.
The native filler-image callback then calls `Game.Init`. All callbacks due at
the initial instant finish before the first policy observation. The tiny-globe
draw still occurs although its web top-bar control is hidden on Steam. Tests
identify these native draw callsites and the loader callback. On a fixed test
tape, startup now takes 21 free draws; the old direct `Launch`/`Init` path took
19 because it omitted the globe and greeting. Initial game time remains zero,
and the native initial frame remains 1. Earlier sample traces do not silently
adopt this new draw order.

An explicit random tape controls unseeded random draws. Without a tape, a seeded
32-bit generator supplies reproducible samples. The game's explicitly seeded
PRNG operations remain in the source. The adapter restores the tape generator
when the source calls `Math.seedrandom()` without an argument. This reset is an
environment assumption. Neither a tape nor the sample generator specifies or
implements the selected independent 53-bit law. Finite experiments use native
dates within their valid range; they do not implement an unbounded calendar.

Summary recording omits replay arrays while retaining the final observation,
completion result, action and draw counts, and source identities. Use
`--summary-only` for long experiments. It cannot be combined with `--trace` and
does not produce a replay. Full recording remains the default. Both modes pin
all ten model implementation and configuration dependencies, plus Node and
V8 versions, platform, and architecture. This includes the completion logic and
its catalogue, profile and mathematical assumptions. Replay rejects a different dependency or execution
runtime. The earlier one-hour archive predates these pins. The six-hour summary
has the earlier three-module pins and a separate dependency snapshot. Neither
is presented as a replay validated against the current ten-dependency set.

Replay and evaluation results include `strategyReview`. It records that full
strategy admissibility is not certified. The action guards check implemented
controls and current-save history. They cannot determine whether a timestamp
was selected to change a seeded outcome. That rule requires a review of the
policy's decisions, even when the action replay succeeds.

Set `maintenanceReload: { atMs: [1000, 2000] }` to request maintenance at fixed
elapsed times. Use `{ firstMs: 1000, everyMs: 2000 }` for a fixed period. The
schedule is copied and frozen before the new save starts. The policy cannot
change it, supply a save, or request a reload after an observed outcome.
Requests wait for initial save loading, normal gameplay, and a closable prompt.
Requests that overlap coalesce. These guards depend on the game lifecycle;
they do not test a random reward.

Each request clicks the native Options, Change language, and English controls.
The source requests a current save even when English is already selected.
Native Logic waits for minigame loading and save completion before it calls
`App.reload`. The adapter then discards the old VM, DOM, and timer queue. It
keeps the current native save, browser storage, elapsed clock, and continuing
free-draw stream. The fresh page runs the pinned startup, including the native
100ms delay before `LoadSave`. The isolated Steam fixture completes storage
writes after the current task at zero host latency. Full IPC and browser task
ordering remain a separate refinement obligation.

Reload is not an identity transition. Native save/load code rounds Garden ages
and Market values, reconstructs buffs from saved arguments, discards shimmers,
and resets unsaved timers and display counters. Tests cover these effects,
current-save progress, old-callback removal, fixed scheduling, and exact replay.
The implemented schedules form one allowed subclass. They do not establish
complete coverage of all allowed maintenance policies. Earlier results for
policies without reloads still apply to that narrower class.

The `export-save` action opens Options and clicks its native Export save control.
The `saveExport` observation contains the readonly textarea text while that
prompt is open. The policy can decode this text, including the game startup
seed. Repeated observations read the same textarea; they do not serialize the
game again. Export retains the native `WriteSave(1)` effects: it clears
`toSave`, updates `lastDate` and `lastSaveData`, and does not write browser or
Steam storage. Six textarea cases are checked against pinned Chromium 87 in
`save-export-witness.json`.

Export remains available after a scheduled maintenance request. Because native
export clears `toSave`, it can cancel the requested storage write. If the game
then attempts to reload without a new save written after that request, the
adapter stops with `STALE_MAINTENANCE_SAVE` and records an `inadmissible-trace`
failure. This excludes an earlier-state restoration; it is not a native game
error. Native Ctrl+S before navigation can request the current save again.
Tests check both paths and replay of the valid path.

`actions()` enumerates core current choices. `act()` accepts more parameterized
operations through 62 named action types. The source callsite report classifies
334 sites and leaves 19 explicitly partial. Classification does not prove
exhaustive behavior. General tooltip and crate pointer states and the external
Steam Music service remain partial. Viewport tests use simplified pane geometry
rather than a full browser layout engine. Mutation observers run as zero-delay
timers instead of browser microtasks. Canvas pixels and audio are inert. The
DOM is constructed before page scripts run; this is not an HTML parser with
interleaved script execution. Dynamically appended pinned scripts and their
load callbacks run synchronously, while image load callbacks use zero-delay
timers. Resource errors, real loading delays, and full browser task and
microtask ordering remain environment obligations. The raw
VM handle is for diagnostics and synthetic tests; arbitrary VM code is not a
permitted policy action. A solver that only searches the enumerated choices
cannot establish a lower bound over all legal gameplay strategies.

The `cookie-pointer` action dispatches native enter, leave, down, up, and click
handlers with document propagation. Tests check their mouse state, sound draws,
click throttle, and replay. The original `click` action still invokes the game
callback directly. These two input paths have different side effects.

The `tooltip-pointer` action dispatches the native handlers for identified
controls and statistics crates identified by item type and ID. It preserves
the current crate, held-pointer gating, dynamic redraws, and delayed hiding.
Selected hidden or covered controls are rejected. Anonymous non-crate targets,
complete CSS hit testing, and general pointer paths are not covered. Observations
include rendered tooltip text and the visible ticker text. Native seeded text,
including fortune lucky numbers, remains available for public-history inference.
The native export can expose the startup seed. An undrawn ticker message and
future free random draws are not observations.

## Proof boundary

The Lean completion predicate uses generated identities from this contract. Its
checked statements establish the specified finite predicate, including required
item failures and shadow invariance. Generation checks detect stale identities.
They do not prove that JavaScript execution refines Lean transition semantics.

The unbounded stochastic theorem is a verification rule for supplied models and
certificates. It does not synthesize a full-game value function. Infinite action
traces also need a time-progress argument: summing action durations alone can
give zero cost to an infinite sequence of zero-duration actions that never
completes. Such a sequence has infinite completion time.

`HittingTime.lean` defines a separate completion-time expectation from finite
execution prefixes. At each time cap, an unfinished prefix receives the cap.
The depth limit is taken before the supremum over caps. Thus a permanent
zero-time stall has infinite completion time, while the known-missing geometric
pet retry has zero expected extra time. The native transition programs and
their source correspondence are still required.

`hand-picked-bound.mjs` records a necessary source timing constraint. Even with
all legal maturity reductions, a natural lump is not mature before an integer
clock difference of 64,436,019 ms. Lean checks the rational threshold arithmetic;
engine tests check the binary64 calculation and adjacent integer timestamps.
These checks do not prove a full engine refinement. The concrete Lean sugar-clock
transitions now imply minimum attempt spacing and the no-success/no-completion
event inclusion. Eleven native transition projections and all seven source timer
assignments are checked. The conditional two-attempt expected bound additionally
needs a bound on success probability after every
permitted observation. It is not inferred from the source's `choose([0,1])` call.

A full optimality result still requires all of the following:

1. Complete legal actions and exact transitions, including the browser adapter,
   Steam environment, numeric operations, observations, clocks, and randomness.
2. A legal policy that reaches the terminal set, with its expected elapsed time.
3. A matching lower bound against every admissible history-dependent policy,
   including unbounded random waits and unsuccessful paths.
4. A checked connection from those transitions and that policy to the game and mod.

No file in this directory asserts that these obligations have been discharged.

## Policy experiments

`policy-runtime.mjs` gives policy code immutable JSON observations and legal
action methods. The separate audit session owns source hashes, the environment,
the action history, and consumed random draws. Policy code receives no engine
handle, future random tape, experiment seed, or clock control. A failed action
stops that session. The Node VM limits capabilities; it is not an operating-system
security boundary.

The experiment seed controls the diagnostic free-draw generator. It differs
from the game's startup seed, which the policy may read from native export.

The wrapper also accepts a finite `sequence` of at most 1,000 flat native inputs.
It supplies no observations between those precommitted inputs. Replay stores
their expansion, and every native action and timer checkpoint remains visible
to the evaluator. Censoring includes zero-time inputs at the horizon and stops
when a requested positive-time prefix would leave it. Decision budgets count
wrapper calls. These macros are not new native game actions, and their expansion
has not been formalized in Lean. Batching may change a policy's response to an
event that occurs within the batch.

`evaluate-policy.mjs` observes the initial state, native actions, and timer
callbacks. It records the first full completion event, including an event during
a long wait. Lean checks the first hit on these recorded chronological traces.
The check does not prove legality or completeness of the supplied trace.

Run a fixed-horizon experiment with:

```sh
npm run evaluate:policy -- --policy completion-candidate --seconds 60 --seeds 1,2,3
```

Use `--policy growth` to run the earlier purchase baseline. `--output FILE`
saves the experiment and replay data. `--trace` adds all event observations;
these can be large. The diagnostic experiment seed is visible to the experiment
runner, not the policy.

`--decision-timeout-ms` sets the wall-time guard for one policy decision.
`--max-same-time-actions` sets the consecutive same-time decision budget.
The result records these values and the horizon and total decision budget in
`experimentBudgets`, separately from the modeled environment. A failed decision
also records `decisionFailure`: its exact public JSON observation, suggested
actions, current memory, policy hash, and decision index. No fallback action
runs after that failure. This record supports diagnosis. It does not add private
generator state or future random values. Its public observation can contain
the native export textarea if the policy has opened it. The failure record is
not itself a resumable engine save.

The summary reports the empirical restricted mean, `mean(min(T, horizon))`.
An unfinished path contributes the entire horizon. Action failures and decision
limits do not count as full-horizon samples. No unrestricted expectation or
optimality certificate is inferred from this statistic.

`completion-policy.mjs` composes growth, Garden, Stock Market, ascension, seasonal,
miscellaneous, and final-run production controllers.
It preserves first-run Neverclick and Hardcore conditions, uses native sugar
harvests and finite level costs, and reserves requested planting and holding
costs against discretionary purchases. Random rewards and penalties can still
change the bank. It handles owned prompts, held pointer input, and shimmer timing,
and clears current-run control state after reincarnation. It requests additional
Garden sacrifices to fund the finite level requirements. Its name identifies
the objective; no full completing new-save trajectory or expected time has yet
been demonstrated for this candidate.

`ascension-policy.mjs` buys the 129 heavenly upgrades with native parent and
digit-gate checks, coordinates an active loan, and reaches counted-reset goals.
Growth precedes counted-reset grinding. Large prestige targets use native
binary64 checks. The final growth targets are 1e72 cookies in one run, 1e56 raw
CpS, and 1e31 handmade cookies. `production-policy.mjs` then collects current
building holdings and tracks the native production families. Final count targets
are 1,000 Cursors and 700 of every other building.

The default bake milestone is persistent once its native achievement is won.
An ordinary seasonal retry does not force that milestone again; custom targets
above the native threshold still need the specified current-run amount.
Loan preparation stops at office level 2 while resets remain possible. Final market
collection and final production purchases require both ascension and seasonal
completion. The default market controller has no lifetime decision counter cap.
Explicit experiment caps remain diagnostic failures, not gameplay time bounds.

`season-policy.mjs` covers hearts, Santa, reindeer, Halloween, Easter, research,
pledges, fortunes, wrinklers, and dragon drops. `misc-policy.mjs` handles dunking,
Grandma sale, early and late golden clicks, gifting, veil protection, and Golden
switch access. Native fixture tests exercise these paths and their composition.
`goal-coverage.json` maps every target achievement, owned upgrade, and access
item to a native trigger family. A complete inventory is not a reachability proof.

After final-run preparation and required Garden work, the candidate grows a
clover/Nursetulip crop until Black cat's paw is won. It keeps mature plants and
replaces dead plants. `golden-garden.mjs` uses exact integer row dynamic
programming for the mature two-crop clay frequency. Alternating full rows give
2.9207763671875, compared with 2.35 for all clovers. Exhaustive small-plot tests
and a native full-plot test check the result. This is not a minimum-time crop
schedule: maturity, death, planting cost, and the Nursetulip production penalty
also matter. Elder Covenant is retained after the required wrath goals because
clovers do not increase wrath-cookie frequency.

Season-switch uses are bounded before requesting an ordinary reset, which
prevents unbounded exponential switch costs within one run. The helper display
expands without rerolling existing sprite indices. Dragon petting learns
quarter-to-drop assignments only from new visible unlocks. Known-missing quarters
allow same-time retries; unknown partial ownership uses a positive delay, and a
known completed quarter waits for its boundary. Native tests cover these cases.

`combo-policy.mjs` uses observed buffs and public native quotes for Pantheon,
dragon aura, FtHoF, and funded Godzamok cycles. A pending buyback or owned aura
prompt takes priority over other controls. The growth estimates remain local
heuristics. The fresh-save one-hour sample in `experiments/` predates this final
combo integration and does not complete the target.

The later six-hour sample in `experiments/new-save-six-hour.json` wins Neverclick
and Hardcore and ends with 57 normal achievements, 57 bought upgrades, and 1,430
missing terminal conditions. It is censored at 21,600,000 ms. Its compressed
summary and source snapshot are saved separately; it has no action replay.
One unfinished path supplies no unrestricted expected completion time.

The later `experiments/new-save-24h-request-failed.json` records a requested
24-hour experiment with 50 clicks per second. It stopped at 51,170,068 ms after
a policy decision exceeded the one-second VM guard. It had two ascensions,
71 normal achievements, 83 bought upgrades, no harvested lump, and 1,389 missing
conditions. It is unscored, not a 24-hour censored sample. Its compressed result
and immutable source snapshot are retained under `dist/experiments` with hashes.
That snapshot precedes the corrected page startup. The original decision memory
and suggested action list were not saved, so the failed call cannot be reproduced
exactly from its final observation. Short probes with replacement memories do
not establish that the cause was environmental.

`garden-policy.mjs` covers all 34 seeds, the required sacrifice and rebuild, seven
upgrade drops, 1,000 harvests, and the full mature plot. `market-policy.mjs`
targets the eight trading and office achievements and the final current office.
It can prepare an active loan for Debt evasion but leaves the ascent decision to
the whole-game scheduler. Both controllers use observed state, not future random
values. Native-kernel regressions start with funded, unlocked fixtures and
advance minigame steps directly. They are subsystem tests, not new-save routes
or expected-time results.

Before Make my day, startup shares are retained unless a sale qualifies for that
achievement. This prevents repeated purchase-overhead losses from selling a
holding after its value falls below the single-sale threshold. The native
alternating-price regression checks both the hold and the eventual award.
`market-recurrence.mjs` records conservative invariant and forcing-block bounds.
The Lean rational projection derives an 801-tick purchase-band block and a 231-tick
sale-band block. Its initial state box and the binary64 refinement remain
separate obligations. Boundary probes and a funded extreme-price completion
fixture are evidence about those cases, not a uniform full-game expectation.


## Source interpreter and host checks

The Lean source interpreter reads the actual pinned scripts through a typed AST.
It represents source closures, heaps, continuations, DOM trees, and pending host
requests explicitly. Unknown operations stop with an unresolved model request.
They are not counted as failed gameplay paths. `lean/README.md` records the
current source execution and proof boundaries.

AST schema v2 retains each function's original UTF-16 source text, including
comments and accessor names. The interpreter uses that text for function
reflection and primitive conversion. Missing text remains an unresolved request.
The native host catalogue separately records each known native callable's text;
a changed `name` property does not change that record.

`tools/probe-lean-startup.mjs` runs the page scripts in order, then an optional
load handler and a stated task budget. Each result records the executable,
request, frontend and probe hashes. Its file-origin storage, fixed random
inputs, UTC clock and omitted Steam host are diagnostic choices. Language storage
is empty by default. `--language-setting EN` writes only `CookieClickerLang=EN`
through modeled Storage before the page scripts. This explicit environment
fixture supplies no game save. It matches the executable adapter's English
setting, but the probe still follows global `App=0`; it does not execute the
external Steam wrapper. With English configured, the source `Game.Init`, its
first Logic/Loop and two Draw calls, and the loader callback have returned in the
diagnostic run. The empty-language web branch still requires content-height modeling
for the first language prompt. The probe does not establish
that all page loading, rendering or legal input paths are modeled.
`prompt-layout-audit.json` records exact source spans and the startup branch
conditions. It also records the obligations for a larger-action lower-bound
model. The direct prompt-height statement writes CSS position, but its callback,
public observations and pointer action reachability cannot be discarded without
proof. No executable transition is replaced by this audit.
The optional `diagnosticProduction` output reads a fixed list of own production
properties and callback source text from the actual interpreter heap. It also
records the selected callbacks' actual lexical environment chains, with binding
names and values only for `Game` and `window`. It does
not call accessors or export hidden random-generator state. The normal execution
result is unchanged. The export does not certify completed initialization and
is not an input to the policy.

The native comparison runner uses an isolated temporary copy of the installed
Electron 11.5.0 / Chromium 87 executable. It supplies its own audit entry and
profile, denies permissions and external requests, and does not load the game
entry or a player save. Data-image and media access require an explicit audit
option. `game-assets.json` records 379 local file hashes and metadata; regenerate
it with `node tools/capture-game-assets.mjs`. The Lean data generator is
`node tools/generate-browser-assets.mjs`. Asset bytes are not included.

Primitive console logs retain their raw arguments as explicit events. The native
console check compares these records with Chromium inspector events. Object
previews and other console methods remain unresolved. Canvas dimensions follow
the pinned Chromium parser and setter, including its 2³¹−1 limit.
`canvas-host-witness.json` pins the relevant source. The adapter creates 2D contexts with
their native prototype, stable identity, canvas reference and alpha setting. It
executes option getters and enum conversions in the pinned native order, even
when the context already exists. On macOS, the pinned conversion source forces
`desynchronized` to false. Other context modes, context resets after dimension
changes, drawing and pixel readback remain explicit requests.

The base Event adapter uses source callbacks and the pinned Chromium 87 event
path and registration order. The native Event check covers callback removal,
replacement, nested dispatch, exception reporting, cancellation and Window
state after dispatch. It also checks option-getter order, one-time and passive
listeners, and object `handleEvent` callbacks. Resource callbacks use the same dispatcher. These checks
do not establish input legality, trusted input, activation actions or complete
event semantics.

Cookie access has an explicit origin setting. With a fresh file-origin store
and the pinned default scheme policy, reads return an empty string and writes
cannot store a cookie. The setter still runs source string conversion. Opaque
origins throw `SecurityError` after conversion; an unspecified origin remains
unresolved. `cookie-host-witness.json` pins the native source. The cookie check
uses new temporary file and data profiles and does not read user cookies. HTTP
cookie stores and changes to the native scheme registry remain unmodeled.

The current browsing-context name has explicit UTF-16 state. An unspecified
initial name remains unresolved until a setter establishes its value. The
`Window.name` binding validates its receiver, runs source string conversion,
then changes that state. Reentrant conversion callbacks use the same state;
their writes remain if conversion throws. Saved native accessors still read
and write the browsing-context name after source replaces the own property.
`window-name-witness.json` pins the source and native tests. Navigation and
other Window lifecycles remain separate requirements.

`DOMRect` and `DOMRectReadOnly` store four binary64 coordinates, retain their
native prototype identities, and execute source conversions for construction,
mutation and `fromRect`. Their edge calculations use the pinned Chromium
NaN guard and C++ comparison rules, including signed-zero ties. The geometry
check compares these values with the native engine. This does not supply the
stylesheet cascade, renderer layout or a `getBoundingClientRect` result.
`geometry-host-witness.json` records the source hashes and open requirements.

The separate CSS adapter parses the two pinned stylesheets into closed token,
selector and declaration data. It retains order, specificity, duplicate
declarations and invalid vendor rules. Actual connected `link` elements select
configured loaded source in DOM order. A closed Lean parser reads the actual
text in runtime `style` elements, including the two image rules created by
`Game.Launch`. The Lean cascade then reads live IDs, classes, attributes and
inline declarations. Unknown dynamic selector states, media selection and
runtime CSS grammar outside the parser remain explicit requests. For the
supported definite-size boxes, one narrow projection permits unknown selector
states when every possible overflow declaration sets both axes to `hidden` or
both to `visible`. Kernel lemmas show that both axes have the same candidates
and cascade winner, and that every selected winner retains those values.
Axis-specific overrides, mixed values, scrolling values and other dynamic
geometry prevent the projection. The model does not assume that hover is false.

The layout adapter computes a restricted set of root and positioned block
boxes from that cascade and the configured viewport. It accepts integral pixel
lengths and 0/100 percent lengths, with zero margins, padding and effective
borders. It checks a bounded exact integer range. The native comparison covers
the game’s `html`, `body`, `wrapper` and `game` boxes in both web and app layouts.
It supplies no measured rectangle to Lean. Fonts, general flow, fractional
layout, transforms, scrolling, painting and hit testing remain open.
A separate display query can prove that an ancestor has `display:none`.
That result makes descendant boxes zero without parsing their unrelated border,
transform or text-height rules. Unknown dynamic display and `all` resets do not
permit this result. Native comparisons include the hidden prompt and the actual
`Game.UpdatePrompt` height statement.
A separate horizontal query computes content, padding and border widths for
non-replaced block boxes. It permits integral box edges and min/max constraints,
with root/body rules that exclude viewport scrollbars. Integer percentages are
accepted only when the intermediate binary32 product and quotient are exact.
It checks preceding floats and generated floats, and only permits the stated
paint-only transition grammar. That grammar admits the seven native easing
keywords after a nonnegative duration. The easing rule preserves the required
paint-property set; timing functions, delays and reordered forms remain explicit.
It does not infer text height or supply CSS
animation, layout-flush event, scrolling or paint semantics.
The vertical size query accepts definite heights and positioned boxes stretched
between definite top/bottom insets. It computes content, padding and border
heights without using horizontal min/max sizes. It supports exact integral
percent results, pixel edges and min/max height constraints. Content-dependent
heights and percentage vertical edges remain explicit. The native checks include
the source `sectionLeft` box and both `DrawBackground` canvas-height assignments.
Run `node lean/check_javascript_height.mjs --engine` for this query.
The focus-style query also checks inherited visibility. A positive result
requires a supported box; it does not by itself permit a native focus action.
`css-layout-witness.json` records the source pins and limits. Run
`node lean/check_javascript_css.mjs --engine` to compare the pure calculation
and the live DOM adapter with the isolated native browser. These finite tests
do not prove renderer refinement.

The background-position adapter keeps binary64 px/percent values in its style
cache. Native CSS tokens clamp their magnitude to the finite binary32 range;
values inside that range keep binary64 precision. CSSOM getters and attribute
text use the pinned six-significant-digit format. Checks include the actual
ascend-meter assignment at fractional offsets and large frame counts. This
stores declarations; it does not place or paint background images. Relative
units, computed values and multiple layers remain explicit. Run
`node lean/check_javascript_background_position.mjs --engine`; the source pins
are in `css-position-witness.json`.

The transform declaration adapter accepts the source-used 2D function grammar.
It keeps lossless numeric text in the style cache and uses the pinned Chromium
small-integer or `%.6g` format for CSSOM and attribute text. Native comparisons
cover rounding ties, aliases, invalid declarations, source conversions and the
actual ascend-meter and big-cookie assignments. Transform geometry and pixel
output remain explicit requirements. Relative physical lengths, 3D functions,
CSS Typed OM and full style lifecycle effects are not supplied. Run
`node lean/check_javascript_transform.mjs --engine` for these checks;
`css-transform-witness.json` records the source and limits.

The color model retains native eight-bit RGBA values. It accepts the stated hex,
comma RGB/RGBA and base-keyword grammar. CSSOM and Canvas use separate serializers;
Canvas alpha text follows the pinned 15-digit Decimal path. A kernel proof checks
the CSSOM alpha choice against logical binary32 arithmetic for all 256 byte
values. Native tests also run the market palette and `setCols` source statements.
Other color grammar, environment-dependent Canvas colors and pixel rendering
remain open. Run `node lean/check_javascript_color.mjs --engine`;
`css-color-witness.json` records the source pins and limits.

The fixed-pixel Canvas font parser retains size, ordered families, the generic
family flag and original source text. It keeps this data separate from getter
text, which can be identical for quoted and generic families. The Canvas setter
uses source string conversions and preserves the parsed font through save and
restore. A canvas dimension reset restores the default font. Native tests run
the five font assignment statements from the pinned game source. Font metrics,
shaping, pixel output and full style lifecycle behavior remain open. Run
`node lean/check_javascript_font.mjs --engine` for the pure parser comparisons
and `node lean/check_javascript_canvas.mjs --engine` for the Canvas state checks.

Canvas rectangle fills retain ordered commands with their drawing state, parsed
RGBA colors, matrix and target dimensions. Numeric source conversions and the
native rectangle adjustment run before a command is stored. These commands do
not supply pixel results. A rectangle with one zero side can still change pixels
under a full-canvas composite mode, so the model retains it. Clip changes, pixel
readback and large-allocation behavior remain explicit boundaries. Run
`node lean/check_javascript_canvas_fill.mjs --engine` for source-effect and command
checks, including the actual milk rectangle statement.

The border shorthand parser keeps native width and style defaults. For example,
`border:none` resets the width to medium, which becomes 3 CSS pixels if a later
declaration sets a solid style. The parser checks the color even when only box
dimensions are needed. Native tests cover all 25 border shorthand declarations
in the pinned stylesheets. Fractional lengths, complete color syntax and invalid
declaration recovery remain explicit. Run
`node lean/check_javascript_border.mjs --engine`; `css-border-witness.json` records
the source pins and the medium-width proof.

`css-properties.json` records 555 native JavaScript style names. The pinned
engine maps 533 of them to inline CSS declarations. The table permits known
empty-property queries and removals. Legacy names, unsupported value parsing,
and shorthand reconstruction with unmodeled values remain explicit requests.
Regenerate the capture with `node tools/capture-css-properties.mjs` and the Lean
table with `node tools/generate-css-properties.mjs`.

The timer adapter now follows the pinned Chromium 87 source. Timer delay uses
signed 32-bit Web IDL conversion, then a minimum of 1 ms. Nesting increments
before the test; the new nesting level 5 or greater has a 4 ms minimum. Repeating
timers schedule the next task before their callback. Thus the source's
1000/30 ms loop timer requests 33 ms. Asset tasks are a separate task category.
Cross-category deadline order and zero asset latency remain environment choices.
`timer-host-witness.json` records source hashes, rules, and reproduction.

The building action guard follows native hit testing. The first visible mystery
rows can receive clicks while locked. Later rows with `toggledOff` have
`display:none` and cannot receive a click. An unlocked row can be reached by
ordinary store scrolling. `product-hit-test-witness.json` records the eight
native layout cases. This check does not establish every legal UI action.

`JavaScriptCompletion` projects required fields from the explicit source heap,
then applies the same pinned goal list. `JavaScriptCompletionMonitor` checks that
projection before every source step and retains checked selector access from
visited source states. It records the first complete state, including a transient
hit inside a callback, without giving the player another observation or action.
The private history starts empty. Global source invariants, full native coverage
and the public observation model remain unproved.


The Storage witness pins Chromium and Electron source for the 100 MiB quota.
`node tools/audit-storage-host.mjs` checks both native storage areas at the exact
UTF-16 byte boundary in a temporary file-origin profile. The Lean storage tests
also execute the actual game wrappers. Unconfigured origin or quota, native
multiple-key iteration order, and unimplemented reflection remain explicit.

The stochastic source wrapper branches only at actual free-random requests.
It rejects the diagnostic random tape as a model input. A finite execution can
return, remain pending, or expose missing semantics. The checked prefix rule
resumes only pending work. These definitions do not yet establish a full legal
control and public-observation model or an optimal completion policy.

The experimental spell-count phase now uses one ordinary Conjure Baked Goods
cast per precommitted reset. Wizard level 1 gives native reset magic 5 and cost 4;
either spell outcome increments the retained counter. The phase requires the
actual 100 profitable resets, growth goals and a funded normal-run entry, and
finishes its final reincarnation before final collection. A continuous 999-cast
source witness takes 5,335,760 ms with no resource injection after its explicit
entry and no extra sugar. Those zero-profit resets do not replace the 100-reset
requirement. `tools/audit-grimoire-reset-route.mjs --check` reproduces the witness.
This remains a conditional route; it does not establish new-save reachability
or finite expected full completion.

The early profitable-reset candidate now targets 2^90 current-run earned cookies
and a strictly positive native prestige gain until 100 counted resets. It permits
prestige activation purchases after the first-run challenges and permits normal
permanent upgrade assignments. Neither the native reset count nor the Lucky gates
requires a general activation hold. The old hold is available only through the
explicit `withholdEarlyPrestigeActivation: true` diagnostic option. The candidate
uses the first ripe lump for Temple level 1 and batches one second of inputs. Funded reset-ledger tests do not
prove the required income from a new save.

The helper setup phase withholds 18 Grandma artwork upgrades and their permanent
assignments until the helper achievement is won. It uses an already scheduled
reset and Season switcher, then funds 24 Grandmas and Christmas before the fixed
3,350 ms sweep. It checks animation and the display premises, with a conservative
time bound restricted to the stated single-loop diagnostic profile. It does not
read sprite positions or select another reset from a failed outcome. The native
funded setup and worst-seed checks remain conditional route evidence.

`godzamok-loop-policy.mjs` is a standalone opt-in finite input prefix. It reduces
Cursors to one, waits once for any old Devastation buff to expire, and emits real
store controls for up to 2^56 sell/rebuy cycles at one mathematical time. It
maintains its own cent recurrence; it does not read an exact native multiplier
to select the cap stop. The default candidate and mod do not import it.
The six supplied-entry diagnostics in `godzamok-loop-witness.json` execute 2,181
cycles, with checks after each input. They do not execute the enormous full
prefix or assign its endpoint. Exact frame, buff-duration and Garden snapshot
fields still need a proved public-observation mapping. Full source and physical
input correspondence, host-resource bounds, later funding and restoration, and
new-save entry remain open. Run `node tools/probe-godzamok-loop.mjs --check` to
reproduce these finite checks.

`experiments/new-save-interrupted-30h.json` records the superseded candidate's
interrupted 48-hour request. Its last progress record is at 108,000,900 ms with
zero ascensions. No final observation or requested-horizon result was produced.
The linked archive preserves the policy, runner, four captured modules and log;
it is not a full replay or completion-time estimate.


## Bounded income controller

`early-funding-policy.mjs` sends finite batches of actual Cursor sales and
buybacks after Hardcore, Neverclick, Temple level 1, diamond Godzamok and Plastic
mouse. It then waits for a gains update and sends at most eight seconds of native
clicks. The default budget is 16,384 cycles. The controller uses one Cursor or a
funded batch of 100, retains actual debits and sale proceeds, and checks each
batch result. It reserves a safe remaining buff duration because selling more
buildings does not refresh an existing Devastation buff. The scheduler preserves
transaction ownership. Between bursts, fallback growth ranks other building
types so the next burst does not sell the latest growth purchase. Final building
collection remains separate. A partial or lost burst after a scheduled current-save
reload releases that ownership and retains the observed bank and clicks. This
recovery does not assume that native reload preserves the stacked buff. A zero
click rate disables this controller unless the
caller supplies a positive funding-specific rate.

The candidate withholds One mind until Temple level 1. This preserves the
proposed nonmeaty first-lump path. It does not prove a complete route.

`experiments/new-save-first-reset.json` records a separate initialized sample
with a fixed `1e12` early reset target. It reaches its first completed normal
reincarnation at 20,820,634 ms with Hardcore, Neverclick and prestige 1. The
archive retains the exact policy, original runner, progress log and final
observation. This summary-only sample uses diagnostic stream seed 1. It has no
complete replay trace, IID expectation estimate or optimality certificate. It
does not justify changing the default `2^90` reset target.

The superseded bounded-route experiment was stopped after 59,908,600 simulated
milliseconds. Its controller predates the duration, reload-recovery and
reinvestment fixes. It had no ascensions and had not reached Temple level 1 or
a funding burst. The final observation and exact frozen policy are archived in
[`experiments/new-save-superseded-16h.json`](experiments/new-save-superseded-16h.json).
The separate first-reset milestone is not part of that trajectory. Neither
experiment supplies a complete route or an expected-time bound.

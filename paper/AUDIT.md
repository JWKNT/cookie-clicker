# Strategy audit, updated 30 October 2026

The requested objective is minimum expected completion time from a new save.
The target includes all normal achievements, upgrades, and unlocks. The user excludes shadow achievements and a few long sugar-lump gates.
This does not exclude every calendar achievement. The named profile fixes the audit's interpretation of the narrow sugar exceptions.
[completion-target.json](completion-target.json) links the executable contract. [model/catalogue.json](../model/catalogue.json) records runtime identities, including the name that the earlier static inventory could not resolve.
The original paper optimizes several surrogate objectives. It does not solve this completion problem.

This audit uses the original paper, readable mod source, and the installed Steam game source.
Section names identify the original claims because edits can change line numbers.
The mathematical counterexamples below use exact rational arithmetic.
The writing is ASD-STE100-guided. A complete dictionary review has not been performed.

## 1. Greedy purchases are not globally optimal

The pairwise exchange theorem is correct for positive income and positive gains, fixed prices, additive gains, and an initially insufficient bank.
It compares two prescribed consecutive purchases. It does not choose an optimal sequence of three or more purchases.

Start with bank zero and income one. The offers `(price, income gain)` are:

| Offer | Price | Gain | Initial exchange index |
| --- | ---: | ---: | ---: |
| A | 3 | 1 | 6 |
| B | 5 | 4 | 25/4 |
| C | 6 | 6 | 7 |

Greedy chooses A first. At income two, B has index `15/4` and C has index `4`.
Thus greedy chooses ABC and takes `3 + 5/2 + 6/6 = 13/2` seconds.
The order BCA takes `5 + 6/5 + 3/11 = 356/55` seconds.
It saves `3/110` seconds. Every comparison that selects the greedy order is strict.

An exact finite purchase planner must compare complete admissible sequences or use a valid Bellman recurrence.
Its objective must specify the target: final bank, cumulative cookies, or ownership of a required set.
These targets are different.

## 2. The current ascension planner omitted direct completion

`SolveForGoal` in `src/Cache/Stats/AscensionMath.js` initialized the current-run cost to infinity.
Its loop excluded the terminal target. Thus every selected plan contained another ascension.
The fresh-run dynamic program did include a final run without ascension.

The original implementation returns `ascendNow: true` for this input:

```js
PlanAscension(
  {
    cookiesReset: 0,
    cookiesRun: 1e12,
    income: 2e9,
    runTime: 1000,
    overhead: 1e12,
  },
  { currentSpeed: 1, speedAt: () => 1.2 },
  { gridSize: 20 },
)
```

Every reset costs at least `1e12` seconds. Direct continuation reaches each considered goal in less than `2.6e7` seconds.
Initialize the candidate cost with direct continuation. Select an ascension only if it improves that cost.
The paper's current-run recurrence needs the same terminal alternative and no terminal ascension overhead.

## 3. A dynamic program is exact only for its specified model

The finite-grid Bellman recurrence is a valid shortest-path recurrence.
It is exact for its edge costs, admissible grid, terminal goal, and allowed actions.
It does not prove that estimated run durations equal game durations.
It also does not prove that a median decision across five goals minimizes any one goal's cost.
The 10% speed filter removes actions. Its effect needs an explicit restriction or a separate dominance proof.

## 4. The heavenly ratio rule has narrow assumptions

The individual-item ratio rule is correct when chip effort is constant, gains are independent, and each upgrade takes effect immediately after purchase.
It also assumes a fixed set of required purchases and no prerequisites.
In the game, prestige levels do not have constant effort. Upgrades can be bought together on an ascension screen.
Those differences make the direct game application a heuristic.

For a counterexample with variable effort, let `q(B) = B`.
Take A with price 1 and multiplier 2. Take B with price 2 and multiplier 100.
The ratio rule puts A first because `1/2 > 99/200`.
Its acquisition time is `integral(0,1,B) + integral(1,3,B)/2 = 5/2`.
Buying B first takes `integral(0,2,B) + integral(2,3,B)/100 = 81/40`.
This counterexample does not contradict the constant-effort theorem. It prevents its unrestricted use.

## 5. The proposed block extension used the wrong cost

For a fixed sequential block, define its effective acquisition time as
`D = sum_j p_j / product_(k<j) m_k`, and its multiplier as `M = product_j m_j`.
The exact exchange density of independent blocks is `(1 - 1/M) / D`.
The denominator is generally not the sum of prices.
Ancestor-closure selection remains a heuristic even after this correction.
A reference to Sidney decomposition does not establish this specific greedy algorithm.

## 6. Bank yield is an instantaneous comparison

Below the Lucky cap, a banked cookie adds `0.15*g*lambda` to expected instantaneous income.
This identity does not prove an optimal dynamic reserve policy for indivisible purchases.
For a purchase affordable at bank `b`, the exact Lucky contribution to the income change is

```text
lambda*g*(min(0.15*(b-p),900*(c+delta)) - min(0.15*b,900*c)).
```

Add the purchase's non-Lucky income change before comparing the two instantaneous rates.
The cap can change after a purchase. A fixed all-or-nothing reserve omits this effect.
Future affordability, unlocks, transient buffs, and the completion horizon also affect the decision.

## 7. The achievement delay threshold needs a denominator

For a permanent multiplier `1+x` and a baseline completion time `H`, a pause of `D` pays exactly when
`D < H*x/(1+x)`, under the stated time-rescaling model.
Equivalently, `(1+x)*(H-D) > H` at a fixed wall-clock horizon.
The original proposition changed this exact condition to `D < H*sum(x_i)` and retained “if and only if.”
That replacement is a first-order approximation.

For several milk achievements, evaluate the kitten product at `milk + 0.04*count`.
Multiplying one achievement's gain by the count is generally not exact.
For completion, an achievement can be mandatory even when its income return is zero.
The income-based criterion cannot decide whether to omit a required achievement.

## 8. The late-game formula is not a finite-goal policy theorem

The telescoping lower bound is valid under the power-law and common-speed assumptions.
A schedule attains it when every step minimizes the stated quotient and the steps reach the specified goal exactly.
A repeated minimizing step plus a final partial step need not attain the bound.
A stationary equation alone is not a proof of uniqueness or finite-goal optimality.
The assumptions omit real-time timers, discrete prestige, and changes in the run curve.

## 9. Mean income does not determine expected completion time

Random golden cookies, buffs, garden mutations, and other events affect the distribution of completion time.
Replacing these events with their mean income changes the stochastic control problem.
For example, choose a constant income of one or three with equal probability, then produce three cookies.
The expected completion time is two, while three divided by the mean income is only `3/2`.
State-dependent choices can further change expected completion time.
A stochastic proof needs transition probabilities, durations, and a completion predicate.

## 10. Completion has dependencies that the existing heuristics do not cover

`AutoGarden.js` has a fixed list of 16 target mutations. It does not encode every garden dependency or layout.
The checkerboard lemma establishes neighboring parent coverage. It does not prove maximum mutation yield or sufficient parent counts for every mutation.
`AutoGrimoire.js` pursues Force the Hand of Fate. It does not optimize all required spell-count objectives.
`AutoLumps.js` spends lumps on repeatable income boosts and selects levels by income value.
That policy does not prove fastest completion of a required set of level achievements.
Excluding particular sugar-lump achievements does not remove lump costs from minigame dependencies.
These are explicit scope gaps, not proofs that the named mechanics have no value.

## 11. Several formulas are conditional approximations

The golden-cookie interval formula replaces a finite product with an integral and then extends the integration range.
The paper should call it an approximation, not an exact lemma about the game's interval distribution.
The full-magic casting argument fixes maximum magic and spell cost. Selling towers and changing the cap fall outside that model.
The stock-market percentage assumes the stated purchase and sale prices both occur. It does not bound waiting time or opportunity cost.
The wrinkler sale rule assumes exponential reinvestment and a fixed respawn loss. The game does not guarantee these paths.

## 12. Historical numerical tables are not reproducible from this checkout

The paper reports purchase, ascension, and fresh-game simulator results.
This checkout contains mathematical helper tests and mod tests, but no simulator that reproduces those historical tables.
The original random-pair tests also use unseeded randomness.
The historical percentages compare selected policies in a simplified economy. They do not measure distance from the true game optimum.
Keep these results labeled as historical and unverified until the simulator, configuration, seeds, and output are supplied.

## Formal proof boundary

Useful exact targets include finite deterministic purchase planning and finite stochastic policy certification.
A stochastic certificate must quantify over all admissible contingent policy trees in its specified model.
Probabilities must be nonnegative and normalized. Terminal leaves must satisfy the completion predicate.
A lower-bound theorem plus an attaining policy proves optimality for that model.
A full-game optimality claim additionally needs a checked game model and a proof that its policy implements legal game actions.
The present repository did not supply that model at the start of this audit.


## Installed game evidence

The inspected installation identifies itself as version `2.053` in `src/index.html`, line 17.
Its source directory is `Cookie Clicker.app/Contents/Resources/app/src` in the Steam installation.
The audit read these files without changing the installation or the save.

| File | SHA-256 |
| --- | --- |
| `main.js` | `a8813ec2ee97edf5ebff6a3ce2037dcb65c08abd13c123bb92efda89b06ef4f7` |
| `minigameGarden.js` | `184eacacd9325d493412dcda07f63d3a791939f83889b4349b6099d04be8e6c9` |
| `minigameGrimoire.js` | `9efea1feb898dc9b719dd971bd27a71f083a8855b910013c524aea9b6d2a349d` |

The following references use line numbers from these exact files.

- `main.js`, lines 7791–7796: the next building price uses the free-building floor, price modifiers, and upward rounding.
- `main.js`, lines 7826–7885: individual buys use that price. Sales return its product with the sale multiplier, rounded down before decrementing holdings.
- `main.js`, lines 7886–7900: a sale adds to an existing Godzamok multiplier. It does not restart that buff.
- `main.js`, lines 9554–9562 and 10398–10403: an upgrade pays its price before its callback. Chocolate egg then pays 5% of the remaining bank.
- `main.js`, lines 14455–14514: wrinklers pay on the game update after their health falls to `0.5` or less.
- `main.js`, line 14469: Dragon Guts multiplies the wrinkler payout by `1 + 0.2*auraMult`.
- `main.js`, lines 4655–4670 and 16290–16294: withered cookies are removed from earned cookies. Wrinkler payouts are then added by `Game.Earn`.
- `minigameGrimoire.js`, lines 486–488: regeneration has a positive floor and depends on both current magic and its cap.

The revised rounded Godzamok cost matches the individual sale and buy loops under unchanged modifiers.
The egg forecast must count only the bank and assets that its execution policy actually collects.
The revised mod includes the Dragon Guts payout factor and suspends spending during the cash-in wait.
Regression tests check both changes. The integrated verification passes
148 mod tests and ESLint, 244 root Node tests, and seven patcher tests.
The current engine-backed Lean check passes 259 theorem dependency audits,
47 JavaScript/Lean observation comparisons, 13 event traces, native Garden
contract probes, 11 sugar-transition projections, and 14 timing/click projections.
Forty-four audited declarations use no axioms. The other dependencies are only
standard Lean axioms; no forbidden dependency is present. These checks do not
certify full-game optimality.

The final paper was rebuilt with Tectonic and copied to `paper.pdf`. All 33 pages
were rendered for visual review, with detailed checks of the changed probability,
Godzamok, golden-cookie, and experiment sections. Text extraction found no
replacement glyphs or content outside the page bounds. The final PDF SHA-256 is
`312cf5b55ce4ba5f30e9494acc733d76534ea3570aab697b0dbbdc93520c5f0f`.


## Completion contract and executable game

The initialized Steam engine resolves all 643 achievement identities: 622 normal,
17 shadow, and four unused dungeon entries. It also supplies 875 upgrade identities,
20 buildings, all four minigames, and all 34 seeds. Eight consumed source files have
pinned hashes. The earlier static achievement inventory remains available as source evidence.

The explicit profile requires 598 normal achievements after 24 individual sugar
exceptions: 20 building-level achievements, the 365-lump total, and three normal
unusual-lump achievements. It retains 845 current-owned upgrades and 17 toggle
or selector access conditions. Steam requires Steamed cookies; Web cookies is
debug content in this edition. All finite progression and cosmetic unlocks count.
No ordinary upgrade was found to be mutually exclusive with another ordinary upgrade;
source lock/reset operations of that kind act on toggles and seasonal triggers.

The final milk requires 600 normal achievements. The 598 specified achievements
plus the level achievement implied by required cursor level 12 yield only 599.
At least one additional normal achievement is therefore necessary. It can be an
individual sugar exception. The aggregate milk requirement does not reinstate all
24 exceptions. This distinction is checked in the completion tests and Lean predicate.

Garden sacrifice grants ten lumps and increases the lifetime lump total. A
cumulative lump count does not prove a fixed calendar wait. Cursor level 12 and
farm level 9 retain their costs. All 34 seeds must be unlocked after the required
sacrifice. Ordinary upgrades must be owned after the final ascension. A record
that these items were once obtained is insufficient.

`npm run audit:game` validates the installed constructors and the generated
requirements, then checks a fresh isolated save. The runtime adapter executes
native game callbacks with an explicit clock and random stream. Tests cover
click throttling, purchases, passive income, minigame loading, source mismatches,
action replay, and agreement between the two completion snapshot readers.
The installation and the player's save remain unchanged.

This is an executable audit adapter, not a verified full-game stochastic model.
Its action coverage is incomplete. The default fixed herald count, UTC calendar,
browser shims, and random-stream reset are environment assumptions. A replay is
evidence for a specific trace, not a probability law or a global lower bound.

## Unbounded proof issue

A finite policy tree cannot cover every random wait. The new unbounded theorem
compares the suprema of expected accumulated costs of finite truncations, under
explicit Bellman and residual-tail assumptions. These assumptions still need a
full-game instantiation. They are not discharged by recording game traces.

Accumulated cost also needs a connection to completion time. An infinite sequence
of zero-duration actions can have cost zero and never complete. Its completion
time is infinite. A kernel-checked counterexample records this distinction.
A full-game theorem must exclude such time behavior or give unsuccessful paths
their correct cost. No optimal full-game policy or matching certificate is supplied.

`HittingTime.lean` now gives completion time its own operational definition.
At a fixed elapsed-time cap, an unfinished finite prefix costs the cap. The
expectation takes the infimum over prefix depth and then the supremum over
time caps. The same definition gives infinite time to a permanent zero-time
stall and zero expected added time to the known-missing pet retry.
The proofs use the exact IID53 kernel, hidden startup averaging, public action
and observation histories, and legality on reachable unfinished histories.
Finite independent private policy mixtures also preserve a common prefix lower
bound. The full native transition program, its source correspondence, and a
global attaining policy are not supplied by this construction.

## Native policy and mod integration

The adapter now exposes 61 action types. Its AST report classifies 334 source
sites, including 13 explicitly partial entries. Native tooltip entry and exit
now preserve crate state, held-input guards, and delayed hiding. General tooltip
caller coverage, external Steam Music, layout, and browser
microtask behavior still need exact models. A classified site is not a proof of
callback equivalence.

Startup now executes the active inline page scripts, the native load handler,
English language loading, launch, and filler-image callback in source order.
The native top-bar globe and console greeting both consume free draws before
seed creation. The reviewed fixed tape takes 21 startup draws instead of the
former 19. Initial elapsed time remains zero, initial frame remains 1, and
catalogue identities are unchanged. Dynamic script callbacks still use the
explicit zero-asset-latency fixture. Older experiments retain their old source
and draw order; they are not relabeled as runs of this adapter.

The full bundled mod now runs in the isolated native engine. Its regression
tests exercise ordinary play, menus, payout collection, Chocolate egg, ascent,
Legacy purchase, and reincarnation. Version 2.053.15 uses the native Escape input
to end the five-second ascent animation. It checks actual pending wrinkler
payouts and removes two fixed waits. Version 2.053.16 also removes the one-minute
dragon-pet batch wait. Its bounded batches stop on a visible unlock, learn quarter
assignments from those unlocks, and preserve menus and volume. The local patcher
archive is described in [RELEASE-2.053.17.md](../source/RELEASE-2.053.17.md).
Version 2.053.17 projects each native sale credit and buyback debit against the
bank in execution order. It checks full buyback affordability again immediately
before a sale. Nominal price sums are insufficient at large bank values.
Version 2.053.18 runs the buyer on every frame and buys consecutive building
copies in one call. It also stops seasonal round trips for heart biscuits. A
worker's timer keeps a hidden window at full speed. The heavenly planner values
the Unshackled upgrades together from building shares of CpS, buys cheap upgrades
for "All the stars in heaven" and waits for a prestige level that sells Lucky
payout. Its archive is described in [RELEASE-2.053.18.md](../source/RELEASE-2.053.18.md).
No release was published during this audit.

The separate observation-only candidate combines resource growth, Garden,
Stock Market, ascension, seasonal, miscellaneous, and final production controllers. Garden regressions use the
native mutation and growth kernel to complete the seed log, sacrifice, rebuild,
seven drops, 1,000 harvests, and the full mature plot. Market regressions attain
the eight trading and office goals on three random streams. They use funded,
unlocked subsystem fixtures. They do not establish a full new-save route.

The composed candidate preserves Neverclick and Hardcore, tracks prompt and
pointer ownership, protects required resource reserves, and stops explicitly if
a subsystem budget expires. Native fixtures exercise all 129 heavenly purchases,
large-number Lucky gates, active-loan ascent, and current-run cleanup. Seasonal
fixtures cover hearts, Santa, reindeer, Halloween, Easter, research, pledges,
fortunes, wrinklers, and dragon drops. The target-to-trigger inventory covers
598 achievements, 845 owned upgrades, and 17 access items with no unclassified
target. This inventory does not establish reachability. A legal whole-game
completing trajectory and its expected time have not been demonstrated.

Final growth targets include 1e72 cookies baked within a run, 1e56 raw CpS,
and 1e31 handmade cookies. Current holdings require 1,000 Cursors and 700 of
every other building. Native per-building production flags are checked
separately. Required lump levels cost 126 lumps; further Garden sacrifices
can supply this finite debt. Farm9→10 is a fallback when the last milk still
needs one more normal achievement. Slow rare crops can receive elderwort
support. Its maturation comparison is conditional on fixed ticks, paired
uniforms, and survival, not a full-game cookie/time dominance result.

The final natural-cookie count phase now grows golden clovers and Nursetulips
until Black cat's paw is won. An exact integer row dynamic program compares
every mature two-crop clay layout. Alternating full rows give a frequency
multiplier of 2.9207763671875, compared with 2.35 for all clovers. Exhaustive
small-plot comparisons and a native full-plot effect check pass. The controller
keeps mature plants, renews dead plants, and reserves native planting costs.
It retains Elder Covenant after required wrath goals. These improvements do
not optimize growth and renewal times or the Nursetulip production penalty.
The layout planner has not been formalized in Lean.

The native count requires timer-leading golden or wrath cookies, including
chain leaders. Fortune rewards, Dragon Orbs, Force the Hand of Fate, storm drops,
and Distilled essence duplicates have no `spawnLead` flag and do not themselves
increase the count. A continuing chain sets both timer limits to 90 frames.
The native hazard comparison produces the next leader after 91 updates. Untimed
cookies can change the shared chain, so their pop order affects future leaders.
Three native regressions check these distinctions. A fixed multi-minute lower
bound on all counted interarrival times would be false.

Loan preparation now stops at office level 2 while further resets are possible.
Final market holdings, brokers, and offices wait for both reset and seasonal
goals. The default market controller has no lifetime decision cap. Repeated
season switches are bounded within a run before an ordinary-reset request;
their exponentially increasing costs previously allowed a permanent stall.
The controller also clears current-run memory after a zero-prestige reset,
which does not increase the native reset counter. A won default bake milestone
remains valid after that reset; a larger custom bake target still needs its
specified current-run amount. The first Grandma is kept through Hardcore.

## Zero-time Godzamok cycles and bank rounding

Inputs have zero modeled latency. Thus every finite sequence of same-time
building trades belongs to the comparison class, subject to native affordability.
The practical mod's three-millisecond budget and four-pass limit do not restrict
that mathematical class.

A diagnostic native state holds 101 Mines, a bank of `2^90`, and diamond Godzamok.
One thousand sell-100/rebuy-100 cycles restore those holdings, leave the bank
unchanged, and produce a multiplier of 1,001 without advancing the clock or the
buff timer. Click production updates on the next native frame. A separate
prepared boundary case shows `+1` saturating at `2^53`; larger increments can
advance beyond that value. Selling the last Temple does not remove the slotted
god: the native query reads the retained Pantheon slots.

`GodzamokRounding.lean` proves `unitIterations(n) = min(n+1, 2^53)` for its exact
integer binary64 projection. It also proves that a bank of `2^90` is unchanged
by each integer debit at most `2^36` and each integer refund at most `2^37`,
including ties. The per-copy Mine prices in the tested cycle satisfy those
bounds. The bank theorem covers arbitrary finite folds of such transactions.
Native comparisons check 113 numeric boundaries and 200 price projections.
These results do not execute quadrillions of inputs or prove new-save access to
the diagnostic state. They also do not prove equivalence of other callback,
counter, sound, and random-draw effects. A full strategy proof must preserve them.

## Selected random law and native retry timing

The user selected independent uniform 53-bit free draws, unchanged explicitly
seeded native generators, and an unbounded monotone mathematical clock.
`model/mathematical-assumptions.json` records this choice. A no-argument
`Math.seedrandom()` returns to the free law in this model; native browser entropy
reseeding is not claimed to have that law. LCG sample streams are reproducibility
devices, not implementations of the selected IID law.

Lean checks interval masses on that exact finite grid. Its adaptive Hand-picked
tree allows arbitrary free-draw observations and stopping. At most n attempts
leave failure mass at least 2^-n; this is derived from the kernel. Applying it to
arbitrary native histories still needs source correspondence and the infinite
probability construction. A fail-closed inventory audits all 23 reseed sites and
eight enclosing callback bodies. Lean now checks the control-flow phase analysis
for branches, early returns, loops, and calls. Seven source helpers are expanded.
Unresolved callees produce an unknown phase instead of an assumed identity.
Three callback closures have no unresolved explicit calls. Exceptions, host
operations, extraction, and the other calls still require source refinement.
The excluded You-tooltip leak is detected.

`StartupSeed.lean` proves all 26 thresholds of the rounded native letter
selection projection. Under IID53, a, f, k, o, u, and y each have
346,430,740,566,962 input indices; the other 20 letters each have
346,430,740,566,961. The five-letter prior is the product of those weights divided
by `(2^53)^5`. The proof quantifies over all input indices. Native checks cover
the bucket table, 104 numeric boundary cases, five seed weights, and five actual
`makeSeed` calls. Full JavaScript/host refinement remains separate.

`model/seed-inference.mjs` computes exact weighted posteriors from visible
English fortune numbers, without access to a game handle or private seed.
An exhaustive scan of all 11,881,376 startup seeds maps `(73,43,10,64)` to
exactly `aaodk` and `abeby`, with unequal weights. A visible Mice clicking mice
tooltip separates that pair: its seeded spelling is `blasphemouse` for the
first seed and `blasphemous` for the second. The pinned scan and quote refinement
are in `model/seed-inference-witness.json`. Native comparisons cover 700 seeded
draws. This does not establish that every seed can be identified, but it rules
out silently restricting all legal strategies to ignore such information.
The runtime exposes rendered ticker text; changes to a private seed or raw ticker
string do not change that observation until the native draw updates the DOM.

`SeededWitness.lean` implements the short ASCII key, ARC4 key scheduling, byte
discard, and output normalization for an explicit helper-Grandma witness.
The exact draws agree with the native seed `aaaao 1 0`; the final draw selects
the elf variant for all 19 possible Grandma-synergy counts. Five fixed blocks of
the 53-bit free grid generate the seed with probability at least 2^-25. This is a
source projection and a concrete witness, not a general renderer refinement.

`PetRetry.lean` checks the native pet trigger's exact mass
225179981368525/4503599627370496. For a fixed quarter whose item is known to be
missing, repeat-until-unlock has zero additional modeled elapsed time almost
surely. Every finite cap retains positive failure probability. The infinite
failure path still has infinite hitting time and has zero mass. An already-owned
quarter is a checked countercase to unconditional retries. The controller learns
quarter mappings only from observed new drops and waits when ownership leaves
the phase uncertain. The practical mod bounds each batch for responsiveness.

The finite-Date obstruction is retained only as a diagnostic of a different
clock model. It is not used to declare every strategy optimal with infinite
expectation under the user's unbounded-clock choice.

## Market reachability and startup losses

The earlier controller could sell a holding below the 86,400-dollar Make my day
threshold, lose overhead, and then buy again without winning the achievement.
It now keeps those shares until a sale qualifies. A native alternating-quote
regression checks that the former loss loop is absent.

`MarketRecurrence.lean` translates a specified forcing tick over exact rationals.
From its explicit price and velocity box, it derives 801 ticks to the purchase
band and 231 ticks to the sale band, for the 18 Bank-level 1 resting prices and
Supreme Intellect strength up to 1.1. The draw-word model bounds the pair by
337,464 IID53 atoms and gives a positive finite-cylinder lower bound. Native
comparison covers 576 boundary transitions; the largest observed price and
velocity differences from the rational function are 2.91e-11 and 5.69e-14.
Finite probes do not prove a uniform rounding-error bound.

A funded native controller fixture starts at the upper price bound with all
goods at velocity 300, no office or shares, and 2,000 level 12 Cursors. The previous
completed run reaches all eight market goals in 61,710 native ticks. This is a
specified positive-probability path from a supplied access state. It is not a
new-save route or a uniform finite-expectation certificate. The arbitrary-draw
state invariant, full source/cylinder correspondence, scheduling, and funding
remain separate obligations.

## First-hit traces and necessary bounds

The evaluator checks every completed native action and timer callback. A
completion during a wait is retained even if a later reset loses required
ownership. Lean checks the first complete observation and the absence of an
earlier complete checkpoint on the supplied chronological trace. Finite-horizon
experiments score an unfinished path at the full horizon, reject failed or
budget-limited runs, and hold the policy and environment fixed across samples.
Their restricted sample mean is not the unrestricted expectation.

Full recordings retain the replay. Summary recording retains counts and the
final state without a replay. Current replay metadata pins all eight transitive
model code and configuration dependencies and the Node/V8 execution environment.
Tests change an actual copied completion function and profile and verify
rejection. Historical experiments retain their original, narrower pin sets.

The Garden trace theorem requires two Juicy queenbeet seed acquisitions and two
complete seed-log states. Its first-Seedless transition contract is explicit and
checked on supplied observations. Native probes also check pebbles unlocking a
seed on death, so the theorem does not claim that two manual harvests are
necessary. The source-to-all-executions proof is absent.

The conditional Hand-picked tail argument gives a necessary expected-time bound
of 128,872,038 integer game-clock milliseconds. It assumes minimum spacing
64,436,019 ms, conditional failure probability at least one half, and the clock
and required-goal connection to the full completion survival function. The Lean
certificate uses rational survival tails. An arbitrary policy's connection to
such a lower certificate remains an explicit obligation. Lean checks transfer
to an arbitrary expectation cut when the finite-tail soundness bridge is supplied.
Never completing has
infinite hitting time. No policy attaining this bound, or any matching bound
for all required goals, has been established.

The concrete `SugarClock` transition system now derives the minimum spacing
and no-success/no-completion event inclusion. The native audit covers all seven
timer assignments and kernel-checks eleven projected transitions. Conditional
probability and full source-to-model refinement remain separate premises.
`PolicySemantics` checks public-history noninterference, the 20 ms accepted-click
bound, and finite wrapper-decision bounds from clock ranks and experiment limits.
These limits are not universal restrictions on gameplay strategies.

## Fresh-save experiment

The recorded one-hour sample reaches 30 normal achievements and Neverclick,
with Hardcore still pending and no ordinary upgrades bought. It ends with
7,096,933.219069983 cookies baked, 5,963.8 CpS, and 1,519 missing terminal
conditions. It is censored at 3,600,000 ms. The experiment used the composed
policy before the final combo-controller integration; its exact policy hash,
environment and compressed replay hash are in
`model/experiments/new-save-one-hour.json`. This single sample supplies no
unrestricted expected-time estimate. An earlier unbatched four-hour attempt
was stopped unscored after over 50 minutes of computation.

A later six-hour fresh-save sample used the revised phase schedule and summary
recording. It won both Neverclick and Hardcore and ended with 57 normal
achievements, 57 bought upgrades, 749,701,193,954.4066 cookies baked, and
36,323,453.385966875 CpS. It had not ascended and still lacked 1,430 terminal
conditions. The evaluator processed 72,875 decisions and 1,432,438 native
checkpoints. The sample is censored at 21,600,000 ms; it provides no unrestricted
expectation. `model/experiments/new-save-six-hour.json` records the policy,
environment, summary archive, and source snapshot hashes. Summary recording
does not supply an action replay. The dependency snapshot distinguishes files
captured before the run from dependencies recorded afterward.

A 24-hour request with 50 clicks per second stopped at 51,170,068 ms
(14h 12m 50.068s). A policy decision exceeded the one-second VM execution guard.
The result has status `policy-error` and is unscored. It cannot contribute a
24-hour censored observation. It had two ascensions, 71 normal achievements,
83 bought upgrades, 1,389 missing conditions, and no harvested lump. The run
processed 173,415 decisions, 4,949,512 native actions, 6,484,686 checkpoints,
and 108,798,707 sample draws.

`model/experiments/new-save-24h-request-failed.json` records the compressed result
and immutable source snapshot with their hashes. The snapshot predates the page
startup correction. The original failed decision's memory and suggested action
list were not saved. Short probes with replacement memories do not reproduce
that call and do not determine why it exceeded the wall-time guard. No full-game
completion or expected-time result follows from this failed experiment.

The evaluator now records the exact public input tuple and policy hash when a
decision fails. It records wall-time and decision budgets separately from the
modeled environment, and the CLI exposes both timeout and same-time limits.
Regression tests force failure after two successful memory updates. They check
that no fallback action runs, the completed prefix is retained, full and summary
diagnostics agree, and the result remains unscored. This change cannot recover
the missing decision memory from the earlier run.

## Source interpreter audit extension

The `JavaScriptSyntax`, `JavaScriptState`, `JavaScriptEval`, and
`JavaScriptBuiltins` modules execute syntax over an explicit heap and stack.
A closure contains its source body and environment index. It does not call a
native JavaScript oracle. Property accessors and source callbacks resume through
data continuations. Missing operations produce an unresolved request. A runner
fuel limit leaves the execution running and does not assign a gameplay outcome.

`tools/compile-game-ast.mjs` produces an artifact for the pinned game sources.
The typed Lean decoder checks 153,252 nodes in 40 compilation units. These cover
seven JavaScript files, three inline scripts, four page handlers, and 26 complete
literal handlers. Incomplete handler fragments remain recorded boundaries.
Decoding checks structure, bit patterns, UTF-16 units, references, and unit roots.
It does not prove that Acorn parsed the source bytes correctly. The full native
AST is generated locally and is not redistributed in the repository.

Ordinary numbers have binary64 bit patterns. `JavaScriptNumber` uses Lean's
logical floating-point model. `JavaScriptNumberString` implements decimal
conversion and the source-used parse radices. `JavaScriptMath` translates the
required V8 8.7 mathematical routines, with their original operation order and
license. Unsupported cases, including unimplemented generic parseInt radices,
remain explicit. The mathematical routines do not call opaque native floats.
General correctness and totality for every binary64 input remain proof tasks.

The installed game engine is Electron 11.5.0 / V8 8.7.220.31 / Unicode 13.0.
`model/native-engine.mjs` runs its Node entry point with `ELECTRON_RUN_AS_NODE=1`.
It does not start the game or access the user save. `--engine` selects this
engine for the compatibility checks. The number suite passes 72,384 cases,
including signed zero, subnormals, transcendental functions, and large-angle
reduction. Using a recent Node engine for these checks would test a different
numeric implementation.

`JavaScriptUnicodeData` is generated from four hash-pinned Unicode 13 files.
`JavaScriptUnicode` preserves UTF-16 units and implements full default casing,
including final sigma and supplementary characters. The native check compares
11,456 strings and all 1,114,112 code points for Letter, Cased, and Case_Ignorable.
`JavaScriptRegExp` has an explicit ordered backtracking matcher and passes 947
native cases. `JavaScriptStringRegExp` handles match, search, replace, and split,
including source exec overrides and replacement callbacks. Named replacement
groups and custom split species remain unresolved.

The shared evaluator suite passes 291 installed-engine cases, including 105
executions of exact game helper source. These finite comparisons do not prove
semantic equivalence for all source executions.

`JavaScriptArraySort` executes an explicit translation of the pinned V8 TimSort,
including the source comparator and its call order. The schedule comparison
covers 2,505 arrays and 1,975,984 comparator calls; 32 additional Lean source
executions check sparse arrays, mutations, getters, failures, and merge paths.
`JavaScriptEncoding` covers URI conversion, legacy escape/unescape, and browser
base64. Its native check covers 263,326 cases, including all UTF-16 single units.

`JavaScriptCalendar` supplies an unbounded integer UTC Gregorian calendar.
Kernel proofs establish the 400-year period and selected boundary dates. Checks
compare 5,408 native finite-range cases and 48 large-period extension cases.
`JavaScriptDate` supplies the source-used finite UTC prefix, with 24 native
checks. Source clock values beyond that prefix remain unresolved. The integer
calendar does not yet remove binary64 timestamp limits throughout source code.

`JavaScriptCompletion` reads the interpreter heap directly. It uses the pinned
full completion predicate and rejects unknown host fields, accessors, malformed
counts, and noncanonical catalogue entries. An inductive access-history relation
starts empty and records only observed bought or unlocked flags. Kernel theorems
show that every recorded access has an observed witness and that a successful
heap check satisfies every required goal. Tests cover 65 source-heap fixtures and
one actual new-save data projection. Full source transitions must still preserve
the field invariants and invoke this tracker at public atomic boundaries.

`JavaScriptBrowser` retains DOM nodes, event handlers, resource requests, and
timers as explicit state. The strict HTML parser and complete entity table pass
9,182 native comparisons, including the pinned index tree. Ordered page and load-task diagnostics expose missing host operations.
They have not completed initialization. The explicit environment fixture does
not verify the external Steam wrapper or parser-blocking document visibility.
The asset manifest records native metadata and hashes for 298 images and 81
MP3 files. No asset bytes are redistributed. Metadata does not prove decoding,
canvas behavior, or resource-event order.

`JavaScriptRandom` constructs the binary64 representation of every allowed
free draw directly. Kernel proofs cover all 2^53 indices: the result is finite
and nonnegative, its decoded rational value is exactly k/2^53, and distinct
indices have distinct encodings. This is the deterministic encoding of the
selected law. A diagnostic tape does not itself establish independence.


`JavaScriptExecution` branches at actual free-random requests through the IID53
program constructor. It rejects diagnostic tapes. Seeded calls remain source
operations. Its checked prefix-composition theorem resumes pending execution
without repeating finished callbacks or skipping missing model operations.
Kernel results also preserve elapsed time, normalize mass, and connect a
successful returned-heap completion check to every pinned goal. Fuel remains a
private approximation parameter, not a policy restriction or observation.
The boundary access log reads the actual global Game object. Inclusion of all
transient completion/access checkpoints remains a source-refinement task.

`JavaScriptBrowserStorage` uses explicit origin and quota inputs. The pinned
Electron patch sets the file-origin quota to 104,857,600 bytes. Both keys and
values count as two bytes per UTF-16 unit. The native witness checks both areas
at the exact limit in temporary profiles. Source comparisons cover SameObject,
string conversion and callback order, receiver checks, quota failure, and the
game's wrappers. Multiple-key iteration order, exotic reflection, cross-window
events, and backend failures remain explicit boundaries. No player save is read.

`JavaScriptCylinder` proves that a successful finite branch of the concrete
source prefix has event mass at least 1/2^(53*d), where d is its free-draw count.
The native Garden word is not yet a kernel-checked source trace. A uniform retry
bound also needs a common draw count and a source invariant at every entry.
`CollectionEnvelope` checks extracted catalogue factor budgets and proves a
reset-counter barrier for arbitrary finite prefixes: old <=2^1000 and earned
<=2^940 imply the integer-rounded update remains <=2^1000. The per-epoch earned
bound and its source/binary64 refinement are still premises.

`Binary64WaitLattice` proves that accepted Number-valued waits lie on the exact
2^-1074 ms lattice. This result concerns that input representation; it does not
restrict arbitrary external strategies or bound zero-time action histories.
`ChromiumTimerIds` proves the active-ID bound and freshness rules for the explicit
coordinator. `BootstrapArithmetic` proves scaled integer rounding bounds for
passive Cursor income and repeated 0.01 multiplier additions. Source-callback
refinement and the complete new-save route remain open.

The complete browser host, unbounded source-clock bridge, legal control relation,
public observation projection, proper completion policy, and optimality
certificate are still required.

The arithmetic bridge now includes `JavaScriptRoundingBridge`,
`JavaScriptDyadicArithmeticBridge`, and `CollectionEnvelopeNative`. Kernel proofs
connect residual bits, nearest-even rounding, normalization, and packing to the
integer projection for every input below 2^1023. They cover zero, small exact
integers with negative canonical exponents, actual interpreter addition, and
affordable subtraction. The counter wrappers retain explicit input and source
credit premises.

`JavaScriptFractionalRoundingBridge` proves the actual packed rounding bound for
N/2^d: if N>=2^(52+d), 53<=B<=1021, and
N<=2^(B+d)+2^(B+d-53), the result is finite, nonnegative, and at most 2^B.
No divisibility premise is needed. This includes the exact halfway tie. Source
callback bounds and the full route invariant still require proof.

The AST format now retains exact UTF-16 source text for functions, including
accessors. The native host catalogue records 3167 immutable callable texts.
`JavaScriptLexer` and `JavaScriptParser` parse the pinned source grammar. The
358 checks include structural comparison of all 40 pinned source units and
240 generated precedence cases. `JavaScriptDynamicFunction` uses that parser,
retains native parameter/body conversion order and wrapper text, and passes
44 checks, including 40 native comparisons. Unsupported modern parameter forms
and legacy active-call reflection remain explicit. These comparisons do not
prove universal equivalence to the native parser.

`JavaScriptCounterSource` executes the extracted `Game.Earn` and `Game.Spend`
bodies for arbitrary 64-bit operands in an explicit counter heap. Kernel proofs
check field updates, normal statement completion, ordinary function invocation,
argument binding, the undefined return value, and restoration of the caller. `cbv_opaque` prevents
the proof evaluator from expanding the already-defined arithmetic during this
structural proof; it does not add a logical assumption. The source generator
checks the pinned main.js hash and retains compound-assignment order.
`JavaScriptCounterFrame` proves body execution with arbitrary extra objects,
environments, and game fields. `JavaScriptCounterLens` permits Game at any heap
index, either counter-field order, and arbitrary other fields before, between,
and after the counters. Its whole-machine equality preserves unrelated state.
The entry uses explicit declarative bindings; correspondence to the initialized
game's actual environment chain and field invariants remains to be proved.
`JavaScriptEnvironment.identifier_declared_eq_original` checks that the browser
environment layer preserves the core identifier result for an immediate
declarative binding.


`JavaScriptNaturalArithmetic` proves exact binary64 addition and affordable
subtraction for natural operands below 2^52, including zero. The extracted lump
callbacks supply checked early maturity/ripe/overripe times, the zero-Grandma
wrath prefix, and a nonmeaty yield support of one through seven.
`JavaScriptLumpPrefix` proves that any 136 such credits supply the 136 lumps for
the proposed finite levels. The timing calculation gives 11,260,800,136 ms for
136 ripe intervals with one millisecond slack each. These are source fragments
and arithmetic results. The full heap, random-range, input-scheduling, and
new-save funding invariants remain obligations.

The user permits scheduled maintenance reloads that save the current state and
then reload it. Outcome retries and earlier-save restoration remain forbidden.
The adapter implements a precommitted schedule through the native save/load
path, with a fresh VM, retained current save, and continuing free-draw stream.
It retains the native startup delay, save rounding, and temporary-effect loss.
Requests during loading or ascension are deferred. This implementation covers
a scheduled subclass; it is not a proof that all permitted reload schedules
are represented.


`JavaScriptScaledArithmeticBridge` now connects the actual binary64 additions
to the earlier scaled integer recurrences. `native_passive_reaches_billion`
checks the repeated native `0.1/30` credit from zero: within 512 billion
additions its finite nonnegative value is at least one billion.
`native_cent_cap_reached` checks that 2^56 additions of native `0.01` to one
give exactly native 2^47. These are universal arithmetic results. The source
production, sale, buyback, and scheduling invariants remain separate.
`JavaScriptLumpSourceComposition.source_times` also runs the intact timing
callback with the actual `Has`, `auraMult`, and Pantheon `hasGod` helpers in
three explicit early layouts.

Source functions now retain inferred names as metadata, configurable length,
and the tested getter/setter construction rules. Inferred names do not create
lexical self bindings. Strict functions use the shared throwing accessors.
Unknown active caller/arguments descriptors of sloppy functions stop only
operations that require them; ordinary inherited call/apply remains available.
The 53 checks include 43 native comparisons and ten explicit reflection limits.

The CSS layer parses both pinned stylesheets outside Lean, then decodes typed
selectors and declarations into Lean. Its selector, cascade, and integral
positioned-box subset passes 301 checks, including 271 native comparisons.
Another 77 checks exercise the live Browser adapter. It derives geometry from
connected links, live element fields, declaration state, and the explicit
viewport; native rectangles are not input. A closed Lean CSS parser now handles runtime stylesheet text, including the
actual Game.Launch background rules. General layout, hit testing, and unsupported
stylesheet grammar remain open. The input-event adapter passes 160
checks, including 156 native comparisons and ten actual mouse/key callback
slices. Event fields do not by themselves prove trusted input targeting or
default activation.

The combined `python3 lean/check.py --engine` run passed at the CSS/input/function
metadata checkpoint, with 649 proof reports and no added logical assumptions.
Its checkers use temporary regular files for fixture input. A sampled macOS
process had blocked in `readToEnd` while waiting for input-pipe EOF; the transport
change preserves fixture bytes, exit status, and timeouts. Two tests cover empty
and large UTF-8 fixtures, failures, timeouts, and temporary-file removal.


`JavaScriptCounterEnvironment` proves the same counter-body updates through the
builtin driver, including local `howmuch` and an outer Window data binding for
`Game`. It retains arbitrary Game heap placement, counter-field order, and extra
objects. The concrete entry-environment layout remains explicit.
`JavaScriptGodzamokSource` executes the selected native sale branch with actual
Pantheon and buff/aura helpers for arbitrary multiplier and deadline bits. It
adds one native cent, preserves the deadline and the twelve entry objects apart
from `multClick`, and connects the result to the scaled arithmetic theorem. The
whole sale prefix, prices, buyback, and UI admission remain separate obligations.


`JavaScriptBankCycleBridge` proves native refund/debit identities for every
canonical finite bank from 2^58 to below 2^1023: adding any integer from zero
through four, or subtracting any integer from zero through fifteen, preserves
the bit pattern. The proof covers the lower binade at powers of two and every
finite repeated-cycle prefix. Native Cursor formulas give refund four without
a free Cursor and three with Starter kit. The full price-modifier and source
cycle invariants remain obligations. `JavaScriptThresholdBridge` connects the
actual earned15 recurrence to the intact `canLumps` callback and proves it
returns true by the stated finite credit bound.

The focus adapter passes 88 checks, including 80 native comparisons. Its
supported fragment retains nested focus callbacks and exact activeElement
fallback rules. Native default scrolling, editable selection, and focus loss
from DOM/style mutation remain explicit. Element size metrics pass 72 checks,
including 55 native comparisons and three actual animation-helper slices.
Window.name passes 40 checks, including 39 native comparisons; an existing
global accessor survives `var` hoisting, and the initializer uses its setter.

The full native audit passed with 705 registered reports after adding three
previously omitted theorem names and three elapsed-wrapper equivalences. The wrappers save the elapsed
scalar before taking a transition; reflexivity proves equality to the old
expressions. This permits runtime heap reuse without changing any transition.


`JavaScriptBrowserCanvasState` models the pinned drawing-state stack and its
native scalar setters. Canvas checks pass 334 cases, including 328 native
comparisons. Dimension changes reset drawing state and saved states while
preserving context identity and creation alpha. Raster drawing, paths,
transforms, fonts and CSS colors remain explicit boundaries.

`JavaScriptCssWidth` computes a guarded horizontal used-width fragment from the
actual DOM and CSS inputs. Its 128 cases pass through both the pure and live
Browser interfaces, including 110 native comparisons. Percentage calculations
retain the pinned binary32 restrictions. The overflow projection has checked
cascade guards; layout-triggered events and complete renderer effects are still
separate from the returned sizes.

`JavaScriptHasFrame.native_has_body` executes the intact Has body through the
builtin driver in 59 steps. In normal ascension it returns the actual bought
value and preserves all objects and caller state, apart from its local temporary.
Heap positions and unrelated fields are arbitrary. Ordinary object kinds, own
data descriptors, and the local-to-Window environment layout are explicit.
The actual initialized closure environments remain a composition obligation.

`JavaScriptLoopArithmeticBridge` proves the native 33 ms timer conversion, negative
latency credit, nonpositive accumulated-delay invariant, and finite calendar and
counter bounds for 512 billion passive frames plus 150 initial frames.
`JavaScriptLoopSource` executes the extracted catch-up, latency, clamp and timeout
statements. The catch-up loop is skipped on every represented prefix. The full
Loop/Logic/callee and initialized-scheduler composition is not yet proved.


The full native audit passed at the canvas/width/Has/Loop checkpoint with 777
registered theorem reports, with only the standard Lean logical assumptions.
The repository suite passed 305 JavaScript tests and seven patcher tests. The
rebuilt 39-page paper passed visual inspection of its changed pages.


The integrated clock/export/font/matrix checkpoint passed the full native audit
with 1,000 registered theorem reports and only standard Lean logical assumptions.
The repository suite passed 313 JavaScript tests and seven patcher tests. The
rebuilt 40-page paper passed visual inspection of pages 31–40.

The source interpreter now uses exact extended timestamp and calendar values
without changing ordinary binary64 arithmetic. Fifteen source-specific annotations
cover save/gift readers and zero timestamp initializers. Erasing them reproduces
the pinned original syntax. The checks execute native source calendar, gift,
Pantheon, Garden save, and counter code at large dates; missing propagation or
source refinement is still a separate obligation. Native export inspection is
allowed through the visible readonly textarea. The runtime retains export's save
bookkeeping and rejects a maintenance trace that would restore a stale save.

The actual Has source-call proof retains argument allocation and the caller frame.
Its source property lookup and literal argument take a further 12 interpreter
steps. The ComputeCps call retains the native Math.pow invocation and exact Cursor
base result. GetTiered declaration setup and its first local assignment are checked;
the remaining body, CalculateGains, whole Logic/Draw callbacks and full route are
not certified by these helper results.

Canvas checks pass 491 cases (484 native). Affine arithmetic passes 1,489 native
cases and 261 source-call cases (257 native). Snapshots preserve matrix, parsed
font metadata and drawing fields. The fixed font fragment passes 221 cases
(202 native); fixed color parsing/serialization passes 7,203 (7,191 native).
These tests retain coercion callbacks, singular transforms, zero dimensions,
save/restore and dimension resets. Nonzero C-library rotations, general painting,
readback, font lifecycle, context loss and full renderer refinement remain open.

This checkpoint is not an optimal full-game strategy or a global certificate.
The complete transition/refinement, a legal attaining policy, and a matching
expected-time lower bound remain required.


The next integrated audit passed with 1,032 registered theorem reports and only
standard Lean logical assumptions. The repository suite passed 320 JavaScript
tests and seven patcher tests. The 41-page paper was rebuilt; pages 31–41 were
visually inspected. The first audit attempt found an obsolete negative fixture
for fillRect; it now checks the remaining pixel-readback boundary, and the entire
suite passed on rerun.

The native arguments.callee descriptor is retained through actual calls. Strict
arguments use the captured throwing intrinsic; missing direct-call identities
stay unresolved. Function checks pass 74 cases, including 64 native comparisons.
The native two-element choice arithmetic has a universal kernel proof: multiply
the IID53 encoded draw by two and apply the actual Number.floor implementation;
the result is each index with probability exactly one half. Source call binding
and the global generator-phase invariant are separate requirements. The phase
audit records 23 seedrandom sites in eight owning functions and keeps exception
paths explicit, since resets are not protected by finally.

Textarea checks pass 157 cases, including 156 native comparisons. Parsed native
export text, dirty values, direct text-child dependencies, CR/LF normalization,
reflection and source conversions are retained. Selection checks pass 82 cases,
including 80 native comparisons. Native select events are queued for explicit
rendering opportunities; active dispatch batches cannot expose a policy boundary.
Focused FrameSelection, selectionchange tasks and caret scrolling remain open.
The CSS suite passes 328 cases (292 native) and 87 live Browser cases; focus passes
96 (87 native). Source diagnostics now return from Game.Init and enter the
first-launch language prompt; that prompt and complete startup remain unfinished.

Rectangle checks pass 82 cases (79 native), retaining typed geometry and drawing
snapshots including exact color bytes. A native pixel witness shows why empty
rectangles cannot simply be deleted under copy/source-in composition. Complete
rasterization and readback remain open.

FullObservation proves that a public policy lifts into a stronger competitor
class with complete current-state observations and an enlarged legal action set.
The lift preserves startup averaging, admissibility, every capped expectation and
the hitting-time lower cut. Thus a universal lower bound in that class transfers
to public strategies. This theorem supplies no game-specific value function or
attaining policy; full-game optimality remains unproved.


The source-choice and focused-host checkpoint passed the full native audit with
1,184 registered theorem reports and only standard Lean logical assumptions.
The repository suite passed 320 JavaScript tests and seven patcher tests. The
41-page paper was rebuilt and pages 30–41 were visually inspected. Sandboxed
Chromium workers aborted before producing output; the isolated encoding check
and the full audit passed outside that sandbox. Audit profiles were temporary,
networking was blocked, and player saves were not loaded.

The intact choose([0,1]) expression now resolves the global source declaration,
allocates the literal array and mapped arguments object, and reaches a free draw
in 43 source steps. Eighteen response steps return its exact native value. The
composed unripe branch takes 75 steps to that request and 31 response steps
through caller return, the mutable amount write, and its native award gate.
Every prior object and the native allocations are retained. The intact Win body
writes the achievement flag in 98 steps under its entry contract; notifications,
counting, recalculation and the Steam callback remain in its pending continuation.
Sixteen native source checks cover these effects and failure ordering under
explicit diagnostic callback fixtures. Initialized entry correspondence, the
triggerAnim/canLumps/Date prefix, global free-generator phase, and complete Win
composition are still separate obligations. These results do not establish the
whole harvested-event law or a full-game optimality certificate.

Focused textarea selection passes 81 cases (65 native), retaining cached ranges,
frame selection, internal revision identity and distinct deferred selection-change
and select-event queues. Border checks pass 110 cases (100 native), including all
25 pinned source declarations. Width and height each pass 145 cases through the
pure and Browser interfaces (119 and 107 native respectively). Background
position passes 161 checks (154 native), preserving internal precision separately
from CSS text. The existing Browser suite passes 489 cases.

The configured-English diagnostic returns from native source initialization,
first Logic/Loop callbacks, two Draw calls and the loader callback. Later tasks
drain all twelve pending image requests before reaching a nonzero native canvas
rotation. The empty-language web fixture still reaches the unresolved first
language prompt. Neither fixture executes the external Steam wrapper. Prompt
and canvas source inventories identify callback, alias, task, observation and
input-reachability obligations; they do not assert general display noninterference.
The full-game transition refinement, a legal attaining completion policy and a
matching expected-time lower bound remain open.


A proof-only follow-up passed 1,299 registered axiom reports with standard Lean
logical assumptions and no proof placeholders. It did not change the interpreter
or browser drivers from the fully tested 1,184-report checkpoint. The repository
suite now passes 326 JavaScript tests and seven patcher tests.

The actual literal Game.Win call reaches the achievement write in 135 steps,
with mapped arguments, declaration setup and arbitrary declarative closure paths.
JavaScriptLumpWin composes that call with the actual successful choice response:
167 post-draw source steps reach Hand-picked.won=1. Allocations, elapsed time,
exactly one free draw and the five pending native effects remain in the result.
A complete necessary-event theorem still needs initialized-frame invariants,
current-save provenance, exclusion of debug award routes, and global free-RNG
phase preservation. Notification/platform suffix completion is also unproved.

JavaScriptRandomSmallChoiceBridge proves the actual binary64 multiply/floor
calculation for every IID53 draw at array lengths five and six. Golden yields
2..7 have counts [1501199875790166,1501199875790165,1501199875790165,
1501199875790165,1501199875790165,1501199875790166] out of 2^53. Meaty yields 0, 1, 2
have counts [3602879701896397,1801439850948198,3602879701896397]. The exact means
remain 9/2 and 1. These laws differ from uniform source-array positions; three
native bucket boundaries differ from a real-arithmetic floor calculation.
The source audit checks 2,055 actual native choose results. The whole harvest
callback and its free-generator entry condition remain separate obligations.

The mathematical optimum remains unproved. Native export inspection is allowed.
The user has now forbidden timing chosen to change seeded outcomes, including
harvest timestamps selected using the exported seed. This excludes the audited
seed-search tactic. A complete admissibility model must constrain decision rules:
the same timestamp can result from an ordinary schedule or from a seed search.
The observed trace alone cannot establish this distinction.

The probability and composed-award paper update was built with tectonic, copied
to paper.pdf and visually checked on pages 30–41. The final PDF has 41 pages
and 275,019 bytes. No mod runtime or release version changed in this follow-up.


The final proof-only choice-body follow-up passes 1,329 registered axiom reports.
JavaScriptChoiceArraySource executes the intact choose body for an arbitrary
native length descriptor and selected data-property value. Its lengths-five
and -six specializations connect the exact rounded bucket calculation to the
source return and event masses. The native array allocation, call setup and
complete harvestLumps composition for these two arrays remain open. The browser
and executable drivers are unchanged from the full native audit; the repository
suite remains at 326 JavaScript and 7 patcher tests. The reviewed paper.pdf remains
current. The full-game optimum is not established.


Unmerged renderer continuation: /tmp/cookie-canvas-integration/CHECKPOINT.json
records an isolated symbolic-transform prototype, source hashes and validation.
Its matrix cache is absent after an unresolved native rotation; save/restore and
paint snapshots retain the operation history. The clone passed 259 build jobs,
39 deferred cases (34 native), existing Canvas 491, Fill 82 and matrix 1489 + 261
checks, and five standard-only theorem reports. Its actual source probe reaches
the loaded-shine drawImage call after rotation. Shared code retains the earlier
explicit rotation boundary. The clone has not been merged: C-library/backend
refinement, normal-return correspondence and drawImage admission/source snapshots
remain obligations. The fancy graphics preference does not skip the shine draw.


The 30 October follow-up applies the user's explicit ban on timing chosen to
change seeded outcomes. Native current-save export inspection remains allowed.
The evaluator now records `strategyReview`: action replay cannot certify the
reason for a selected timestamp. The mathematical-assumptions file is included
in the ten-file replay dependency set. Its hash changes invalidate old replays.
The mod's lump controller uses observed maturity and ripeness, without seed
search. The dragon controller learns exhausted quarters from actual drops;
source quarter selection uses one fixed seeded permutation.

The randomized-controller semantics now permits fresh private samples and
remembered state at every decision. Its capped lower-certificate theorem places
no bound on the total number of decisions or draws. It includes deterministic
controller values unchanged and assigns infinite time to permanent zero-time
stalls. Each individual sampler and transition still terminates. This closes a
competitor-model gap; it does not supply a full-game value certificate.

The source eligibility prefix now executes canLumps, its real call allocations
and return, Date.now(), timestamp subtraction and the local age write. The
69-step prefix preserves all pre-existing objects and consumes no free draw;
composition reaches the unripe free draw in 144 steps. The original arithmetic
JavaScriptLumpPrefix module remains intact; the new composition is
JavaScriptLumpClickPrefix. Two DOM animations, initialized frames, global
RNG-phase preservation and complete achievement provenance remain unproved.
Forty-eight source comparisons pass, including 36 installed-native cases and
12 unbounded-clock cases; their DOM/award callbacks are diagnostic fixtures.

The reviewed canvas checkpoint is now merged. Nonzero native rotations retain
an operation history and invalidate the numeric cache. drawImage retains an
immutable source scene, source identity and drawing snapshot. It does not
supply pixels or an origin-clean result. Native error objects, unsupported
resource selection, path operations and readback remain explicit boundaries.
The native-transform, backend, allocation and raster realization conditions are
still open. The exact image-byte audit admits 245 of 246 PNGs and all 46 JPEGs;
the excluded PNG has orientation metadata. The image-call suite passes 78
cases (61 native comparisons), with another 39 transform-history cases
(34 native comparisons) and 82 fill cases (79 native comparisons).

The particle effect audit records seven complete source functions, nine live
callsites, two returned aliases, random draws and image-load jobs. Twelve
guarded source fixtures pass. A cache miss can invoke Loader.loaded unless
Loader.doneLoading is already 1. An economic projection must retain that effect
or prove the phase invariant. The audit is not a Lean simulation theorem.

Full-game optimality remains unproved. There is no proved proper new-save route,
attaining policy, expected value or matching universal lower bound. The audit
has also found no valid proof that the requested optimum fails to exist.

The frozen canvas interpreter completes the configured-English 180-task source
prefix at Game.T=155 and drawT=156. It consumes 181 of the 4,096 diagnostic
uniform53 indices, drains 23 resource events, and returns with no pending
continuation. Four thousand ninety-six fixed draws are a finite test path, not
an expectation calculation. The diagnostic took 270.22 seconds on the host.
The earlier 120-task attempt stopped after its 100-value tape was exhausted;
that was a diagnostic limit, not a semantic failure. The probe now accepts
`--random-input-count` and records the chosen count separately from game rules.
The full Steam wrapper, universal callback coverage and global optimality remain
open. A separate core exception-object audit found that synthetic own `name`
properties still need native prototype refinement; the new drawImage
DOMException branches remain explicit instead of using that approximation.


Validation for the merged follow-up: `python3 lean/check.py --engine` passes
with 1,431 registered theorem reports, using only propext, Classical.choice and
Quot.sound. The full pinned-engine suite includes the new image, deferred-transform
and lump-prefix checks. `npm test` passes 326 JavaScript tests and seven patcher
tests; the mod suite passes 179 tests. The release remains 2.053.18, with the
existing manifest and bundle unchanged by this follow-up. The paper was built
with tectonic, copied to paper.pdf, and all 42 pages were visually inspected.
The final PDF is 278,995 bytes with SHA-256
f6e738f7c0875067dc3ddd473f3ecef9eee3ccc6eff0adb4e2105f0fa282d91f.
These checks do not establish full-game refinement, a proper completing route,
or global optimality.


## Native opening composition and source input follow-up

The new `JavaScriptBootstrapLadder.native_ladder_billion` theorem composes the
eight-stage binary64 opening, with seven first-affordable purchases after
the initial Cursor. It reaches bank at least one billion from zero within
6,660,050 production credits. Every stage retains a zero or normal bank at
most 2^30. Three supporting modules prove exact dyadic progress, affordable
subtraction including cancellation, and first-hit upper bounds. These results
accept arbitrary retained normal bank denominators. They do not assume the
new stage resets the bank to zero.

The conditional tick allowance is 6,660,208, or 219,786,864 ms at 33 ms per tick.
Fifteen 20 ms click gaps give 219,787,164 ms from a ready entry. The diagnostic's
separate 200 ms readiness premise gives 219,787,364 ms. Readiness, source
CalculateGains/Logic preservation, native purchase admission and
cookiesEarned>=bank preservation are still unproved. This improves a
conservative arithmetic construction; it is not an optimal-opening theorem.

The native bootstrap witness now executes seven actual purchases at explicitly
injected affordability boundaries, retains the existing Temple, and checks
the new CpS values and both achievement flags at a separate injected boundary.
It does not execute the intervening long trajectory.

The seeded callback entry now has 32 source steps to the exact timestamp-qualified
UTF-16 argument and one further step into the captured library closure, with
its real mapped arguments and lexical allocation. Twenty-nine focused cases
pass, including 27 ordinary native comparisons and two selected extended-clock
arguments. The complete seeded setup and callback have not been composed.
The separately proved 14-step reset/return endpoint uses the explicitly
selected zero-argument restoration rule. Fifteen cases pass, including twelve
intact computeLumpType calls and thirteen native comparisons under that rule.
This is not vanilla seedrandom function-identity refinement.

The reviewed MouseEvent fragment admits only the stated script-generated
paths; a click must be canceled before completion. Trusted pointer targeting,
page coordinates and general default actions remain unresolved. Thirty cases
pass with 23 native comparisons. The fresh-media fragment passes 16 cases with
ten native comparisons; three additional checks cover parsed autoplay and
monotone removal provenance. Playback and volume-change tasks remain open.

The exact source-click diagnostic and its reproduction command are retained
in `model/source-click-stages.json` and `model/source-click-witness.json`. The
reviewed replay earns one cookie and records one click, consumes 48 free draws,
and retains the real sound request before stopping at volume 0.140625. It uses
a synthetic null-view event sequence, so it does not establish an ordinary
physical input or any complete gameplay route.

Validation: `python3 lean/check.py --engine` passes with 1,550 registered theorem
reports and only the standard propext, Classical.choice and Quot.sound
dependencies. The full pinned-engine suite includes both seeded-entry/reset
checks and both new browser checks. `npm test` passes 326 JavaScript tests and
seven patcher tests. The mod source and 2.053.18 release were not changed in this
follow-up. The 43-page paper was built with tectonic and visually checked;
unchanged pages retain the prior inspection. `paper.pdf` is 282,730 bytes with
SHA-256 `a3fdb457c4578ab8de1abf063824dd72ac9efc18b9e5f33a44b35552bc530071`.

The full requested result remains open. No full-game proper new-save policy,
attaining expected-time value or matching universal lower bound has been
proved. No valid full-game nonattainment obstruction has been established
either. Finite binary64 fields alone do not prove finite normalization of
zero-time histories or the existence of an optimal strategy.


## Timestamp-string extension and complete production calls

The selected mathematical assumptions now extend timestamp-derived text to
arbitrary finite length. The source interpreter retains tagged timestamp text,
exact traversal in the captured native mixkey activation, and provenance through
the actual save-codec helpers. Economic Numbers and the storage quota are
unchanged. The mixkey activation is accepted by an exact source-body recognizer;
its soundness and its native-body acceptance are kernel checked. Bounded integer
conversions, arbitrary native byte masks, and the selected exact-index operations
are proved. The complete tagged seed loop and its composition with ARC4 remain
open; finite seeded comparisons are not a termination proof.

The production proof now includes the complete GetTieredCpsMult member call,
both registry loops, all final guards and caller return. It retains every
executed Has allocation. The eighteen complete Farm-through-You callbacks
compose that call with magicCpS, their actual compound assignments and final
return, including the original me.cps(me) expression. The complete eff call
returns one when its default is omitted and the named effect is absent. The
complete auraMult call returns zero for two native No aura selectors and a
different requested name. These theorems retain the source property reads,
argument objects, local environments and original caller state. The global
Game-read lemma permits the actual nonconfigurable Window property.

The source catalogue inventory checks 20 building callbacks, 305 tier entries,
72 synergy edges, 20 fortunes, 18 Grandma ties and 359 distinct upgrade objects.
These are source and snapshot checks, not initialized-state theorems. Cursor,
Grandma, full CalculateGains/Logic preservation, native input admission and
completion of the full route still require composition proofs.

Validation for this checkpoint: the complete pinned-engine command
`python3 lean/check.py --engine` passes with 1,959 registered theorem reports
and only propext, Classical.choice and Quot.sound. The native suite includes
31 timestamp-text seed cases and 8 save-codec cases. A host-only run under
Node 23.6.0 fails a Math.log comparison by one bit; the target Electron 11.5.0 /
V8 8.7.220.31-electron.0 run passes all 72,384 Number cases. The host-only result
must not be reported as a successful native verification. The earlier JavaScript
and mod runs in this continuation pass 326 page/model tests, 7 patcher tests and
179 mod tests. No mod bundle or version changed in this checkpoint.

The paper was built with tectonic and copied to paper.pdf. All 44 pages were
inspected in contact sheets, and the changed production page was inspected at
full reading size. The PDF is 286,745 bytes with SHA-256
`e418623e309c824451e79a492cc6efe239884fea16d61f57acaf19fba2b792c9`.

There is still no proved full-game transition refinement, proper new-save
completion policy, attaining expected-time value or matching universal lower
bound. There is also no proved full-game nonattainment obstruction. The main
requested optimum remains open.

## Complete building callback checkpoint

The shared kernel now checks all twenty no-upgrade building source callbacks.
The eighteen common callbacks retain their explicit canonical positive normal
base-CpS premise. Cursor covers the eight finite opening amount boards, executes
all twenty building rows and all nested helpers, and returns the native 0.1.
Grandma executes its complete building and synergy loops and returns native one.
Their arithmetic results follow from executed source statements. Each call
retains its arguments, environments and nested allocations and returns to the
original caller. These are conditional call theorems; source initialization has
not yet established every catalogue and environment premise.

The complete heavenly multiplier call executes all eight Has calls, its aura
call and missing-God branch and returns zero in 902 interpreter steps. The
missing-buff call returns zero in 42 steps. The empty mod-hook call keeps the
native array-length lookup and returns its input with all allocations retained.
The shared audit passes 2,352 reports using only the standard allowed axioms.
These proof-only additions do not alter the interpreter checked by the earlier
full pinned-engine suite. The Cursor integration checks all twenty checkpoint
file hashes before copying the frozen source.

The paper was rebuilt and copied to paper.pdf. The changed pages 37 and 38 were
rendered and inspected. The PDF has 44 pages and 287,426 bytes, with SHA-256
`ba993d4456daeeaa9910a267b8232988a4f0eb189d75b7ec71b4d4fc9527e498`.
No mod source or release bundle changed in this checkpoint.

The full CalculateGains callback still needs the cache-write loop, mouse-CpS
call and complete new-achievement side effects. Source initialization, whole
Logic/Draw preservation, native input admission, the proper completion route
and the minimum expected-time proof remain open. No global optimality claim
follows from this checkpoint.

## Native completion counter, controlled execution, and discarded magic

The completion predicate now requires the actual `Game.AchievementsOwned`
counter to reach 600, in addition to the normal achievement flags. The native
milk selector reads that counter. `Game.Win` sets the flag before notification
work and before incrementing the counter, so a thrown callback can leave them
different. Missing, invalid and accessor-backed counts fail closed. The
collection manifest now has 1,559 conditions. The corrected normalized and
source-heap comparisons pass 56 and 77 cases, plus one actual new-save
source-data comparison. The existing two-sugar-achievement consequences remain.

The controlled source kernel composes actual interpreter ticks, IID53 requests,
timer/resource queue selection and returned-boundary completion. It retains
rational deadlines, reactive waits, native allocations and private source
steps. The decision-machine extension permits unbounded private computation
and sampling before an action. Missing transitions have no numerical cost;
genuine divergence and noncompletion cost infinity. Native physical input,
maintenance scheduling, task priority, observations, policy restrictions and
completion-checkpoint coverage remain explicit obligations.

The source proof now executes the tagged seed expression through its complete
mixkey return in the BrowserRuntime. Its exact cost is
`250 + 93*N + 2*min(N,256)` steps for any finite UTF-16 seed length `N`.
ARC4 construction, generated-function installation and the remaining complete
callback are still open. New general arithmetic proves actual JavaScript
remainder for natural operands below 2^52 with a positive divisor. Further
source proofs cover the complete EN localization call, dense-array queue
operations, source member calls, first cache-field creation, and the actual
dispatcher clock laws. The combined kernel audit passes 3,456 reports with
only `propext`, `Classical.choice` and `Quot.sound`; no proof placeholders or
unchecked native decision commands are present.

A new source regression rejects unconditional persistence of completion to a
callback return. In a supplied late-game state, a second Garden sacrifice
earns Green, aching thumb during its initial harvest and then clears 33 required
seeds. Completion holds between those operations, including the native counter.
A separate harvest retains completion at the same elapsed time in that
fixture. These are conditional adapter regressions, not new-save reachability
or a general replacement-policy proof.

The paper's full-magic rule now states its fixed-capacity, fixed-cost,
continuous-regeneration objective. A potential argument bounds every schedule,
including nonperiodic schedules: `n*D <= T + H(m0) - H(mT)`. This is an
asymptotic cast-frequency result. It is not a fixed-goal or native full-game
optimality theorem.

Local mod candidate 2.053.19 spends otherwise discarded magic immediately
before an already-planned ordinary ascension. It runs after cash-in, loans and
the Lucky wait, respects the Grimoire switch, and stops at the 999-cast award
or affordability. Both outcomes of Haggler's Charm and Diminish Ineptitude
retain cookies and lumps. Reset clears their temporary buffs and retains
their count and achievements. No extra reset, outcome cancellation, seed
search or future RNG read is added. This is a tested heuristic improvement;
seeded state and future observations still depend on cast history.

Validation passes 330 repository tests, seven patcher tests, 190 mod tests,
full mod source/test ESLint, and the readable webpack build. Webpack reports
three advisory bundle-size warnings. The manifest and every archived mod file
hash agree. The candidate bundle has 688,914 bytes and SHA-256
`b27ca5e295a0670806a41ff8becd291727c73cda3f0be299297cfb8bae866073`.
The local archive has 278,986 bytes and SHA-256
`f22dcaadef57c5184c014c95ca280b5a5d5d1da197160b020918f3b60ec71e6f`.
It has not been published or installed in the player's game.

The complete `python3 lean/check.py --engine` suite also passes against the
pinned installed engine in isolated temporary profiles. It checks the source
generators, builds all 553 targets, checks all 3,456 theorem reports, and runs
the native numerical, browser, source, completion and policy comparisons.
The corrected completion observation had made the diagnostic catalogue's
runtime identity stale. Re-executing `audit-tiered-catalogue.mjs` reproduced its
descriptor and production results and updated that identity. No old witness
hash was changed without rerunning its audit. The player's save was not loaded.

The rebuilt paper has 46 pages and 296,091 bytes, with SHA-256
`8f929fa5a5d8e7d0207c12d124fb5f56a49bae18147565cc4028636de5f04576`.
All pages were inspected in contact sheets; pages 23, 43 and 44 were also
inspected at full reading size. The build retains the existing algorithm.sty
UTF-8 warning. The author and license text are unchanged.

No complete source refinement, proper new-save completion policy, attained
expected-time value or matching universal lower bound has been established.
The requested full-game optimality result remains open.

## Source microstate completion and reset-based spell counts

The completion monitor now reads the source heap before each interpreter step.
This addresses the tested Garden callback that reaches completion during its
initial harvest, then locks seeds before return. The 17 selector-access flags
have separate checked descriptor reads, so a transient unlock is retained even
when the full game snapshot is not yet available. A log entry carries its actual
Game-root and descriptor-read equations. Unknown host fields and getters remain
explicit missing-model results.

Four new completion theorems establish the native-counter projection and gate:
every successful snapshot has the recorded native counter; a completed snapshot
passes the gate; and a false gate cannot hide a completed snapshot. Known absent
Game/counter fields during startup can therefore be rejected without inventing a
complete catalogue. The private first-hit kernel preserves the source heap and
controller information, has no mid-callback decision, and retains a found time
through every longer cost prefix. Missing semantics have no numerical cost.
The 21 registered new theorem reports add no full-game refinement or minimizer.

`lean/check_javascript_completion_monitor.mjs` passes 10 source microstate cases,
including transient completion, transient access, absence during startup,
unsupported getters and a hit before a later source failure. Two corresponding
pinned-engine heap comparisons pass. These are supplied synthetic states, not
new-save reachability claims.

The frozen ARC4 loop checkpoint adds 16 source modules and 117 registered reports.
It proves the two original constructor loops plus their intervening statement
in 37,661 builtin-machine steps, from explicit nonempty normalized-key and
empty-state-array premises. It retains all 256 initialization writes, 256 schedule
iterations and the original key. Thirteen native constructors and 104 subsequent
generator calls are registered in the pinned-engine suite. The remaining
constructor setup, empty-key branch, discarded generator prefix, runtime lift
and installed seeded function are still open.

The experimental completion policy now has a separate ordinary-reset spell
phase. It requires actual 100 profitable resets and the funded growth boundary,
casts once per reset at Wizard level 1, and finishes its last reincarnation before
final collection. A continuous 999-cast diagnostic source run takes 5,335,760 ms
from its explicit 1e57-cookie/one-lump entry, with 859 successes and 140 backfires.
No later funds, mana, achievements or random outcomes are assigned, and no
additional lump is spent. Both outcomes use the same reset schedule. The native
profitable-reset count remains 1 in that witness; these cycles cannot replace
the separate 100-reset goal. The route is conditional, not a new-save theorem.

The runtime adds only the visible Grimoire open-state field for this checkpoint.
The save-export source/textarea audit and tiered-catalogue audit were reexecuted
against the new runtime, rather than editing stored hashes. A composed-controller
regression now checks all three final-collection gates: reset, seasonal and
spell-count progress. The root suite passes 337 Node tests and 7 patcher tests.
The mod remains local version 2.053.19; this experimental policy is not installed
in the player's game.

The revised paper was built with tectonic, copied to paper.pdf, and all 47 pages
were visually inspected in contact sheets. Changed pages 24, 33 and 44 were also
inspected at higher resolution, with no clipping or layout defects found.

The full pinned-engine validation passed after these changes: 585 build jobs,
3,594 registered theorem reports with only standard logical dependencies, all
native comparison checks, and the ten new microstate cases. The current 47-page
PDF has 298,856 bytes and SHA-256
`72b0b2c2e02c8c35b189efa8d6ac26c197f19c2e406f5b9f0f22fdbfe69abc90`.
The full-game source/input refinement, proper new-save policy, attained expected
time and matching universal lower bound remain unproved.

## Complete ARC4 constructor and closed Escape input path

The integrated source-core constructor executes real invocation dispatch, mapped
arguments, declarations, the empty-key fallback, both permutation loops, the
nested generator allocation, all 256 discarded generator steps and return. It
takes 72,669 steps for a nonempty key or 72,684 for an empty key. A further
37-declaration composition consumes the retained mixkey result and reaches this
return through the actual p write and new k(j) call; the q assignment remains
pending. Entropy mixing, seeded floating-output termination, random-function
installation and full Runtime composition remain open.

The closed physical Escape-release path derives the target and event fields
from explicit document/focus/device premises. Its intact source callback returns
in 147 BrowserRuntime steps and proves the key, activity and ascent-timer writes.
The isolated Chromium down/up check passes. Source key-down reachability and
general native input are not established.

The complete pinned-engine suite passed after the event-admission change and
constructor integration: 628 build jobs and 3,920 standard-only declaration
reports. The subsequent proof-only seed continuation passed a 632-job build and
all 3,957 registered declaration reports. The placeholder scan covers 498 Lean
files and rejects proof placeholders and additional logical assumptions. These
counts are validation evidence, not a global strategy certificate.

The current private completion monitor also proves provenance through visited
source states, starting with an empty access log. It does not infer new-save
reachability from a satisfying synthetic heap.

The reviewed helper setup withholds the 18 artwork-changing Grandma upgrades
and their permanent-slot assignments until its fixed sweep succeeds. Animation
and a conditional single-loop time bound are checked; no private draw counter
is exposed. The integrated root suite at that checkpoint passed 354 Node tests
and seven patcher tests.

The superseded new-save experiment was interrupted after its last progress
record at 108,000,900 ms, with zero ascensions and about 3.15e19 earned cookies.
It did not produce a final observation or finish its requested 48-hour horizon.
`model/experiments/new-save-interrupted-30h.json` records that status and the
hashed source/progress archive. It supplies no completion-time expectation.

`model/GLOBAL-OPTIMALITY-OBLIGATIONS.md` states the required concrete global
theorem and the remaining timing, state, same-time control, information and
proper-route obligations. No full-game minimizing policy, matching lower bound,
or valid full-new-save nonattainment proof has been established.

The final candidate removes the default hold on the five prestige activation
upgrades. Native profitable-reset and Lucky rules do not require that hold.
The old restriction remains an explicit diagnostic option. Normal permanent
assignments remain enabled; the helper phase excludes only its artwork choices.
The standalone finite Godzamok controller emits real store inputs and maintains
its own cent recurrence. It is not imported by the default candidate or mod.
Nine controller tests and a six-case, 2,181-cycle source diagnostic pass; these
remain supplied-boundary tests with no full-prefix endpoint substitution.
The CLI now implements a read-only `--check` mode. Its witness was regenerated
through execution after that CLI change and then reproduced with `--check`.

Final integrated `npm test`: 365 Node tests and seven patcher tests passed, with
no failures or skips. The additional nine affected controller tests passed after
the CLI correction. The local mod remains version 2.053.19 with its previously
validated 190 mod tests and unchanged bundle/archive hashes. It is not published
or installed into the player's game.

The final paper was rebuilt with tectonic and copied to `paper.pdf`. All 48
pages were inspected in contact sheets; changed pages 21, 33 and 42 were also
inspected at higher resolution. No clipping or overlapping content was found.
The final PDF has 302,634 bytes and SHA-256
`7228819cdbe7a88efe7c5e5e966cf826dd0c00919ab2d2aa00a005cb09e66cfc`.
The paper explicitly retains the unproved global result and does not certify
the mod as the fastest admissible full-game strategy.

## Completion counts, selected herald environment, and source composition

The selected environment now fixes heralds at 100, with no later external
changes. Policy sessions reject a different count. The ordinary Steam callback
still computes that value from the adapter's fixed player-count reply; the
native source callback and host connection remain separate proof obligations.

The completion reader no longer rejects finite nonnegative integer Numbers
above the JavaScript safe-integer range. Such a value can satisfy a native
threshold even when adding one no longer changes it. The source-heap reader and
JSON reader now agree on this rule. JSON values first undergo native binary64
decimal conversion. Lean checks exact count conversion at 2^53, 2^1000 and the
largest finite Number; negative, fractional and nonfinite counts remain invalid.
These fixtures do not establish reachability of the large values.

The retained seed setup now includes the actual constructor, q assignment,
state-array string conversion, entropy-pool mixing, random-closure installation
and p return. A canonical factory derives its later frames from the original
entry frame. No helper result or later heap is supplied as an independent
premise. Full initialized entry, runtime composition and seeded floating-output
termination remain open at this checkpoint.

The conditional Dragon Orbs schema has an exit-mass lower bound of 2^-265
within two eligible sale/pop cycles. Its finite-prefix survival and expected
block bounds are proved. The pinned engine checks all 3,840 syntactic effect-list
paths. Full sale/pop execution, input legality and arbitrary reset/reload
interleavings are not supplied by this schema.

The standard Steam restoration path retains its 100 ms native timer delay.
Lean executes the intact scheduling statement in its explicit entry frame and
proves the lower bound for modeled timer registration and firing. A fresh
ready state before restoration is distinct from the restored save. Alternative
entries and all pre-load controls remain to be covered.

The Garden age projection has 102 candidate values, including the two native
fractional immortal caps. It preserves economic age through current-save
truncation and common integer growth. It preserves the distinct Elderwort
tooltip widths before and after truncation; it does not assert that their
public observations are equal. All 3,612 prepared native growth-fragment checks
pass. The full randomFloor and source growth contracts remain open.

The App=0, English startup diagnostic now executes the original Game.Init
callback and first loop to an idle ready state, with 20 buildings and 875
upgrades. This required a 16-million-step task budget. It is a finite source
execution in the documented web fixture, not a proof of Steam startup or of
native pointer-target geometry. Three reported target rectangles still require
additional layout semantics.

Validation passed: 368 root Node tests, seven patcher tests, an 804-job Lean
build, 4,331 standard-only declaration reports, and the full pinned-engine
suite. The native Node worker now receives its unchanged input bytes through
a regular temporary file. This prevents the observed macOS pipe EOF stall;
empty and large UTF-8 transport fixtures pass. The successful full suite
followed, and supersedes, the interrupted transport attempt.

The 49-page paper was built with tectonic and copied to paper.pdf. All pages
were inspected in contact sheets. Changed pages 4, 5, 33, 34, 40 and 41 were
also inspected at higher resolution, with no clipping or overlapping text.
This PDF has 307,618 bytes and SHA-256
`c08c74f750739a64434370bd11547771e9c45880a93c6f2d2235cf6a7d8e04a4`.
The local mod remains version 2.053.19 with its prior test and build evidence.
No complete attaining full-game policy or matching universal lower bound has
been proved.

## Muted clicks, captured source frames, and complete pricing calls

Local mod 2.053.20 retains the native click-sound callback during muted
auto-clicks. It sets volume to zero during the native call and restores the
previous volume and pointer fields in finally. This preserves the random draw
and sound-index update that the former replacement callback omitted. Paired
source tests compare economic state, sound bookkeeping and subsequent random
outputs under free and seeded generators. They also check that the native
same-time click guard rejects a second click. All 193 mod tests and full ESLint
pass. The readable build succeeds with its three bundle-size advisory warnings.

The completion source reader now rejects explicitly unresolved catalogue
descriptors, including a placeholder that otherwise resembles a valid owned
entry. Six new cases cover achievements, upgrades, seeds, spells and gods.
The full reader check passes 91 source-heap cases and one native new-save data
projection. The private completion monitor passes ten source-microstate cases
and two native transient comparisons. These synthetic complete heaps do not
prove new-save reachability.

The seed-library inspection constructs a proof of the actual captured frame.
The finite runtime inspector then checks every browser dispatch against the
source-core calculation through constructor, pool update, random installation
and return. The direct-call interface retains the native Math receiver. A
non-ASCII fixture takes 100,181 prepared-entry steps, returns the same original
p value as the pinned native engine and preserves the free-draw count. Two
fixtures with a damaged intrinsic or descriptor are rejected. Inspection is a
private diagnostic and does not change continued game execution. Universal
startup entry and seeded floating-output normalization remain open.

The source pricing batch has 20 modules and 112 declaration reports. It
executes the complete modifyBuildingPrice body and getPrice call under explicit
no-modifier descriptor/helper-frame premises, including all twelve nested
calls, fourteen arguments allocations and the original caller continuation.
The full member call takes 1,304 source steps and preserves all pre-existing
objects. Actual reverse-price quotes and sale credits remain distinct. Nine
source-runtime controller tests pass; six supplied fixtures execute 2,181
cycles and retain the prior semantic results. No new physical-browser input
comparison or complete repeatable source cycle is claimed.

All 370 root Node tests and seven patcher tests pass. The first full run
reported two wall-time budget failures under concurrent compilation and one
version-comparison error. The timeout regression now permits one second for
its finite decisions before the deliberate infinite loop; the compiler test
has a sixty-second process budget. The version test compares Steam's numeric
ModVersion numerically, so 2.05320 and its parsed value 2.0532 agree. The focused
rerun and the subsequent complete root suite pass.

The default Number checker now selects the pinned game engine when installed.
The earlier host comparison failed on the already documented one-bit Math.log
difference in Node 23.6.0. No modeled arithmetic was changed. All 72,384 cases
pass against Electron 11.5.0 / V8 8.7.220.31. The checker reports its engine and
labels the fallback as a host-compatibility comparison. The complete driver
also contains checks that require native-engine mode. The npm script now
supplies --engine, and an unsupported invocation without that flag stops
immediately with an actionable command. The earlier no-engine attempts are
not recorded as successful full audits.

The complete pinned-engine audit passes: 854 Lean build jobs and 4,591
registered declaration reports, with only standard logical dependencies.
Generated source checks, proof-placeholder scanning, the full native comparison
suite and the remaining model/trace bridges all pass. The captured-seed
positive and negative regression is included in that run. The successful log
is /tmp/cookie-audit/v20-lean-pinned-full-check.log.


The served paper matches the tectonic output byte for byte. Its 49 pages were
rendered and checked in contact sheets. Pages 4, 29, 34, 35, 41 and 42 received
higher-resolution review during this revision; changed page flow was checked
through page 48. No clipping or overlapping content was found. The final PDF
has 309,256 bytes and SHA-256
`a8fec678fbd56129301d399db38c3deba84506ddd839a36e4aad81893e1dc61d`.
The existing algorithm.sty UTF-8 warning remains; the rendered algorithms are
intact.

The 689,150-byte mod bundle has SHA-256
`de19c2fa58020e339dcba55728ea4741e3d87d65634775debee0bfc07ec0a02d`.
The 279,107-byte patcher archive has SHA-256
`c455ea77c8cbff6f574fe8cf01bfb2da8aae759d4024f4ac9d11e6779d0f9747`.
Its bundled mod, metadata and manifest match the workspace. This candidate has
not been published or installed into the live game.

Full-game optimality remains unproved. The independent global review found no
valid new-save nonattainment argument either. A complete admissible route,
finite expected completion time, full source/input correspondence and a
matching bound over all allowed strategies remain required. The exact open
claims are recorded in model/GLOBAL-OPTIMALITY-OBLIGATIONS.md.


## 2026-10-31: native rounding, bounded funding and further source composition

Full-game optimality is still unproved. This continuation establishes no complete
new-save route, finite expected completion time or matching universal lower bound.
It also establishes no full-new-save nonattainment counterexample. The five
remaining obligations are in `model/GLOBAL-OPTIMALITY-OBLIGATIONS.md`.

### Controller and mod

The experimental completion controller now owns a bounded funding transaction.
It checks the observed bank, native purchase debits, retained sale proceeds and
remaining buff duration. It uses a fixed finite cycle budget and at most 400
clicks per burst. It disables the default burst when the configured click rate
is zero. It handles an interrupted receipt without assuming that a maintenance
reload preserves the buff or accepts every click. Between bursts, its fallback
ranking excludes Cursors that the next burst would sell. Final collection is
unchanged. One mind waits for the first Temple level. These are tested candidate
changes, not a proper-route theorem.

The actual mod is now version 2.053.21. Its immediate Godzamok estimate uses the
native rounded multiplier increase instead of the nominal sold-count bonus.
The paper uses the rounded slot literal as well as the rounded product and sum.
An absorbed increase has zero click benefit, including when the income estimate
is infinite. Native bank-gain cycles remain eligible. The long-run forecast uses
a fresh multiplier of one and remains heuristic.

Three source-runtime tests compare 21 supplied boundary cases across all slots.
The unit tests cover even and odd halfway ties, zero gain, bank profit and future
buff forecasts. All 197 mod tests and full source/test ESLint pass. Webpack builds
the readable mod with its three existing size advisories. The final bundle has
689,663 bytes and SHA-256
`2d0b2336f9163f537b6a0a7a5032958d06864d24da1200319dfd64412b16add5`.
The patcher archive has 279,293 bytes and SHA-256
`6c1694209205253f9dd96062d9fe8c3ff6ef09617dc4cd530881372f02d1389a`.
Every bundled file matches the workspace manifest. The Tools card and source
versions agree. No installation or publication was performed.

### Formal results and their limits

One original source catalogue now supplies the sequential price helper frames.
It survives native economic property writes and retained allocations. Complete
already-won Win and already-unlocked string Unlock calls retain their native
locals, arguments objects and caller returns. Array Unlock recursion and the
complete Cursor purchase callback remain open.

The complete one-Cursor sum and reverse quote calls now take 1,410 and 1,520
steps after preparation. They retain earlier heap objects, elapsed time and
free-draw count. Sixteen comparisons pass against Electron 11.5.0 / V8 8.7.
The reusable check is `lean/check_javascript_cursor_quotes.mjs --engine`, now
registered in the full driver. It uses supplied source frames. It does not prove
full buy/sell, refresh/rebuild, native-input or initialized-entry composition.

The actual ARC4 constructor supplies a permutation invariant. The source PRGA
byte step and finite traversals project to the exact invertible byte transition.
Lean proves a finite all-zero classifier with bound `256^258`. No execution of
that enormous enumeration is claimed. The new normalization recurrence uses
native Number operations and retains denominator overflow. A nonzero future
byte witness implies finite recurrence completion. An all-zero stream with zero
numerator and extra byte has no result at any finite recurrence bound. The
retained JavaScript random closure and universal required-seed nonzero witness
remain unproved.

The integrated Lean build passes all 895 jobs. All 4,959 registered declaration
reports use only standard logical foundations. The source scan finds no proof
placeholders or forbidden evaluation shortcuts. Earlier in this continuation,
the full pinned-engine driver passed with 4,717 reports. Later additions were
proof modules and the focused quote comparison, not changes to the interpreter.
The final integrated build, complete axiom audit and focused pinned comparison
were then rerun. These are distinct validation runs, not a claim that the entire
native suite was repeated after every proof addition.

### Experiments and document checks

A separate initialized source-adapter sample reaches its first normal
reincarnation after 20,820,634 milliseconds, with Hardcore, Neverclick and one
prestige level. It uses a fixed lower first-reset target and a fixed diagnostic
stream. It has no independent full replay and supplies no expected-time bound.
Its frozen receipt is `model/experiments/new-save-first-reset.json`.

The superseded controller experiment was stopped at 59,908,600 milliseconds,
with zero ascensions and no Temple level or funding burst. It predates the
duration, reload-recovery and reinvestment fixes. Its exact policy, final result
and listed dependencies are archived separately in
`model/experiments/new-save-superseded-16h.json`. The archive has 190,062 bytes and
SHA-256 `146d311d9df283acf5db53f6be6957ca6b9936fd58642f37709be641712be977`.
This interrupted run is not merged with the separate first-reset sample.

All 385 final repository tests and seven patcher tests pass. The final root log
is `/tmp/cookie-audit/v21-root-final-tests.log`. The earlier complete root runs
also passed after the funding/recovery integration. No simulation limit is
used as a restriction on the competing mathematical strategies.

Tectonic builds the final 51-page paper. The served `paper.pdf` matches the build
byte for byte. All pages were rendered and inspected in contact sheets. Pages
21, 35, 42, 45 and 46 were also inspected at higher resolution. No clipping or
overlap was found. The existing algorithm.sty UTF-8 warning remains, and the
rendered algorithms are intact. The PDF has 315,464 bytes and SHA-256
`22ada299b61a45f314507f7ef9edfaabe3d2bce3048a9d00861d43db624bf7d0`.

## 2026-10-31 integrated source audit after version 2.053.21

The full-game optimality theorem remains unproved. No complete legal route with
finite expected completion time, attaining controller, or matching universal
lower bound has been established. The additions below do not change that status.

### Source execution and native checks

The integrated Lean build passes 1,019 jobs. The complete
`python3 lean/check.py --engine` run then passes, including all 5,813 registered
axiom reports, generated-source checks, pinned-engine comparisons and normalized
completion checks. Every report uses only the standard logical foundations.
The final audit log is `/tmp/cookie-audit/current-full-lean-engine-audit-v2.log`,
with SHA-256
`aed2a113aba43a5e329d9b930483255587b6ea51d4dad4a8e7a9cf2d60015802`.
The runtime hash in the active tiered-catalogue witness was stale. Regeneration
changed only that hash; all twenty descriptor records remained identical.

A compiled-driver failure exposed an initialization error in the proof support
code. Two finite state-space lists in `Arc4Orbit.lean` were evaluated eagerly,
before the driver read its input. They enumerate all byte tables and their
counter states. Those logical definitions are now noncomputable proof data.
Their definitions and mathematical results remain unchanged. The rebuilt native
driver accepts empty input in under one second. Its captured-seed regression now
checks empty input first, then validates three complete source draws against the
pinned engine and rejects two damaged frames. No diagnostic timeout is treated
as a nonterminating game path.

The retained random closure has a complete conditional execution proof from an
explicit future nonzero byte witness. The three captured draws construct that
witness for their actual source heaps. A further theorem proves eventual nonzero
output for an injective byte table with its zero byte at slot zero, and for any
orbit that reaches such a table. Universal liveness for all required seed states
remains open.

The complete amount-one Cursor purchase callback has a 758-step invocation
proof. The initial two Cursor upgrades must already be unlocked and Click must
already be won. The proof derives intermediate frames from the original
catalogue and retains allocations and caller state. The muted PlaySound call is
also composed through native invocation and return: 99 steps with default volume
and 109 with an explicit nonmusic volume. Separate random sound selection is
retained.

### Funding and route evidence

The finite funding construction uses native refund/debit operations, cent
stacking and 400 click additions. For 2^22 <= N <= 2^49 and a representable bank
256N <= b < 2^59, one episode gives 168N <= b' - b <= 4528N. At most two episodes
reach 512N. These arithmetic results retain binary64 rounding. Initialized source
entry, first buff creation, accepted input timing, passive-credit interleaving
and repeated full callbacks still require proof.

The portable first-ripe receipt in `model/experiments/new-save-first-ripe`
reproduces its frozen policy and source dependencies. At the recorded 26.5-hour
boundary, the native-source adapter has reached Temple level 1 and a funding
burst. This is one fixed diagnostic stream, not a complete route or a bound on
expected completion time.

The separate portable receipt in `model/experiments/cursor-cycle-source`
contains nineteen verified payload files and a compressed exact request. Its
source generator reproduces all 47,067,433 request bytes, with SHA-256
`52fb65af37571ac769cdc90d8d3841917250d47f0af4fe4e3c6c3edec906a5aa`.
The accepted funded fixture executes store-mode change, Cursor sale, store-mode
change and Cursor purchase through intact callbacks. It restores the Cursor
amount, increases bought by one, changes Devastation from native 1.01 to native
1.02, preserves elapsed time and consumes exactly two free draws. It retains
239 new objects and 191 new environments. The portable build reproduces the
accepted driver hash, and the integrated request regeneration passes. The
expensive historical cycle was not rerun merely to copy its archive. Physical
input refinement and universal repetition are explicitly unproved.

The collection ledger now specifies one precommitted final reset. It does not
reset after an unfavorable veil outcome. Its direct-click route uses the finite
helper cover and stops at the actual award. The immutable earlier experiment
keeps its original controller; its results must not be attributed to this later
ledger.

### Repository and document checks

All 397 repository tests and seven patcher tests pass. The final root log is
`/tmp/cookie-audit/current-root-tests-final.log`. This continuation made no further
mod-source change after the tested 2.053.21 build described above.

Tectonic builds the updated 53-page paper, and the served `paper.pdf` matches the
build exactly. All pages were rendered and inspected. Pages 35, 43 and 52 were
also inspected at higher resolution. No overlap or clipping was found. The
existing algorithm.sty UTF-8 warning remains. The PDF has 324,421 bytes and
SHA-256 `1ebe93ad7bff3021120471edd59b3e79336d2bc678577702f1d10c5c4345f8f3`.

The later calendar and arbitrary-layout transaction proofs are still being
composed in private work directories at this checkpoint. They are not included
in the 1,019-job or 5,813-declaration totals above.

### Calendar and original-transaction integration

Fifteen further proof modules are now integrated. The shared build passes
1,034 jobs, and the complete declaration audit passes 6,011 reports with only
standard foundations. The source scan also passes. The audit log is
`/tmp/cookie-audit/current-transactions-calendar-axioms.log`, SHA-256
`37efc63bd34fff38ff89f366a590c9690c8f15878b8a9fca8bdf0ae70b133cea`.
The natural-season source generator check passes and is registered in the full
check driver. These later changes are proof modules and a source-generation
check. They do not change interpreter transitions; the full native suite above
was not repeated after these proof-only additions.

The new results cover original-layout Earn/Spend calls, existing-buff lookup,
the three Devastation branches, exact year decoding, and the extracted natural
season recurrence. The calendar bound is less than 733 days on a fixed daily
grid, with one day of slack. Native Number/Date correspondence and whole
maintenance callbacks are still required. The source transactions still need
composition through a full accepted purchase/sale and repeated-cycle invariant.
No global optimality conclusion follows from this integration.

The rebuilt paper remains 53 pages. It has 327,180 bytes and SHA-256
`9f712007231b3c0d69d381df172611c6caa08514f56cf2b86598745efa4baaec`. The served copy matches exactly. All pages were inspected in contact
sheets, and pages 36, 43 and 44 were inspected at higher resolution. No overlap
or clipping was found. The existing algorithm.sty warning remains.

### Native sale composition and guarded recovery controller

The shared build now passes 1,097 jobs. The complete declaration audit passes
6,643 reports with only standard foundations, and the proof-source scan passes.
The audit log is `/tmp/cookie-audit/current-sale-reprice-axioms.log`, SHA-256
`90cd2f4d769f6e11368a243eae0706e7485e5d2d547ed96bce011a485a412cce`.
The additions include ordinary-prefix native calendar arithmetic, the complete
312-step Godzamok branch, original sale entry and loop control, allocating
header calls, and the successful-sale numeric updates through the second
price assignment. The latter now composes in 1,405 steps from one original
entry, or 1,416 with the actual amount guard. The 71/81-step successful suffix
and 31/197-step no-aura Orbs conditional are also checked from explicit entries.
Their remaining whole-callback and initialized-input composition is open.
These are proof additions; interpreter transitions did not change, so the
previous complete native-engine suite was not repeated for these additions.

The separate natural-season recovery tail is integrated with its guarded
entry, fixed dirt, bounded holdings and trades, and delayed final office.
Its 14 new tests and 48 existing subsystem tests pass. The full repository
suite passes 411 tests and seven patcher tests. The log is
`/tmp/cookie-audit/current-recovery-tail-tests.log`. The frozen earlier
new-save experiment and default completion controller were not changed.
The tail is not a proper new-save route or an optimal strategy.

The updated paper builds to 54 pages and 330,852 bytes. Its SHA-256 is
`d764b4cf801a6ebc3b1f0c447b013e9d688d9f7617b4a1abfcba04060434ac1d`;
the served copy matches the build. All 54 pages were rendered and inspected,
with detailed checks on pages 44 and 49. No clipping or overlap was found.
The existing algorithm.sty UTF-8 warning remains. The inspection receipt is
`/tmp/cookie-audit/current-paper-render-v5/inspection.json`.

The full-game expected-time optimum remains unproved. No complete native
source refinement, proper legal new-save route, attaining controller or
matching lower bound is supplied by these checkpoints.

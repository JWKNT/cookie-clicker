# Full-game completion and strategy proofs

This project formalizes the terminal predicate for the pinned Steam game, version 2.053.
It does **not** prove an optimal full-game strategy.
The full-game transition model, an optimal policy, and its global certificate remain unproved.

## Build and check

Use Lean 4.33.1 and Python 3.9 or newer. No Mathlib download is needed.

```sh
python3 lean/check.py --engine
```

The check verifies generated inventories, builds the Lean modules and executables,
checks proof axioms, and compares the model with the pinned game engine and source.
It defaults to two Lean worker threads to limit build memory use. Set
`LEAN_NUM_THREADS` before the command to use a different thread count.
It also compares the Lean and JavaScript completion predicates on normalized observations.
The full audit requires `--engine`, including the parser and other source
comparisons. `npm run test:lean` supplies that flag. Without it, the driver
stops before the build and prints the required command. The standalone Number
checker uses the pinned engine when it is installed. If it is absent, that
checker's host-compatibility fallback can fail because Math implementations
differ: Node 23.6.0 has a one-bit difference on a tested Math.log input. The
checker prints the selected comparison engine.

The engine check creates an isolated VM. It does not load or change the player's save.
The engine source must match the hashes in `model/game-source.mjs`.

The approved external environment fixes heralds at 100 with no later changes.
`model/policy-runtime.mjs` enforces this value for policy evaluations. The native
Steam callback otherwise receives an external player count; the fixed reply is
an explicit model assumption. Its source scheduling still needs refinement.

All audited proofs use only Lean's standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.
The project contains no `sorry`, `admit`, custom axioms, or `native_decide`.
Concrete calculations use `decide +kernel`. The exact audit commands are in `Audit.lean`.

## Actual completion predicate

`CookieClicker.FullGame.complete` checks the normalized fields used by `model/completion.mjs`.
`Inventory.lean` contains the actual names and IDs selected by `model/completion-requirements.json`:

- 598 individually required normal achievements.
- All 622 normal achievement identities, with at least 600 won flags and the native `AchievementsOwned` counter at least 600 for the last milk unlock.
- 845 currently owned upgrades and 17 available or previously accessed selectors.
- All 34 current Garden seeds, all soils, four minigames, spells, gods, goods, and loans.
- Required building levels, dragon and Santa levels, the last office, and a normal run outside ascension transitions.
- Game version, Steam edition, and matching selector-access history.

The profile excludes 24 sugar achievements from individual requirements.
Those achievements still count toward the milk unlock. At least two must supplement the 598 individual targets.
Shadow achievements affect neither the required list nor the normal achievement count.
Required lump costs and unlock thresholds remain in the model.

The generator copies the complete selected inventory and records its SHA-256 digest and source hashes.
Run these commands after an intentional profile or catalogue change:

```sh
node tools/generate-completion-requirements.mjs
python3 lean/generate_inventory.py
python3 lean/check.py --engine
```

The proved properties include:

- `complete_iff_all_goals`: completion holds exactly when every generated goal holds.
- `missing_goal_blocks`: any missing generated goal makes completion false.
- `terminal_predicate_satisfiable`: an explicit synthetic observation satisfies the whole predicate.
- `new_save_incomplete`: a snapshot without `Wake and bake` cannot satisfy completion. The engine regression checks this premise on a new save.
- `excluded_not_required`: every declared sugar or shadow exception is absent from the individual achievement list.
- `shadow_flags_do_not_matter`: changing a shadow flag cannot change completion.
- `completion_requires_two_distinct_sugar_achievements`: full completion requires two distinct won names from the actual 24 sugar exceptions. The proof checks the complete 622-name partition.

The terminal witness proves consistency of the predicate. It does not prove that the witness is reachable by legal play.
The JSON parser accepts typed normalized observations and rejects malformed required fields.
Regression cases cover every requirement category, the 600-achievement boundary, transient states, wrong versions, and invalid fields.
These comparisons do not constitute a formal proof that the JavaScript extractor or game transitions refine the Lean definitions.

`GardenAge.lean` proves a finite age projection for ordinary Garden growth. It
retains each integer mortal age and each non-mature immortal age, and groups
mature immortal ages. Its candidate domain has 102 values: integers 0–99 and the
two native fractional caps 86.5 and 72.25. The kernel checks native binary64 cap
arithmetic. It proves closure under integer growth, death, age-zero replacement,
current-save truncation and the persistent Seedless transition. Equal projected
ages stay equal under common growth outcomes. Full source growth bounds,
`randomFloor` execution and heap refinement remain separate obligations.

The projection is economic, not complete public-observation equivalence. Native
tooltips place the Elderwort growth bar at 221 pixels for 86.5 and 220 pixels for 86;
Lean checks this difference. `check_garden_age.mjs` compares 3,612 prepared cases
with the intact native growth/clamp/death statements, supplying the integer
growth outcome explicitly. It does not establish a full-game observation or
attainment theorem.

`JavaScriptOrbsSyntax.lean` retains the pinned source tests for the golden-cookie
effect list. `JavaScriptOrbsSelection.lean` proves that its list projection has
at most 18 entries and starts with Frenzy or Clot. The native checker covers all
3,840 syntactic paths, plus the actual choice and threshold arithmetic.
`JavaScriptOrbsEpisode.lean` and `JavaScriptOrbsSchema.lean` construct a
five-designated-draw certificate for exit within two eligible Orbs sale/pop
cycles. Other draws remain arbitrary finite adaptive continuations. The schema
therefore has survival at most `(1 - 2^-265)^k` through `k` blocks, and each
finite-prefix expected block count is at most `2^265`.

These are conditional control-schema results. Full native callback execution,
buff creation, shimmer target legality, source-entry preservation, and reduction
of interleaved controls to the schema remain open. The result does not establish
that every same-time gameplay strategy has a finite or compact control closure.

`HandPicked.lean` also checks that `Hand-picked` is required and verifies the source-audited maturity expression:

```text
(20 hours - 1 hour - 7 minutes) / (1 + 1.1 * 0.05)
= 13,596,000,000 / 211 milliseconds.
```

The first eligible integer game-clock difference is at least `64,436,019` milliseconds for this exact threshold.
JavaScript tests separately check the engine's binary64 threshold and clock behavior.
This is not a formal translation of the engine code or an expected waiting-time result.
This arithmetic result makes no assumption of fair independent random draws. It gives no bound on repeated attempts after save rollback.

## Conditional Hand-picked expected-time bound

`HandPickedExpectation.lean` uses integer game-clock hitting time. `RationalTailCertificate.survival t`
is a rational lower bound for the probability that full completion has not occurred by millisecond `t`.
It can equal that probability when the true tail is rational. A path that never completes stays in this event at every time.
The certificate uses all finite sums of its rational tail bounds, expressed as a rational lower cut.
It permits infinite lower bounds and does not use accumulated action cost.

`FiniteTailsSound` states the separate link to an actual expectation: each strict lower bound on a finite certificate sum
must be below that expectation. `certificate_cut_refines` and `certificate_bound_transfers` prove the comparison of lower cuts.
`certificate_monotone` proves that increasing each rational tail bound preserves every certified bound.
These interfaces do not require the actual probability tails or expectation to be rational.
The soundness link must still be proved for a chosen stochastic model. This project does not supply a measure-theoretic translation of the game engine.

`finite_tail_lower_bound` proves the lower bound `d * sum(k=0..n-1, 2^(-k))` for every finite number `n` of attempt intervals.
`expected_hitting_time_lower_bound` then proves an unrestricted expectation of at least `2*d`.
The required `HandPickedBridge` has three explicit premises:

1. The initial attempt-survival bound is one.
2. After each attempt, the next failure-survival bound is at least half the previous bound.
   A success probability at most one half conditional on every unsuccessful history is sufficient. Independence is not required.
   Histories where the next attempt never occurs must remain unsuccessful. This is not the probability that `n` attempts actually occurred and failed.
3. At every integer offset before the end of interval `n`, the full-completion tail certificate is at least the failure-survival bound after `n` attempts.
   This requires the native clock/reset correspondence, a first attempt no earlier than `d`, repeated attempts at least `d` apart,
   no rollback, and Hand-picked as a completion requirement.

`conditional_hand_picked_bound` specializes the result to `d = 64,436,019` and gives `128,872,038` milliseconds.
`certified_hand_picked_bound` transfers that result to an arbitrary expectation lower cut under `FiniteTailsSound`.
The engine tests check the clock arithmetic. They do not establish the probability law or the bridge for every legal policy.
In particular, the result cannot be applied to policies that manipulate native RNG state or restore earlier saves.
This is a necessary conditional lower bound. It supplies neither an attaining strategy nor a full-game optimum.

`positive_noncompletion_mass_infinite` proves that any positive probability remaining uncompleted forever gives infinite expectation.
`never_completion_has_infinite_expectation` checks the all-unsuccessful case. These results exclude the zero-cost noncompletion interpretation.

## Concrete sugar-clock transitions

The selected stochastic model now uses independent uniform 53-bit free draws and an unbounded monotone mathematical clock.
An explicit native seed retains the seeded generator. A no-argument `seedrandom()` returns to the free IID law.
This last rule is an explicit idealization; native no-argument reseeding obtains entropy and installs another seeded generator.
The Date-ceiling diagnostic in `CLOCK-MODEL-AUDIT.md` does not apply to the selected unbounded-clock objective.

`UniformRandom.lean` defines the finite uniform kernel, proves normalization and event-mass bounds, and checks the exact
one-half probability of the two-item unripe-harvest choice. This conclusion requires that the choice uses the free kernel.
It does not prove that every full-game history reaches that branch in free mode.

The same module checks two explicit 53-bit input blocks, each of probability `1/32`, that select the letters `a` and `o`.
Their five-draw independent cylinder has probability `1/33,554,432` and selects `aaaao`.
The product law is the selected model, not a probability space derived from all engine execution.

`StartupSeed.lean` now checks the complete letter distribution, including binary64 multiplication rounding.
For a free index `k`, it represents the normal dyadic product `26 * (k / 2^53)` by rounding the exact integer `26*k`
to its 53-bit significand and then scaling by `2^-53`. The selected letter is that rounded numerator divided by `2^53`.
`letter_lt_boundary` proves every one of the 26 bucket thresholds for every `k < 2^53`.
A proved rounding-error bound handles indices away from each threshold; kernel calculations handle the remaining nearby indices.
This is a universal theorem for the numeric projection, not an inference from the finite boundary probes.

`letter_mass` derives each exact bucket probability from the uniform kernel and the interval partition.
`exact_bucket_sizes` shows that `a`, `f`, `k`, `o`, `u`, and `y` each have 346430740566962 indices;
the other letters each have 346430740566961. Thus the letters are not exactly uniform on 26 choices.
`priors_normalized` checks total mass one. `seed_mass_five` gives each five-letter seed's probability as the product
of its five bucket counts divided by `(2^53)^5`, and `seed_mass_five_positive` proves every such seed has positive mass.
The independent free-draw law is the selected assumption; explicitly seeded later observations are not resampled independently.

`check_startup_seed.mjs` compares all bucket boundaries and counts with the public-inference module,
checks native numeric values and seed weights, and audits the pinned `choose` and five-draw `makeSeed` source bodies.
With `--engine`, native five-draw seed calls agree with the same alphabet indexing.
These checks do not prove the complete game's source refinement or the native implementation of binary64 arithmetic.
They supply the exact prior for public-history inference without permitting hidden-seed inspection or outcome manipulation.

`SeededWitness.lean` translates the short ASCII seed path, ARC4 key scheduling, the 256-byte discard, and output normalization.
`helper_draws_exact` kernel-checks three exact outputs for `aaaao 1 0`. `helper_selects_last` checks the third draw's selection
for all list lengths from 2 through 20. `check_rng.mjs --engine` compares these exact fractions with native explicit seeding.
The diagnostic seed is never read or installed by the gameplay policy. Native tests separately check that the last artwork
entry is the elf and that the visible pointer action wins the achievement. This finite source projection is not a full JavaScript refinement.

`rng-phase-inventory.json` records all 23 explicit reseed calls in the eight pinned source files and their eight callback bodies.
The AST audit rejects source or call-site changes. Its local normal-return analysis restores free mode in each body except
the selected-You tooltip branch; excluding that forbidden branch removes the direct leak. Early-return mutations test this check.
The analysis treats other called helpers as phase-preserving and does not cover implicit exceptions. It therefore reports a local
source fact, not a whole-engine invariant. Native probes exercise all eight callback bodies, including the forbidden leak only as a diagnostic.

`RngPhase.lean` supplies a checked control-flow analysis for that source projection. It keeps fallthrough and return exits
separate, includes nondeterministic branches and any finite number of loop iterations, and models function invocation without
letting a callee's return end its caller. `analysis_sound` proves that every represented finite execution is included in the
computed phase relation. `restores_free_sound` transfers a checked relation to every represented normal callback return.
Kernel tests reject both early-return leaks and unresolved calls after a reset.

`generate_rng_phase.mjs` extracts the actual eight callback bodies into `NativeRngPhase.lean` and records their source hashes
and call obligations in `rng-phase-programs.json`. The local variants retain the former call-preservation premises.
The conservative variants instead give unknown callees both possible output phases. Seven simple source helper bodies,
including `choose`, `randomFloor`, `shuffle`, `Game.Has`, and `Game.auraMult`, are expanded and kernel-checked.
This closes the explicit callee phase obligations for `computeLumpType` and the two audited seeded upgrade descriptions.
The other five callback closures retain unresolved callees, including native spell effects and display callbacks.
They are not certified by silently assuming those callees preserve phase. The forbidden You-tooltip variant still fails its check.

This narrows a source-proof obligation but is not a verified JavaScript compiler. Acorn parsing and extraction, native host
operations, ordinary object/prototype integrity, implicit exceptions, and the correspondence of JavaScript execution to the
projected commands remain outside Lean. The extractor rejects unsupported control statements and direct Math assignments.
Negative mutations check that unknown callbacks, changed fresh-array receivers, early exits, and unsupported exception paths
do not receive an unconditional phase certificate. These results alone do not establish a free-draw law at every legal harvest.

`AdaptiveHandPicked.lean` then uses this exact free kernel in finite adaptive trial trees. Intervening free draws can change
later actions, and a policy can stop without success. `adaptive_failure_lower` proves failure mass at least `2^(-n)` for
at most `n` eligible target trials. It computes the one-half factor from the kernel rather than taking conditional fairness
as an input. `full_trial_budget_attains` checks equality when every trial is used. These are finite probability results;
the source correspondence for all callback histories and the infinite-history probability-space extension remain open.

`PetRetry.lean` treats a different native branch: petting a ready dragon while the current quarter's seed-selected item is
known to be missing. The exact IID53 trigger probability is `225,179,981,368,525 / 4,503,599,627,370,496`.
The source's two-second check gates sound only. Native tests confirm repeated trials at the same clock value.
`failure_tends_to_zero` and `first_success_mass_normalized` check the geometric first-success law.
`retry_state_completion` connects representative native branch outcomes to the first successful checkpoint.
`expected_additional_time_zero` checks zero expected extra elapsed time. `infinite_failure_has_infinite_hitting_time`
retains infinite hitting time on the null all-failure path. `local_time_minimum` matches the nonnegative time lower bound
for this known-missing local goal. No experiment input cap is treated as a game restriction.
If the current quarter's item is already owned, retries supply no other item; the native test also checks that countercase.
This result does not solve the policy's hidden quarter-map problem or full-game completion.

`MarketRecurrence.lean` translates the selected falling and rising market forcing ticks over exact rationals, including
mode updates, the small global disturbance, mean reversion, velocity damping, the low-price correction, and final mode reset.
It derives the velocity and price inequalities from these operations. `forced_preserves_box` preserves
`1 ≤ price ≤ resting + 250,000` and `|velocity| ≤ 300` under these forcing ticks.
`falling_block_low` and `falling_block_buy_band` prove that 801 ticks reach price at most 5 and at most 65% of resting price.
`rising_block_sale_band` proves that 231 ticks reach at least 105% of resting price.
The assumptions are a fixed aura boost between 0 and 1.1, Bank level 1's resting price between 10 and 180, and an initial state in that box.
The first tick aligns the mode; 200 further ticks establish the velocity sign; the price phases take 600 and 30 ticks.
These are recurrence witnesses, not a price-predicting policy or a full-game optimum.

`MarketForcingEvent.lean` defines the corresponding typed IID53 draw words. It checks at most 18 draws per good,
at most 327 per tick over 18 goods, and a positive cylinder-mass lower bound for a block with at most 337,464 draws.
The event word can depend on hidden pre-tick state; it is not supplied to the policy.
`check_market.mjs --engine` compares the exact-rational one-tick function with 576 native boundary transitions.
This finite comparison is not a uniform binary64 error proof. The box invariant for arbitrary non-forced native draws,
the complete native draw-order refinement, variable-aura composition, and a full trading-completion certificate remain separate obligations.

`SugarClock.lean` defines a rational-clock projection of the native sugar handlers. It includes all 16 maturity modifier combinations,
the ripe and overripe formulas, type-dependent yield support, immature and ripe clicks, failed and successful unripe attempts,
automatic harvests, first activation, ordinary gains, spending, type changes, offline catchup, and hard resets.
The model has no saved-timestamp restore operation. Hard resets preserve a ghost count of prior attempts even when they clear achievements.
Type selection remains a seeded external outcome. The model does not replace it with an independent uniform type draw.

The transition proofs derive these facts:

- `step_preserves_invariant`: after `n` attempts, the formation timer is at least `n * 64,436,019` and at most the current clock.
- `attempts_times_spacing_le_clock`: `n` attempts require at least `n * 64,436,019` elapsed milliseconds.
- `hand_picked_not_before_minimum`: no reachable state can win Hand-picked before the first minimum interval.
- `ordinary_gain_preserves_timer` and `failed_attempt_resets`: external gains keep the timer; every failed attempt resets it.
- `no_success_implies_no_completion`: failure in the first `n` attempts implies no earlier full-completion checkpoint before the end of interval `n`.
  The statement covers the whole prior trace, so a later reset cannot hide an earlier hit.

`bridge_from_sugar_runs` uses that last theorem to construct the earlier Hand-picked clock bridge.
It does not assume attempt spacing or the clock event inclusion.
`sugar_run_expected_lower_bound` transfers the `128,872,038` millisecond bound under the remaining event-bound, conditional-failure,
snapshot-projection, and expectation-soundness premises. `EventBounds` is a monotone rational certificate interface, not a supplied probability measure.
The ideal independent-unseeded law and its applicability at each attempt are not proved here.

With `--engine`, `check_sugar.mjs` obtains 11 projected transitions from the pinned native handlers and generates Lean propositions for them.
The kernel checks each transition and resulting clock invariant. The check also audits all seven assignments to `Game.lumpT`
and confirms that native type selection is deterministic for a fixed seed and timestamp and restores unseeded draws afterward.
These are prepared diagnostic fixtures, not new-save policy trajectories. A source-wide refinement proof remains open,
including binary64 rounding, arbitrary legal callback histories, and the correspondence between native state and the projection.

## Completion time from finite execution prefixes

`HittingTime.lean` defines an operational completion-time expectation from the selected IID53 kernel.
A `Program` can consume an adaptive finite sequence of free draws. Its normalization, order properties,
and composition law are proved from that kernel. Native seeded updates remain deterministic transition code.
Each represented transition program terminates. Native callback termination must be proved or represented by separate
internal semantics that do not expose internal execution counts to the policy.
An environment has a nonnegative unbounded rational clock and must preserve it on every transition leaf.
Policies receive the entire public observation and action history. They receive no private draw indices.
This permits inference of hidden information from public history. This interface covers deterministic history policies;
`MixedExpected` also permits finite private randomization over these policies, sampled independently before the concealed
native startup law. `uniform_mixture_lower_bound` transfers a common finite-cap prefix bound through that randomization.
It does not interchange per-policy limits or cover an unrestricted infinite private random tape.
`InitialExpected` averages over one concealed startup program before either limit, so the same policy is used for all
possible initial seeds. `Admissible` requires a legal selected action at every reachable unfinished public history.
The native action restrictions must instantiate that legality predicate; completed states require no further action.

At elapsed-time cap `H` and execution depth `n`, a completed prefix costs `min(T,H)` and an unfinished prefix costs `H`.
The expectation is the rational lower cut of `sup H, inf n, capped(H,n)`. The order of limits is part of the definition.
`capped_depth_decreasing` and `capped_horizon_increasing` check the two monotonicity properties.
`expected_downward` and `expected_rounded` check the lower-cut properties. `completed_exact` gives the exact elapsed time
of a completed checkpoint, including times larger than an individual cap. `prefix_lower_bound` and `prefix_upper_bound`
prove bounds directly from these finite-prefix calculations.

The same semantics checks both zero-time cases. `Stall.infinite_completion_time` gives infinite completion time to a
permanent incomplete stall, even though its accumulated action cost is zero. `NativePet.capped_retry` derives
`H * failure(n)` from the actual rational projection `PetRetry.pet` and its exact native trigger threshold.
`NativePet.expected_retry_zero` then gives zero expected extra elapsed time by taking the depth limit at each fixed cap.
It does not require every path to finish and does not discard the null infinite-failure path.

This supplies an explicit operational objective for formal transition programs. It does not supply the full native
transition program, a measure-theoretic source refinement over infinite engine executions, or a full-game optimal policy.
All completion checkpoints inside a native action must be retained by a future source refinement.

## Observation history and action timing

`PolicySemantics.lean` models the evaluator's decision interface: a public observation, suggested actions, and prior memory.
Each value is exact serialized JSON text. This preserves object-key order, which JavaScript policy code can observe.
A bare action keeps prior memory. A wrapped `{action, memory}` replaces it; omitted wrapped memory becomes `null`.
`private_history_noninterference` and `same_public_prefix_same_decisions` prove that a controller with these inputs cannot use
private environment data or future observations to change an earlier decision. This is a theorem about the typed controller interface,
not a formal verification of Node's VM or of the public status of every snapshot field.

Native `Game.ClickCookie` rejects ordinary clicks less than 20 milliseconds after the last accepted click.
The source also blocks early frames and ascension states; keyboard clicks with zero event detail have a slower limit.
`accepted_click_rate_bound` proves `accepted <= floor(elapsedMs / 20) + 1` for the projected native click transitions.
Raw action calls consume no simulated time, but repeated same-time calls do not produce an unlimited number of accepted cookie clicks.
This cookie throttle does not impose a rate limit on other controls.

The raw interface accepts `wait(0)`. Positive waits can also round to no clock change when added to the absolute binary64 timestamp.
`zero_wait_not_nonZeno` shows why observation-only access alone does not ensure time progress.
The evaluator's same-time and total-decision budgets stop such experiments with `decision-limit`; they do not turn the result into completion or a valid censored sample.

For an actual finite binary64 interval, nonnegative elapsed values have finitely many ordered bit ranks.
`finite_clock_decision_bound` proves a decision bound from a finite rank range and the same-time cap.
`no_infinite_bounded_clock_execution` proves that no infinite admitted execution can remain in that interval while satisfying those rules.
This result uses finite representable clocks. It assumes no positive delay for every input and makes no continuous-time counterexample claim about the game.
The rank encoding, guard correspondence, and native transitions have regression checks; a complete binary64 semantics refinement remains open.

`check_policy_semantics.mjs --engine` checks the actual VM memory protocol, unavailable RNG/private channels, a positive sub-ULP stall,
and 14 kernel-checked native clock-budget/cookie-click transition projections.
The policy VM is a capability restriction, not an operating-system security boundary.
The evaluator also supports a bounded, flat sequence of ordinary actions without intermediate policy observations.
The decision-budget theorems count wrapper decisions, including one decision for such a sequence.
The cookie-click theorem counts individual accepted native clicks. The macro expansion itself is not yet formalized in Lean.
An experiment budget restricts which experiments finish; it is not a proved global admissibility rule for every legal gameplay policy.
These results do not establish existence of an attaining full-game optimum, or remove the need for the full transition and probability models.

## Native zero-time Godzamok cycles and integer rounding

`GodzamokRounding.lean` defines binary64 round-to-nearest, ties-to-even for nonnegative integer inputs.
It uses the 53-bit significand, binade spacing, nearest-multiple rounding with an even quotient at ties,
and positive infinity after exponent overflow. Fractional and subnormal inputs are outside this integer projection.
The definitions use exact natural arithmetic. They do not replace native floating-point addition by rational addition.

For repeated native increments of exactly one, `unit_iterations_exact` proves the multiplier after `n` increments
from one is `min(n + 1, 2^53)`. The fixed point is reachable after the finite, enormous count `2^53 - 1`.
This does not impose an input budget. It is not a bound for other sale batch sizes: a checked increment of two passes `2^53`.
`hundred_times_cent_scaled` checks the native 100-copy increment's significand calculation: the exact product of
100 with binary64 `0.01`, scaled by `2^59`, is `2^59 + 12` and rounds to `2^59`.

At the exactly representable bank `2^90`, the adjacent lower and upper spacings differ.
`binary64_debit_rounds_away` proves that any integer debit at most `2^36` leaves that bank unchanged.
`binary64_refund_rounds_away` proves the corresponding result for refunds at most `2^37`.
Both include the halfway case because ties select the even significand of `2^90`.
The next larger debit and refund each change the bank. `arbitrarily_many_finite_cycles` proves unchanged bank for
every finite sequence of such per-copy transactions, together with the unit-increment recurrence.

`check_godzamok_rounding.mjs` compares these definitions with native binary64 operations around relevant binade,
tie, and overflow boundaries. With `--engine`, it also kernel-checks the native Mine price and refund projections
for the diagnostic holding cycle from 101 copies to one and back. Those costs satisfy the proved bounds at `2^90`.
This is a numerical projection, not an execution of quadrillions of inputs. Native source refinement, every other
callback effect, time/frame preservation, and reachability of the supplied fixture still need separate proofs.
It prevents a full-game proof from silently excluding very long finite sequences of zero-time legal actions.

## First completion in engine event traces

`Trace.lean` and the `tracecheck` executable use the full pinned completion predicate on event observations.
The runtime emits an initial observation and an observation after every completed timer callback and native action.
The trace checker proves these properties of its first reported hit:

- The reported observation satisfies every completion goal.
- Every earlier checkpoint is incomplete.
- Its integer game-clock time is minimal among complete checkpoints in a chronological trace.
- Later goal loss, including an ascension at the same timestamp, cannot erase the first hit.
- No hit in a finite prefix does not exclude completion later.

The decoder returns the trace with a Lean proof that its timestamps are chronological.
It checks each normalized observation and rejects a mismatched profile digest.
The executable reads an array of trace objects from standard input.
Each object has `schemaVersion: 1`, `checkpointSemantics: "native-action-and-timer-boundaries-v1"`,
`profileId`, `requirementsSha256`, and `records` in the runtime's `onTransition` format.
The digest is the SHA-256 of the exact `model/completion-requirements.json` bytes.
The result contains `valid`, `observations`, and `firstCompletion`, which is either `null` or an `elapsedMs` record.

These checks connect actual recorded observations to the evaluator's first-hit calculation.
They do not prove that the record contains every required boundary or that its JavaScript transitions were legal.
Checkpoint semantics treat a completed native action or timer callback as one transition.
They do not inspect arbitrary internal statements inside a synchronous callback.
Times are integer game-clock offsets. No continuous wall-clock or global-policy optimality theorem follows from this trace check.

## Required Garden repetitions

`GardenInvariant.lean` checks the actual required `Seedless to nay` achievement and `queenbeetLump` seed identity.
It tracks each change from unknown to known for the Juicy queenbeet seed. Its native-transition contract states:
the first Seedless award requires a full seed log before the transition and leaves that seed unknown afterward.

- `first_award_requires_full_log` identifies the first required complete log.
- `any_full_completion_requires_two_juicy_acquisitions` proves that a trace from a fresh seed log needs at least two acquisitions before any full-completion checkpoint.
- `full_completion_requires_two_full_logs` proves that a complete terminal observation requires the earlier log and a distinct complete log after sacrifice.

These theorems use the full pinned completion predicate and an explicit transition-contract premise.
The `tracecheck` result includes the checked contract status and acquisition count in its `garden` field.
The native engine check tests every missing-seed sacrifice guard, mature and immature acquisition,
sacrifice reset, reacquisition, and the pebbles seed-drop path. Juicy queenbeet is not plantable.
Two acquisitions do not necessarily mean two manual harvests: pebbles can unlock the seed when a mature plant dies.
The source probes use prepared diagnostic states. They do not prove all JavaScript transitions satisfy the contract or exhibit a legal new-save completion policy.

## Unbounded stochastic cost certificates

`Unbounded.lean` defines history-dependent strategies and exact finite truncations of accumulated action cost.
It represents an expectation by its rational lower cut. This representation permits irrational and infinite expectations.
`verified_unbounded_cost_optimal` derives a global cost comparison from:

1. Nonnegative state values and local Bellman inequalities for every legal action.
2. Bellman equality for the chosen strategy.
3. A proof that expected remaining potential tends to zero for every alternative with finite expected cost.

Alternatives with infinite expected cost are covered directly.
The strategy definition uses deterministic choices based on the full observation history, with finite rational transition laws.
No full-game value function, attaining strategy, or tail certificate is supplied.
The theorem is not a full-game expected-completion-time proof.

Accumulated action cost is not automatically time to completion.
`ZenoCounterexample.zero_cost_without_completion` proves that a zero-duration self-loop has zero cost at every horizon and never completes.
`UniformTimeProgress` states one sufficient condition to exclude such time behavior.
No corresponding game-level time-progress or measure-theoretic hitting-time equivalence proof is supplied.
A real completion theorem must discharge these obligations and justify the random law and allowed policy class.

`Stochastic.lean` also proves a finite-depth Bellman certificate theorem.
Every leaf must complete within its depth bound.
A three-state example has a checked optimal expected time of `5/2` seconds.
Finite normalized mixtures of those bounded-depth policies cannot beat the certified value.

## Deterministic mathematical subresults

`complete_global_optimal` proves minimum completion time for a separate finite purchase model.
All available offers are required once. Prices are fixed, production gains are additive and nonnegative, and the initial rate is positive.
The proof covers every order and all nonnegative rational waits.
`Waiting.lean` proves that advancing a purchase to its first affordable time cannot delay completion.
This model has no random cookies, changing prices, unlocks, ascensions, or minigames.

The strict counterexample uses rate 1, bank 0, and offers `(price, gain)` equal to `(3,1)`, `(5,4)`, and `(6,6)`.
The exchange-index greedy order takes `13/2` time units. The optimum takes `356/55`, a gain of `3/110`.
Lean checks the strict greedy choices, every order's minimum, and the exact difference.

Other checked results are the target-bank Bellman recurrence, residual-bank identities, and the exact achievement delay threshold:

```text
(H - D) * (1 + x) > H  iff  D < H * x / (1 + x), for x >= 0.
```

The exact BigInt rational reference solver is `tools/completion-model.mjs`.
Lean does not verify that JavaScript implementation.

## Explicit source evaluator and native compatibility checks

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
engine for the compatibility checks; the Number checker also selects it by
default when installed. The number suite passes 72,384 cases,
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


## Native opening arithmetic and seeded-call boundaries

`JavaScriptBootstrapLadder.native_ladder_billion` composes eight native
production recurrences and seven first-affordable native subtractions. Starting
with bank zero after the initial Cursor purchase, it reaches bank at least
one billion within 6,660,050 production credits. Intermediate banks are zero
or normal binary64 values and stay at most 2^30. The credit constants are the
actual binary64 divisions of the eight audited no-upgrade CpS totals by 30.

`JavaScriptBoundedAddition`, `JavaScriptBoundedSubtraction`, and
`JavaScriptBoundedBank` prove the required arithmetic for arbitrary retained
normal bank denominators. They cover rounding loss, first-hit overshoot and
near cancellation. `elapsed_allowance` checks the stated multiplication and
addition of tick and input budgets. It does not prove source scheduling.
The conservative allowance is 219,787,164 milliseconds from a ready entry,
or 219,787,364 milliseconds with the diagnostic's separate 200-millisecond
startup premise. The latter premise is not a startup theorem.

The revised bootstrap diagnostic executes the seven actual purchases at
explicitly injected affordability boundaries. It retains one Temple for the
later Godzamok setup. It does not run the long intervening timer trajectory.
`JavaScriptCounterLadder.native_ladder_earned_billion` now couples the bank to
lifetime earnings throughout the same route. It starts from bank zero and
earnings 15, adds each native credit to both counters, and subtracts each
purchase from the bank. It proves the native earnings comparison with one
billion within the same budget. `JavaScriptRoundingOrder` proves rounding
monotonicity and exact power-of-two scaling; `JavaScriptScaledOrder` connects
those results to native addition and subtraction at a shared dyadic scale.
The native numeric purchase guards and the intact Earn/Spend bodies preserve
the invariant under their explicit entry frames.
The source production invariant, initialized call frames, legal purchase
admission, automatic callback preservation and scheduler refinement remain open.
Thus the theorem does not yet establish the new-save Hardcore award, a proper
full-game strategy, or an optimal opening.

`JavaScriptTieredCall.source_call` now composes the complete actual
`Game.GetTieredCpsMult` call for this no-upgrade opening. It executes the
source argument, invocation and declaration scan, both full native enumeration
loops, both final guards, and the return to the caller. Each executed `Game.Has`
call retains its native arguments object and environment. The result is native
one, and the original object graph is preserved. Its premises describe the
actual catalogue descriptors, zero ownership, lexical paths and enumeration
order. They still need proofs from source initialization and through automatic
callbacks. `JavaScriptCommonCpsComplete` now composes the complete eighteen callbacks
from Farm through You, including the original `me.cps(me)` expression, both
nested multiplier calls, their allocations, native compound assignments and
return. A canonical positive normal base-CpS value is preserved exactly.
`JavaScriptCommonCpsLocals`, `JavaScriptCommonCpsSource` and
`JavaScriptCommonCpsBody` supply the native local frame and source statements.
`JavaScriptEffCall.source_call` proves the complete 58-step call with an omitted
default and an absent named effect, retaining the actual property lookup and
argument/local allocations. `JavaScriptAuraCall.source_call` executes the
complete 161-step auraMult call with both selectors at the native No aura slot
and a different requested aura name. Both guards, the actual short-circuit
branch and caller return are retained. The Game identifier read follows the
original lexical path and Window descriptor, including its native
nonconfigurable property flag.
The complete Cursor and Grandma source calls now also pass the shared kernel
check. Cursor executes all 22 statements, all 20 building rows and all nested
helpers, and returns the exact native 0.1 value. Its finite amount boards cover
the eight opening stages. Grandma executes all 18 statements, the building and
synergy loops, all helper calls and caller return, and yields native one.
Both proofs derive the final arithmetic from the executed source and preserve
all prior objects. The complete heavenly multiplier call returns zero in 902
steps, including all eight Has calls and the aura call. The missing-buff call
returns zero in 42 steps. An empty mod hook returns its input value with its
actual argument allocation and array-length lookup retained.
The shared audit now passes 2,352 registered proof reports. These additions
change proof modules, not the interpreter semantics used in the earlier full
pinned-engine suite. Initialized catalogue reachability, complete CalculateGains
and Logic preservation, native input admission, and the full completion route
remain open. These call proofs do not establish an optimal strategy.

`JavaScriptSeedrandomEntry` and `JavaScriptSeedrandomInvocation` execute the
first computeLumpType statement to its actual captured source closure: 32 steps
construct the exact seed argument and step 33 allocates its mapped arguments
and lexical environment. The selected timestamp codec must return successfully.
Twenty-nine focused checks include 27 ordinary native comparisons and two
selected extended-clock cases. `JavaScriptSeedrandomFlatten` proves the actual
helper call for every UTF-16 string. `JavaScriptSeedrandomSetup` composes
declaration setup, argument selection, that helper call and return, and the
real mixkey arguments in 128 Builtins steps from the prepared library state.
It preserves original object properties, elapsed time and free-draw count.
The later tagged-source theorem below now composes this path through the
BrowserRuntime and complete mixkey return. ARC4 and random-function installation
remain open.

The selected timestamp-text extension is now executable in the source machine.
It retains the actual seeded library and changes the captured mixkey activation's
index initializer to an exact index. A total syntax recognizer has a kernel
proof that each accepted body is the complete pinned helper body. The stored
closure text is unchanged. Tagged text passes through the native save helpers,
including their URI, base64, map, join and regex operations. Ordinary arrays,
economic Numbers and storage quotas retain their existing behavior.

`JavaScriptTimestampTextSemantics` proves the index increment, comparison,
decreasing remaining length, low bits and actual character read.
`JavaScriptIndexBits` connects all bounded natural conversions and the low-byte
mask to native binary64 operations. Thirty-one finite comparisons test the
complete seeded path, including a 65,536-digit explicit timestamp seed. Eight
more test actual save-codec round trips. Native Date-prefix tests and extended
explicit-text generator tests are separate claims. The tagged Flatten and Setup paths now also have source proofs.
`JavaScriptTimestampMixkeyComplete.actual_captured_helper` proves the complete
captured m call for every finite tagged seed length N. It includes the actual
UTF-16 traversal, native key-array writes, retained o source call, native apply
and fromCharCode, and return to the original caller. Its exact cost is
88 + 93*N + 2*min(N,256) interpreter steps; elapsed time and free-draw count do
not change. The theorem derives the final byte-array shape and intrinsic-path
preservation. It requires the captured library/descriptor graph and initially
empty native key array. No finite timestamp-length bound is assumed. Source
setup-to-mixkey composition now retains the 128-step setup, captured invocation
and complete mixkey body. `TimestampSeedRuntimeSource.actual_source_path` also
lifts the actual seed expression through that return to BrowserRuntime in
250 + 93*N + 2*min(N,256) steps. ARC4 initialization, generated-function
installation and general source propagation remain open. General index
arithmetic such as `e+1` still projects through Number; the selected source loop
uses the exact `e++` transition.

`JavaScriptSeedrandomReset` and `JavaScriptSeedrandomSource` execute the final
reset statement and implicit return in 14 steps under the selected no-argument
restoration rule. Other objects, lexical environments, time and free-draw count
are preserved. Fifteen focused checks include twelve intact computeLumpType
calls and thirteen native comparisons under the same selected rule. This is
not a claim that vanilla seedrandom restores the same function identity.

The entry and return proofs are not connected by a proof of the intervening
seedrandom/ARC4 setup and complete callback. Initial heap correspondence, the
global RNG-phase invariant and source-byte-to-AST refinement remain open.
No full-game attaining policy, expected completion value or matching universal
lower bound has been established.

The script-generated MouseEvent fragment retains source callback order and
cancellation. A click must be canceled before it can complete; trusted pointer
delivery, native hit testing, page-coordinate snapshots and general defaults
remain explicit boundaries. The fresh-audio fragment supplies paused=true only
while no admitted operation could have started playback. Autoplay provenance
is monotone, including parser allocation and attribute removal. Playback and
volume-change tasks remain unresolved.

The configured-English source diagnostic executes the cookie handlers with a
synthetic null-view mouse sequence. It reaches one cookie and one recorded click
and retains the real sound request, then stops at the volume setter. It is not
a legal-input refinement proof. Native targeting still requires the button's
UA layout, hover state, page-coordinate snapshot and ordinary pointer sequence.
The complete muted PlaySound bodies now have numeric-volume and default-volume
proofs, with 13 native source comparisons. A separate isolated native witness
uses trusted input to open Options, set the range slider to zero, and earn one
cookie. It omits the Steam wrapper and selects English. The first Options click
can start audio before muting; that transition and resource/input ordering
remain open. The witness is in `model/native-muted-input-witness.json` and can
be regenerated with `node tools/probe-native-muted-input.mjs`.

Earlier validation: the full `python3 lean/check.py --engine` run
passes all 1,550 registered theorem reports with standard logical dependencies
only. The source-click reproduction and explicit diagnostic assumptions are
in `model/source-click-witness.json`. The full-game optimality statement remains
unproved.


The later complete pinned-engine checkpoint passes 1,959 registered reports
and the full native suite, including timestamp text, save codecs and production
source checks. Run `python3 lean/check.py --engine` for the pinned target.
Node 23.6.0 differs by one bit on a tested Math.log input and is not a substitute
for that engine. The full-game optimality statement is still unproved.

The next shared source checkpoint adds the complete 4,400-step mouseCps call,
the nineteen exact numeric building-constructor prefixes, and the full tagged
mixkey traversal and return. The constructor results retain the nine price
statements after the three CpS statements and do not prove whole constructor
reachability. Native source comparisons agree for all nineteen numeric cases.
The new mutation frame handles ordinary cache writes without requiring equality
of the old and new game objects. The achievement-count helper is complete for
all string pools. Notification setup and both fast-note preference paths are
proved prefixes; the constructor, rendering, log and full Win suffix still need
composition. The complete new-save route and optimum remain unproved.

`JavaScriptTimingOrderWitness` checks a native counterexample to simply identifying
all action times with the same integer Date.now value. The configured GFD payment
and Logic callback orders leave different magic values; the witness retains the
source fragments and pinned engine versions in `model/timing-order-witness.json`.
Run `node tools/audit-timing-order.mjs --check` to reproduce it. This local fragment
does not establish new-save reachability, a whole-game timed quotient, or failure
of global attainment.

The native milk counter is an independent required observation. `Game.Win`
writes the won flag before notification calls and before the counter increment.
The predicate therefore requires both the existing flag count and the actual
`progression.achievementsOwned` value to reach 600. Missing or invalid native
counts fail closed. The source-heap projection reads `Game.AchievementsOwned`;
it does not fabricate the value from flags. The earlier two-sugar consequences
still hold, and the current collection manifest has 1,559 conditions.

`JavaScriptBrowserTime` proves clock preservation through the actual resource
preparation, Event allocation, dispatch setup, node updates and callback setup.
Its `fire_next_task_elapsed` theorem gives max(current time, selected deadline)
for the actual dispatcher. `fire_next_task_monotone` is unconditional;
`fire_next_task_before_deadline` proves the selected task cannot overshoot a
player deadline when both its due time and current time are within that bound.
These are scheduler laws, not native input refinement or an optimality result.

`JavaScriptControlledExecution` composes source ticks, free draws, actual
timer/resource selection, rational deadlines and returned-boundary completion.
Committed waits retain their deadline through callbacks. Interruptible waits
return control after the next completed callback. `JavaScriptPrivateController`
also permits unbounded private computation and sampling before an action. Its
finite sampler embedding preserves the emitted-action and leaf-cost laws.
Source internals do not enter the public history. Genuine noncompletion and
zero-time divergence have infinite cost. Missing model work has no numerical
cost. The current physical input boundary still returns explicit missing
requirements; this kernel does not yet define a playable full-game policy.
Maintenance navigation, task priority, public observations, policy restrictions,
startup and completion-checkpoint coverage still require refinement.

A conditional source regression in `tests/completion-reachability.test.mjs`
shows that completion can be transient inside a second Garden sacrifice.
Its initial harvest can earn the final harvest-count achievement before the
same callback clears 33 required seed flags. A separate harvest retains
completion in that fixture. This is not a reachable new-save proof or a general
replacement-policy theorem. It rules out an unconditional persistence shortcut
for the current returned-boundary kernel.

`JavaScriptNaturalRemainder.native_remainder` proves the actual bit-level
JavaScript remainder result for all natural operands below 2^52 with a positive
divisor. It uses canonical binary64 fields, exact dyadic alignment and logical
rounding. `byte_remainder` supplies the ARC4 key-index case. No enumeration of
operand pairs is used.

The current ARC4 proof executes both original constructor loops and their
intervening statement in 37,661 builtin-machine steps. It requires a normalized
nonempty byte key and an empty state array, retains the original key, and proves
all 256 initialization writes and 256 key-schedule iterations. The later constructor composition below closes setup, the empty-key branch
and the discarded prefix; full runtime composition remains open. Thirteen pinned-engine constructor fixtures and 104
subsequent generator calls check the executable source interpreter.

`JavaScriptCompletionMonitor` now checks the actual source heap before every
interpreter step. It records the 17 selector-access bits from checked data
properties, including transient access inside a callback. Each positive history
bit has its source-read witness. The startup gate distinguishes known absent
fields from unknown descriptors; a proved false gate cannot hide a completed
projection. A true probe has a full projected witness satisfying every goal.
The private first-hit kernel preserves the game heap, elapsed time and controller
information. It stops the cost computation at that hit, grants no mid-callback
input, and preserves the hit through every longer prefix. Unsupported reads
remain missing model operations with no numerical cost. Ten executable source
fixtures and two native heap comparisons cover transient completion/access,
startup absence, and accessors. Full source/host/input refinement and global
optimality are still unproved.

The following constructor prefix derives its own instance, mapped arguments,
hoisted variables, native field initializers and empty-key normalization from
the actual constructor dispatcher and caller heap. The retained execution after
dispatch takes 37,738 steps for a nonempty key or 37,753 steps for an empty key,
through completion of both permutation loops. The later complete constructor proof includes the nested generator assignment
and discard call; the runtime lift remains open.

The completion monitor also proves access-history provenance along its actual
controlled runs. Every scan retains earlier entries and adds entries from only
its current source heap. Starting with an empty log, every positive historical
access has a checked root/descriptor witness at a previously visited microstate.
This does not assume that an arbitrary satisfying heap is reachable from a new
save; complete source reachability remains open.

The complete source-core ARC4 constructor now starts before its invocation
dispatch and returns the actual fresh instance. It takes 72,669 steps for a
nonempty key or 72,684 for an empty key, retaining all native allocations,
permutation writes, generator fields and caller state. Its discarded g(256)
executes all actual byte reads, swaps and binary64 accumulator operations.
The setup composition below includes entropy-pool mixing and Math.random
installation under linked native frames. Seeded floating-output termination
and complete BrowserRuntime composition remain open.

The closed Escape-release adapter derives its target from document and focus
state and its fields from retained physical device state. It accepts HID page 7,
usage 41; it takes no target, callback result, trust flag or RNG value from the
controller. The actual trusted event and intact source callback return after
147 BrowserRuntime steps. The proof checks the native key, activity and ascent
timer writes, elapsed time, IID queue and caller restoration. Its entry frame is
conditional, with one Window listener and an ordinary unfocused HTML body.
The prior physical key-down, initialized source frame, general controls and full
native input refinement remain open. Run `node tools/audit-escape-input.mjs --check`
from the repository root for the isolated pinned-engine down/up fixture.

The retained seeded-library continuation now consumes the mixkey return, writes
its real p binding, resolves k and j, and executes new k(j) through the complete
constructor return. It derives the byte key and retained heap facts from that
mixing result. This source-core segment takes 72,681 steps for nonempty input
or 72,696 for empty input. The actual q assignment is pending at its exit; the
following composition executes it and the setup return.


`JavaScriptSeedrandomSetupComplete.lean` composes the retained constructor result
through the q assignment, actual q.S conversion, ordinary native entropy mixing,
Math.random closure allocation and property write, and return p. It takes 25,003
source-core steps after the constructor return, or 97,684 steps after nonempty
initial mixing (97,699 for empty input). The ordinary mixkey loop retains an
existing entropy pool; it does not reset it to an empty array. The installed
closure retains the setup lexical environment and ARC4 object. Elapsed time and
free-draw consumption are unchanged.

`JavaScriptTimestampSeedSetupFactory.lean` now constructs those linked inputs
from the original constructor/library frame, an original nonempty byte pool,
intrinsic lookup and object-separation facts, and the original writable
Math.random property. It derives every post-execution helper frame and preserves
the original p text, elapsed time and free-draw count. No future helper result
or frame is supplied.

`JavaScriptSeedrandomCapturedFrame.lean` constructs that original frame from the
captured source heap. It checks actual closures, descriptors, lexical paths,
prototype paths, pool bytes and native Math receiver. The source-body checker
returns equality proofs. It does not compare printed representations.
`JavaScriptBrowserCoreTrace.lean` checks each finite source/runtime dispatch and
returns a composed run proof. `JavaScriptSeedrandomCapturedInvocation.lean`
connects that result to the direct invocation of the retained source function.

The actual post-main capture passes these proof-returning checks. Its ASCII
fixture takes 99,991 runtime transitions after invocation dispatch. The direct
call adds one transition. The non-ASCII regression compares the original p return
with the pinned native engine and rejects two damaged intrinsic/property cases.
The diagnostic does not alter the continuing source state or supply private
values to the policy. Full startup reachability, a later Math.seedrandom property
lookup and universal seeded output termination remain separate obligations.


`JavaScriptCompletionCounts.lean` removes the former safe-integer restriction
from source completion reads. Threshold comparisons use the native represented
integer even when adding one can no longer change it. The general conversion
lemma and checks at 2^53, 2^1000, negative zero and the largest finite binary64
integer retain that behavior. `ObservationJson.lean` parses numeric fields with
binary64 decimal conversion before checking the count. Source-heap and normalized
fixtures test the large-count boundaries; they are not reachability claims.
Catalogue reads also reject explicitly unresolved descriptors. Six source-heap
regressions cover achievement, upgrade, seed, spell and god entries, including an
absent but unresolved spell. These partial-heap fixtures do not claim vanilla
reachability.

`JavaScriptReloadGateSource.lean` executes the intact Steam startup scheduling
statement, keeping its original LoadSave callback. `JavaScriptReloadGateTime.lean`
connects it to actual modeled timer registration and firing: standard saved-state
restoration cannot occur before registration plus 100 ms. The ready flag can be
set before that restoration. The minimal source-entry frame, initialized Steam
state, full save decoder, alternate entry reachability and all reload
interleavings remain distinct obligations. The native source-fragment checker
covers seven saveData cases and the Export callback's direct effects.

The Cursor source generator retains eleven native functions. The checked price
profile executes getPrice and getSellMultiplier with explicit descriptor and
helper-frame premises. `JavaScriptPriceComplete.lean` executes all thirteen
modifyBuildingPrice statements and twelve nested source calls in the stated
no-modifier profile. `JavaScriptCursorGetPriceCall.source_call` composes the
actual member call, arithmetic, modifier call and return in 1,304 source steps.
The retention theorem preserves every pre-existing heap object and retains all
fourteen arguments allocations. The four amount/free cases check native prices
of fifteen or eighteen. These are conditional source results; initialized entry
and preservation through a buy/sell pair are not proved.

DOM/text/style/class-list frame proofs retain source allocations and writes.
The native reverse-price display also differs from an actual unit refund: with
one free-covered Cursor it displays four while sell credits three. Neither the
source-call proofs nor the six diagnostic cycle fixtures compose refresh,
rebuild, buy/sell or every finite sequence of admitted native cycles.


The price catalogue constructors now derive all nested helper frames from one
original world. They retain actual closure scopes and allocations and reconstruct
the catalogue after economic property writes. Object separation handles the
Cursor's `bought` field without changing the upgrade ownership fields. The
complete buy/sell cycle and initialized entry remain open.

The complete already-won `Game.Win` string call takes 93 steps after preparation.
The complete already-unlocked `Game.Unlock` string call takes 76. Both include
native hoisting, arguments allocation and caller return. The Win call writes its
local `it` binding. Earlier objects, elapsed time and free-draw count remain
unchanged. `JavaScriptUnlockPairCall.lean` composes the actual two-element array
expression and both recursive calls in 266 steps. `JavaScriptCursorBuyOriginal.lean`
then executes the entire Cursor purchase callback at amount one, with the two
initial upgrades already unlocked and Click already won. The body takes 700
steps; invocation, declaration setup and return take 758. One original catalogue,
closure paths and receiver property determine the later frames. The theorem
retains allocations and preserves earlier objects, elapsed time and free draws.
The surrounding store purchase, sale, refresh and physical-input callbacks still
need composition and an invariant for repeated cycles.

The actual ARC4 constructor now has a permutation invariant. The source byte
cursor projects to a finite invertible transition, including the post-swap output
byte and bounded traversals. `Arc4Orbit.allZero_iff` proves that checking
`256^258` bytes decides whether all future output is zero. A nonzero witness gives
a nonzero byte within the same bound after every offset. The bound covers all
byte tables and is not a practical enumeration result. No theorem yet proves a
nonzero witness for every required game seed. The complete random closure is
now composed under that explicit witness premise. These results do not establish finite
expected full-game completion or an optimal strategy.

The full one-copy Cursor sum and reverse quote calls now execute from one
original catalogue. Their prepared calls take 1,410 and 1,520 source steps.
They retain the actual arguments allocations, helper calls, caller returns,
original heap objects, elapsed time and free-draw count. Sixteen comparisons
pass in the pinned Electron engine. Complete buy/sell, refresh/rebuild, native
input and initialized-entry composition remain open.

`SeedrandomNormalizationLoops.normalize_from_nonzero` proves finite completion
of the native normalization recurrence from a nonzero PRGA output witness.
`normalize_all_zero` proves that the zero branch never returns at a finite
recurrence bound. The denominator retains native binary64 operations, including
overflow. `JavaScriptSeedrandomDrawInvocation.lean` now composes the actual
closure invocation, six-byte call, repeated retained source calls, both loops
and final caller return under the nonzero-orbit premise. The captured setup's
actual output heap supplies a checked frame for that call. No later helper
result or frame is assumed.

`JavaScriptSeedrandomDrawEvaluation.lean` computes a finite nonzero-prefix
witness and the source growth and shrink frames. On success it returns the
concrete final machine and Number bits with an exact source-execution equation.
Its budget misses remain unresolved; they do not prove nontermination.
Three captured cases pass this check and match the pinned native library on
identical seed text: one non-ASCII string, and the selected extended timestamp
renderings `8640000000000001` and `(2*10^40+1)/2`. Each returned heap supplies a
valid next-draw frame. This is finite validation, not universal reachable-seed
safety or a full-game expected-time proof.

### Native audio invocation and finite funding episodes

`JavaScriptAudioExpression.lean` composes the original global PlaySound call with its native receiver rule, argument allocation, declaration scan, body and caller return. With the sound setting zero, the invocation takes 99 source steps with omitted volume or 109 with an explicit nonmusic volume. Earlier objects and environments, elapsed time and free-draw count remain unchanged. The separate random sound-selection calls are retained by the surrounding source.

`JavaScriptFundingProfile.lean` evaluates the eight-building, Temple level 1, Plastic mouse scalar base. For 2^22≤N≤2^49 and 256N≤b<2^59, the concrete arithmetic episode uses N native four-cookie refunds and fifteen-cookie debits, N native cent increments, and 400 native click additions. Its bank gain lies between 168N and 4528N. `two_episodes_double` proves that at most two episodes reach 512N. These theorems do not assume exact real arithmetic in place of native rounding. They still require initialized source reachability, first buff creation, accepted-click scheduling, passive-credit interleaving and callback preservation.

`Arc4ZeroOrigin.lean` proves that an injective byte-state orbit containing S[0]=0 has an eventual nonzero output. It does not prove that every required game seed reaches this structural class. Universal seeded-loop liveness and full-game optimality remain open.

### Original transaction calls and natural-season recurrence

`JavaScriptCounterOriginalMember.lean` executes the complete numeric Earn and
Spend member calls from the original Game/Window objects and lexical paths.
The underlying invocations take 43 and 24 steps. They retain mapped arguments,
declaration scan and the native undefined return. The second Earn write uses
the frame produced by the first write. Original objects, unrelated properties,
caller environments, time and free draws are retained.

`JavaScriptHasBuffExisting.lean` executes the complete existing-buff member call
in 56 steps, including both native reads. Its original closure paths construct
the callee read frame. `JavaScriptDevastationExisting.lean` executes the original
existing-buff conditional in 37, 46 or 55 steps for diamond, ruby or jade. It
uses native multiplication and addition on arbitrary Number bits. The actual
write supplies its next frame and preserves other fields and state. These
results still need the surrounding sale, purchase and physical-input proof.

`JavaScriptCalendarYear.lean` proves that the actual nine-step year decoder is
correct for every integer UTC day. `JavaScriptSeasonRecurrence.lean` uses the
source-extracted integer seasonal formulas and ordered guards. A fixed daily
rational-phase grid reaches each required natural season in less than 733 days,
with one day of slack. Business days mask five dates in leap years and three in
common years. The loaded/expired field formulas preserve a nonpositive timer
and select the new base season. This is a sufficient calendar bound, not an
optimal waiting time. Native Number/Date correspondence, maintenance timing and
full callback composition remain open. The registered generator check is
`node tools/generate-natural-season-formula.mjs --check`.

The portable finite full-cycle receipt is in
`model/experiments/cursor-cycle-source`. Its generator reproduces the original
request exactly. It retains the intact callbacks and all their observed effects
in a supplied funded fixture. It does not prove initialized reachability,
physical targeting or universal repetition.


### Whole Godzamok branch, sale entry, and native calendar arithmetic

`JavaScriptGodzamokOriginalBody.actual_branch` executes the intact existing-buff
Godzamok conditional in 312 source steps from one original entry. It includes
the original Pantheon call, buff lookup, caller-local writes, outer success
guard and diamond update. All later helper frames are constructed. Three
argument objects and environments remain allocated. Original success and sold
locals, writable buff data, and the specified diamond/no-aura profile are entry
premises. A preceding legal sale is still to be proved.

`JavaScriptBuildingSellEntry.actual_invocation_prefix` reaches the intact first
amount-one sale-loop body in 139 source steps, including the real mapped
arguments and 14-binding local layout. `BuildingSellLoop.first_iteration_exits`
checks the actual 19-step back edge after a completed first body. These results
retain the full source; the intervening economic body and later callbacks are
not supplied by the loop-control proofs. `JavaScriptPropertyUpdate.lean` checks
native property increment/decrement with rounding and prefix/postfix results.

`JavaScriptIntegerDivision.native_div_floor` covers every numerator below 2^40
and positive denominator below 2^40. `CalendarNumeric.source_prefix_ordinal`
retains the native subtract/divide/floor expression and its source denominator.
`SeasonNumeric.native_prefix_computus` connects all eleven source Number
expressions to the extracted integer Easter date for the nonnegative ordinary
Date prefix; `native_prefix_constructor_month` covers M-1. These proofs use the
configured UTC calendar. Native local-time equivalence, source Math/Date
bindings and callbacks, extended-clock propagation, and maintenance timing
remain open. The registered check is
`node tools/generate-season-numeric-formula.mjs --check`.

### Native sale header and economic body

`SaleHeader.actual_header` composes both allocating native header calls and
the actual price and giveBack initializers in 1,519 source steps. The source
Math.floor assignment takes 28 steps with arbitrary native Number bits.
`SaleReprice.actual_prefix` now composes the first five successful-sale
numeric updates and the complete second price assignment in 1,405 steps.
`actual_guarded_prefix` includes the original amount guard in 1,416 steps.
One original entry supplies the source catalogue; binding and property
transports derive its later Math, upgrade, buff, effect and Pantheon frames.
The actual changed amount becomes the second call's amount input.

`SaleTailSource.actual_suffix` executes the remaining successful-block tail in
71 or 81 steps, depending on its native row guard. Its original suffix entry
still needs composition with the earlier calls. `SaleOrbsNoAura.Entry.actual_guard`
covers the intact no-aura conditional in 31 or 197 steps, including the complete
aura call on the longer path. It retains its actual allocation and no free draw.
These lemmas do not provide startup reachability, a complete repeated store
cycle, or global expected-time optimality.

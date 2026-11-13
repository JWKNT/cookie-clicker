# Full-game optimality: theorem and open obligations

Audit date: 2026-10-31. Status: **not proved**. No complete attaining policy, full-game value, matching lower bound, or full-new-save nonattainment counterexample has been established. The source callback proofs and native tests do not change that status.

## The theorem that is required

Let `K` be the controlled process for the pinned full game, with the approved random, clock, timestamp-string and input assumptions, and a fixed herald count of 100. Let `s₀` be its actual new-save state. Let `G` be the complete normal-achievement, current-upgrade and unlock predicate in `completion-profile.json` and `completion-requirements.json`, including the actual native achievement counter. Let `τ` be the time of the first complete source state. A path that never completes, including an infinite zero-time action sequence, has `τ=∞`.

The required result is a **concrete public controller `π`** such that:

```
π obeys the agreed controls;
for every admissible native history-dependent randomized controller σ,
    Eₛ₀[τπ] ≤ Eₛ₀[τσ].
```

The expected values are extended nonnegative values. A useful finite optimum also requires `Eₛ₀[τπ] < ∞`; the user did not supply that as an assumption. If every admissible strategy has infinite expectation, that different conclusion needs a universal proof and an explicit report. No such result is established here. The proper-route work below aims to rule out that degenerate case by construction.

The proof must include the implemented controller and its source transitions. A definition that selects an unknown Bellman minimizer is not this result. An infimum or an ε-optimal sequence does not prove that an attaining policy exists. Diagnostic decision limits are not restrictions on the competitor class.

The existing larger-competitor argument permits a lower bound against fully observed players with wider controls. This avoids an exact characterization of the timing ban **only if an independently admissible public controller attains that same bound**. Existence of a minimizer in the larger class does not establish its legality, public implementation, or equality with the restricted value. In particular, permitted seed inspection does not permit choosing action times to change seeded outcomes.

## Five unmet obligations

| Obligation | What must be proved for this game | Current limit |
| --- | --- | --- |
| 1. Exact timing reduction | Define native input, task and timer ordering with the agreed unbounded clock. If action times are reduced to a lattice, preserve each source trace and its completion cost, including same-tick ordering and reactions between tasks. | Chromium stores internal timestamps and deadlines in integer microseconds. This alone does not quantize external arrival or completion cost. The current rational-delay model has not been proved equivalent to that carrier. |
| 2. Sufficient state projection | Remove unreachable allocations and presentation history while preserving economic effects, callback payloads, free-RNG law, source completion checks and native target legality. | Finite numbers and finite catalogues do not make the current heap, DOM, observation histories or controller memory finite. Source effect audits have remaining alias, callback and host contracts. |
| 3. Same-time control closure | Prove that every admitted finite same-time action history is represented by an exact finite or compact control closure. Keep any proper geometric free retries and assign infinite noncompletion paths their required cost. | Dragon Orbs, resource/counter rounding, spell refunds/refills and native current-save reloads need composed source invariants. Arbitrary finite action counts cannot be replaced by experiment caps. |
| 4. Public information and attainment | Either prove that the projected state is publicly sufficient, or handle its actual hidden-state beliefs and same-time observations. Establish minimizing selectors without an assumed argmin. | Finite hidden state alone is insufficient when free noisy observations allow longer and longer finite cutoffs. Public seed export addresses one dragon-phase issue; it does not establish a universal observation theorem. |
| 5. A proper full-goal route and a matching bound | Compose a legal new-save controller through every required goal; bound all stochastic retry tails and preserve funding, counters, current ownership and UI access. Then prove no admissible controller is faster in expectation. | The arithmetic opening, source helper proofs, funded implications, collection recipes and incomplete fresh-save experiments do not yet compose into such a route. No matching full-game lower bound has been supplied. |

A positive elapsed tick and a finite fully observed same-time closure could support a stochastic-shortest-path existence argument. Those premises must first be proved for the actual process. Even that existence result would not identify an executable admissible mod policy or establish equality with a larger-class bound.

## Concrete source evidence

The pinned game hashes are in `game-source.mjs`. `main.js` has SHA-256 `a8813ec2ee97edf5ebff6a3ce2037dcb65c08abd13c123bb92efda89b06ef4f7`. These are source facts, not a completed invariant over all reachable states:

- The native catalogue has 20 buildings. The Garden allocates a 6×6 plot (`minigameGarden.js:1056–1064`), with its largest unlock rectangle `[0,0,6,6]` at1480. These bound those containers, not the whole state.
- `Game.particlesN=50` initializes the fixed particle pool (`main.js:5914–5918`). `Game.Notes` retains at most 50 entries (`6177–6179`). `NotesById` is a separate retained table; the 50-entry bound must not be applied to it. The audio path uses 12 `SoundInsts` (`884–885`), with separate cached sounds and native host state.
- Distilled essence creates at most one additional shimmer beside a timer spawn (`5277–5280`). It is not a recursive pop/duplication rule. Ordinary cookie-chain continuation affects the later spawn timer (`5725`). These facts do not remove Dragon Orbs or spell-generated shimmers from the action space.
- Dragon Orbs requires no counted golden shimmer, a qualifying sale and a random trial; a successful trial only spawns when the buff table is empty (`7902–7913`). Proving a uniform same-time exit law also needs the full pop, buff, sale, reset and reload paths. No such global closure theorem is claimed.
- Gambler's Fever Dream schedules its child cast after 1000 ms (`minigameGrimoire.js:204–215`). If the child `M.castSpell` call returns false, the callback immediately refunds the outer cost at209. An admitted backfire returns true and does not trigger that refund. The additional 1500 ms timeout delays only the popup. Thus this refund path is not an immediate zero-time resource renewal. Other mana/resource bounds remain to be composed.
- The Options language path sets `toSave` and `toReload` (`main.js6584–6585`). Logic performs the save and later requires `!toSave&&!isSaving` before navigation (`16621–16634`). This source path is not a free repeated identity reload. It does not by itself classify every native browser/App maintenance control, and the diagnostic adapter's schedule and lifecycle guards are not universal competitor restrictions.
- Dragon petting has no gameplay cooldown; the two-second guard controls its growl sound (`14943–14968`). Its seeded drop permutation and current quarter can be computed from permitted public information. Waiting for a new available drop phase is distinct from searching timestamps to change a seeded outcome. The implemented decision rule, not just its realized trace, must respect the timing restriction.

The Garden age analysis removes one proposed source of unlimited hidden precision. Growth uses `randomFloor` (`minigameGarden.js:1885`); mortal ages then remain integer-valued until death at 100. Only Elderwort and Everdaisy are immortal. After Seedless to nay, their native caps are 86.5 and 72.25. `GardenAge.lean` proves a 102-value age-domain invariant for the integer-growth projection, checks the exact native cap arithmetic, and proves that current-save truncation preserves its economic age projection. Equal projected ages remain equal after each common integer growth outcome. The complete source growth bound, `randomFloor` contract and heap refinement are still required. This is not a full-game sufficient-state theorem.

The projection keeps every mortal age and non-mature immortal age, and groups mature immortal ages. It is not an equality of all public observations: the native Elderwort growth indicator is at 221 pixels for age 86.5 and 220 pixels after truncation to 86. The Lean calculation and 3,612 native source-fragment fixtures preserve this distinction. Any full-game projection must retain the extra observation or prove that it cannot improve future economic control.

`JavaScriptOrbsSchema.lean` proves a conditional exit bound for two consecutive eligible Dragon Orbs sale/pop cycles. The source-derived list projection always starts with Frenzy or Clot and has at most 18 entries. Five designated IID53 draws can force a sale success, break an existing chain, force the next sale success, bypass last-effect removal and select the first entry. All other draws remain arbitrary finite adaptive continuations. The resulting schema has exit mass at least `2^-265`, survival through `k` blocks at most `(1 - 2^-265)^k`, and finite-prefix expected block count at most `2^265`. These statements are proved from the explicit schema, not assumed exit probabilities.

The pinned-engine audit checks all 3,840 syntactic list paths and the native choice and threshold arithmetic. The schema still requires a source refinement for the full sale/pop callbacks, target legality, actual buff creation, and entry preservation. It does not remove interleaved reloads, ascensions, forced cookies or automatic tasks. It is therefore not a closure theorem for every same-time strategy.

The standard Steam save restoration has a checked 100 ms timer gate.
`JavaScriptReloadGateSource.lean` executes the intact scheduling statement in
an explicit data/lexical entry frame; `JavaScriptReloadGateTime.lean` proves
actual modeled registration and firing retain the delay at every nesting depth.
The fresh ready state before LoadSave is distinct from the restored save.
Native Export does not restore it. Initialized entry, full LoadSave effects,
alternative restoration reachability, pre-load controls and overlapping
navigations are not yet covered by a universal theorem.

Completion count readers now accept nonnegative finite integer binary64 values
above 2^53−1. The former safe-integer guard could exclude a threshold-satisfying
source state. Lean converts the represented integer without an exact-unit-step
assumption; the source and JSON checkers cover the largest finite value. No
reachability claim follows from the large-count fixtures.

The captured seed-library setup now has a proof-producing frame inspection and
finite browser-runtime trace certificate. It executes the original constructor,
entropy-pool update, random-closure installation and return. A non-ASCII fixture
agrees with the pinned native result; damaged intrinsic and descriptor fixtures
are rejected. This does not establish full startup reachability or termination
of every later seeded floating-output normalization loop. Finite tests cannot
remove a positive-probability noncompletion tail from the expected-time goal.
The actual constructor now supplies the permutation invariant from its identity
array and source swaps. The exact source PRGA step projects to a finite invertible
byte-state transition. Lean proves a finite classifier: all future output bytes
are zero if and only if the first `256^258` output bytes are zero. A nonzero output
witness therefore bounds later zero runs. This enormous bound is a theorem, not
an executed enumeration. No proof supplies a nonzero witness for every reachable
256-entry orbit or every admitted timestamp seed. Complete source composition
through floating-output normalization now holds under an explicit nonzero-orbit
witness. A finite evaluator constructs concrete source returns for three
captured seeds and matches their native output bits. It does not remove the
universal liveness obligation. No reachable nonterminating orbit has been
established either.

The complete Cursor price call now retains the full no-modifier source branch,
all allocations and all pre-existing objects. Its descriptor/helper-frame
premises still need an initialized entry and preservation through the full
buy/sell/refresh sequence. It is not a new-save funding certificate.

The amount-one Cursor purchase callback also has a complete 758-step source
invocation proof when its two initial upgrades are already unlocked and Click
is already won. Its recursive array unlock, declaration setup and return retain
all allocations. One original catalogue supplies the intermediate frames; no
post-call helper frame is assumed. The surrounding store sale and purchase,
refresh, native input and initialized-entry invariant remain open.

The muted PlaySound invocation is now composed through original argument allocation, declaration scan, the complete executed body and caller return. It retains old objects and environments, time and free-draw count. It takes 99 steps with omitted volume and 109 with an explicit nonmusic volume; global call-expression proofs retain function lookup and pure argument reads. Muting does not erase the separate source sound-selection draws.

The finite funding arithmetic now supplies a concrete two-episode doubling construction. For 2^22≤N≤2^49 and a representable bank256N≤b<2^59, one episode of N native refund/debit cycles, native cent stacking and 400 native click additions gives 168N≤b′−b≤4528N. The eight-building/Temple1/Plastic scalar profile is kernel evaluated. Source entry, first buff creation, passive gains, physical click acceptance and buff scheduling still need composition. The portable new-save sample in `experiments/new-save-first-ripe` reaches Temple level 1 and a funding burst by the recorded 26.5-hour boundary; it is one frozen Node/LCG sample, not a uniform random-history bound or a complete route.

A further ARC4 theorem proves an eventual nonzero output for every injective byte table with S[0]=0, and for any orbit that reaches such a table. No proof says that every required native orbit reaches this class. The universal seed-liveness obligation remains open.

Arbitrarily many possible zero-time trials do not by themselves refute
attainment. The permitted pet retry can succeed after finitely many trials
almost surely and have zero expected additional elapsed time. A nonattainment
argument must instead identify an actual reachable obstruction for the full
completion objective. No such argument, finite-expectation full route, or
matching bound was obtained in the current review.

## Native timing pins and their limit

`native-clock-source-pins.json` records exact URLs, source byte counts and SHA-256 hashes at Chromium tag 87.0.4280.141.

- [`base/time/time.h`](https://chromium.googlesource.com/chromium/src/+/refs/tags/87.0.4280.141/base/time/time.h) stores `TimeDelta.delta_` and `TimeBase.us_` as signed 64-bit microseconds. The double conversion functions scale their inputs and saturating-cast to the integer carrier.
- [`base/time/time_mac.cc`](https://chromium.googlesource.com/chromium/src/+/refs/tags/87.0.4280.141/base/time/time_mac.cc) converts Mach time to integer microseconds. The hardware timebase can skip representable microsecond values; availability of every integer tick is not proved.
- [`ui/events/base_event_utils.cc`](https://chromium.googlesource.com/chromium/src/+/refs/tags/87.0.4280.141/ui/events/base_event_utils.cc) converts native event seconds through `TimeDelta::FromSecondsD`. The pinned Cocoa event and WebInputEvent paths retain that carrier.
- [`TimerBase`](https://chromium.googlesource.com/chromium/src/+/refs/tags/87.0.4280.141/third_party/blink/renderer/platform/timer.cc) uses `TimeTicks` plus `TimeDelta`; [`TaskQueueImpl`](https://chromium.googlesource.com/chromium/src/+/refs/tags/87.0.4280.141/base/task/sequence_manager/task_queue_impl.cc) stores and compares those deadlines and posting order.

The 23 ms versus 23.5 ms GFD witness rejects a one-millisecond quotient. It does not reject a microsecond carrier. An input offset that does not change the native `TimeTicks` reading cannot change a later native timer deadline through that offset alone. This still leaves external event arrival, task ordering, wall/monotonic-clock alignment, host lateness and the elapsed-time objective to refine. This audit makes no clock-assumption change and proves neither attainment nor nonattainment.

The original-layout transaction calls now retain complete Earn/Spend invocation
and return, with the second Earn frame derived from the first native write. The
complete existing-buff lookup and the three native Devastation conditional
branches also have source proofs. The original heap and lexical premises remain
explicit. These results remove helper-call/frame gaps within the transaction;
they do not establish the surrounding full sale/purchase or physical-input
invariant. The accepted full-cycle diagnostic is archived reproducibly in
`experiments/cursor-cycle-source`, with both physical-input and universal-cycle
proof flags false.

The extracted integer calendar now has a universal natural-season recurrence
proof. The actual year decoder supplies its interval, and a precommitted daily
grid reaches a two-date seasonal window in less than 733 days with one day of
slack. It retains the ordered guards, including the five-date Business window
in leap years, and the load/expiration field formulas for a nonpositive timer.
The source generator checks all eleven computus expressions and five guards.
Ordinary-prefix Number division, ordinal subtraction and complete computus
arithmetic now correspond to the extracted integer formulas. Source Date
construction/getters, local-time equivalence to the configured UTC carrier,
extended-clock propagation and full maintenance/expiration callbacks remain
distinct obligations. The one-day slack does not assume a restoration
latency bound and is not a full-route expected-time bound.

The complete existing-buff Godzamok conditional now derives all its helper
frames from one original entry and executes in 312 source steps. The native
amount-one sale invocation reaches its first loop body in 139 steps; its
completed first iteration exits in 19 more loop-control steps. These results
still do not establish the intervening successful economic body or full sale,
price/refresh, buyback, input-admission and repeated-cycle invariant. The
original entry predicates and the global obligations above remain explicit.

The sale body now has a composed original-entry proof through its five numeric
updates and second price assignment: 1,405 source steps, or 1,416 with the original
amount guard. The first two header initializers also compose in 1,519 steps.
Catalogue constructors preserve actual binding/property changes and helper
allocations. The remaining 71/81-step successful suffix and 31/197-step no-aura
Orbs conditional are checked from their own original entries. Full source
composition, initialized entry and the universal input/repetition obligations
remain. These results supply no matching completion-time lower bound.

The separate `recovery-tail-policy.mjs` is a guarded final-run candidate. It
uses precommitted daily maintenance, natural seasons, dirt, bounded holdings
and transactions, and a deferred final office. Its complete predicate is the
unchanged `assessCompletion`. Its entry requires Farm level 10, Cursor level 12, all prior
reset work and the named earlier achievements. Its 14 new tests and 48 existing
subsystem tests pass, as do all 411 repository tests and seven patcher tests.
The conditional controller is not a new-save route or a finite-expectation
proof; `RECOVERY-TAIL-SCOPE.md` lists its unproved composition requirements.

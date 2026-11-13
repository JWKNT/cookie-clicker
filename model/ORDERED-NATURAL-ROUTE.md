# Ordered natural-season candidate

This candidate joins a new-save controller to the separate natural-season tail.
It does not establish a complete trajectory, finite expected completion time,
or optimality. The original running experiment is unchanged. The writing in
this record is ASD-STE100-guided.

`orderedNaturalPlan()` commits to current-save maintenance at 86,400,000 ms and
every 86,400,000 ms thereafter, before the new save starts. The policy receives
public observations. It does not read a seed, provide an outcome tape, restore
an earlier save, or choose an action time from a predicted seeded outcome.

The state machine uses these phases:

| Phase | Required behavior and release condition |
|---|---|
| Resources | Preserve Neverclick and Hardcore. Withhold research, freeze the Garden, harvest only ripe lumps, and buy Temple 1, Farm 10, Wizard tower 1, Bank 1 and Cursor 12. Their total level cost is 136 lumps. Finish the planned ascension, heavenly and spell work; collect the counted natural golden cookies, their timing achievements, and the Christmas helper. |
| Elder | After all five level targets and the counted-cookie prerequisites, allow native research and Eldeer/Wrath collection. Require the remaining prefix achievements, all heavenly upgrades, dragon 27 and prestige at least 2^82 before release. |
| Final reset | Execute one precommitted final normal reset. Its release and count do not depend on Thick-skinned, a seed, or a failed veil trial. This candidate uses a separate final reset even if an earlier spell reset was complete. |
| Veil | Use the existing direct-click phase: sell the starter buildings, wait for actual zero unbuffed CpS, and buy each native zero-price veil. No reset follows a failed direct click. The quoted egg must not provide flat production. |
| Rebuild | Restore ordinary holdings and deterministic upgrades, train the dragon, keep both auras at zero, and use diamond Godzamok alone. The default release target is a finite bank of 2^304 and all 20 current building count targets. |
| Tail | Use the actual tail entry guard, natural seasons, dirt Garden, bounded holdings, no golden-cookie pops/spells/loans/auras, and office 4 until its existing final-office release. Return success only from the full completion predicate. |

No phase assigns a resource, building, upgrade, achievement, multiplier or future
outcome. A failed native guard produces an explicit blocked/deferred result.
Such a result is an unresolved route obligation, not a recovery theorem.

The prefix preserves exclusive ownership of funding, spell-reset, helper-pointer
and prompt workflows. It retains public milestones through scheduled reloads.
Before Hardcore, the retained earned counter also detects a temporary fresh
pre-load realm. After Hardcore, retained challenge and ascension milestones
provide the guard. These checks do not prove an upper bound on restoration time.

The funding phase uses actual store controls. It sells/rebuys 100 Cursors at the
same elapsed time. A diamond Godzamok sale adds `100 * 0.01` in native operation
order. The default target is 2^53, so this is an enormous but finite candidate
input sequence; the tests execute only short prefixes. It retains the observed
bank and earned counter during that sequence, restores the chosen Cursor count,
waits for a native gains frame, and emits at most 400 clicks over at most 8 seconds.
It checks the actual buff lifetime and refuses a click whose observed credit
rounds away at the current bank. The 2^304 target is conditional: a full native
funding trajectory from the new save and a preserved lower income bound are not
proved. A bank fixture is not evidence of that trajectory.

The tail partition now follows the native award conditions for aggregate current
ownership. In particular, the 700-upgrade achievement must be collected by the
tail; requiring it before the Garden and seasonal upgrade collection can block
the intended route. The source audit finds the intact `Game.Win` calls and their
enclosing conditions at main.js 16388–16505 for 39 such awards. All 598 required
normal achievements are assigned: 52 to the prefix, Thick-skinned to the direct
veil phase, and 545 to the tail. The 24 excluded normal achievements remain listed
separately. This static partition is not a proof that the controller reaches each
award or that every native callback preserves the phase conditions.

Run the source-linked partition check with:

```
node tools/audit-natural-route-partition.mjs --check
```

The finite tests include a genuine fresh-save opening, then separately labelled
conditional native handoffs. The latter execute a finite Godzamok prefix, the
planned final reset and direct veil phase, native rebuild-to-tail release, the
final office action, and a coherent 699-to-700 upgrade purchase followed by the
native achievement check. These pieces are not concatenated into an alleged
new-save completion sample.

The following probability and source obligations remain for a proper route:

- The finite no-research prefix must preserve wrath 0 through each ripe harvest,
  obtain all 136 lumps and complete the source actions and scheduled reloads.
  The level budget and conditional ripe-yield formulas alone are insufficient.
- Every funding burst and its purchases must preserve a finite production frame
  and pay for the next stage. The proposed upper/lower production profiles and
  2^304 bank window are not universal source bounds. Repeated market profit buys
  use a threshold below 128 in the bounded Bank-level profile. Initial holdings
  and transaction goals can buy above that threshold; their finite cost and the
  native price/production bounds still need proof.
- Counted golden-cookie spawns, an Elder frenzy overlapping a live reindeer,
  Christmas helper access, and all four dragon-drop phases need actual legal
  retry schedules with uniform conditional success events. The helper and veil
  finite seed scans remain diagnostic certificates, not kernel theorems.
- Every Garden recipe, drop and rebuilt seed log needs a bounded recovery state
  and a positive conditional success cylinder. Seasonal wrinkler/reindeer drops
  and fortunes need the same composition. Individual tape witnesses do not prove
  those probabilities under all interleaved native callbacks.
- Hand-picked needs the actual free-generator phase at each eligible unripe
  attempt. The proved choose arithmetic does not establish that invariant for
  the entire controller. No deliberate reseeding or outcome retry is added.
- The market schedule needs finite-mean entry and profit/transaction completion
  from its actual reachable prices, holdings and modes. Its current thresholds
  are a candidate, not a certified recurrence argument.
- The extended UTC recurrence must be composed with native save/launch/load and
  returned availability; input, timer, random-stream and first-hit semantics must
  be refined. UTC configuration is explicit; another local-time/DST environment
  is not covered by the current calendar proof.

No matching full-game lower bound or attaining-policy theorem follows from this
checkpoint. The implementation makes the ordered candidate reviewable and removes
specific controller deadlocks; the full mathematical task remains open.

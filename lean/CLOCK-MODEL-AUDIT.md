# Clock and probability audit

This is a model diagnostic. It is not a completion route or an optimality claim.

The user has now selected an unbounded monotone mathematical clock, independent uniform 53-bit unseeded draws, and preservation of explicitly seeded native generators. A no-argument `seedrandom()` returns to the independent free-draw law. The Date-ceiling obstruction below therefore does **not** apply to the selected idealized objective. It remains a checked explanation of why literal bounded Date semantics cannot silently substitute for that objective. The exact calendar and arithmetic extension still needs implementation and correspondence checks.

## Result

A common finite clock ceiling, the audited minimum attempt spacing, and a positive conditional failure chance leave positive probability of never obtaining Hand-picked. Since this achievement is required, assigning infinite hitting time to unsuccessful paths then gives infinite expected completion time. This makes expected completion time alone a degenerate comparison of policies. It does not identify a useful strategy.

`FiniteClockObstruction.lean` checks this implication. For elapsed-clock ceiling `B`, `bounded_clock_attempt_cap` proves at most `floor(B / 64,436,019)` eligible attempts in each concrete sugar run. `capped_failure_excludes_completion` proves that failure at all those attempts excludes every complete checkpoint, including earlier first hits. `bounded_clock_persistent_tail` gives the positive lower-tail mass `2^(-floor(B / 64,436,019))`. `bounded_clock_infinite_expected_completion` transfers its divergent finite tail sums to every strict rational lower bound on the actual expectation.

The inputs still include the observation projection, conditional failure inequality, and soundness of the probability/expectation bridge. No exact probability law for the native engine is supplied by this theorem. In particular, it cannot be applied merely because an experiment uses the LCG sample stream.

## Which clock is currently used

ECMAScript time values are bounded by `8,640,000,000,000,000` milliseconds in either direction. `TimeClip` returns `NaN` outside that range. `Date.now` returns a time value, but the specification does not define useful gameplay beyond the representable calendar. See the [time-value definition](https://tc39.es/ecma262/multipage/numbers-and-dates.html#sec-time-values-and-time-range), [TimeClip](https://tc39.es/ecma262/multipage/numbers-and-dates.html#sec-timeclip), and [Date.now](https://tc39.es/ecma262/multipage/numbers-and-dates.html#sec-date.now).

The runtime adapter uses a different function: `ClockDate.now()` returns `Math.floor(clock.now)` without `TimeClip`. Its `new Date()` constructor still uses the native Date representation. A diagnostic boot at `8,640,000,000,000,001` returns that value from `Date.now()` but returns `NaN` from `new Date().getTime()`. Thus its time counter can pass the Date limit while calendar features cease to work. `check_clock_model.mjs --engine` reproduces this distinction. The diagnostic changes the start timestamp only to audit the model; it is not an admissible policy.

If the standard Date upper limit were imposed as a global ceiling from the fixed start `1,793,275,200,000`, the conditional cap would be `134,058,665` eligible attempts. Lean checks this integer division. It does not compute the enormous denominator of the resulting positive failure mass.

The paper's conditional tail theorem uses unbounded natural-number horizons. A lower cut on this domain is valid even when some paths never complete. It does not itself define an unbounded engine clock. The runtime's current evaluator uses finite safe-integer horizons and binary64 timestamp arithmetic. Neither its finite experiments nor the LCG define the full infinite-horizon probability law. The paper does not currently provide a complete unbounded-clock extension of calendar, arithmetic, and seeded operations.

## Why a clock extension needs more than a type change

The pinned source reads time for production, Garden and Pantheon timers, seasons, dragon drops, and seeds. Examples are `main.js:4524` (`Game.seed + '/' + Game.lumpT`), `main.js:4995–4997` (Cyclius), `main.js:1296–1307` (calendar seasons), and `main.js:14962` (minute-dependent dragon drops). The Grimoire seeds by spell count. Seeded calls must retain their own generator state and source order.

Replacing all absolute timestamps with an unbounded integer, or periodically subtracting a common epoch, can change seed strings, calendar results, trigonometric inputs, binary64 rounding, and timer order. Such an extension can define a useful idealized game, but it is not automatically a refinement of the installed engine. A finite input delay can also round to no clock change; policy admissibility must continue to rule out infinite zero-progress input sequences.

## Next exact work

The first required choice is a single environment contract: clock arithmetic and calendar beyond the Date range, unseeded probability law, restoration after seeded calls, legal observations, and time-progress rules. An independent uniform draw from `Fin (2^53)` is a finite exact rational kernel, but it must be declared as a model assumption. It is not supplied by the ECMAScript random specification or by the LCG evaluator.

Once that contract is fixed, the next concrete bridge is the random-call dispatcher: explicit unseeded and seeded generator states, preservation of seeded native calls, finite uniform unseeded outcomes, and a proof that policy decisions cannot see the unconsumed stream. Its source call sites must be translated in order, including callbacks that affect later generator state. That produces a transition law, not an optimality result.

There is a specific reset choice to resolve. The embedded native `Math.seedrandom()` with no argument obtains entropy through `crypto.getRandomValues` (with a fallback) and installs a newly seeded generator. It does not restore the original `Math.random` function. The runtime deliberately overrides that no-argument case to restore its sample stream. Therefore "independent unseeded draws, native seeded generators unchanged" must state how no-argument resets behave. Independent entropy bytes followed by the native generator are different from fresh independent draws on each subsequent call.

A full proof then still needs the complete state and action transition semantics, first-hit completion correspondence, a policy that reaches every target, and a matching expected-time lower bound over every admissible policy. Existing predicate, sugar, trace, and policy-interface results discharge parts of those obligations. They do not replace them. No ready verified Lean JavaScript interpreter has been established for this source. A verified operational translation, with checked abstractions that preserve optimal decisions, remains a substantial separate task.

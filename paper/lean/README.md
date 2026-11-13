# Lean proofs for "Four decisions in Cookie Clicker"

Lean 4 has checked three statements of the paper, with rational numbers.

| Paper | Lean, in the namespace `CookieClicker` |
| --- | --- |
| Theorem 2.4: the recursion gives the least time for a fixed list of items, over all orders and all waits | `complete_global_optimal` in `CookieClicker/Waiting.lean` |
| Example 2.2: the times 13/2 and 356/55, and the three comparisons of the index | `greedy_counterexample` in `CookieClicker/Completion.lean`, `counterexample_greedy_choices` and `counterexample_gap` in `CookieClicker/Checks.lean` |
| Proposition 5.2: the inequality for a pause | `achievement_break_even` in `CookieClicker/Checks.lean` |

The other statements of the paper have no formal proof.

## Check

Install Lean 4.33.1 with [elan](https://github.com/leanprover/elan). The project needs no other package.

```sh
lake build
```

The build compiles the four files and `Paper.lean`, which prints the axioms of each proof. The proofs use
`propext`, `Classical.choice` and `Quot.sound` only.

## The model

`Offer` is an item with a price and a gain, and `State` is a bank and an income rate. `complete` is the
recursion of Theorem 2.4. `DelayedCompletion s offers t` says that a schedule buys all offers from the state
`s` in the time `t`: in some order, with a wait of any length before each purchase, and each purchase when
the bank holds its price.

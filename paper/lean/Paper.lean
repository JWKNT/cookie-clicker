import CookieClicker.Checks

/-! The statements of the paper "Four decisions in Cookie Clicker" that Lean checks.

All numbers are rational. `lake build` compiles the four files in `CookieClicker/` and this
file. Each `#print axioms` command lists the axioms that a proof uses.

* Theorem 2.4 is `complete_global_optimal`. The function `complete` is the recursion of the
  theorem. `DelayedCompletion s offers t` says that a schedule buys all offers from the state `s`
  in the time `t`, in some order, with a wait of any length before each purchase.
* Example 2.2 is `greedy_counterexample`, with `counterexample_greedy_choices` for the three
  comparisons of the index and `counterexample_gap` for the difference of 3/110.
* The inequality of Proposition 5.2 is `achievement_break_even`.
-/

open CookieClicker

#check @complete_global_optimal
#print axioms complete_global_optimal
#print axioms greedy_counterexample
#print axioms counterexample_greedy_choices
#print axioms counterexample_gap
#check @achievement_break_even
#print axioms achievement_break_even

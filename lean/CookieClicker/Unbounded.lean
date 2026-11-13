import CookieClicker.Stochastic

/-! Certificates for unbounded accumulated stochastic cost.

Expected cost is represented by the rational lower cut of its finite
truncations. This permits irrational and infinite expectations without replacing
them by rational numbers. The result requires an explicit vanishing residual.
No Cookie Clicker transition model or optimal policy is asserted here.
-/
namespace CookieClicker.Unbounded
open Stochastic

/-- The outcome history permits decisions to depend on past observations. -/
abbrev History := List Nat

/-- A strategy stops exactly at complete states and otherwise selects a legal action. -/
structure Strategy {S : Type} (model : Model S) where
  choose : History → S → Option (Action S)
  stop_iff : ∀ history s, choose history s = none ↔ model.complete s
  legal : ∀ history s action, choose history s = some action → action ∈ model.actions s

/-- Expected accumulated action cost through at most n actions, stopped at completion. -/
def cost {S : Type} {model : Model S} (policy : Strategy model) :
    Nat → History → S → Rat
  | 0, _, _ => 0
  | n + 1, history, s =>
    match policy.choose history s with
    | none => 0
    | some action => action.duration + weighted (List.finRange action.count)
        action.probability (fun i => cost policy n (history ++ [i.val]) (action.successor i))

/-- Expected potential after n actions, with zero potential at terminal states. -/
def residual {S : Type} {model : Model S} (policy : Strategy model) (value : S → Rat) :
    Nat → History → S → Rat
  | 0, _, s => value s
  | n + 1, history, s =>
    match policy.choose history s with
    | none => value s
    | some action => weighted (List.finRange action.count) action.probability
        (fun i => residual policy value n (history ++ [i.val]) (action.successor i))

/-- This lower cut represents the supremum of finite expected elapsed costs. -/
def ExpectedCost {S : Type} {model : Model S} (policy : Strategy model) (s : S) : Rat → Prop :=
  fun bound => ∃ n, bound < cost policy n [] s

/-- Inclusion of lower cuts is the extended-real comparison of expected costs. -/
def NoSlower {S : Type} {model : Model S} (a b : Strategy model) (s : S) : Prop :=
  ∀ bound, ExpectedCost a s bound → ExpectedCost b s bound

/-- Local Bellman conditions, including terminal equality and nonnegative potential. -/
structure Certificate {S : Type} (model : Model S) (value : S → Rat) : Prop where
  nonnegative : ∀ s, 0 ≤ value s
  terminal : ∀ s, model.complete s → value s = 0
  lower : ∀ s a, a ∈ model.actions s →
    value s ≤ a.duration + weighted (List.finRange a.count) a.probability
      (fun i => value (a.successor i))

/-- The selected action attains local Bellman equality at every history. -/
def Attains {S : Type} {model : Model S} (value : S → Rat)
    (policy : Strategy model) : Prop :=
  ∀ history s a, policy.choose history s = some a →
    value s = a.duration + weighted (List.finRange a.count) a.probability
      (fun i => value (a.successor i))

/-- Expected remaining potential tends to zero along the policy's truncations. -/
def Vanishes {S : Type} {model : Model S} (value : S → Rat)
    (policy : Strategy model) (s : S) : Prop :=
  ∀ epsilon : Rat, 0 < epsilon → ∃ n, ∀ m, n ≤ m → residual policy value m [] s < epsilon

theorem weighted_add {I : Type} (indices : List I) (prob f g : I → Rat) :
    weighted indices prob (fun i => f i + g i) =
      weighted indices prob f + weighted indices prob g := by
  induction indices with
  | nil => simp [weighted, Rat.zero_add]
  | cons i rest ih =>
    simp only [weighted, ih]
    grind

theorem residual_nonnegative {S : Type} {model : Model S} {value : S → Rat}
    (nonnegative : ∀ s, 0 ≤ value s) (policy : Strategy model) (n : Nat)
    (history : History) (s : S) : 0 ≤ residual policy value n history s := by
  induction n generalizing history s with
  | zero => exact nonnegative s
  | succ n ih =>
    simp only [residual]
    split
    · exact nonnegative s
    · rename_i a heq
      exact weighted_nonneg _ _ _ a.probability_nonnegative (fun i => ih _ _)

theorem cost_nonnegative {S : Type} {model : Model S}
    (policy : Strategy model) (n : Nat) (history : History) (s : S) :
    0 ≤ cost policy n history s := by
  induction n generalizing history s with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [cost]
    split
    · exact Rat.le_refl
    · rename_i a heq
      have hw := weighted_nonneg (List.finRange a.count) a.probability
        (fun i => cost policy n (history ++ [i.val]) (a.successor i))
        a.probability_nonnegative (fun i => ih _ _)
      have hd := a.duration_nonnegative
      grind

theorem cost_monotone {S : Type} {model : Model S}
    (policy : Strategy model) (n : Nat) (history : History) (s : S) :
    cost policy n history s ≤ cost policy (n + 1) history s := by
  induction n generalizing history s with
  | zero => exact cost_nonnegative policy 1 history s
  | succ n ih =>
    simp only [cost]
    split
    · exact Rat.le_refl
    · rename_i a heq
      exact Rat.add_le_add_left.mpr
        (weighted_mono _ _ _ _ a.probability_nonnegative (fun i => ih _ _))

/-- Local inequalities imply the finite-truncation bound for every strategy. -/
theorem finite_bound {S : Type} {model : Model S} {value : S → Rat}
    (certificate : Certificate model value) (policy : Strategy model) (n : Nat)
    (history : History) (s : S) :
    value s ≤ cost policy n history s + residual policy value n history s := by
  induction n generalizing history s with
  | zero => simp [cost, residual, Rat.zero_add]
  | succ n ih =>
    cases hc : policy.choose history s with
    | none => simp [cost, residual, hc, Rat.zero_add]
    | some a =>
      have hl := certificate.lower s a (policy.legal history s a hc)
      have hw := weighted_mono (List.finRange a.count) a.probability
        (fun i => value (a.successor i))
        (fun i => cost policy n (history ++ [i.val]) (a.successor i) +
          residual policy value n (history ++ [i.val]) (a.successor i))
        a.probability_nonnegative (fun i => ih _ _)
      rw [weighted_add] at hw
      simp only [cost, residual, hc]
      grind

/-- Equality propagates from the selected actions to every finite truncation. -/
theorem finite_equality {S : Type} {model : Model S} {value : S → Rat}
    (_certificate : Certificate model value) (policy : Strategy model)
    (attains : Attains value policy) (n : Nat) (history : History) (s : S) :
    value s = cost policy n history s + residual policy value n history s := by
  induction n generalizing history s with
  | zero => simp [cost, residual, Rat.zero_add]
  | succ n ih =>
    cases hc : policy.choose history s with
    | none => simp [cost, residual, hc, Rat.zero_add]
    | some a =>
      have hl := attains history s a hc
      have hw := weighted_congr (List.finRange a.count) a.probability
        (fun i => value (a.successor i))
        (fun i => cost policy n (history ++ [i.val]) (a.successor i) +
          residual policy value n (history ++ [i.val]) (a.successor i))
        (fun i => ih _ _)
      rw [weighted_add] at hw
      simp only [cost, residual, hc]
      grind

/-- Vanishing residual is the condition needed to pass to unbounded expectations. -/
theorem lower_cut_bound {S : Type} {model : Model S} {value : S → Rat}
    (certificate : Certificate model value) (policy : Strategy model) (s : S)
    (vanishes : Vanishes value policy s) (bound : Rat) (below : bound < value s) :
    ExpectedCost policy s bound := by
  have epsilon_pos : 0 < value s - bound := by grind
  obtain ⟨n, hn⟩ := vanishes (value s - bound) epsilon_pos
  have residual_small := hn n (Nat.le_refl _)
  have truncation := finite_bound certificate policy n [] s
  exact ⟨n, by grind⟩

/-- An attaining strategy with vanishing residual has exactly the proposed value. -/
theorem expected_cost_exact {S : Type} {model : Model S} {value : S → Rat}
    (certificate : Certificate model value) (policy : Strategy model)
    (attains : Attains value policy) (s : S) (vanishes : Vanishes value policy s) :
    ∀ bound, ExpectedCost policy s bound ↔ bound < value s := by
  intro bound
  constructor
  · rintro ⟨n, hn⟩
    have heq := finite_equality certificate policy attains n [] s
    have hnonneg := residual_nonnegative certificate.nonnegative policy n [] s
    grind
  · exact lower_cut_bound certificate policy s vanishes bound

/-- A rational upper bound exists for every finite truncation. -/
def FiniteExpectedCost {S : Type} {model : Model S} (policy : Strategy model) (s : S) : Prop :=
  ∃ bound : Rat, ∀ n, cost policy n [] s ≤ bound

/-- Every rational threshold is exceeded when the expected cost is infinite. -/
theorem infinite_cost_exceeds {S : Type} {model : Model S} (policy : Strategy model) (s : S)
    (infinite : ¬ FiniteExpectedCost policy s) : ∀ bound, ExpectedCost policy s bound := by
  classical
  intro bound
  apply Classical.byContradiction
  intro h
  apply infinite
  refine ⟨bound, ?_⟩
  intro n
  apply Rat.not_lt.mp
  intro hn
  exact h ⟨n, hn⟩

/-- Unbounded verification with a tail obligation for every finite-cost alternative.
Infinite-cost alternatives are covered directly. A full-game instantiation still
needs its transition semantics, policy, Bellman certificate, and tail proof.
-/
theorem verified_unbounded_cost_optimal {S : Type} {model : Model S} {value : S → Rat}
    (certificate : Certificate model value) (policy : Strategy model)
    (attains : Attains value policy) (s : S)
    (tails : ∀ alternative : Strategy model,
      FiniteExpectedCost alternative s → Vanishes value alternative s) :
    (∀ bound, ExpectedCost policy s bound ↔ bound < value s) ∧
    ∀ alternative : Strategy model, NoSlower policy alternative s := by
  have finite : FiniteExpectedCost policy s := by
    refine ⟨value s, ?_⟩
    intro n
    have heq := finite_equality certificate policy attains n [] s
    have hnonneg := residual_nonnegative certificate.nonnegative policy n [] s
    grind
  have exact_value := expected_cost_exact certificate policy attains s (tails policy finite)
  refine ⟨exact_value, ?_⟩
  intro alternative bound h
  by_cases finite_alt : FiniteExpectedCost alternative s
  · exact lower_cut_bound certificate alternative s (tails alternative finite_alt) bound
      ((exact_value bound).mp h)
  · exact infinite_cost_exceeds alternative s finite_alt bound

/-- A sufficient uniform time-progress condition excludes zero-time and Zeno paths.
The full engine must establish an appropriate time-progress condition before its
accumulated-cost objective can be identified with elapsed time to completion.
-/
def UniformTimeProgress {S : Type} (model : Model S) : Prop :=
  ∃ delta : Rat, 0 < delta ∧ ∀ s a, a ∈ model.actions s → delta ≤ a.duration

namespace ZenoCounterexample

def zeroAction : Action Unit where
  duration := 0
  count := 1
  probability := fun _ => 1
  successor := fun _ => ()
  duration_nonnegative := by decide +kernel
  probability_nonnegative := by intro i; decide +kernel
  probability_normalized := by decide +kernel

def model : Model Unit where
  complete := fun _ => False
  actions := fun _ => [zeroAction]

def policy : Strategy model where
  choose := fun _ _ => some zeroAction
  stop_iff := by intro history s; simp [model]
  legal := by intro history s a h; cases h; simp [model]

theorem every_truncation_zero (n : Nat) (history : History) :
    cost policy n history () = 0 := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
    simp [cost, policy, zeroAction, weighted, List.finRange,
      Rat.zero_add, Rat.one_mul, Rat.add_zero]
    exact ih _

/-- Finite accumulated cost does not imply that completion ever occurs. -/
theorem zero_cost_without_completion :
    (∀ n, cost policy n [] () = 0) ∧ ¬model.complete () :=
  ⟨fun n => every_truncation_zero n [], fun h => h⟩

theorem time_progress_fails : ¬UniformTimeProgress model := by
  rintro ⟨delta, positive, progress⟩
  have bound := progress () zeroAction (by simp [model])
  change delta ≤ 0 at bound
  grind

end ZenoCounterexample

end CookieClicker.Unbounded

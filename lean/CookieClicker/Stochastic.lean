import Std

/-!
Finite stochastic completion policies and Bellman certificates.

Each action has a nonnegative duration and a finite rational probability law.
Every policy leaf must satisfy the completion predicate. A depth bound limits
all paths, rather than assigning a penalty to an unfinished leaf.

The theorems verify certificates for this explicit model. They do not assert
that the model contains every Cookie Clicker action or transition.
-/
namespace CookieClicker.Stochastic

/-- A finite weighted sum, with exact rational arithmetic. -/
def weighted {I : Type} (indices : List I) (prob value : I → Rat) : Rat :=
  match indices with
  | [] => 0
  | i :: rest => prob i * value i + weighted rest prob value

theorem weighted_mono {I : Type} (indices : List I) (prob f g : I → Rat)
    (hp : ∀ i, 0 ≤ prob i) (hfg : ∀ i, f i ≤ g i) :
    weighted indices prob f ≤ weighted indices prob g := by
  induction indices with
  | nil => exact Rat.le_refl
  | cons i rest ih =>
    have hm := Rat.mul_le_mul_of_nonneg_left (hfg i) (hp i)
    simp only [weighted]
    grind

theorem weighted_congr {I : Type} (indices : List I) (prob f g : I → Rat)
    (hfg : ∀ i, f i = g i) : weighted indices prob f = weighted indices prob g := by
  have heq : f = g := funext hfg
  rw [heq]

theorem weighted_nonneg {I : Type} (indices : List I) (prob f : I → Rat)
    (hp : ∀ i, 0 ≤ prob i) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ weighted indices prob f := by
  induction indices with
  | nil => exact Rat.le_refl
  | cons i rest ih =>
    have hm := Rat.mul_nonneg (hp i) (hf i)
    simp only [weighted]
    grind

/-- An action's duration and finite transition law. -/
structure Action (S : Type) where
  duration : Rat
  count : Nat
  probability : Fin count → Rat
  successor : Fin count → S
  duration_nonnegative : 0 ≤ duration
  probability_nonnegative : ∀ i, 0 ≤ probability i
  probability_normalized : weighted (List.finRange count) probability (fun _ => 1) = 1

/-- The complete state and action model required by the certificate. -/
structure Model (S : Type) where
  complete : S → Prop
  actions : S → List (Action S)

/-- A contingent policy whose every leaf completes within the depth bound. -/
inductive Policy {S : Type} (model : Model S) : Nat → S → Type
  | done {n s} (complete : model.complete s) : Policy model n s
  | act {n s} (action : Action S) (legal : action ∈ model.actions s)
      (continuation : ∀ i, Policy model n (action.successor i)) :
      Policy model (n + 1) s

/-- Expected time includes the duration of every selected action. -/
def expectedTime {S : Type} {model : Model S} {n : Nat} {s : S}
    (policy : Policy model n s) : Rat :=
  match policy with
  | .done _ => 0
  | .act action _ continuation =>
    action.duration + weighted (List.finRange action.count) action.probability
      (fun i => expectedTime (continuation i))

theorem expectedTime_nonnegative {S : Type} {model : Model S} {n : Nat} {s : S}
    (policy : Policy model n s) : 0 ≤ expectedTime policy := by
  induction policy with
  | done _ => exact Rat.le_refl
  | act action legal continuation ih =>
    have hw := weighted_nonneg (List.finRange action.count) action.probability
      (fun i => expectedTime (continuation i)) action.probability_nonnegative ih
    have hd := action.duration_nonnegative
    simp only [expectedTime]
    grind

/-- Bellman inequalities provide a lower bound on every legal policy. -/
structure BellmanBound {S : Type} (model : Model S) (value : Nat → S → Rat) : Prop where
  terminal : ∀ n s, model.complete s → value n s ≤ 0
  action : ∀ n s a, a ∈ model.actions s →
    value (n + 1) s ≤ a.duration + weighted (List.finRange a.count) a.probability
      (fun i => value n (a.successor i))

theorem bellman_lower_bound {S : Type} {model : Model S} {value : Nat → S → Rat}
    (bound : BellmanBound model value) {n : Nat} {s : S}
    (policy : Policy model n s) : value n s ≤ expectedTime policy := by
  induction policy with
  | done complete => exact bound.terminal _ _ complete
  | @act depth state action legal continuation ih =>
    have hw := weighted_mono (List.finRange action.count) action.probability
      (fun i => value _ (action.successor i))
      (fun i => expectedTime (continuation i)) action.probability_nonnegative ih
    have hb := bound.action depth state action legal
    simp only [expectedTime]
    exact Rat.le_trans hb (Rat.add_le_add_left.mpr hw)

/-- Equality at every selected action and terminal leaf certifies attainment. -/
def Attains {S : Type} {model : Model S} (value : Nat → S → Rat)
    {n : Nat} {s : S} (policy : Policy model n s) : Prop :=
  match policy with
  | .done _ => value n s = 0
  | @Policy.act _ _ depth state action _ continuation =>
    value (depth + 1) state =
      action.duration + weighted (List.finRange action.count) action.probability
        (fun i => value depth (action.successor i)) ∧
    ∀ i, Attains value (continuation i)

theorem attains_expectedTime {S : Type} {model : Model S} {value : Nat → S → Rat}
    {n : Nat} {s : S} (policy : Policy model n s) (attains : Attains value policy) :
    expectedTime policy = value n s := by
  induction policy with
  | done complete => exact attains.symm
  | act action legal continuation ih =>
    obtain ⟨step, children⟩ := attains
    have hw := weighted_congr (List.finRange action.count) action.probability
      (fun i => expectedTime (continuation i))
      (fun i => value _ (action.successor i)) (fun i => ih i (children i))
    simp only [expectedTime]
    rw [hw]
    exact step.symm

/-- An attaining Bellman certificate proves optimal expected completion time. -/
theorem certified_optimal {S : Type} {model : Model S} {value : Nat → S → Rat}
    (bound : BellmanBound model value) {n : Nat} {s : S}
    (policy : Policy model n s) (attains : Attains value policy) :
    expectedTime policy = value n s ∧
    ∀ alternative : Policy model n s, expectedTime policy ≤ expectedTime alternative := by
  have exactValue := attains_expectedTime policy attains
  constructor
  · exact exactValue
  · intro alternative
    rw [exactValue]
    exact bellman_lower_bound bound alternative

/-- A normalized probability law preserves a constant expected value. -/
theorem weighted_constant {I : Type} (indices : List I) (prob : I → Rat) (constant : Rat) :
    weighted indices prob (fun _ => constant) =
      weighted indices prob (fun _ => 1) * constant := by
  induction indices with
  | nil => simp only [weighted]; grind
  | cons i rest ih => simp only [weighted]; grind

/-- Randomly mixing bounded-depth legal policies cannot beat the certificate. -/
theorem randomized_mixture_lower_bound {S I : Type} {model : Model S}
    {value : Nat → S → Rat} (bound : BellmanBound model value) {n : Nat} {s : S}
    (policy : Policy model n s) (attains : Attains value policy)
    (indices : List I) (probability : I → Rat)
    (nonnegative : ∀ i, 0 ≤ probability i)
    (normalized : weighted indices probability (fun _ => 1) = 1)
    (alternatives : I → Policy model n s) :
    expectedTime policy ≤ weighted indices probability (fun i => expectedTime (alternatives i)) := by
  have lower := (certified_optimal bound policy attains).2
  have mixed := weighted_mono indices probability (fun _ => expectedTime policy)
    (fun i => expectedTime (alternatives i)) nonnegative (fun i => lower (alternatives i))
  rw [weighted_constant, normalized] at mixed
  grind

/-! A checked finite example. A certain three-second action competes with a
one-second action that either completes or needs three more seconds, each with
probability one half. The latter has optimal expected time 5/2 at depth two.
-/
namespace Example

inductive Stage where
  | start | waiting | complete
  deriving DecidableEq

def certain : Action Stage where
  duration := 3
  count := 1
  probability := fun _ => 1
  successor := fun _ => .complete
  duration_nonnegative := by decide +kernel
  probability_nonnegative := by intro i; decide +kernel
  probability_normalized := by decide +kernel

def gamble : Action Stage where
  duration := 1
  count := 2
  probability := fun _ => 1 / 2
  successor := fun i => if i.val = 0 then .complete else .waiting
  duration_nonnegative := by decide +kernel
  probability_nonnegative := by intro i; decide +kernel
  probability_normalized := by decide +kernel

def model : Model Stage where
  complete := fun s => s = .complete
  actions := fun s => match s with
    | .start => [certain, gamble]
    | .waiting => [certain]
    | .complete => []

def value : Nat → Stage → Rat
  | _, .complete => 0
  | 0, _ => 4
  | _ + 1, .waiting => 3
  | 1, .start => 3
  | _ + 2, .start => 5 / 2

theorem bound : BellmanBound model value := by
  constructor
  · intro n s complete
    change s = .complete at complete
    subst s
    simp [value]
  · intro n s a legal
    cases s with
    | complete => simp [model] at legal
    | waiting =>
      have ha : a = certain := by simpa [model] using legal
      subst a
      simp [value, certain, weighted, List.finRange]
      decide +kernel
    | start =>
      have ha : a = certain ∨ a = gamble := by simpa [model] using legal
      rcases ha with rfl | rfl
      · cases n with
        | zero =>
          decide +kernel
        | succ n =>
          simp [value, certain, weighted, List.finRange]
          decide +kernel
      · cases n with
        | zero =>
          decide +kernel
        | succ n =>
          simp [value, gamble, weighted, List.finRange]
          decide +kernel

def policy : Policy model 2 .start :=
  .act gamble (by simp [model]) (fun i => by
    cases i using Fin.cases with
    | zero =>
      change Policy model 1 .complete
      exact .done rfl
    | succ j =>
      have hj : j = 0 := by apply Fin.ext; omega
      subst j
      change Policy model 1 .waiting
      exact .act certain (by simp [model]) (fun _ => .done rfl))

theorem policy_attains : Attains value policy := by
  constructor
  · decide +kernel
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      have hj : j = 0 := by apply Fin.ext; omega
      subst j
      constructor
      · decide +kernel
      · intro k
        rfl

theorem expected_completion_optimal :
    expectedTime policy = 5 / 2 ∧
    ∀ alternative : Policy model 2 .start, expectedTime policy ≤ expectedTime alternative :=
  certified_optimal bound policy policy_attains

end Example

end CookieClicker.Stochastic

import CookieClicker.UniformRandom
import CookieClicker.HandPickedExpectation

/-! Finite adaptive Hand-picked trial trees under the selected free IID53 law.
The failed native choose([0,1]) branch is computed from the exact finite kernel.
Other free draws can control later decisions; stopping before success remains a
failure. Source phase correspondence and infinite-history measure extension are
separate obligations, not properties assumed by this finite calculation.
-/
namespace CookieClicker.FullGame.AdaptiveHandPicked

open UniformRandom HandPickedExpectation

def sumRange (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumRange f n + f n

def mean (bits : Nat) (f : Nat → Rat) : Rat := sumRange f (size bits) / (size bits : Rat)

theorem sum_indicator (event : Nat → Bool) (count : Nat) :
    sumRange (fun i => if event i then 1 else 0) count =
      (((List.range count).countP event : Nat) : Rat) := by
  induction count with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [List.range_succ, List.countP_append]
    simp only [sumRange, ih, Rat.natCast_add]
    cases chosen : event n <;> simp [chosen, Rat.add_zero]

/-- The tree expectation uses the same uniform finite kernel as eventMass. -/
theorem mean_indicator (bits : Nat) (event : Nat → Bool) :
    mean bits (fun i => if event i then 1 else 0) = eventMass bits event := by
  unfold mean eventMass
  rw [sum_indicator]

theorem sum_mono (f g : Nat → Rat) (count : Nat)
    (bounded : ∀ i, i < count → f i ≤ g i) : sumRange f count ≤ sumRange g count := by
  induction count with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have prefixBound := ih (fun i hi => bounded i (by omega))
    have last := bounded n (by omega)
    simp only [sumRange]
    grind

theorem constant_sum (value : Rat) (count : Nat) :
    sumRange (fun _ => value) count = (count : Rat) * value := by
  induction count with
  | zero => simp [sumRange, Rat.zero_mul]
  | succ n ih =>
    simp only [sumRange, ih, Rat.natCast_add, Rat.natCast_ofNat]
    grind

theorem masked_constant_sum (value : Rat) (threshold count : Nat) :
    sumRange (fun i => if i < threshold then value else 0) count = (min count threshold : Nat) * value := by
  induction count with
  | zero => simp [sumRange, Rat.zero_mul]
  | succ n ih =>
    simp only [sumRange, ih]
    by_cases low : n < threshold
    · rw [if_pos low, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      simp only [Rat.natCast_add, Rat.natCast_ofNat]
      grind
    · rw [if_neg low, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      simp [Rat.add_zero]

theorem mean_mono (bits : Nat) (f g : Nat → Rat)
    (bounded : ∀ i, i < size bits → f i ≤ g i) : mean bits f ≤ mean bits g := by
  have positive : (0 : Rat) < (size bits : Rat) := Rat.natCast_pos.mpr (size_positive bits)
  apply Rat.le_of_mul_le_mul_right (c := (size bits : Rat)) _ positive
  simp only [mean, Rat.div_mul_cancel (by grind : (size bits : Rat) ≠ 0)]
  exact sum_mono f g _ bounded

theorem mean_constant (bits : Nat) (value : Rat) : mean bits (fun _ => value) = value := by
  unfold mean
  rw [constant_sum]
  have positive : (0 : Rat) < (size bits : Rat) := Rat.natCast_pos.mpr (size_positive bits)
  rw [Rat.mul_comm]
  exact Rat.mul_div_cancel (by grind)

theorem mean_lower (bits : Nat) (f : Nat → Rat) (lower : Rat)
    (bounded : ∀ i, i < size bits → lower ≤ f i) : lower ≤ mean bits f := by
  have h := mean_mono bits (fun _ => lower) f bounded
  rw [mean_constant] at h
  exact h

theorem mean_half_mask (bits : Nat) (value : Rat) :
    mean (bits + 1) (fun i => if i < size bits then value else 0) = value / 2 := by
  unfold mean
  rw [masked_constant_sum]
  have positive := size_positive bits
  have doubled : size (bits + 1) = size bits * 2 := Nat.pow_succ _ _
  rw [Nat.min_eq_right (by omega), doubled, Rat.natCast_mul]
  have hpos : (0 : Rat) < (size bits : Rat) := Rat.natCast_pos.mpr positive
  have cancel := Rat.div_mul_cancel (a := (size bits : Rat) * value)
    (b := (size bits : Rat) * 2) (by grind)
  have halfCancel := Rat.div_mul_cancel (a := value) (b := 2) (by decide +kernel)
  grind

private theorem half_at_most_one (n : Nat) : halfSurvival n ≤ 1 := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have cancel := Rat.div_mul_cancel (a := halfSurvival n) (b := 2) (by decide +kernel)
    simp only [halfSurvival]
    grind

/-- An observation can inspect any free outcome before choosing a later action.
A target trial consumes one of the remaining attempt opportunities. On success,
the no-success event ends. On failure, its continuation can depend on the draw.
The latter even permits more information than the native binary choice reveals.
-/
inductive Tree : Nat → Type where
  | stop (attemptBudget : Nat) : Tree attemptBudget
  | observe {n : Nat} (next : Draw 53 → Tree n) : Tree n
  | attempt {n : Nat} (next : Draw 53 → Tree n) : Tree (n + 1)

def rangeDraw (index : Nat) : Draw 53 := ⟨index % size 53, Nat.mod_lt _ (size_positive 53)⟩

def noSuccessMass {n : Nat} : Tree n → Rat
  | .stop _ => 1
  | .observe next => mean 53 (fun index => noSuccessMass (next (rangeDraw index)))
  | .attempt next => mean 53 (fun index =>
      if index < size 52 then noSuccessMass (next (rangeDraw index)) else 0)

theorem noSuccessMass_bounds {n : Nat} (tree : Tree n) :
    0 ≤ noSuccessMass tree ∧ noSuccessMass tree ≤ 1 := by
  induction tree with
  | stop _ => change (0 : Rat) ≤ 1 ∧ (1 : Rat) ≤ 1; decide +kernel
  | observe next ih =>
    constructor
    · apply mean_lower; intro i _; exact (ih (rangeDraw i)).1
    · have h := mean_mono 53 (fun i => noSuccessMass (next (rangeDraw i))) (fun _ => 1)
        (fun i _ => (ih (rangeDraw i)).2)
      rw [mean_constant] at h
      exact h
  | attempt next ih =>
    constructor
    · apply mean_lower
      intro i _
      by_cases low : i < size 52
      · simpa only [if_pos low] using (ih (rangeDraw i)).1
      · simp only [if_neg low]; exact Rat.le_refl
    · have h := mean_mono 53
        (fun i => if i < size 52 then noSuccessMass (next (rangeDraw i)) else 0) (fun _ => 1)
        (by
          intro i _
          by_cases low : i < size 52
          · simpa only [if_pos low] using (ih (rangeDraw i)).2
          · simp only [if_neg low]; decide +kernel)
      rw [mean_constant] at h
      exact h

/-- No conditional-fairness field is supplied: the factor one-half follows from
the computed free kernel at each native target branch, including adaptive noise.
-/
theorem adaptive_failure_lower {n : Nat} (tree : Tree n) :
    halfSurvival n ≤ noSuccessMass tree := by
  induction tree with
  | stop n => exact half_at_most_one n
  | @observe n next ih =>
    apply mean_lower
    intro i _
    exact ih (rangeDraw i)
  | @attempt n next ih =>
    have h := mean_mono 53
      (fun i => if i < size 52 then halfSurvival n else 0)
      (fun i => if i < size 52 then noSuccessMass (next (rangeDraw i)) else 0)
      (by
        intro i _
        by_cases low : i < size 52
        · simpa only [if_pos low] using ih (rangeDraw i)
        · simp only [if_neg low]; exact Rat.le_refl)
    rw [mean_half_mask 52] at h
    exact h

/-- Arbitrarily many modeled nuisance draws cannot improve the finite target
failure bound. Source correspondence must identify each attempted unripe choice
as a target node in free mode; seeded outputs are not observation nodes here.
-/
theorem stopped_policy_included (n : Nat) : noSuccessMass (.stop n) = 1 := rfl

def useEveryAttempt : (n : Nat) → Tree n
  | 0 => .stop 0
  | n + 1 => .attempt (fun _ => useEveryAttempt n)

/-- Using every available target trial attains the probability bound. This is
about the finite eligible-trial count, not their earliest possible game times.
-/
theorem full_trial_budget_attains (n : Nat) :
    noSuccessMass (useEveryAttempt n) = halfSurvival n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [useEveryAttempt, noSuccessMass, ih]
    exact mean_half_mask 52 (halfSurvival n)

end CookieClicker.FullGame.AdaptiveHandPicked

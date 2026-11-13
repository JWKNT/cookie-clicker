import CookieClicker.UniformRandom
import CookieClicker.HandPickedExpectation

/-! The native zero-time dragon-pet retry, at a fixed calendar quarter whose
seed-selected drop is known to be missing. The selected IID53 law supplies each
free trial. Explicitly seeded drop selection is fixed, not resampled here.
This is a local acquisition result, not a full-game optimality certificate.
-/
namespace CookieClicker.FullGame.PetRetry

open UniformRandom

/-- Exact binary64 value of the native literal expression 1/20. -/
def nativeThreshold : Rat := 3602879701896397 / 72057594037927936
def successfulIndices : Nat := 450359962737050
def successProbability : Rat := 225179981368525 / 4503599627370496
def failureProbability : Rat := 1 - successProbability

theorem native_threshold_count :
    (nativeThreshold * (size 53 : Rat)).ceil = (successfulIndices : Int) := by
  decide +kernel

theorem native_trial_iff (draw : Draw 53) :
    value draw < nativeThreshold ↔ draw.val < successfulIndices := by
  have positive : (0 : Rat) < (size 53 : Rat) := Rat.natCast_pos.mpr (size_positive 53)
  unfold value
  rw [Rat.div_lt_iff positive]
  have h := Rat.lt_ceil_iff (x := nativeThreshold * (size 53 : Rat)) (y := (draw.val : Int))
  rw [native_threshold_count] at h
  simpa only [Rat.intCast_natCast, Int.ofNat_lt] using h.symm

theorem exact_success_probability :
    eventMass 53 (interval 0 successfulIndices) = successProbability := by
  rw [interval_mass _ _ _ (by omega) (by decide +kernel)]
  decide +kernel

theorem exact_failure_probability :
    eventMass 53 (interval successfulIndices (size 53)) = failureProbability := by
  rw [interval_mass _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem probability_bounds : 0 < successProbability ∧ successProbability < 1 ∧
    0 < failureProbability ∧ failureProbability < 1 ∧
    failureProbability * (21 / 20) ≤ 1 := by
  decide +kernel

/-- A pet samples the free trigger, then uses the already fixed missing drop.
This transition charges no elapsed time, as in the native input adapter.
-/
structure State where
  elapsed : Nat
  missing : Bool
  deriving DecidableEq

def pet (state : State) (draw : Draw 53) : State :=
  { state with missing := state.missing && decide (successfulIndices ≤ draw.val) }

theorem pet_preserves_time (state : State) (draw : Draw 53) :
    (pet state draw).elapsed = state.elapsed := rfl

theorem pet_acquires_iff (state : State) (draw : Draw 53) (missing : state.missing = true) :
    (pet state draw).missing = false ↔ value draw < nativeThreshold := by
  rw [native_trial_iff]
  simp [pet, missing]

/-- Exact finite-prefix failure probability under independent free trials. -/
def failure : Nat → Rat
  | 0 => 1
  | n + 1 => failure n * failureProbability

def firstSuccess (n : Nat) : Rat := failure n * successProbability

/-- The first-success weights are computed finite cylinders of the selected
independent free kernel, not an additional supplied probability distribution.
-/
theorem first_success_cylinder (n : Nat) :
    cylinderMass 53 ((List.replicate n (interval successfulIndices (size 53))) ++
      [interval 0 successfulIndices]) = firstSuccess n := by
  induction n with
  | zero => simp [cylinderMass, exact_success_probability, firstSuccess, failure, Rat.mul_one, Rat.one_mul]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [cylinderMass, exact_failure_probability]
    rw [ih]
    change failureProbability * (failure n * successProbability) =
      (failure n * failureProbability) * successProbability
    clear ih
    grind

theorem failure_positive (n : Nat) : 0 < failure n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have positive := probability_bounds.2.2.1
    unfold failure
    exact Rat.mul_pos ih positive

theorem finite_prefix_mass (n : Nat) :
    HandPickedExpectation.sumFrom firstSuccess 0 n = 1 - failure n := by
  induction n with
  | zero => simp [HandPickedExpectation.sumFrom, failure]; decide +kernel
  | succ n ih =>
    simp only [HandPickedExpectation.sumFrom, Nat.zero_add, firstSuccess, failure]
    rw [ih]
    unfold failureProbability
    grind

private theorem failure_rate (n : Nat) : failure n * (1 + (n : Rat) / 20) ≤ 1 := by
  induction n with
  | zero => simp [failure]; decide +kernel
  | succ n ih =>
    have tpositive := failure_positive n
    have qbound := probability_bounds.2.2.2
    have npositive : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
    have coefficient : failureProbability * (1 + ((n + 1 : Nat) : Rat) / 20) ≤
        1 + (n : Rat) / 20 := by
      have h := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt qbound.1) npositive
      simp only [Rat.natCast_add, Rat.natCast_ofNat]
      grind
    have h := Rat.mul_le_mul_of_nonneg_left coefficient (Rat.le_of_lt tpositive)
    simp only [failure]
    grind

private theorem exists_nat_above (q : Rat) : ∃ n : Nat, q < (n : Rat) := by
  let z := q.ceil + 1
  have hceil : q ≤ (q.ceil : Rat) := Rat.le_ceil
  have hz : (q.ceil : Rat) < (z : Rat) := Rat.intCast_lt_intCast.mpr (by dsimp [z]; omega)
  have hnat : (z : Rat) ≤ (z.toNat : Rat) := Rat.intCast_le_intCast.mpr (Int.self_le_toNat z)
  exact ⟨z.toNat, by grind⟩

theorem failure_tends_to_zero (epsilon : Rat) (positive : 0 < epsilon) :
    ∃ n, failure n < epsilon := by
  obtain ⟨n, large⟩ := exists_nat_above (20 / epsilon)
  have product := (Rat.div_lt_iff positive).mp large
  have rate := failure_rate n
  have npositive : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have coefficient : (0 : Rat) ≤ 1 + (n : Rat) / 20 := by grind
  refine ⟨n, Rat.not_le.mp ?_⟩
  intro tooLarge
  have h := Rat.mul_le_mul_of_nonneg_right tooLarge coefficient
  grind

theorem failure_decreasing {earlier later : Nat} (ordered : earlier ≤ later) :
    failure later ≤ failure earlier := by
  induction later generalizing earlier with
  | zero =>
    have same : earlier = 0 := by omega
    subst earlier
    exact Rat.le_refl
  | succ later ih =>
    by_cases same : earlier = later + 1
    · subst earlier; exact Rat.le_refl
    · have positive := failure_positive later
      have q := probability_bounds.2.2.2.1
      have step := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt q) (Rat.le_of_lt positive)
      simp only [Rat.mul_one] at step
      exact Rat.le_trans step (ih (by omega))

theorem failure_eventually_small (epsilon : Rat) (positive : 0 < epsilon) :
    ∃ cutoff, ∀ later, cutoff ≤ later → failure later < epsilon := by
  obtain ⟨cutoff, small⟩ := failure_tends_to_zero epsilon positive
  refine ⟨cutoff, ?_⟩
  intro later ordered
  have h := failure_decreasing ordered
  grind

/-- Every finite cap has positive failure probability, but the infinite-failure
branch has zero mass. This result does not remove that branch from the path space.
-/
theorem infinite_failure_mass_zero (mass : Rat) (nonnegative : 0 ≤ mass)
    (prefixBound : ∀ n, mass ≤ failure n) : mass = 0 := by
  apply Rat.le_antisymm _ nonnegative
  apply Rat.not_lt.mp
  intro positive
  obtain ⟨n, small⟩ := failure_tends_to_zero mass positive
  have bound := prefixBound n
  grind

/-- The exact masses of finite first-success indices sum to one. -/
theorem first_success_mass_normalized (epsilon : Rat) (positive : 0 < epsilon) :
    ∃ n, 1 - epsilon < HandPickedExpectation.sumFrom firstSuccess 0 n ∧
      HandPickedExpectation.sumFrom firstSuccess 0 n ≤ 1 := by
  obtain ⟨n, small⟩ := failure_tends_to_zero epsilon positive
  refine ⟨n, ?_, ?_⟩ <;> rw [finite_prefix_mass]
  · grind
  · have h := failure_positive n; grind

/-- `none` is the infinite-failure outcome. Finite outcomes number failures
before the first successful pet, whose first terminal checkpoint has elapsed 0.
-/
abbrev Outcome := Option Nat

def completedAt : Outcome → Nat → Bool
  | none, _ => false
  | some failures, attempts => decide (failures < attempts)

def hittingTime : Outcome → Option Nat
  | none => none
  | some _ => some 0

def rejectedDraw : Draw 53 := ⟨successfulIndices, by decide +kernel⟩
def acceptedDraw : Draw 53 := ⟨0, size_positive 53⟩

/-- Representative draws for each success/failure class of the native branch.
Every draw in a class has the same local state effect.
-/
def outcomeDraw : Outcome → Nat → Draw 53
  | none, _ => rejectedDraw
  | some failures, index => if index < failures then rejectedDraw else acceptedDraw

def retryState (outcome : Outcome) : Nat → State
  | 0 => { elapsed := 0, missing := true }
  | n + 1 => pet (retryState outcome n) (outcomeDraw outcome n)

theorem retry_state_time (outcome : Outcome) (attempts : Nat) :
    (retryState outcome attempts).elapsed = 0 := by
  induction attempts with
  | zero => rfl
  | succ n ih => exact ih

theorem retry_state_completion (outcome : Outcome) (attempts : Nat) :
    (retryState outcome attempts).missing = !completedAt outcome attempts := by
  induction attempts with
  | zero => cases outcome <;> simp [retryState, completedAt]
  | succ n ih =>
    unfold retryState pet
    rw [ih]
    cases outcome with
    | none => simp [completedAt, outcomeDraw, rejectedDraw]
    | some failures =>
      by_cases before : n < failures
      · have before' : ¬failures < n := by omega
        have before'' : ¬failures < n + 1 := by omega
        simp [outcomeDraw, completedAt, before, before', before'', rejectedDraw]
      · have now : failures < n + 1 := by omega
        simp [outcomeDraw, completedAt, before, now, acceptedDraw, successfulIndices]

theorem finite_outcome_first_hit (failures : Nat) :
    completedAt (some failures) (failures + 1) = true ∧
    ∀ earlier, earlier ≤ failures → completedAt (some failures) earlier = false := by
  simp [completedAt]

theorem infinite_failure_has_infinite_hitting_time :
    hittingTime none = none ∧ ∀ index, completedAt none index = false := by
  simp [hittingTime, completedAt]

/-- Truncate hitting time before taking expectations. Every finite first-hit
outcome has time zero; the retained infinite-failure outcome is charged `cap`.
-/
def truncatedTime (outcome : Outcome) (cap : Nat) : Nat :=
  match hittingTime outcome with
  | none => cap
  | some time => min time cap

def expectedTruncated (failureMass : Rat) (cap prefixLength : Nat) : Rat :=
  HandPickedExpectation.sumFrom
    (fun index => firstSuccess index * (truncatedTime (some index) cap : Rat)) 0 prefixLength +
    failureMass * (truncatedTime none cap : Rat)

/-- With the proved zero infinite-failure mass, all expectation truncations are
zero. The first-hit convention still assigns infinity to the null failed path.
-/
theorem expected_additional_time_zero (cap prefixLength : Nat) :
    expectedTruncated 0 cap prefixLength = 0 := by
  unfold expectedTruncated
  induction prefixLength with
  | zero => simp [HandPickedExpectation.sumFrom, Rat.zero_mul, Rat.add_zero]
  | succ n ih =>
    simp [HandPickedExpectation.sumFrom, truncatedTime, hittingTime, Rat.zero_mul,
      Rat.mul_zero, Rat.add_zero] at *
    exact ih

/-- Zero elapsed acquisition time meets the universal nonnegative time bound.
Applicability requires the fixed quarter's selected item to be missing and every
trial to use the declared free kernel. This is only the local pet subproblem.
-/
theorem local_time_minimum (competitor : Rat) (nonnegative : 0 ≤ competitor)
    (cap prefixLength : Nat) : expectedTruncated 0 cap prefixLength ≤ competitor := by
  rw [expected_additional_time_zero]
  exact nonnegative

end CookieClicker.FullGame.PetRetry

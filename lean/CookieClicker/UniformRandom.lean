import Std

/-! Exact finite uniform draws for the selected unseeded probability model.
These are independent draws only when supplied by the full probability model.
Explicitly seeded native generators are not replaced by this kernel. The native
binary64 evaluation and the source-to-kernel refinement remain separate checks.
-/
namespace CookieClicker.FullGame.UniformRandom

def size (bits : Nat) : Nat := 2 ^ bits

theorem size_positive (bits : Nat) : 0 < size bits := Nat.pow_pos (by decide)

abbrev Draw (bits : Nat) := Fin (size bits)

def value {bits : Nat} (draw : Draw bits) : Rat := (draw.val : Rat) / (size bits : Rat)

/-- Probability of a predicate under one uniform draw, before any source refinement. -/
def eventMass (bits : Nat) (event : Nat → Bool) : Rat :=
  (((List.range (size bits)).countP event : Nat) : Rat) / (size bits : Rat)

theorem mass_nonnegative (bits : Nat) (event : Nat → Bool) : 0 ≤ eventMass bits event := by
  have positive := Rat.natCast_pos.mpr (size_positive bits)
  apply Rat.le_of_mul_le_mul_right (c := (size bits : Rat)) _ positive
  unfold eventMass
  rw [Rat.zero_mul, Rat.div_mul_cancel (by grind)]
  exact Rat.natCast_nonneg

theorem mass_at_most_one (bits : Nat) (event : Nat → Bool) : eventMass bits event ≤ 1 := by
  have positive := Rat.natCast_pos.mpr (size_positive bits)
  apply Rat.le_of_mul_le_mul_right (c := (size bits : Rat)) _ positive
  unfold eventMass
  rw [Rat.one_mul, Rat.div_mul_cancel (by grind)]
  apply Rat.natCast_le_natCast.mpr
  simpa using (List.countP_le_length (p := event) (l := List.range (size bits)))

def interval (lower upper : Nat) (index : Nat) : Bool := decide (lower ≤ index ∧ index < upper)

theorem count_interval (lower upper count : Nat) (ordered : lower ≤ upper) :
    (List.range count).countP (interval lower upper) = min count upper - min count lower := by
  induction count with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases lo : lower ≤ n <;> by_cases hi : n < upper <;>
      simp [interval, lo, hi, Nat.min_def] <;> grind

theorem interval_mass (bits lower upper : Nat) (ordered : lower ≤ upper)
    (bounded : upper ≤ size bits) :
    eventMass bits (interval lower upper) = ((upper - lower : Nat) : Rat) / (size bits : Rat) := by
  unfold eventMass
  rw [count_interval _ _ _ ordered]
  rw [Nat.min_eq_right bounded, Nat.min_eq_right (Nat.le_trans ordered bounded)]

theorem certain_mass (bits : Nat) : eventMass bits (fun _ => true) = 1 := by
  have positive := Rat.natCast_pos.mpr (size_positive bits)
  have count : (List.range (size bits)).countP (fun _ => true) = size bits := by simp
  unfold eventMass
  rw [count]
  have cancel := Rat.mul_div_cancel (a := 1) (b := (size bits : Rat)) (by grind)
  simpa only [Rat.one_mul] using cancel

/-- A draw with one extra bit splits into two equally sized half intervals. -/
theorem fair_half (bits : Nat) :
    eventMass (bits + 1) (interval (size bits) (size (bits + 1))) = 1 / 2 := by
  have positive := size_positive bits
  have doubled : size (bits + 1) = size bits * 2 := Nat.pow_succ _ _
  rw [interval_mass _ _ _ (by omega) (by omega)]
  rw [show size (bits + 1) - size bits = size bits from by omega]
  rw [doubled, Rat.natCast_mul]
  have p : (0 : Rat) < (size bits : Rat) := Rat.natCast_pos.mpr positive
  have neq : (size bits : Rat) ≠ 0 := by grind
  have cancel := Rat.div_mul_cancel (a := (size bits : Rat)) (b := (size bits : Rat) * 2) (by grind)
  have twoCancel := Rat.div_mul_cancel (a := 1) (b := 2) (by decide +kernel)
  grind

/-- The native two-item choice uses floor(2u). For exact rational u, this is
the top bit of the finite index. The binary64 correspondence is tested separately.
-/
def chooseTwo {bits : Nat} (draw : Draw (bits + 1)) : Nat := draw.val / size bits

theorem choose_two_support {bits : Nat} (draw : Draw (bits + 1)) : chooseTwo draw < 2 := by
  unfold chooseTwo
  apply (Nat.div_lt_iff_lt_mul (size_positive bits)).mpr
  have bound := draw.isLt
  have doubled : size (bits + 1) = size bits * 2 := Nat.pow_succ _ _
  omega

theorem choose_two_success_iff {bits : Nat} (draw : Draw (bits + 1)) :
    chooseTwo draw = 1 ↔ size bits ≤ draw.val := by
  have support := choose_two_support draw
  unfold chooseTwo at *
  have positive := size_positive bits
  have below := Nat.div_lt_iff_lt_mul (x := draw.val) (y := 1) positive
  simp only [Nat.one_mul] at below
  omega

theorem uniform53_unripe_success_mass :
    eventMass 53 (interval (size 52) (size 53)) = 1 / 2 := fair_half 52

/-- A finite cylinder under the declared independent-draw law. -/
def cylinderMass (bits : Nat) : List (Nat → Bool) → Rat
  | [] => 1
  | event :: rest => eventMass bits event * cylinderMass bits rest

def letterA : Nat → Bool := interval 32477881928153 313952858638809
def letterO : Nat → Bool := interval 4882508249865610 5163983226576266

theorem letter_a_mass : eventMass 53 letterA = 1 / 32 := by
  unfold letterA
  rw [interval_mass _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem letter_o_mass : eventMass 53 letterO = 1 / 32 := by
  unfold letterO
  rw [interval_mass _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem letter_a_index (index : Nat) (inside : letterA index = true) :
    index * 26 / size 53 = 0 := by
  simp only [letterA, interval, decide_eq_true_eq] at inside
  have denominator : size 53 = 9007199254740992 := by decide +kernel
  rw [denominator]
  omega

theorem letter_o_index (index : Nat) (inside : letterO index = true) :
    index * 26 / size 53 = 14 := by
  simp only [letterO, interval, decide_eq_true_eq] at inside
  have denominator : size 53 = 9007199254740992 := by decide +kernel
  rw [denominator]
  omega

/-- An explicit independent-draw cylinder produces the five selected buckets.
Source alphabet indexing and binary64 multiplication are checked separately.
-/
theorem helper_seed_cylinder_mass :
    cylinderMass 53 [letterA, letterA, letterA, letterA, letterO] = 1 / 33554432 := by
  simp only [cylinderMass, letter_a_mass, letter_o_mass]
  decide +kernel

end CookieClicker.FullGame.UniformRandom

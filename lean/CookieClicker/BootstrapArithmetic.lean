import CookieClicker.GodzamokRounding
import CookieClicker.JavaScriptNumber

/-! Arithmetic for a proposed finite new-save funding route.
The cent recurrence is the binary64 integer projection after scaling native
Godzamok multipliers by 2^59. Source-call and scaling refinement are separate
obligations. This file does not assert native full-game reachability. -/
namespace CookieClicker.FullGame.BootstrapArithmetic
open GodzamokRounding
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

def centNumerator : Nat := 5764607523034235
def multiplierScale : Nat := 2 ^ 59
def centCap : Nat := 2 ^ 106
def centLowerStep : Nat := 2 ^ 50

theorem native_cent_literal :
    JavaScript.Number.magnitudeFraction (JavaScript.Number.ofScientific 1 (-2)) =
      (centNumerator, multiplierScale) := by decide +kernel

theorem native_cent_cap_fixed :
    JavaScript.Number.add (JavaScript.Number.ofNat (2 ^ 47))
      (JavaScript.Number.ofScientific 1 (-2)) = JavaScript.Number.ofNat (2 ^ 47) := by decide +kernel

theorem roundMultiple_lower_error (spacing n : Nat) (positive : 0 < spacing) :
    n ≤ roundMultiple spacing n + spacing / 2 := by
  have remainder := Nat.mod_lt n positive
  have decomposition := Nat.mod_add_div n spacing
  rw [Nat.mul_comm spacing (n / spacing)] at decomposition
  dsimp only [roundMultiple]
  split
  · simp only [Nat.add_mul, Nat.one_mul]
    omega
  · rename_i notUp
    simp only [Nat.add_zero]
    have notAbove : ¬ spacing < 2 * (n % spacing) := by
      intro above
      simp [above] at notUp
    omega

theorem roundMultiple_le_multiple (spacing n bound : Nat)
    (positive : 0 < spacing) (within : n ≤ bound) (multiple : spacing ∣ bound) :
    roundMultiple spacing n ≤ bound := by
  have remN := Nat.mod_lt n positive
  have decompN := Nat.mod_add_div n spacing
  rw [Nat.mul_comm spacing (n / spacing)] at decompN
  have boundEq := Nat.div_mul_cancel multiple
  have quotient : n / spacing ≤ bound / spacing := Nat.div_le_div_right within
  dsimp only [roundMultiple]
  split
  · rename_i up
    have strict : n / spacing < bound / spacing := by
      by_cases strict : n / spacing < bound / spacing
      · exact strict
      · have equal : n / spacing = bound / spacing := by omega
        have zeroRem : n % spacing = 0 := by rw [equal, boundEq] at decompN; omega
        simp [zeroRem] at up
        omega
    have order := Nat.mul_le_mul_right spacing (show n / spacing + 1 ≤ bound / spacing by omega)
    simpa only [Nat.add_zero, boundEq] using order
  · have order := Nat.mul_le_mul_right spacing quotient
    simpa only [Nat.add_zero, boundEq] using order

theorem spacing_below_cap (n : Nat) (below : n < centCap) :
    0 < integerSpacing n ∧ integerSpacing n ≤ 2 ^ 53 ∧ integerSpacing n ∣ centCap := by
  unfold integerSpacing
  split
  · simp [centCap]
  · rename_i notSmall
    have nonzero : n ≠ 0 := by omega
    have logarithm : n.log2 < 106 := (Nat.log2_lt nonzero).mpr below
    have exponent : n.log2 - 52 ≤ 53 := by omega
    refine ⟨Nat.two_pow_pos _, Nat.pow_le_pow_right (by decide) exponent, ?_⟩
    exact Nat.pow_dvd_pow 2 (by omega)

theorem rounded_near_cap (n : Nat) (lower : centCap ≤ n)
    (upper : n ≤ centCap + centNumerator) : roundedInteger n = centCap := by
  have positive : n ≠ 0 := by unfold centCap at *; omega
  have logarithm : n.log2 = 106 := (Nat.log2_eq_iff positive).mpr
    ⟨lower, by unfold centCap centNumerator at *; omega⟩
  have notSmall : ¬ n < 2 ^ 53 := by unfold centCap at *; omega
  have quotient : n / 2 ^ 54 = 2 ^ 52 := by unfold centCap centNumerator at *; omega
  have remainder : n % 2 ^ 54 = n - centCap := by unfold centCap centNumerator at *; omega
  have notAbove : ¬ 2 ^ 54 < 2 * (n - centCap) := by unfold centCap centNumerator at *; omega
  simp only [roundedInteger, integerSpacing, if_neg notSmall, logarithm]
  change roundMultiple (2 ^ 54) n = centCap
  simp only [roundMultiple, quotient, remainder]
  have even : ((2 ^ 52) % 2 == 1) = false := by decide +kernel
  simp only [even, Bool.and_false, Bool.or_false, decide_eq_true_eq, if_neg notAbove, Nat.add_zero]
  rfl

theorem cent_step_bounds (n : Nat) (within : n ≤ centCap) :
    min (n + centLowerStep) centCap ≤ roundedInteger (n + centNumerator) ∧
    roundedInteger (n + centNumerator) ≤ centCap := by
  by_cases below : n + centNumerator < centCap
  · obtain ⟨positive, spacingBound, multiple⟩ := spacing_below_cap _ below
    have error := roundMultiple_lower_error _ (n + centNumerator) positive
    have halfBound : integerSpacing (n + centNumerator) / 2 ≤ 2 ^ 52 := by omega
    have growth : n + centLowerStep ≤ roundedInteger (n + centNumerator) := by
      unfold roundedInteger centLowerStep centNumerator at *
      omega
    exact ⟨Nat.le_trans (Nat.min_le_left _ _) growth,
      roundMultiple_le_multiple _ _ _ positive (Nat.le_of_lt below) multiple⟩
  · have rounded := rounded_near_cap (n + centNumerator) (by omega) (by omega)
    rw [rounded]
    exact ⟨Nat.min_le_right _ _, Nat.le_refl _⟩

def centIterations : Nat → Nat
  | 0 => multiplierScale
  | n + 1 => roundedInteger (centIterations n + centNumerator)

theorem cent_iterations_bounds (n : Nat) :
    min (multiplierScale + n * centLowerStep) centCap ≤ centIterations n ∧
    centIterations n ≤ centCap := by
  induction n with
  | zero => simp [centIterations, multiplierScale, centCap]
  | succ n ih =>
    obtain ⟨stepLower, stepUpper⟩ := cent_step_bounds _ ih.2
    refine ⟨?_, stepUpper⟩
    simp only [centIterations]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem cent_cap_reached_by_finite_prefix : centIterations (2 ^ 56) = centCap := by
  obtain ⟨lower, upper⟩ := cent_iterations_bounds (2 ^ 56)
  have target : min (multiplierScale + 2 ^ 56 * centLowerStep) centCap = centCap := by
    decide +kernel
  rw [target] at lower
  omega

theorem cent_cap_fixed : roundedInteger (centCap + centNumerator) = centCap :=
  rounded_near_cap _ (by omega) (by omega)

def passiveScale : Nat := 2 ^ 61
def passiveIncrement : Nat := 7686143364045647
def passiveTarget : Nat := 1000000000 * passiveScale
def passiveLowerStep : Nat := 2 ^ 52

theorem native_cursor_frame_increment :
    JavaScript.Number.magnitudeFraction
      (JavaScript.Number.div (JavaScript.Number.ofScientific 1 (-1)) (JavaScript.Number.ofNat 30)) =
      (passiveIncrement, passiveScale) := by decide +kernel

theorem native_temple_plastic_mouse_base :
    JavaScript.Number.add (JavaScript.Number.ofNat 8)
      (JavaScript.Number.mul (JavaScript.Number.ofNat 7800) (JavaScript.Number.ofScientific 1 (-2))) =
      JavaScript.Number.ofNat 86 := by decide +kernel

/-- Native `0.1/30` has this exact dyadic numerator over 2^61. -/
theorem passive_numerator_margin :
    passiveLowerStep + 2 ^ 38 ≤ passiveIncrement := by decide +kernel

theorem passive_step_progress (n : Nat) (below : n < passiveTarget) :
    n + passiveLowerStep ≤ roundedInteger (n + passiveIncrement) := by
  have bound : n + passiveIncrement < 2 ^ 92 := by
    unfold passiveTarget passiveScale passiveIncrement at *
    omega
  have spacing : 0 < integerSpacing (n + passiveIncrement) ∧
      integerSpacing (n + passiveIncrement) ≤ 2 ^ 39 := by
    unfold integerSpacing
    split
    · decide +kernel
    · rename_i notSmall
      have nonzero : n + passiveIncrement ≠ 0 := by omega
      have logarithm : (n + passiveIncrement).log2 < 92 := (Nat.log2_lt nonzero).mpr bound
      refine ⟨Nat.two_pow_pos _, Nat.pow_le_pow_right (by decide) ?_⟩
      omega
  have error := roundMultiple_lower_error _ (n + passiveIncrement) spacing.1
  have half : integerSpacing (n + passiveIncrement) / 2 ≤ 2 ^ 38 := by omega
  have margin := passive_numerator_margin
  unfold roundedInteger
  omega

def passiveIterations : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let old := passiveIterations n
    if old < passiveTarget then roundedInteger (old + passiveIncrement) else old

theorem passive_iterations_progress (n : Nat) :
    min (n * passiveLowerStep) passiveTarget ≤ passiveIterations n := by
  induction n with
  | zero => simp [passiveIterations]
  | succ n ih =>
    simp only [passiveIterations]
    split
    · rename_i below
      have next := passive_step_progress _ below
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [Nat.add_mul, Nat.one_mul]
      omega

theorem passive_reaches_billion_in_finite_frames :
    passiveTarget ≤ passiveIterations (512 * 1000000000) := by
  have reached := passive_iterations_progress (512 * 1000000000)
  have exactBudget : min (512 * 1000000000 * passiveLowerStep) passiveTarget = passiveTarget := by
    decide +kernel
  rw [exactBudget] at reached
  exact reached

/-- Below one billion, even a 1/512-cookie frame increment suffices in this
many frames. The native Cursor gain and frame-clock refinements are separate. -/
theorem challenge_frame_budget : 512 * 1000000000 + 150 < 2 ^ 40 := by decide +kernel

theorem proposed_bootstrap_frame_budget :
    512 * 1000000000 + 150 + 3000000 + 334 * (2 ^ 30 + 256) < 2 ^ 40 := by decide +kernel

/-- Numerical headroom for a proposed triangular eight-stage rebuild plan.
The bound does not establish that each native stage satisfies its click premise. -/
theorem proposed_income_frame_budget :
    36 * ((2 ^ 48 + 399) / 400) * 334 + 2 ^ 40 < 2 ^ 53 := by decide +kernel

theorem low_bank_burst_gain (bank cycles : Nat) (large : 1024 ≤ bank)
    (chosen : cycles = bank / 32) : 16 * cycles ≤ bank ∧ bank / 4 ≤ 9 * cycles := by
  subst cycles
  omega

theorem first_lump_nonmeaty (draw : Rat) (nonnegative : 0 ≤ draw) :
    ¬ draw < (1 / 10 : Rat) * 0 := by
  have zero : (1 / 10 : Rat) * 0 = 0 := by decide +kernel
  rw [zero]
  change ¬ draw.blt 0 = true
  rw [nonnegative]
  decide

end CookieClicker.FullGame.BootstrapArithmetic

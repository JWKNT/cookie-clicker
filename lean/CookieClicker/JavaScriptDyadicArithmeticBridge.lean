import CookieClicker.JavaScriptRoundingBridge

/-! Algebraic composition for the actual logical Float.Model operations.
The first results remove exact powers of two before native normalization.
These statements do not assume a separate arithmetic oracle or native evaluator.
-/
namespace CookieClicker.JavaScript.DyadicArithmeticBridge
open Float.Model Float.Model.UnpackedFloat RoundingBridge
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 2048
set_option maxHeartbeats 2000000

theorem repeat_succ_front {α : Type} (f : α → α) (k : Nat) (x : α) :
    Nat.repeat f (k+1) x = Nat.repeat f k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Nat.repeat] using congrArg f ih

theorem shift_even (n : Nat) :
    ExtendedMantissa.shiftRightOne ⟨n * 2, false, false⟩ = ⟨n, false, false⟩ := by
  simp [ExtendedMantissa.shiftRightOne]

theorem shifted_scale (n exponent places : Nat) :
    shifted (n * 2^exponent) (exponent + places) = shifted n places := by
  induction exponent with
  | zero => simp [shifted]
  | succ exponent ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    unfold shifted
    rw [show exponent + 1 + places = (exponent + places) + 1 by omega,
      repeat_succ_front, shift_even]
    exact ih

theorem log2_scaled (n exponent : Nat) (positive : n ≠ 0) :
    (n * 2^exponent).log2 = n.log2 + exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (n * 2^exponent),
      Nat.log2_two_mul (Nat.mul_ne_zero positive (Nat.ne_of_gt (Nat.two_pow_pos _))), ih]
    omega

theorem native_dyadic_target_exponent (n exponent : Nat) :
    Format.binary64.targetExponent (totalExponent n exponent) =
      (n.log2 : Int) + exponent - 52 := by
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
    Format.minExponent]
  omega

theorem native_dyadic_shift (n exponent : Nat) :
    shiftToTargetExponent Format.binary64 n exponent .exact =
      (shifted n (n.log2 - 52), (exponent : Int) + ((n.log2 - 52 : Nat) : Int)) := by
  unfold shiftToTargetExponent
  rw [native_dyadic_target_exponent]
  have gap : ((n.log2 : Int) + exponent - 52 - exponent).toNat = n.log2 - 52 := by omega
  simp only [shiftToExponent, gap]
  rfl

theorem native_scaled_first_shift (n exponent : Nat) (normal : 2^52 ≤ n) :
    shiftToTargetExponent Format.binary64 (n * 2^exponent) 0 .exact =
      shiftToTargetExponent Format.binary64 n exponent .exact := by
  have positive : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 positive).mpr normal
  rw [native_dyadic_shift, native_integer_shift, log2_scaled n exponent positive]
  have difference : n.log2 + exponent - 52 = exponent + (n.log2 - 52) := by omega
  rw [difference, shifted_scale]
  congr 1

theorem native_scaled_roundWithAccuracy (n exponent : Nat) (normal : 2^52 ≤ n) :
    roundWithAccuracy Format.binary64 .positive (n * 2^exponent) 0 .exact =
      roundWithAccuracy Format.binary64 .positive n exponent .exact := by
  unfold roundWithAccuracy
  rw [native_scaled_first_shift n exponent normal]

theorem native_normal_dyadic_round (n exponent : Nat) (normal : 2^52 ≤ n) :
    round Format.binary64 .positive n exponent =
      round Format.binary64 .positive (n * 2^exponent) 0 := by
  have positive : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 positive).mpr normal
  have scaledLarge : 52 ≤ (n * 2^exponent).log2 := by
    rw [log2_scaled n exponent positive]
    omega
  have leftShift : ((exponent : Int) - ((n.log2 : Int) + exponent - 52)).toNat = 0 := by omega
  have rightShift : (0 - (((n * 2^exponent).log2 : Int) - 52)).toNat = 0 := by omega
  unfold round
  rw [native_dyadic_target_exponent, native_integer_target_exponent]
  simp only [decreaseExponent, leftShift, rightShift, Nat.shiftLeft_zero,
    Int.ofNat_zero, Int.sub_zero]
  exact (native_scaled_roundWithAccuracy n exponent normal).symm

theorem scaled_mantissa_normal (mantissa exponent : Nat) (normal : 2^52 ≤ mantissa) :
    2^52 ≤ mantissa * 2^exponent := by
  have positive := Nat.two_pow_pos exponent
  have increasing := Nat.le_mul_of_pos_right mantissa positive
  omega

theorem aligned_value (mantissa exponent common : Nat) (below : common ≤ exponent) :
    mantissa * 2^(exponent-common) * 2^common = mantissa * 2^exponent := by
  rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel below]

theorem native_positive_normalize (mantissa exponent : Nat) (positive : 0 < mantissa) :
    normalize Format.binary64 (mantissa : Int) exponent .positive =
      round Format.binary64 .positive mantissa exponent := by
  have comparison : compare (mantissa : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp [normalize, comparison]

/-- Exact dyadic alignment in the library's addition implementation. All
exponents are nonnegative here, so these operands have integral values. -/
theorem native_positive_add_alignment (m₁ m₂ e₁ e₂ : Nat)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂) :
    UnpackedFloat.add Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      normalize Format.binary64
        ((m₁ * 2^(e₁-min e₁ e₂) + m₂ * 2^(e₂-min e₁ e₂) : Nat) : Int)
        ((min e₁ e₂ : Nat) : Int) .positive := by
  have minimum : min (e₁ : Int) e₂ = ((min e₁ e₂ : Nat) : Int) := by omega
  have gap₁ : ((e₁ : Int) - ((min e₁ e₂ : Nat) : Int)).toNat = e₁-min e₁ e₂ := by omega
  have gap₂ : ((e₂ : Int) - ((min e₁ e₂ : Nat) : Int)).toNat = e₂-min e₁ e₂ := by omega
  simp only [UnpackedFloat.add, decreaseExponent, minimum, gap₁, gap₂, Nat.shiftLeft_eq,
    Sign.apply, Int.natCast_add]

/-- Actual native addition of two positive normal integer-valued operands
rounds their exact integer sum according to the proved nearest-even rule.
Overflow packing is handled by the separate packing bridge. -/
theorem native_positive_add_projection (m₁ m₂ e₁ e₂ : Nat)
    (normal₁ : 2^52 ≤ m₁) (normal₂ : 2^52 ≤ m₂) :
    RepresentsNat
      (UnpackedFloat.add Format.binary64
        (.finite .positive m₁ e₁ (by omega)) (.finite .positive m₂ e₂ (by omega)))
      (roundedInteger (m₁ * 2^e₁ + m₂ * 2^e₂)) := by
  let common := min e₁ e₂
  let aligned := m₁ * 2^(e₁-common) + m₂ * 2^(e₂-common)
  have firstNormal := scaled_mantissa_normal m₁ (e₁-common) normal₁
  have secondNormal := scaled_mantissa_normal m₂ (e₂-common) normal₂
  have normal : 2^52 ≤ aligned := by dsimp only [aligned]; omega
  have large : 2^53 ≤ aligned := by dsimp only [aligned]; omega
  have scaledLarge : 2^53 ≤ aligned * 2^common := by
    have increasing := Nat.le_mul_of_pos_right aligned (Nat.two_pow_pos common)
    omega
  have value : aligned * 2^common = m₁ * 2^e₁ + m₂ * 2^e₂ := by
    dsimp only [aligned]
    rw [Nat.add_mul, aligned_value m₁ e₁ common (Nat.min_le_left _ _),
      aligned_value m₂ e₂ common (Nat.min_le_right _ _)]
  rw [native_positive_add_alignment]
  change RepresentsNat (normalize Format.binary64 (aligned : Int) common .positive) _
  rw [native_positive_normalize aligned common (by omega), native_normal_dyadic_round aligned common normal]
  rw [← value]
  exact native_large_integer_round _ scaledLarge

theorem native_positive_sub_alignment (m₁ m₂ e₁ e₂ : Nat)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂) :
    UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      normalize Format.binary64
        ((m₁ * 2^(e₁-min e₁ e₂) : Nat) - (m₂ * 2^(e₂-min e₁ e₂) : Nat) : Int)
        ((min e₁ e₂ : Nat) : Int) .positive := by
  have minimum : min (e₁ : Int) e₂ = ((min e₁ e₂ : Nat) : Int) := by omega
  have gap₁ : ((e₁ : Int) - ((min e₁ e₂ : Nat) : Int)).toNat = e₁-min e₁ e₂ := by omega
  have gap₂ : ((e₂ : Int) - ((min e₁ e₂ : Nat) : Int)).toNat = e₂-min e₁ e₂ := by omega
  simp only [UnpackedFloat.sub, decreaseExponent, minimum, gap₁, gap₂, Nat.shiftLeft_eq,
    Sign.apply]

/-- Nonnegative subtraction, including cancellation, has the exact aligned
integer difference before rounding. No saturated Nat subtraction is substituted
for a negative native result. -/
theorem native_nonnegative_sub_alignment (m₁ m₂ e₁ e₂ : Nat)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (affordable : m₂ * 2^(e₂-min e₁ e₂) ≤ m₁ * 2^(e₁-min e₁ e₂)) :
    UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      normalize Format.binary64
        ((m₁ * 2^(e₁-min e₁ e₂) - m₂ * 2^(e₂-min e₁ e₂) : Nat) : Int)
        ((min e₁ e₂ : Nat) : Int) .positive := by
  rw [native_positive_sub_alignment, Int.ofNat_sub affordable]

theorem native_positive_sub_projection (m₁ m₂ e₁ e₂ : Nat)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (normalDifference : 2^53 ≤ m₁ * 2^(e₁-min e₁ e₂) - m₂ * 2^(e₂-min e₁ e₂)) :
    RepresentsNat
      (UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂))
      (roundedInteger (m₁ * 2^e₁ - m₂ * 2^e₂)) := by
  let common := min e₁ e₂
  let aligned := m₁ * 2^(e₁-common) - m₂ * 2^(e₂-common)
  have affordable : m₂ * 2^(e₂-common) ≤ m₁ * 2^(e₁-common) := by
    change 2^53 ≤ aligned at normalDifference
    dsimp only [aligned] at normalDifference
    omega
  have large : 2^53 ≤ aligned := normalDifference
  have normal : 2^52 ≤ aligned := by omega
  have scaledLarge : 2^53 ≤ aligned * 2^common := by
    have increasing := Nat.le_mul_of_pos_right aligned (Nat.two_pow_pos common)
    omega
  have value : aligned * 2^common = m₁ * 2^e₁ - m₂ * 2^e₂ := by
    dsimp only [aligned]
    rw [Nat.sub_mul, aligned_value m₁ e₁ common (Nat.min_le_left _ _),
      aligned_value m₂ e₂ common (Nat.min_le_right _ _)]
  rw [native_nonnegative_sub_alignment _ _ _ _ positive₁ positive₂ affordable]
  change RepresentsNat (normalize Format.binary64 (aligned : Int) common .positive) _
  rw [native_positive_normalize aligned common (by omega), native_normal_dyadic_round aligned common normal]
  rw [← value]
  exact native_large_integer_round _ scaledLarge

theorem native_negative_scaled_first_shift (n denominatorExponent : Nat) (normal : 2^52 ≤ n) :
    shiftToTargetExponent Format.binary64 (n * 2^denominatorExponent)
        (-(denominatorExponent : Int)) .exact =
      shiftToTargetExponent Format.binary64 n 0 .exact := by
  have positive : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 positive).mpr normal
  have target : Format.binary64.targetExponent
      (totalExponent (n * 2^denominatorExponent) (-(denominatorExponent : Int))) =
      (n.log2 : Int) - 52 := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, log2_scaled n denominatorExponent positive, Int.natCast_add]
    omega
  have gap : ((n.log2 : Int) - 52 - (-(denominatorExponent : Int))).toNat =
      denominatorExponent + (n.log2 - 52) := by omega
  unfold shiftToTargetExponent
  rw [target, native_integer_target_exponent]
  simp only [shiftToExponent, gap]
  change (shifted (n * 2^denominatorExponent) (denominatorExponent + (n.log2 - 52)),
      -(denominatorExponent : Int) + ((denominatorExponent + (n.log2 - 52) : Nat) : Int)) =
    (shifted n (((n.log2 : Int) - 52 - 0).toNat),
      0 + ((((n.log2 : Int) - 52 - 0).toNat : Nat) : Int))
  rw [shifted_scale]
  have rightGap : ((n.log2 : Int) - 52 - 0).toNat = n.log2 - 52 := by omega
  rw [rightGap]
  congr 1
  omega

/-- A fractional exponent can encode an exact integer. The actual native
normalizer discards these trailing zero bits without changing its result. -/
theorem native_negative_scaled_round (n denominatorExponent : Nat) (normal : 2^52 ≤ n) :
    round Format.binary64 .positive (n * 2^denominatorExponent) (-(denominatorExponent : Int)) =
      round Format.binary64 .positive n 0 := by
  have positive : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 positive).mpr normal
  have target : Format.binary64.targetExponent
      (totalExponent (n * 2^denominatorExponent) (-(denominatorExponent : Int))) =
      (n.log2 : Int) - 52 := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, log2_scaled n denominatorExponent positive, Int.natCast_add]
    omega
  have leftShift : (-(denominatorExponent : Int) - ((n.log2 : Int) - 52)).toNat = 0 := by omega
  have rightShift : (0 - ((n.log2 : Int) - 52)).toNat = 0 := by omega
  unfold round
  rw [target, native_integer_target_exponent]
  simp only [decreaseExponent, leftShift, rightShift, Nat.shiftLeft_zero, Int.ofNat_zero, Int.sub_zero]
  unfold roundWithAccuracy
  rw [native_negative_scaled_first_shift n denominatorExponent normal]

theorem aligned_integer_value (mantissa n : Nat) (exponent common : Int)
    (positive : 0 < mantissa) (aligned : common ≤ exponent) (commonNonpositive : common ≤ 0)
    (represents : RepresentsNat (.finite .positive mantissa exponent positive) n) :
    mantissa * 2^(exponent-common).toNat = n * 2^(-common).toNat := by
  by_cases nonnegative : 0 ≤ exponent
  · have value : mantissa * 2^exponent.toNat = n := by
      simpa only [RepresentsNat, if_pos nonnegative] using represents
    have gap : (exponent-common).toNat = exponent.toNat + (-common).toNat := by omega
    rw [gap, Nat.pow_add, ← Nat.mul_assoc, value]
  · have value : mantissa = n * 2^(-exponent).toNat := by
      simpa only [RepresentsNat, if_neg nonnegative] using represents
    have gap : (-exponent).toNat + (exponent-common).toNat = (-common).toNat := by omega
    rw [value, Nat.mul_assoc, ← Nat.pow_add, gap]

theorem native_positive_add_alignment_int (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂) :
    UnpackedFloat.add Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      normalize Format.binary64
        ((m₁ * 2^(e₁-min e₁ e₂).toNat + m₂ * 2^(e₂-min e₁ e₂).toNat : Nat) : Int)
        (min e₁ e₂) .positive := by
  simp only [UnpackedFloat.add, decreaseExponent, Nat.shiftLeft_eq, Sign.apply,
    Int.natCast_add]

/-- Actual native addition, for exact integer-valued operands whose common
alignment exponent is nonpositive. This includes integer credits such as one,
which are encoded with a negative exponent in canonical binary64 form. -/
theorem native_integer_add_projection_nonpositive (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (commonNonpositive : min e₁ e₂ ≤ 0) (largeSum : 2^53 ≤ n₁+n₂) :
    RepresentsNat
      (UnpackedFloat.add Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂))
      (roundedInteger (n₁+n₂)) := by
  let common := min e₁ e₂
  have first := aligned_integer_value m₁ n₁ e₁ common positive₁ (Int.min_le_left _ _)
    commonNonpositive represents₁
  have second := aligned_integer_value m₂ n₂ e₂ common positive₂ (Int.min_le_right _ _)
    commonNonpositive represents₂
  have exponent : common = -((-common).toNat : Int) := by dsimp only [common]; omega
  have normal : 2^52 ≤ n₁+n₂ := by omega
  have scaledPositive : 0 < (n₁+n₂) * 2^(-common).toNat :=
    Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  rw [native_positive_add_alignment_int, first, second, ← Nat.add_mul]
  change RepresentsNat (normalize Format.binary64
    (((n₁+n₂) * 2^(-common).toNat : Nat) : Int) common .positive) _
  have comparison : compare (((n₁+n₂) * 2^(-common).toNat : Nat) : Int) 0 = .gt :=
    Int.compare_eq_gt.mpr (by omega)
  simp only [normalize, comparison, Int.toNat_natCast]
  have normalized := native_negative_scaled_round (n₁+n₂) (-common).toNat normal
  rw [← exponent] at normalized
  rw [normalized]
  exact native_large_integer_round _ largeSum

/-- The native Add projection for normal positive, integer-valued operands,
without a restriction on the sign of their canonical exponents. -/
theorem native_integer_add_projection (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (normal₁ : 2^52 ≤ m₁) (normal₂ : 2^52 ≤ m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ (by omega)) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ (by omega)) n₂)
    (largeSum : 2^53 ≤ n₁+n₂) :
    RepresentsNat
      (UnpackedFloat.add Format.binary64
        (.finite .positive m₁ e₁ (by omega)) (.finite .positive m₂ e₂ (by omega)))
      (roundedInteger (n₁+n₂)) := by
  by_cases nonpositive : min e₁ e₂ ≤ 0
  · exact native_integer_add_projection_nonpositive m₁ m₂ n₁ n₂ e₁ e₂
      (by omega) (by omega) represents₁ represents₂ nonpositive largeSum
  · have nonnegative₁ : 0 ≤ e₁ := by omega
    have nonnegative₂ : 0 ≤ e₂ := by omega
    have cast₁ : (e₁.toNat : Int) = e₁ := by omega
    have cast₂ : (e₂.toNat : Int) = e₂ := by omega
    have value₁ : m₁ * 2^e₁.toNat = n₁ := by
      simpa only [RepresentsNat, if_pos nonnegative₁] using represents₁
    have value₂ : m₂ * 2^e₂.toNat = n₂ := by
      simpa only [RepresentsNat, if_pos nonnegative₂] using represents₂
    have native := native_positive_add_projection m₁ m₂ e₁.toNat e₂.toNat normal₁ normal₂
    simpa only [cast₁, cast₂, value₁, value₂] using native

theorem normal_target_exact (mantissa : Nat) (exponent : Int)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53) (expLower : -1074 ≤ exponent) :
    Format.binary64.targetExponent (totalExponent mantissa exponent) = exponent := by
  have logarithm : mantissa.log2 = 52 :=
    (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower, upper⟩
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
    Format.minExponent, logarithm]
  omega

theorem native_exact_normal_roundWithAccuracy (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa) (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) :
    roundWithAccuracy Format.binary64 .positive mantissa exponent .exact =
      .finite .positive mantissa exponent positive := by
  have target := normal_target_exact mantissa exponent lower upper expLower
  have shift : shiftToTargetExponent Format.binary64 mantissa exponent .exact =
      (⟨mantissa, false, false⟩, exponent) := by
    simp [shiftToTargetExponent, target, shiftToExponent,
      ExtendedMantissa.ofMantissaAndAccuracy, HShiftRight.hShiftRight, Nat.repeat]
  unfold roundWithAccuracy
  rw [shift]
  change (let pair := shiftToTargetExponent Format.binary64 mantissa exponent .exact
    if h : pair.1.mantissa = 0 then UnpackedFloat.zero .positive
    else UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) = _
  rw [shift]
  simp only [Nat.ne_of_gt positive, ↓reduceDIte]

theorem native_small_dyadic_round (mantissa exponent : Nat)
    (positive : 0 < mantissa) (small : mantissa < 2^52) :
    RepresentsNat (round Format.binary64 .positive mantissa exponent)
      (mantissa * 2^exponent) := by
  have logarithm : mantissa.log2 < 52 := (Nat.log2_lt (by omega)).mpr small
  let places := 52 - mantissa.log2
  let enlarged := mantissa * 2^places
  let finalExponent : Int := (exponent : Int) - places
  have placesBound : places ≤ 52 := by dsimp only [places]; omega
  have enlargedPositive : 0 < enlarged := Nat.mul_pos positive (Nat.two_pow_pos places)
  have enlargedLog : enlarged.log2 = 52 := by
    dsimp only [enlarged]
    rw [log2_scaled mantissa places (by omega)]
    dsimp only [places]
    omega
  have enlargedBounds : 2^52 ≤ enlarged ∧ enlarged < 2^53 :=
    (Nat.log2_eq_iff (by omega : enlarged ≠ 0)).mp enlargedLog
  have shift : ((exponent : Int) - ((mantissa.log2 : Int) + exponent - 52)).toNat = places := by
    dsimp only [places]
    omega
  have finalLower : -1074 ≤ finalExponent := by dsimp only [finalExponent]; omega
  unfold round
  rw [native_dyadic_target_exponent]
  simp only [decreaseExponent, shift, Nat.shiftLeft_eq]
  change RepresentsNat (roundWithAccuracy Format.binary64 .positive enlarged finalExponent .exact) _
  rw [native_exact_normal_roundWithAccuracy enlarged finalExponent enlargedPositive
    enlargedBounds.1 enlargedBounds.2 finalLower]
  change if 0 ≤ finalExponent then enlarged * 2^finalExponent.toNat = mantissa * 2^exponent
    else enlarged = mantissa * 2^exponent * 2^(-finalExponent).toNat
  split
  · rename_i nonnegative
    have gap : places + finalExponent.toNat = exponent := by dsimp only [finalExponent] at *; omega
    dsimp only [enlarged]
    rw [Nat.mul_assoc, ← Nat.pow_add, gap]
  · rename_i negative
    have gap : exponent + (-finalExponent).toNat = places := by dsimp only [finalExponent] at *; omega
    dsimp only [enlarged]
    rw [Nat.mul_assoc, ← Nat.pow_add, gap]

theorem roundMultiple_exact_of_dvd (spacing n : Nat) (positive : 0 < spacing)
    (multiple : spacing ∣ n) : roundMultiple spacing n = n := by
  have remainder : n % spacing = 0 := Nat.mod_eq_zero_of_dvd multiple
  simp only [roundMultiple, remainder, Nat.mul_zero]
  have notBelow : ¬spacing < 0 := by omega
  have notZero : (spacing == 0) = false := by simp; omega
  simp only [notBelow, decide_false, Bool.false_or, notZero,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  exact Nat.div_mul_cancel multiple

theorem scaled_small_integer_exact (mantissa exponent : Nat)
    (positive : 0 < mantissa) (small : mantissa < 2^53) :
    roundedInteger (mantissa * 2^exponent) = mantissa * 2^exponent := by
  have logarithm : mantissa.log2 < 53 := (Nat.log2_lt (by omega)).mpr small
  rw [roundedInteger, integer_spacing_matches_native, log2_scaled mantissa exponent (by omega)]
  have powerBound : mantissa.log2 + exponent - 52 ≤ exponent := by omega
  apply roundMultiple_exact_of_dvd _ _ (Nat.two_pow_pos _)
  exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 powerBound) mantissa

theorem native_integer_dyadic_round (mantissa exponent : Nat) (positive : 0 < mantissa) :
    RepresentsNat (round Format.binary64 .positive mantissa exponent)
      (roundedInteger (mantissa * 2^exponent)) := by
  by_cases normal : 2^52 ≤ mantissa
  · rw [native_normal_dyadic_round mantissa exponent normal]
    exact native_normal_integer_round _ (scaled_mantissa_normal mantissa exponent normal)
  · have small : mantissa < 2^52 := by omega
    rw [scaled_small_integer_exact mantissa exponent positive (by omega)]
    exact native_small_dyadic_round mantissa exponent positive small

/-- Native subtraction for all affordable positive integral-exponent operands,
including complete and near cancellation. -/
theorem native_integer_sub_projection_nonnegative (m₁ m₂ : Nat) (e₁ e₂ : Nat)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (affordable : m₂ * 2^e₂ ≤ m₁ * 2^e₁) :
    RepresentsNat
      (UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂))
      (roundedInteger (m₁ * 2^e₁ - m₂ * 2^e₂)) := by
  let common := min e₁ e₂
  let first := m₁ * 2^(e₁-common)
  let second := m₂ * 2^(e₂-common)
  let difference := first - second
  have firstValue : first * 2^common = m₁ * 2^e₁ :=
    aligned_value m₁ e₁ common (Nat.min_le_left _ _)
  have secondValue : second * 2^common = m₂ * 2^e₂ :=
    aligned_value m₂ e₂ common (Nat.min_le_right _ _)
  have alignedAffordable : second ≤ first := by
    have multiplied : second * 2^common ≤ first * 2^common := by
      simpa only [firstValue, secondValue] using affordable
    exact Nat.le_of_mul_le_mul_right multiplied (Nat.two_pow_pos common)
  have value : difference * 2^common = m₁ * 2^e₁ - m₂ * 2^e₂ := by
    dsimp only [difference]
    rw [Nat.sub_mul, firstValue, secondValue]
  rw [native_nonnegative_sub_alignment _ _ _ _ positive₁ positive₂ alignedAffordable]
  change RepresentsNat (normalize Format.binary64 (difference : Int) common .positive) _
  by_cases zero : difference = 0
  · have zeroValue : m₁ * 2^e₁ - m₂ * 2^e₂ = 0 := by simpa only [zero, Nat.zero_mul] using value.symm
    simp only [zero, zeroValue]
    simp [normalize, RepresentsNat, roundedInteger, integerSpacing, roundMultiple]
  · rw [native_positive_normalize difference common (by omega), ← value]
    exact native_integer_dyadic_round difference common (by omega)

theorem native_small_negative_scaled_round_shape (n denominatorExponent : Nat)
    (positive : 0 < n) (small : n < 2^52) :
    round Format.binary64 .positive (n * 2^denominatorExponent) (-(denominatorExponent : Int)) =
      .finite .positive (n * 2^(52-n.log2)) (-((52-n.log2 : Nat) : Int))
        (Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  have logarithm : n.log2 < 52 := (Nat.log2_lt (by omega)).mpr small
  let places := 52 - n.log2
  let enlarged := n * 2^places
  have placesBound : places ≤ 52 := by dsimp only [places]; omega
  have enlargedPositive : 0 < enlarged := Nat.mul_pos positive (Nat.two_pow_pos places)
  have enlargedLog : enlarged.log2 = 52 := by
    dsimp only [enlarged]
    rw [log2_scaled n places (by omega)]
    dsimp only [places]
    omega
  have enlargedBounds : 2^52 ≤ enlarged ∧ enlarged < 2^53 :=
    (Nat.log2_eq_iff (by omega : enlarged ≠ 0)).mp enlargedLog
  change round Format.binary64 .positive (n * 2^denominatorExponent) (-(denominatorExponent : Int)) =
    .finite .positive enlarged (-(places : Int)) enlargedPositive
  have target : Format.binary64.targetExponent
      (totalExponent (n * 2^denominatorExponent) (-(denominatorExponent : Int))) =
      -(places : Int) := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, log2_scaled n denominatorExponent (by omega), Int.natCast_add]
    dsimp only [places]
    omega
  have exactNormal : roundWithAccuracy Format.binary64 .positive enlarged (-(places : Int)) .exact =
      .finite .positive enlarged (-(places : Int)) enlargedPositive :=
    native_exact_normal_roundWithAccuracy enlarged (-(places : Int)) enlargedPositive
      enlargedBounds.1 enlargedBounds.2 (by omega)
  unfold round
  rw [target]
  by_cases short : denominatorExponent ≤ places
  · have shift : (-(denominatorExponent : Int) - (-(places : Int))).toNat = places-denominatorExponent := by omega
    have shiftedMantissa : (n * 2^denominatorExponent) * 2^(places-denominatorExponent) = enlarged := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le short]
    have shiftedExponent : -(denominatorExponent : Int) - ((places-denominatorExponent : Nat) : Int) =
        -(places : Int) := by omega
    simp only [decreaseExponent, shift, Nat.shiftLeft_eq, shiftedMantissa, shiftedExponent]
    exact exactNormal
  · have shift : (-(denominatorExponent : Int) - (-(places : Int))).toNat = 0 := by omega
    simp only [decreaseExponent, shift, Nat.shiftLeft_zero, Int.ofNat_zero, Int.sub_zero]
    have rightGap : (-(places : Int) - (-(denominatorExponent : Int))).toNat = denominatorExponent-places := by omega
    have mantissaScale : n * 2^denominatorExponent = enlarged * 2^(denominatorExponent-places) := by
      dsimp only [enlarged]
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (by omega : places ≤ denominatorExponent)]
    have exactShift : shifted (n * 2^denominatorExponent) (denominatorExponent-places) =
        ⟨enlarged,false,false⟩ := by
      rw [mantissaScale]
      simpa only [Nat.add_zero, shifted, Nat.repeat] using shifted_scale enlarged (denominatorExponent-places) 0
    have firstShift : shiftToTargetExponent Format.binary64 (n * 2^denominatorExponent)
        (-(denominatorExponent : Int)) .exact = (⟨enlarged,false,false⟩, -(places : Int)) := by
      simp only [shiftToTargetExponent, target, shiftToExponent, rightGap]
      change (shifted (n * 2^denominatorExponent) (denominatorExponent-places),
        -(denominatorExponent : Int) + ((denominatorExponent-places : Nat) : Int)) = _
      rw [exactShift]
      congr 1
      omega
    unfold roundWithAccuracy
    rw [firstShift]
    have normalTarget := normal_target_exact enlarged (-(places : Int)) enlargedBounds.1 enlargedBounds.2 (by omega)
    have secondShift : shiftToTargetExponent Format.binary64 enlarged (-(places : Int)) .exact =
        (⟨enlarged,false,false⟩, -(places : Int)) := by
      simp [shiftToTargetExponent, normalTarget, shiftToExponent,
        ExtendedMantissa.ofMantissaAndAccuracy, HShiftRight.hShiftRight, Nat.repeat]
    change
      (let pair := shiftToTargetExponent Format.binary64 enlarged (-(places : Int)) .exact
       if h : pair.1.mantissa = 0 then UnpackedFloat.zero .positive
       else UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) = _
    rw [secondShift]
    simp only [Nat.ne_of_gt enlargedPositive, ↓reduceDIte]

theorem native_small_negative_scaled_round (n denominatorExponent : Nat)
    (positive : 0 < n) (small : n < 2^52) :
    RepresentsNat (round Format.binary64 .positive (n * 2^denominatorExponent)
      (-(denominatorExponent : Int))) n := by
  rw [native_small_negative_scaled_round_shape n denominatorExponent positive small]
  have logarithm : n.log2 < 52 := (Nat.log2_lt (by omega)).mpr small
  have negative : ¬0 ≤ -((52-n.log2 : Nat) : Int) := by omega
  simp only [RepresentsNat,negative,↓reduceIte,Int.neg_neg,Int.toNat_natCast]

theorem native_negative_scaled_round_is_integer_round (n denominatorExponent : Nat) (positive : 0 < n) :
    round Format.binary64 .positive (n * 2^denominatorExponent) (-(denominatorExponent : Int)) =
      round Format.binary64 .positive n 0 := by
  by_cases normal : 2^52 ≤ n
  · exact native_negative_scaled_round n denominatorExponent normal
  · have small : n < 2^52 := by omega
    have zeroShape := native_small_negative_scaled_round_shape n 0 positive small
    simp only [Nat.pow_zero,Nat.mul_one,Int.ofNat_zero,Int.neg_zero] at zeroShape
    rw [native_small_negative_scaled_round_shape n denominatorExponent positive small,zeroShape]

theorem native_integer_negative_scaled_round (n denominatorExponent : Nat) (positive : 0 < n) :
    RepresentsNat (round Format.binary64 .positive (n * 2^denominatorExponent)
      (-(denominatorExponent : Int))) (roundedInteger n) := by
  by_cases normal : 2^52 ≤ n
  · rw [native_negative_scaled_round n denominatorExponent normal]
    exact native_normal_integer_round n normal
  · have small : n < 2^52 := by omega
    rw [integer_exact_through_cap n (by unfold unitCap; omega)]
    exact native_small_negative_scaled_round n denominatorExponent positive small

theorem native_positive_sub_alignment_int (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂) :
    UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      normalize Format.binary64
        ((m₁ * 2^(e₁-min e₁ e₂).toNat : Nat) - (m₂ * 2^(e₂-min e₁ e₂).toNat : Nat) : Int)
        (min e₁ e₂) .positive := by
  simp only [UnpackedFloat.sub, decreaseExponent, Nat.shiftLeft_eq, Sign.apply]

theorem native_integer_sub_projection_nonpositive (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (commonNonpositive : min e₁ e₂ ≤ 0) (affordable : n₂ ≤ n₁) :
    RepresentsNat
      (UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂))
      (roundedInteger (n₁-n₂)) := by
  let common := min e₁ e₂
  have first := aligned_integer_value m₁ n₁ e₁ common positive₁ (Int.min_le_left _ _)
    commonNonpositive represents₁
  have second := aligned_integer_value m₂ n₂ e₂ common positive₂ (Int.min_le_right _ _)
    commonNonpositive represents₂
  have scaledAffordable : n₂ * 2^(-common).toNat ≤ n₁ * 2^(-common).toNat :=
    Nat.mul_le_mul_right _ affordable
  rw [native_positive_sub_alignment_int, first, second, ← Int.ofNat_sub scaledAffordable, ← Nat.sub_mul]
  change RepresentsNat (normalize Format.binary64
    (((n₁-n₂) * 2^(-common).toNat : Nat) : Int) common .positive) _
  by_cases equal : n₁ = n₂
  · simp [equal, normalize, RepresentsNat, roundedInteger, integerSpacing, roundMultiple]
  · have positive : 0 < n₁-n₂ := by omega
    have scaledPositive := Nat.mul_pos positive (Nat.two_pow_pos (-common).toNat)
    have comparison : compare (((n₁-n₂) * 2^(-common).toNat : Nat) : Int) 0 = .gt :=
      Int.compare_eq_gt.mpr (by omega)
    simp only [normalize, comparison, Int.toNat_natCast]
    have exponent : common = -((-common).toNat : Int) := by dsimp only [common]; omega
    have native := native_integer_negative_scaled_round (n₁-n₂) (-common).toNat positive
    rw [← exponent] at native
    exact native

/-- Actual affordable subtraction of positive exact integers, with arbitrary
canonical exponent signs and all cancellation cases. -/
theorem native_integer_sub_projection (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (affordable : n₂ ≤ n₁) :
    RepresentsNat
      (UnpackedFloat.sub Format.binary64
        (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂))
      (roundedInteger (n₁-n₂)) := by
  by_cases nonpositive : min e₁ e₂ ≤ 0
  · exact native_integer_sub_projection_nonpositive m₁ m₂ n₁ n₂ e₁ e₂
      positive₁ positive₂ represents₁ represents₂ nonpositive affordable
  · have nonnegative₁ : 0 ≤ e₁ := by omega
    have nonnegative₂ : 0 ≤ e₂ := by omega
    have cast₁ : (e₁.toNat : Int) = e₁ := by omega
    have cast₂ : (e₂.toNat : Int) = e₂ := by omega
    have value₁ : m₁ * 2^e₁.toNat = n₁ := by
      simpa only [RepresentsNat, if_pos nonnegative₁] using represents₁
    have value₂ : m₂ * 2^e₂.toNat = n₂ := by
      simpa only [RepresentsNat, if_pos nonnegative₂] using represents₂
    have affordableValues : m₂ * 2^e₂.toNat ≤ m₁ * 2^e₁.toNat := by
      simpa only [value₁,value₂] using affordable
    have native := native_integer_sub_projection_nonnegative m₁ m₂ e₁.toNat e₂.toNat
      positive₁ positive₂ affordableValues
    simpa only [cast₁,cast₂,value₁,value₂] using native

theorem native_integer_add_is_round (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (normal₁ : 2^52 ≤ m₁) (normal₂ : 2^52 ≤ m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ (by omega)) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ (by omega)) n₂)
    (largeSum : 2^52 ≤ n₁+n₂) :
    UnpackedFloat.add Format.binary64
      (.finite .positive m₁ e₁ (by omega)) (.finite .positive m₂ e₂ (by omega)) =
      round Format.binary64 .positive (n₁+n₂) 0 := by
  by_cases nonpositive : min e₁ e₂ ≤ 0
  · let common := min e₁ e₂
    have first := aligned_integer_value m₁ n₁ e₁ common (by omega) (Int.min_le_left _ _)
      nonpositive represents₁
    have second := aligned_integer_value m₂ n₂ e₂ common (by omega) (Int.min_le_right _ _)
      nonpositive represents₂
    have exponent : common = -((-common).toNat : Int) := by dsimp only [common]; omega
    have scaledPositive : 0 < (n₁+n₂) * 2^(-common).toNat :=
      Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    rw [native_positive_add_alignment_int, first, second, ← Nat.add_mul]
    change normalize Format.binary64 (((n₁+n₂) * 2^(-common).toNat : Nat) : Int) common .positive = _
    have comparison : compare (((n₁+n₂) * 2^(-common).toNat : Nat) : Int) 0 = .gt :=
      Int.compare_eq_gt.mpr (by omega)
    simp only [normalize, comparison, Int.toNat_natCast]
    have native := native_negative_scaled_round (n₁+n₂) (-common).toNat largeSum
    rw [← exponent] at native
    exact native
  · have nonnegative₁ : 0 ≤ e₁ := by omega
    have nonnegative₂ : 0 ≤ e₂ := by omega
    have cast₁ : (e₁.toNat : Int) = e₁ := by omega
    have cast₂ : (e₂.toNat : Int) = e₂ := by omega
    have value₁ : m₁ * 2^e₁.toNat = n₁ := by
      simpa only [RepresentsNat, if_pos nonnegative₁] using represents₁
    have value₂ : m₂ * 2^e₂.toNat = n₂ := by
      simpa only [RepresentsNat, if_pos nonnegative₂] using represents₂
    rw [← cast₁, ← cast₂, native_positive_add_alignment]
    let common := min e₁.toNat e₂.toNat
    let aligned := m₁ * 2^(e₁.toNat-common) + m₂ * 2^(e₂.toNat-common)
    have firstNormal := scaled_mantissa_normal m₁ (e₁.toNat-common) normal₁
    have normal : 2^52 ≤ aligned := by dsimp only [aligned]; omega
    have value : aligned * 2^common = n₁+n₂ := by
      dsimp only [aligned]
      rw [Nat.add_mul, aligned_value m₁ e₁.toNat common (Nat.min_le_left _ _),
        aligned_value m₂ e₂.toNat common (Nat.min_le_right _ _), value₁, value₂]
    change normalize Format.binary64 (aligned : Int) common .positive = _
    rw [native_positive_normalize aligned common (by omega), native_normal_dyadic_round aligned common normal, value]

/-- A transfer to the interpreter's actual 64-bit addition. Both operands are
given by their finite normal encodings and exact integral values; the conclusion
describes the result bits, not only a separate rounding recurrence. -/
theorem number_add_integer_projection (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (large : 2^52 ≤ n₁+n₂) (bounded : n₁+n₂ < 2^1023) :
    let bits := Number.add
      (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      Number.magnitudeFraction bits = (roundedInteger (n₁+n₂), 1) := by
  dsimp only
  simp only [Number.add, Float.Model.add,
    normal_model_unpack m₁ e₁ positive₁ lower₁ upper₁ expLower₁ expUpper₁,
    normal_model_unpack m₂ e₂ positive₂ lower₂ upper₂ expLower₂ expUpper₂]
  rw [native_integer_add_is_round m₁ m₂ n₁ n₂ e₁ e₂ lower₁ lower₂ represents₁ represents₂ large]
  exact packed_integer_round_projection (n₁+n₂) large bounded

theorem native_small_dyadic_round_is_integer_round (mantissa exponent : Nat)
    (positive : 0 < mantissa) (small : mantissa < 2^52) :
    round Format.binary64 .positive mantissa exponent =
      round Format.binary64 .positive (mantissa * 2^exponent) 0 := by
  have logarithm : mantissa.log2 < 52 := (Nat.log2_lt (by omega)).mpr small
  let places := 52-mantissa.log2
  let enlarged := mantissa * 2^places
  let finalExponent : Int := (exponent : Int) - places
  have placesBound : places ≤ 52 := by dsimp only [places]; omega
  have enlargedPositive : 0 < enlarged := Nat.mul_pos positive (Nat.two_pow_pos places)
  have enlargedLog : enlarged.log2 = 52 := by
    dsimp only [enlarged]
    rw [log2_scaled mantissa places (by omega)]
    dsimp only [places]
    omega
  have enlargedBounds : 2^52 ≤ enlarged ∧ enlarged < 2^53 :=
    (Nat.log2_eq_iff (by omega : enlarged ≠ 0)).mp enlargedLog
  have targetLeft : Format.binary64.targetExponent (totalExponent mantissa exponent) = finalExponent := by
    rw [native_dyadic_target_exponent]
    dsimp only [finalExponent,places]
    omega
  have targetRight : Format.binary64.targetExponent (totalExponent (mantissa * 2^exponent) 0) = finalExponent := by
    rw [native_integer_target_exponent, log2_scaled mantissa exponent (by omega)]
    dsimp only [finalExponent,places]
    omega
  have leftShift : ((exponent : Int)-finalExponent).toNat = places := by dsimp only [finalExponent]; omega
  have leftReduced : round Format.binary64 .positive mantissa exponent =
      roundWithAccuracy Format.binary64 .positive enlarged finalExponent .exact := by
    unfold round
    rw [targetLeft]
    simp only [decreaseExponent,leftShift,Nat.shiftLeft_eq]
    rfl
  rw [leftReduced]
  unfold round
  rw [targetRight]
  by_cases short : exponent ≤ places
  · have rightShift : (0-finalExponent).toNat = places-exponent := by dsimp only [finalExponent]; omega
    have mantissaEq : (mantissa*2^exponent)*2^(places-exponent) = enlarged := by
      rw [Nat.mul_assoc,← Nat.pow_add,Nat.add_sub_of_le short]
    have exponentEq : (0 : Int)-((places-exponent : Nat) : Int) = finalExponent := by
      dsimp only [finalExponent]; omega
    simp only [decreaseExponent,rightShift,Nat.shiftLeft_eq,mantissaEq,exponentEq]
  · have rightShift : (0-finalExponent).toNat = 0 := by dsimp only [finalExponent]; omega
    simp only [decreaseExponent,rightShift,Nat.shiftLeft_zero,Int.ofNat_zero,Int.sub_zero]
    have nativeGap : (mantissa*2^exponent).log2-52 = exponent-places := by
      rw [log2_scaled mantissa exponent (by omega)]
      dsimp only [places]
      omega
    have mantissaScale : mantissa * 2^exponent = enlarged * 2^(exponent-places) := by
      dsimp only [enlarged]
      rw [Nat.mul_assoc,← Nat.pow_add,Nat.add_sub_of_le (by omega : places ≤ exponent)]
    have exactShift : shifted (mantissa*2^exponent) (exponent-places) = ⟨enlarged,false,false⟩ := by
      rw [mantissaScale]
      simpa only [Nat.add_zero,shifted,Nat.repeat] using shifted_scale enlarged (exponent-places) 0
    have expEq : ((exponent-places : Nat) : Int) = finalExponent := by dsimp only [finalExponent]; omega
    have firstRight : shiftToTargetExponent Format.binary64 (mantissa*2^exponent) 0 .exact =
        (⟨enlarged,false,false⟩,finalExponent) := by
      rw [native_integer_shift,nativeGap,exactShift,expEq]
    have firstLeft : shiftToTargetExponent Format.binary64 enlarged finalExponent .exact =
        (⟨enlarged,false,false⟩,finalExponent) := by
      have lower : -1074 ≤ finalExponent := by dsimp only [finalExponent]; omega
      rw [shiftToTargetExponent,normal_target_exact enlarged finalExponent enlargedBounds.1 enlargedBounds.2 lower]
      simp [shiftToExponent,ExtendedMantissa.ofMantissaAndAccuracy,HShiftRight.hShiftRight,Nat.repeat]
    unfold roundWithAccuracy
    rw [firstLeft,firstRight]

theorem native_dyadic_round_is_integer_round (mantissa exponent : Nat) (positive : 0 < mantissa) :
    round Format.binary64 .positive mantissa exponent =
      round Format.binary64 .positive (mantissa * 2^exponent) 0 := by
  by_cases normal : 2^52 ≤ mantissa
  · exact native_normal_dyadic_round mantissa exponent normal
  · exact native_small_dyadic_round_is_integer_round mantissa exponent positive (by omega)

theorem native_integer_sub_positive_is_round (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (positiveDifference : 0 < n₁-n₂) :
    UnpackedFloat.sub Format.binary64
      (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      round Format.binary64 .positive (n₁-n₂) 0 := by
  have affordable : n₂ ≤ n₁ := by omega
  by_cases nonpositive : min e₁ e₂ ≤ 0
  · let common := min e₁ e₂
    have first := aligned_integer_value m₁ n₁ e₁ common positive₁ (Int.min_le_left _ _)
      nonpositive represents₁
    have second := aligned_integer_value m₂ n₂ e₂ common positive₂ (Int.min_le_right _ _)
      nonpositive represents₂
    have scaledAffordable : n₂ * 2^(-common).toNat ≤ n₁ * 2^(-common).toNat :=
      Nat.mul_le_mul_right _ affordable
    rw [native_positive_sub_alignment_int,first,second,← Int.ofNat_sub scaledAffordable,← Nat.sub_mul]
    change normalize Format.binary64 (((n₁-n₂) * 2^(-common).toNat : Nat) : Int) common .positive = _
    have scaledPositive : 0 < (n₁-n₂) * 2^(-common).toNat :=
      Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    have comparison : compare (((n₁-n₂) * 2^(-common).toNat : Nat) : Int) 0 = .gt :=
      Int.compare_eq_gt.mpr (by omega)
    simp only [normalize,comparison,Int.toNat_natCast]
    have exponent : common = -((-common).toNat : Int) := by dsimp only [common]; omega
    have native := native_negative_scaled_round_is_integer_round (n₁-n₂) (-common).toNat positiveDifference
    rw [← exponent] at native
    exact native
  · have nonnegative₁ : 0 ≤ e₁ := by omega
    have nonnegative₂ : 0 ≤ e₂ := by omega
    have cast₁ : (e₁.toNat : Int) = e₁ := by omega
    have cast₂ : (e₂.toNat : Int) = e₂ := by omega
    have value₁ : m₁ * 2^e₁.toNat = n₁ := by
      simpa only [RepresentsNat,if_pos nonnegative₁] using represents₁
    have value₂ : m₂ * 2^e₂.toNat = n₂ := by
      simpa only [RepresentsNat,if_pos nonnegative₂] using represents₂
    let common := min e₁.toNat e₂.toNat
    let first := m₁ * 2^(e₁.toNat-common)
    let second := m₂ * 2^(e₂.toNat-common)
    let difference := first-second
    have firstValue : first * 2^common = n₁ :=
      (aligned_value m₁ e₁.toNat common (Nat.min_le_left _ _)).trans value₁
    have secondValue : second * 2^common = n₂ :=
      (aligned_value m₂ e₂.toNat common (Nat.min_le_right _ _)).trans value₂
    have alignedAffordable : second ≤ first := by
      apply Nat.le_of_mul_le_mul_right (c := 2^common) _ (Nat.two_pow_pos _)
      simpa only [firstValue,secondValue] using affordable
    have value : difference * 2^common = n₁-n₂ := by
      dsimp only [difference]
      rw [Nat.sub_mul,firstValue,secondValue]
    have differencePositive : 0 < difference := by
      by_cases zero : difference = 0
      · rw [zero,Nat.zero_mul] at value
        omega
      · omega
    rw [← cast₁,← cast₂,native_nonnegative_sub_alignment _ _ _ _ positive₁ positive₂ alignedAffordable]
    change normalize Format.binary64 (difference : Int) common .positive = _
    rw [native_positive_normalize difference common differencePositive,
      native_dyadic_round_is_integer_round difference common differencePositive,value]

theorem represents_zero_unique (value : UnpackedFloat) (represented : RepresentsNat value 0) :
    value = .zero .positive := by
  cases value with
  | infinity sign => cases sign <;> simp only [RepresentsNat] at represented
  | notANumber => simp only [RepresentsNat] at represented
  | zero sign => cases sign <;> simp_all only [RepresentsNat]
  | finite sign mantissa exponent positive =>
    cases sign with
    | negative => simp only [RepresentsNat] at represented
    | positive =>
      by_cases nonnegative : 0 ≤ exponent
      · have value : mantissa * 2^exponent.toNat = 0 := by
          simpa only [RepresentsNat,if_pos nonnegative] using represented
        have positiveValue := Nat.mul_pos positive (Nat.two_pow_pos exponent.toNat)
        omega
      · have value : mantissa = 0 := by
          simpa only [RepresentsNat,if_neg nonnegative,Nat.zero_mul] using represented
        omega

theorem native_integer_sub_is_round (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (affordable : n₂ ≤ n₁) :
    UnpackedFloat.sub Format.binary64
      (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      round Format.binary64 .positive (n₁-n₂) 0 := by
  by_cases positive : 0 < n₁-n₂
  · exact native_integer_sub_positive_is_round m₁ m₂ n₁ n₂ e₁ e₂
      positive₁ positive₂ represents₁ represents₂ positive
  · have zero : n₁-n₂ = 0 := by omega
    have represented := native_integer_sub_projection m₁ m₂ n₁ n₂ e₁ e₂
      positive₁ positive₂ represents₁ represents₂ affordable
    rw [zero] at represented
    have zeroRound : roundedInteger 0 = 0 := by decide +kernel
    rw [zeroRound] at represented
    rw [represents_zero_unique _ represented,zero]
    rfl

theorem number_sub_integer_projection (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (large : 2^52 ≤ n₁-n₂) (bounded : n₁-n₂ < 2^1023) :
    let bits := Number.sub
      (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      Number.magnitudeFraction bits = (roundedInteger (n₁-n₂),1) := by
  dsimp only
  simp only [Number.sub,Float.Model.sub,
    normal_model_unpack m₁ e₁ positive₁ lower₁ upper₁ expLower₁ expUpper₁,
    normal_model_unpack m₂ e₂ positive₂ lower₂ upper₂ expLower₂ expUpper₂]
  rw [native_integer_sub_is_round m₁ m₂ n₁ n₂ e₁ e₂ positive₁ positive₂ represents₁ represents₂ (by omega)]
  exact packed_integer_round_projection (n₁-n₂) large bounded

theorem number_sub_integer_represents (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (affordable : n₂ ≤ n₁) (bounded : n₁-n₂ < 2^1023) :
    RepresentsNatBits
      (Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (roundedInteger (n₁-n₂)) := by
  simp only [Number.sub,Float.Model.sub,
    normal_model_unpack m₁ e₁ positive₁ lower₁ upper₁ expLower₁ expUpper₁,
    normal_model_unpack m₂ e₂ positive₂ lower₂ upper₂ expLower₂ expUpper₂]
  rw [native_integer_sub_is_round m₁ m₂ n₁ n₂ e₁ e₂ positive₁ positive₂ represents₁ represents₂ affordable]
  exact packed_integer_round_represents (n₁-n₂) bounded

end CookieClicker.JavaScript.DyadicArithmeticBridge

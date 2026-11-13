import CookieClicker.JavaScriptScaledArithmeticBridge

/-! Native binary64 addition bounds for the no-upgrade building ladder.
The bank can retain a finer denominator than the current production credit.
These arithmetic bounds do not replace the source production invariant or
establish that the game has reached the represented state.
-/
namespace CookieClicker.JavaScript.BoundedAddition
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.BootstrapArithmetic
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bounded_scaled_round_shape (n D : Nat) (large : 2^52 ≤ n) (bounded : n < 2^(1023+D))
    (scaleBound : D ≤ 1074) :
    ∃ (m : Nat) (e : Int) (positive : 0 < m),
      2^52 ≤ m ∧ m < 2^53 ∧ -(D:Int) ≤ e ∧ e ≤ 971 ∧
      round Format.binary64 .positive n (-(D:Int)) = .finite .positive m e positive ∧
      m*2^(e+D).toNat = roundedInteger n := by
  have nonzero : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have logUpper : n.log2 < 1023+D := (Nat.log2_lt nonzero).mpr bounded
  let places := n.log2-52
  let outputExponent : Int := (places:Int)-D
  let m := (shifted n places).roundedMantissa
  have lower : 2^52 ≤ m := native_rounded_mantissa_lower n large
  have upper : m ≤ 2^53 := native_rounded_mantissa_bound n
  have firstValue : m*2^places = roundedInteger n := by
    simpa only [m,places,roundedInteger,integer_spacing_matches_native] using shifted_rounding n places
  have target : Format.binary64.targetExponent (totalExponent n (-(D:Int))) =
      (n.log2:Int)-D-52 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : (-(D:Int)-((n.log2:Int)-D-52)).toNat = 0 := by omega
  have decrease : decreaseExponent n (-(D:Int)) ((n.log2:Int)-D-52) = (n,-(D:Int)) := by
    unfold decreaseExponent
    rw [gap]
    simp
  have sameRound : round Format.binary64 .positive n (-(D:Int)) =
      roundWithAccuracy Format.binary64 .positive n (-(D:Int)) .exact := by
    unfold round
    rw [target]
    dsimp only
    rw [decrease]
  rw [sameRound]
  unfold roundWithAccuracy
  rw [negative_scaled_shift n D large scaleBound]
  change ∃ (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa),
    2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ -(D:Int) ≤ exponent ∧ exponent ≤ 971 ∧
    (let pair := shiftToTargetExponent Format.binary64 m outputExponent .exact
     if h : pair.1.mantissa = 0 then UnpackedFloat.zero .positive
     else UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) =
      UnpackedFloat.finite .positive mantissa exponent positive ∧
    mantissa*2^(exponent+D).toNat = roundedInteger n
  rw [normal_carry_shift_int m outputExponent lower upper (by dsimp [outputExponent]; omega)]
  by_cases carry : m = 2^53
  · simp only [carry,↓reduceIte]
    refine ⟨2^52,outputExponent+1,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_,?_⟩
    · dsimp [outputExponent]; omega
    · dsimp [outputExponent,places]; omega
    · simp
    · have exponents : (outputExponent+1+D).toNat = places+1 := by dsimp [outputExponent]; omega
      rw [exponents,Nat.pow_succ]
      rw [carry] at firstValue
      omega
  · simp only [carry,↓reduceIte]
    refine ⟨m,outputExponent,by omega,lower,by omega,?_,?_,?_,?_⟩
    · dsimp [outputExponent]; omega
    · dsimp [outputExponent,places]; omega
    · simp [show m ≠ 0 by omega]
    · have exponents : (outputExponent+D).toNat = places := by dsimp [outputExponent]; omega
      rw [exponents]
      exact firstValue

/-- In a bank below 2^31, the loss at one rounding is at most 2^-23.
The displayed inequality is exact integer arithmetic at denominator 2^D. -/
theorem small_bank_rounding_error (n D : Nat) (scaleLower : 23 ≤ D)
    (bounded : n < 2^(31+D)) :
    n ≤ roundedInteger n + 2^(D-23) := by
  have spacing : 0 < integerSpacing n ∧ integerSpacing n ≤ 2^(D-22) := by
    unfold integerSpacing
    split
    · exact ⟨by decide, Nat.one_le_two_pow⟩
    · rename_i notSmall
      have nonzero : n ≠ 0 := by omega
      have logarithm : n.log2 < 31+D := (Nat.log2_lt nonzero).mpr bounded
      exact ⟨Nat.two_pow_pos _, Nat.pow_le_pow_right (by decide) (by omega)⟩
  have error := roundMultiple_lower_error _ n spacing.1
  have halfPower : 2^(D-22)/2 = 2^(D-23) := by
    rw [show D-22 = D-23+1 by omega, Nat.pow_succ, Nat.mul_div_cancel]
    decide
  have half := Nat.div_le_div_right (c := 2) spacing.2
  rw [halfPower] at half
  change n ≤ roundMultiple (integerSpacing n) n + 2^(D-23)
  omega

theorem small_bank_credit_progress (bank credit D gain : Nat)
    (scaleLower : 23 ≤ D) (bounded : bank+credit < 2^(31+D))
    (creditLower : 2^(gain+1) ≤ credit) (gainLarge : D-23 ≤ gain) :
    bank + 2^gain ≤ roundedInteger (bank+credit) := by
  have error := small_bank_rounding_error (bank+credit) D scaleLower bounded
  have margin := Nat.pow_le_pow_right (by decide : 0 < 2) gainLarge
  rw [Nat.pow_succ] at creditLower
  omega

/-- Align both native normal operands before rounding. The bank exponent
can be less than the credit exponent; no shared input scale is required. -/
theorem native_small_bank_progress (m₁ m₂ gain : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (nonpositive : min e₁ e₂ ≤ 0)
    (scaleLower : 23 ≤ denominatorExponent e₁ e₂)
    (bounded : alignedNumerator m₁ m₂ e₁ e₂ < 2^(31+denominatorExponent e₁ e₂))
    (creditLower : 2^(gain+1) ≤ m₂ * 2^(e₂-min e₁ e₂).toNat)
    (gainLarge : denominatorExponent e₁ e₂-23 ≤ gain) :
    let bits := Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    ∃ n, ScaledNormal bits (denominatorExponent e₁ e₂) n ∧
      m₁ * 2^(e₁-min e₁ e₂).toNat + 2^gain ≤ n := by
  let D := denominatorExponent e₁ e₂
  let n := alignedNumerator m₁ m₂ e₁ e₂
  have scaleBound : D ≤ 1074 := by dsimp [D,denominatorExponent]; omega
  have large : 2^52 ≤ n := by
    have term := Nat.mul_le_mul_left m₁ (Nat.one_le_two_pow (n := (e₁-min e₁ e₂).toNat))
    simp only [Nat.mul_one] at term
    dsimp [n,alignedNumerator]
    omega
  have powerBound : 2^(31+D) ≤ 2^(1023+D) := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨m,e,positive,lower,upper,lo,hi,shape,represented⟩ :=
    bounded_scaled_round_shape n D large (Nat.lt_of_lt_of_le bounded powerBound) scaleBound
  dsimp only
  rw [number_add_is_negative_dyadic_round m₁ m₂ e₁ e₂ positive₁ positive₂
    lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂ nonpositive]
  change ∃ k, ScaledNormal (Float.Model.pack (round Format.binary64 .positive n (-(D:Int)))).toBits D k ∧ _
  rw [shape]
  refine ⟨roundedInteger n, ⟨m,e,positive,lower,upper,lo,hi,rfl,represented⟩, ?_⟩
  exact small_bank_credit_progress _ _ D gain scaleLower bounded creditLower gainLarge

theorem small_bank_alignment_bound (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (nonpositive : min e₁ e₂ ≤ 0)
    (bankBound : DyadicLE m₁ e₁ (2^30))
    (creditBound : DyadicLE m₂ e₂ (2^11)) :
    alignedNumerator m₁ m₂ e₁ e₂ < 2^(31+denominatorExponent e₁ e₂) := by
  have bank := aligned_dyadic_upper m₁ (2^30) e₁ (min e₁ e₂)
    (Int.min_le_left _ _) nonpositive bankBound
  have credit := aligned_dyadic_upper m₂ (2^11) e₂ (min e₁ e₂)
    (Int.min_le_right _ _) nonpositive creditBound
  let D := denominatorExponent e₁ e₂
  have smaller : 2^(11+D) < 2^(30+D) := Nat.pow_lt_pow_right (by decide) (by omega)
  have twice : 2^(31+D) = 2^(30+D) * 2 := by
    rw [show 31+D = (30+D)+1 by omega, Nat.pow_succ]
  simp only [← Nat.pow_add] at bank credit
  change _ < 2^(31+D)
  rw [twice]
  dsimp [alignedNumerator,D,denominatorExponent] at *
  omega

/-- A fixed production credit has at least twice the requested gain.
The source bank is bounded independently of its mantissa denominator. -/
theorem native_fixed_credit_progress (m₁ m₂ : Nat) (e₁ e₂ gainExponent : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ -23)
    (bankBound : DyadicLE m₁ e₁ (2^30))
    (creditBound : DyadicLE m₂ e₂ (2^11))
    (gainLower : -22 ≤ gainExponent) (creditScale : e₂ ≤ gainExponent+1)
    (creditLower : 2^(gainExponent+1-e₂).toNat ≤ m₂) :
    let D := denominatorExponent e₁ e₂
    let bits := Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    ∃ n, ScaledNormal bits D n ∧
      m₁ * 2^(e₁-min e₁ e₂).toNat + 2^((D:Int)+gainExponent).toNat ≤ n := by
  let D := denominatorExponent e₁ e₂
  have nonpositive : min e₁ e₂ ≤ 0 := by omega
  have scaleLower : 23 ≤ D := by dsimp [D,denominatorExponent]; omega
  have common : min e₁ e₂ = -(D:Int) := by dsimp [D,denominatorExponent]; omega
  have exponentSum : (gainExponent+1-e₂).toNat + (e₂-min e₁ e₂).toNat =
      ((D:Int)+gainExponent).toNat + 1 := by omega
  have scaledCredit := Nat.mul_le_mul_right (2^(e₂-min e₁ e₂).toNat) creditLower
  rw [← Nat.pow_add, exponentSum] at scaledCredit
  exact native_small_bank_progress m₁ m₂ ((D:Int)+gainExponent).toNat e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂
    (by omega) nonpositive scaleLower
    (small_bank_alignment_bound m₁ m₂ e₁ e₂ nonpositive bankBound creditBound)
    scaledCredit (by omega)

end CookieClicker.JavaScript.BoundedAddition

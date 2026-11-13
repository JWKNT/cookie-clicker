import CookieClicker.JavaScriptRoundingBridge
import CookieClicker.BootstrapArithmetic

/-! Dyadic bounds for fractional credits. A bound on the exact aligned
numerator must be supplied by the source arithmetic. Scaling is not replaced
by a native floating-point oracle.
-/
namespace CookieClicker.JavaScript.FractionalRoundingBridge
open RoundingBridge CookieClicker.FullGame.GodzamokRounding
open CookieClicker.FullGame.BootstrapArithmetic
open Float.Model Float.Model.UnpackedFloat
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

theorem round_near_even_multiple (spacing quotient n : Nat)
    (positive : 0 < spacing) (even : quotient % 2 = 0)
    (lower : quotient*spacing ≤ n) (upper : n ≤ quotient*spacing+spacing/2) :
    roundMultiple spacing n = quotient*spacing := by
  have residualBound : n-quotient*spacing < spacing := by
    have halfSmall : spacing/2 < spacing := Nat.div_lt_self positive (by decide)
    omega
  have decomposition : n = (n-quotient*spacing) + quotient*spacing := by omega
  have division : n/spacing = quotient := by
    rw [decomposition,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt residualBound]
    simp
  have remainder : n%spacing = n-quotient*spacing := by
    calc
      n%spacing = ((n-quotient*spacing)+quotient*spacing)%spacing :=
        congrArg (fun x => x%spacing) decomposition
      _ = n-quotient*spacing := by simp [Nat.add_mod,Nat.mod_eq_of_lt residualBound]
  have noUp : ¬ spacing < 2*(n-quotient*spacing) := by omega
  simp [roundMultiple,division,remainder,even,noUp]

theorem rounded_below_power (n exponent : Nat) (below : n < 2^exponent) :
    roundedInteger n ≤ 2^exponent := by
  have spacing : 0 < integerSpacing n ∧ integerSpacing n ∣ 2^exponent := by
    unfold integerSpacing
    split
    · simp
    · rename_i notSmall
      have nonzero : n ≠ 0 := by omega
      have logarithm : n.log2 < exponent := (Nat.log2_lt nonzero).mpr below
      exact ⟨Nat.two_pow_pos _,Nat.pow_dvd_pow 2 (by omega)⟩
  exact roundMultiple_le_multiple _ _ _ spacing.1 (Nat.le_of_lt below) spacing.2

theorem rounded_near_power (n exponent : Nat) (largeExponent : 53 ≤ exponent)
    (lower : 2^exponent ≤ n) (upper : n ≤ 2^exponent+2^(exponent-53)) :
    roundedInteger n = 2^exponent := by
  have capPositive := Nat.two_pow_pos exponent
  have halfSmaller : 2^(exponent-53) < 2^exponent :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have nextPower : 2^(exponent+1) = 2^exponent*2 := by rw [Nat.pow_succ]
  have nonzero : n ≠ 0 := by omega
  have logarithm : n.log2 = exponent := (Nat.log2_eq_iff nonzero).mpr ⟨lower,by omega⟩
  have big : 2^53 ≤ 2^exponent := Nat.pow_le_pow_right (by decide) largeExponent
  have notSmall : ¬ n < 2^53 := by omega
  have capProduct : 2^52 * 2^(exponent-52) = 2^exponent := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have halfSpacing : 2^(exponent-52)/2 = 2^(exponent-53) := by
    rw [show exponent-52 = (exponent-53)+1 by omega,Nat.pow_succ,Nat.mul_div_cancel]
    decide
  simp only [roundedInteger,integerSpacing,if_neg notSmall,logarithm]
  rw [← capProduct]
  apply round_near_even_multiple _ _ _ (Nat.two_pow_pos _) (by decide +kernel)
  · rw [capProduct]; exact lower
  · rw [capProduct,halfSpacing]; exact upper

/-- A scaled power-of-two barrier also covers fractional inputs after exact
alignment: the numerator need not be divisible by the denominator. -/
theorem rounded_power_barrier (n exponent : Nat) (largeExponent : 53 ≤ exponent)
    (upper : n ≤ 2^exponent+2^(exponent-53)) : roundedInteger n ≤ 2^exponent := by
  by_cases below : n < 2^exponent
  · exact rounded_below_power n exponent below
  · rw [rounded_near_power n exponent largeExponent (by omega) upper]
    exact Nat.le_refl _

theorem negative_dyadic_shift (n denominatorExponent : Nat)
    (large : 2^(52+denominatorExponent) ≤ n) :
    shiftToTargetExponent Format.binary64 n (-(denominatorExponent : Int)) .exact =
      (shifted n (n.log2-52), ((n.log2-52-denominatorExponent : Nat) : Int)) := by
  have nonzero : n ≠ 0 := by have := Nat.two_pow_pos (52+denominatorExponent); omega
  have logLower : 52+denominatorExponent ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have target : Format.binary64.targetExponent (totalExponent n (-(denominatorExponent : Int))) =
      (n.log2 : Int)-denominatorExponent-52 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : ((n.log2 : Int)-denominatorExponent-52-(-(denominatorExponent : Int))).toNat = n.log2-52 := by omega
  have output : -(denominatorExponent : Int) + ((n.log2-52 : Nat) : Int) =
      ((n.log2-52-denominatorExponent : Nat) : Int) := by omega
  unfold shiftToTargetExponent
  rw [target]
  simp only [shiftToExponent,gap,output]
  rfl

theorem negative_dyadic_round_shape (n denominatorExponent : Nat)
    (large : 2^(52+denominatorExponent) ≤ n) (bounded : n < 2^(1023+denominatorExponent)) :
    ∃ (mantissa exponent : Nat) (positive : 0 < mantissa),
      2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ 971 ∧
      round Format.binary64 .positive n (-(denominatorExponent : Int)) =
        .finite .positive mantissa exponent positive ∧
      mantissa*2^exponent*2^denominatorExponent = roundedInteger n := by
  have nonzero : n ≠ 0 := by have := Nat.two_pow_pos (52+denominatorExponent); omega
  have logLower : 52+denominatorExponent ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have logUpper : n.log2 < 1023+denominatorExponent := (Nat.log2_lt nonzero).mpr bounded
  have largeN : 2^52 ≤ n := Nat.le_trans
    (Nat.pow_le_pow_right (by decide) (by omega)) large
  let places := n.log2-52
  let outputExponent := places-denominatorExponent
  let m := (shifted n places).roundedMantissa
  have lower : 2^52 ≤ m := native_rounded_mantissa_lower n largeN
  have upper : m ≤ 2^53 := native_rounded_mantissa_bound n
  have firstValue : m*2^places = roundedInteger n := by
    simpa only [m,places,roundedInteger,integer_spacing_matches_native] using shifted_rounding n places
  have exponentSum : outputExponent+denominatorExponent = places := by
    dsimp [outputExponent,places]; omega
  have target : Format.binary64.targetExponent (totalExponent n (-(denominatorExponent : Int))) =
      (n.log2 : Int)-denominatorExponent-52 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : (-(denominatorExponent : Int)-((n.log2 : Int)-denominatorExponent-52)).toNat = 0 := by omega
  have decrease : decreaseExponent n (-(denominatorExponent : Int))
      ((n.log2 : Int)-denominatorExponent-52) = (n,-(denominatorExponent : Int)) := by
    unfold decreaseExponent
    rw [gap]
    simp
  have sameRound : round Format.binary64 .positive n (-(denominatorExponent : Int)) =
      roundWithAccuracy Format.binary64 .positive n (-(denominatorExponent : Int)) .exact := by
    unfold round
    rw [target]
    dsimp only
    rw [decrease]
  rw [sameRound]
  unfold roundWithAccuracy
  rw [negative_dyadic_shift n denominatorExponent large]
  change ∃ (mantissa exponent : Nat) (positive : 0 < mantissa),
    2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ 971 ∧
    (let pair := shiftToTargetExponent Format.binary64 m outputExponent .exact
     if h : pair.1.mantissa = 0 then UnpackedFloat.zero .positive
     else UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) =
      UnpackedFloat.finite .positive mantissa exponent positive ∧
    mantissa*2^exponent*2^denominatorExponent = roundedInteger n
  rw [native_normal_carry_shift m outputExponent lower upper]
  by_cases carry : m = 2^53
  · simp only [carry,↓reduceIte]
    refine ⟨2^52,outputExponent+1,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_⟩
    · dsimp [outputExponent,places]; omega
    · simp
    · rw [Nat.mul_assoc,← Nat.pow_add]
      have exponents : outputExponent+1+denominatorExponent = places+1 := by omega
      rw [exponents,Nat.pow_succ]
      rw [carry] at firstValue
      omega
  · simp only [carry,↓reduceIte]
    refine ⟨m,outputExponent,by omega,lower,by omega,?_,?_,?_⟩
    · dsimp [outputExponent,places]; omega
    · simp [show m ≠ 0 by omega]
    · rw [Nat.mul_assoc,← Nat.pow_add,exponentSum]
      exact firstValue

theorem packed_fractional_round_projection (n denominatorExponent : Nat)
    (large : 2^(52+denominatorExponent) ≤ n) (bounded : n < 2^(1023+denominatorExponent)) :
    let bits := (Float.Model.pack (round Format.binary64 .positive n (-(denominatorExponent : Int)))).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      ∃ value : Nat, Number.magnitudeFraction bits = (value,1) ∧
        value*2^denominatorExponent = roundedInteger n := by
  obtain ⟨m,e,positive,lower,upper,finite,shape,value⟩ :=
    negative_dyadic_round_shape n denominatorExponent large bounded
  dsimp only
  rw [shape]
  obtain ⟨finiteBits,sign⟩ := normal_pack_finite_nonnegative m e positive lower upper finite
  exact ⟨finiteBits,sign,m*2^e,normal_pack_magnitude m e positive lower upper finite,value⟩

theorem packed_fractional_round_barrier (n denominatorExponent capExponent : Nat)
    (large : 2^(52+denominatorExponent) ≤ n)
    (capLower : 53 ≤ capExponent) (capUpper : capExponent ≤ 1021)
    (bounded : n ≤ 2^(capExponent+denominatorExponent)+2^(capExponent+denominatorExponent-53)) :
    let bits := (Float.Model.pack (round Format.binary64 .positive n (-(denominatorExponent : Int)))).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      ∃ value : Nat, Number.magnitudeFraction bits = (value,1) ∧ value ≤ 2^capExponent := by
  have margin : 2^(capExponent+denominatorExponent-53) ≤ 2^(capExponent+denominatorExponent) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have nextPower : 2^(capExponent+denominatorExponent)+2^(capExponent+denominatorExponent) =
      2^(capExponent+denominatorExponent+1) := by rw [Nat.pow_succ]; omega
  have finitePower : 2^(capExponent+denominatorExponent+1) < 2^(1023+denominatorExponent) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have boundedFinite : n < 2^(1023+denominatorExponent) := by omega
  obtain ⟨finite,sign,value,magnitude,equality⟩ := packed_fractional_round_projection n denominatorExponent large boundedFinite
  have roundedBound := rounded_power_barrier n (capExponent+denominatorExponent) (by omega) bounded
  rw [← equality,Nat.pow_add] at roundedBound
  have valueBound : value ≤ 2^capExponent := Nat.le_of_mul_le_mul_right roundedBound (Nat.two_pow_pos denominatorExponent)
  exact ⟨finite,sign,value,magnitude,valueBound⟩

end CookieClicker.JavaScript.FractionalRoundingBridge

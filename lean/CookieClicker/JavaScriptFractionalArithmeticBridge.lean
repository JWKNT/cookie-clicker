import CookieClicker.JavaScriptDyadicArithmeticBridge
import CookieClicker.JavaScriptFractionalRoundingBridge

/-! Exact dyadic alignment and bounds for actual native addition.
Credits can be fractional; no integrality premise is imposed on either
mantissa/exponent pair. The rounding theorem is supplied separately.
-/
namespace CookieClicker.JavaScript.FractionalArithmeticBridge
open Float.Model Float.Model.UnpackedFloat
open DyadicArithmeticBridge
open RoundingBridge FractionalRoundingBridge
set_option exponentiation.threshold 2048

def DyadicLE (mantissa : Nat) (exponent : Int) (bound : Nat) : Prop :=
  if 0 ≤ exponent then mantissa * 2^exponent.toNat ≤ bound
  else mantissa ≤ bound * 2^(-exponent).toNat

def DyadicGE (mantissa : Nat) (exponent : Int) (bound : Nat) : Prop :=
  if 0 ≤ exponent then bound ≤ mantissa * 2^exponent.toNat
  else bound * 2^(-exponent).toNat ≤ mantissa

theorem aligned_dyadic_upper (mantissa bound : Nat) (exponent common : Int)
    (aligned : common ≤ exponent) (nonpositive : common ≤ 0)
    (bounded : DyadicLE mantissa exponent bound) :
    mantissa * 2^(exponent-common).toNat ≤ bound * 2^(-common).toNat := by
  by_cases nonnegative : 0 ≤ exponent
  · have value : mantissa * 2^exponent.toNat ≤ bound := by
      simpa only [DyadicLE,if_pos nonnegative] using bounded
    have gap : (exponent-common).toNat = exponent.toNat + (-common).toNat := by omega
    rw [gap,Nat.pow_add,← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ value
  · have value : mantissa ≤ bound * 2^(-exponent).toNat := by
      simpa only [DyadicLE,if_neg nonnegative] using bounded
    have gap : (-exponent).toNat + (exponent-common).toNat = (-common).toNat := by omega
    have multiplied := Nat.mul_le_mul_right (2^(exponent-common).toNat) value
    simpa only [Nat.mul_assoc,← Nat.pow_add,gap] using multiplied

theorem aligned_dyadic_lower (mantissa bound : Nat) (exponent common : Int)
    (aligned : common ≤ exponent) (nonpositive : common ≤ 0)
    (bounded : DyadicGE mantissa exponent bound) :
    bound * 2^(-common).toNat ≤ mantissa * 2^(exponent-common).toNat := by
  by_cases nonnegative : 0 ≤ exponent
  · have value : bound ≤ mantissa * 2^exponent.toNat := by
      simpa only [DyadicGE,if_pos nonnegative] using bounded
    have gap : (exponent-common).toNat = exponent.toNat + (-common).toNat := by omega
    rw [gap,Nat.pow_add,← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ value
  · have value : bound * 2^(-exponent).toNat ≤ mantissa := by
      simpa only [DyadicGE,if_neg nonnegative] using bounded
    have gap : (-exponent).toNat + (exponent-common).toNat = (-common).toNat := by omega
    have multiplied := Nat.mul_le_mul_right (2^(exponent-common).toNat) value
    simpa only [Nat.mul_assoc,← Nat.pow_add,gap] using multiplied

def alignedNumerator (m₁ m₂ : Nat) (e₁ e₂ : Int) : Nat :=
  m₁ * 2^(e₁-min e₁ e₂).toNat + m₂ * 2^(e₂-min e₁ e₂).toNat

def denominatorExponent (e₁ e₂ : Int) : Nat := (-min e₁ e₂).toNat

theorem actual_add_negative_dyadic (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂) (nonpositive : min e₁ e₂ ≤ 0) :
    UnpackedFloat.add Format.binary64
      (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      round Format.binary64 .positive (alignedNumerator m₁ m₂ e₁ e₂)
        (-(denominatorExponent e₁ e₂ : Int)) := by
  have positive : 0 < alignedNumerator m₁ m₂ e₁ e₂ := by
    have first := Nat.mul_pos positive₁ (Nat.two_pow_pos (e₁-min e₁ e₂).toNat)
    dsimp only [alignedNumerator]
    omega
  have comparison : compare (alignedNumerator m₁ m₂ e₁ e₂ : Int) 0 = .gt :=
    Int.compare_eq_gt.mpr (by omega)
  have exponent : min e₁ e₂ = -(denominatorExponent e₁ e₂ : Int) := by
    dsimp only [denominatorExponent]
    omega
  rw [native_positive_add_alignment_int]
  change normalize Format.binary64 (alignedNumerator m₁ m₂ e₁ e₂ : Int) (min e₁ e₂) .positive = _
  simp only [normalize,comparison,Int.toNat_natCast,exponent]

theorem actual_add_scaled_bounds (m₁ m₂ bankExponent creditExponent : Nat) (e₁ e₂ : Int)
    (nonpositive : min e₁ e₂ ≤ 0)
    (bankBound : DyadicLE m₁ e₁ (2^bankExponent))
    (creditBound : DyadicLE m₂ e₂ (2^creditExponent))
    (bankLarge : DyadicGE m₁ e₁ (2^52)) :
    2^(52+denominatorExponent e₁ e₂) ≤ alignedNumerator m₁ m₂ e₁ e₂ ∧
    alignedNumerator m₁ m₂ e₁ e₂ ≤
      2^(bankExponent+denominatorExponent e₁ e₂) +
      2^(creditExponent+denominatorExponent e₁ e₂) := by
  have first := aligned_dyadic_upper m₁ (2^bankExponent) e₁ (min e₁ e₂)
    (Int.min_le_left _ _) nonpositive bankBound
  have second := aligned_dyadic_upper m₂ (2^creditExponent) e₂ (min e₁ e₂)
    (Int.min_le_right _ _) nonpositive creditBound
  have lower := aligned_dyadic_lower m₁ (2^52) e₁ (min e₁ e₂)
    (Int.min_le_left _ _) nonpositive bankLarge
  simp only [← Nat.pow_add] at first second lower
  dsimp only [alignedNumerator,denominatorExponent]
  omega

theorem number_add_is_negative_dyadic_round (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (nonpositive : min e₁ e₂ ≤ 0) :
    Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits =
      (Float.Model.pack (round Format.binary64 .positive (alignedNumerator m₁ m₂ e₁ e₂)
        (-(denominatorExponent e₁ e₂ : Int)))).toBits := by
  simp only [Number.add,Float.Model.add,
    normal_model_unpack m₁ e₁ positive₁ lower₁ upper₁ expLower₁ expUpper₁,
    normal_model_unpack m₂ e₂ positive₂ lower₂ upper₂ expLower₂ expUpper₂]
  rw [actual_add_negative_dyadic m₁ m₂ e₁ e₂ positive₁ positive₂ nonpositive]

theorem aligned_numerator_near_cap (m₁ m₂ bankExponent creditExponent : Nat) (e₁ e₂ : Int)
    (nonpositive : min e₁ e₂ ≤ 0)
    (bankBound : DyadicLE m₁ e₁ (2^bankExponent))
    (creditBound : DyadicLE m₂ e₂ (2^creditExponent))
    (bankLarge : DyadicGE m₁ e₁ (2^52))
    (creditSmall : creditExponent+53 ≤ bankExponent) :
    2^(52+denominatorExponent e₁ e₂) ≤ alignedNumerator m₁ m₂ e₁ e₂ ∧
    alignedNumerator m₁ m₂ e₁ e₂ ≤
      2^(bankExponent+denominatorExponent e₁ e₂) +
      2^(bankExponent+denominatorExponent e₁ e₂-53) := by
  obtain ⟨lower,upper⟩ := actual_add_scaled_bounds m₁ m₂ bankExponent creditExponent e₁ e₂
    nonpositive bankBound creditBound bankLarge
  have expBound : creditExponent+denominatorExponent e₁ e₂ ≤
      bankExponent+denominatorExponent e₁ e₂-53 := by omega
  have powerBound := Nat.pow_le_pow_right (by decide : 0 < 2) expBound
  exact ⟨lower,Nat.le_trans upper (Nat.add_le_add_left powerBound _)⟩

/-- Actual binary64 addition preserves a power-of-two barrier even when the
credit is fractional. The bank is at least2^52; its native result is integral. -/
theorem number_add_fractional_barrier (m₁ m₂ bankExponent creditExponent : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (nonpositive : min e₁ e₂ ≤ 0)
    (bankBound : DyadicLE m₁ e₁ (2^bankExponent))
    (creditBound : DyadicLE m₂ e₂ (2^creditExponent))
    (bankLarge : DyadicGE m₁ e₁ (2^52))
    (creditSmall : creditExponent+53 ≤ bankExponent) (capUpper : bankExponent ≤ 1021) :
    let bits := Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      ∃ value : Nat, Number.magnitudeFraction bits = (value,1) ∧ value ≤ 2^bankExponent := by
  obtain ⟨large,bounded⟩ := aligned_numerator_near_cap m₁ m₂ bankExponent creditExponent e₁ e₂
    nonpositive bankBound creditBound bankLarge creditSmall
  dsimp only
  rw [number_add_is_negative_dyadic_round m₁ m₂ e₁ e₂ positive₁ positive₂
    lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂ nonpositive]
  exact packed_fractional_round_barrier (alignedNumerator m₁ m₂ e₁ e₂)
    (denominatorExponent e₁ e₂) bankExponent large (by omega) capUpper bounded

theorem number_add_dyadic_barrier (m₁ m₂ bankExponent creditExponent : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (bankBound : DyadicLE m₁ e₁ (2^bankExponent))
    (creditBound : DyadicLE m₂ e₂ (2^creditExponent))
    (bankLarge : DyadicGE m₁ e₁ (2^52))
    (creditSmall : creditExponent+53 ≤ bankExponent) (capUpper : bankExponent ≤ 1021) :
    let bits := Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      ∃ value : Nat, Number.magnitudeFraction bits = (value,1) ∧ value ≤ 2^bankExponent := by
  by_cases nonpositive : min e₁ e₂ ≤ 0
  · exact number_add_fractional_barrier m₁ m₂ bankExponent creditExponent e₁ e₂
      positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
      nonpositive bankBound creditBound bankLarge creditSmall capUpper
  · have nonnegative₁ : 0 ≤ e₁ := by omega
    have nonnegative₂ : 0 ≤ e₂ := by omega
    let n₁ := m₁ * 2^e₁.toNat
    let n₂ := m₂ * 2^e₂.toNat
    have bound₁ : n₁ ≤ 2^bankExponent := by simpa only [DyadicLE,if_pos nonnegative₁] using bankBound
    have bound₂ : n₂ ≤ 2^creditExponent := by simpa only [DyadicLE,if_pos nonnegative₂] using creditBound
    have largeBank : 2^52 ≤ n₁ := by simpa only [DyadicGE,if_pos nonnegative₁] using bankLarge
    have represented₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁ := by
      simp only [RepresentsNat,if_pos nonnegative₁]; rfl
    have represented₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂ := by
      simp only [RepresentsNat,if_pos nonnegative₂]; rfl
    have powerBound : 2^creditExponent ≤ 2^(bankExponent-53) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have near : n₁+n₂ ≤ 2^bankExponent+2^(bankExponent-53) := by omega
    have smaller : 2^(bankExponent-53) ≤ 2^bankExponent :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have next : 2^bankExponent+2^bankExponent = 2^(bankExponent+1) := by rw [Nat.pow_succ]; omega
    have final : 2^(bankExponent+1) < 2^1023 := Nat.pow_lt_pow_right (by decide) (by omega)
    have bounded : n₁+n₂ < 2^1023 := by omega
    obtain ⟨finite,sign,magnitude⟩ := number_add_integer_projection m₁ m₂ n₁ n₂ e₁ e₂
      positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
      represented₁ represented₂ (by omega) bounded
    exact ⟨finite,sign,_,magnitude,rounded_power_barrier (n₁+n₂) bankExponent (by omega) near⟩

theorem zero_model_unpack : (Number.model Number.positiveZero).unpack = .zero .positive := by
  rfl

theorem number_add_zero_right (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    Number.add (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits Number.positiveZero =
      (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits := by
  simp only [Number.add,Float.Model.add,
    normal_model_unpack mantissa exponent positive lower upper expLower expUpper,zero_model_unpack]
  rfl

theorem number_add_zero_left (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    Number.add Number.positiveZero (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits =
      (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits := by
  simp only [Number.add,Float.Model.add,
    normal_model_unpack mantissa exponent positive lower upper expLower expUpper,zero_model_unpack]
  rfl

theorem number_sub_zero_right (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    Number.sub (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits Number.positiveZero =
      (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits := by
  simp only [Number.sub,Float.Model.sub,
    normal_model_unpack mantissa exponent positive lower upper expLower expUpper,zero_model_unpack]
  rfl

end CookieClicker.JavaScript.FractionalArithmeticBridge

import CookieClicker.JavaScriptBoundedAddition

/-! Normal-or-zero closure for affordable native purchases.
The common input exponent is bounded away from subnormal underflow. The
source route must establish affordability and the bank and price bounds.
-/
namespace CookieClicker.JavaScript.BoundedSubtraction
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge BoundedAddition
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem small_scaled_round_shape (n D : Nat) (positive : 0 < n)
    (small : n < 2^52) (scaleBound : D ≤ 1022) :
    ∃ (m : Nat) (e : Int) (mp : 0 < m),
      2^52 ≤ m ∧ m < 2^53 ∧ -((D+52:Nat):Int) ≤ e ∧ e ≤ 971 ∧
      round Format.binary64 .positive n (-(D:Int)) = .finite .positive m e mp ∧
      m * 2^(e+(D+52:Nat)).toNat = n * 2^52 := by
  have logarithm : n.log2 < 52 := (Nat.log2_lt (by omega)).mpr small
  let places := 52-n.log2
  let m := n*2^places
  let e : Int := -(D:Int)-(places:Int)
  have placesBound : places ≤ 52 := by dsimp [places]; omega
  obtain ⟨lower,upper⟩ := Random.significand_bounds positive (by omega : n < 2^53)
  change 2^52 ≤ m at lower
  change m < 2^53 at upper
  have mp : 0 < m := by omega
  have expLower : -1074 ≤ e := by dsimp [e]; omega
  have target : Format.binary64.targetExponent (totalExponent n (-(D:Int))) = e := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    dsimp [e,places]
    omega
  have gap : (-(D:Int)-e).toNat = places := by dsimp [e]; omega
  have shiftedExp : -(D:Int)-(places:Int) = e := rfl
  have exactRound := native_exact_normal_roundWithAccuracy m e mp lower upper expLower
  refine ⟨m,e,mp,lower,upper,?_,?_,?_,?_⟩
  · dsimp [e]; omega
  · dsimp [e]; omega
  · unfold round
    rw [target]
    simp only [decreaseExponent,gap,Nat.shiftLeft_eq,shiftedExp]
    exact exactRound
  · have exponent : (e+(D+52:Nat)).toNat = 52-places := by dsimp [e]; omega
    rw [exponent]
    dsimp only [m]
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le placesBound]

theorem positive_scaled_round_value (n D : Nat) (positive : 0 < n)
    (scaleBound : D ≤ 1022) (bounded : n < 2^(1023+D)) :
    ScaledNormal (Float.Model.pack (round Format.binary64 .positive n (-(D:Int)))).toBits
      (D+52) (roundedInteger n * 2^52) := by
  by_cases large : 2^52 ≤ n
  · obtain ⟨m,e,mp,lower,upper,lo,hi,shape,represented⟩ :=
      bounded_scaled_round_shape n D large bounded (by omega)
    rw [shape]
    refine ⟨m,e,mp,lower,upper,by omega,hi,rfl,?_⟩
    have exponent : (e+(D+52:Nat)).toNat = (e+D).toNat+52 := by omega
    rw [exponent,Nat.pow_add,← Nat.mul_assoc,represented]
  · obtain ⟨m,e,mp,lower,upper,lo,hi,shape,represented⟩ :=
      small_scaled_round_shape n D positive (by omega) scaleBound
    have exactInteger : roundedInteger n = n := by
      simp [roundedInteger,integerSpacing,show n < 2^53 by omega,unit_spacing_exact]
    rw [shape,exactInteger]
    exact ⟨m,e,mp,lower,upper,lo,hi,rfl,represented⟩

/-- The native subtraction uses signed integer alignment, including exact
cancellation. A positive residual is a normal binary64 value. -/
theorem native_affordable_sub_value (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (commonLower : -1022 ≤ min e₁ e₂) (commonUpper : min e₁ e₂ ≤ 0)
    (affordable : m₂ * 2^(e₂-min e₁ e₂).toNat ≤ m₁ * 2^(e₁-min e₁ e₂).toNat)
    (bounded : m₁ * 2^(e₁-min e₁ e₂).toNat < 2^(1023+denominatorExponent e₁ e₂)) :
    let D := denominatorExponent e₁ e₂
    let difference := m₁ * 2^(e₁-min e₁ e₂).toNat - m₂ * 2^(e₂-min e₁ e₂).toNat
    ScaledValue (Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (D+52) (roundedInteger difference * 2^52) := by
  let D := denominatorExponent e₁ e₂
  let difference := m₁ * 2^(e₁-min e₁ e₂).toNat - m₂ * 2^(e₂-min e₁ e₂).toNat
  have scaleBound : D ≤ 1022 := by dsimp [D,denominatorExponent]; omega
  have common : min e₁ e₂ = -(D:Int) := by dsimp [D,denominatorExponent]; omega
  simp only [Number.sub,Float.Model.sub,
    normal_model_unpack m₁ e₁ positive₁ lower₁ upper₁ expLower₁ expUpper₁,
    normal_model_unpack m₂ e₂ positive₂ lower₂ upper₂ expLower₂ expUpper₂]
  rw [native_positive_sub_alignment_int, ← Int.ofNat_sub affordable]
  change ScaledValue (Float.Model.pack
    (normalize Format.binary64 (difference:Int) (min e₁ e₂) .positive)).toBits
    (D+52) (roundedInteger difference * 2^52)
  rw [common]
  by_cases zero : difference = 0
  · left
    simp [zero,normalize,roundedInteger,integerSpacing,roundMultiple,Number.positiveZero]
    rfl
  · right
    have positive : 0 < difference := by omega
    have comparison : compare (difference:Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
    simp only [normalize,comparison,Int.toNat_natCast]
    apply positive_scaled_round_value difference D positive scaleBound
    dsimp [difference,D]
    omega

theorem bank_at_least_64_exponent (m : Nat) (e : Int)
    (mantissaBound : m < 2^53) (valueLower : DyadicGE m e 64) : -46 ≤ e := by
  by_cases notSmall : -46 ≤ e
  · exact notSmall
  have negative : ¬ 0 ≤ e := by omega
  have value : 64 * 2^(-e).toNat ≤ m := by
    simpa only [DyadicGE,if_neg negative] using valueLower
  have exponent : 47 ≤ (-e).toNat := by omega
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) exponent
  have scaled := Nat.mul_le_mul_left 64 power
  omega

/-- The seven prices after the initial Cursor are at least64. This lower
bound keeps the exact residual away from subnormal underflow, including when
the bank and price are almost equal. -/
theorem native_bounded_purchase_value (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expUpper₁ : e₁ ≤ 971) (expUpper₂ : e₂ ≤ 0)
    (bankLower : DyadicGE m₁ e₁ 64) (priceLower : DyadicGE m₂ e₂ 64)
    (bankUpper : DyadicLE m₁ e₁ (2^30))
    (affordable : m₂ * 2^(e₂-min e₁ e₂).toNat ≤ m₁ * 2^(e₁-min e₁ e₂).toNat) :
    let D := denominatorExponent e₁ e₂
    let difference := m₁ * 2^(e₁-min e₁ e₂).toNat - m₂ * 2^(e₂-min e₁ e₂).toNat
    D ≤ 46 ∧ ScaledValue
      (Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (D+52) (roundedInteger difference * 2^52) := by
  have lo₁ := bank_at_least_64_exponent m₁ e₁ upper₁ bankLower
  have lo₂ := bank_at_least_64_exponent m₂ e₂ upper₂ priceLower
  have nonpositive : min e₁ e₂ ≤ 0 := by omega
  have bound := aligned_dyadic_upper m₁ (2^30) e₁ (min e₁ e₂)
    (Int.min_le_left _ _) nonpositive bankUpper
  simp only [← Nat.pow_add] at bound
  have powBound : 2^(30+denominatorExponent e₁ e₂) < 2^(1023+denominatorExponent e₁ e₂) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨by dsimp [denominatorExponent]; omega, ?_⟩
  exact native_affordable_sub_value m₁ m₂ e₁ e₂ positive₁ positive₂ lower₁ upper₁
    lower₂ upper₂ (by omega) expUpper₁ (by omega) (by omega) (by omega)
    nonpositive affordable (Nat.lt_of_le_of_lt bound powBound)

end CookieClicker.JavaScript.BoundedSubtraction

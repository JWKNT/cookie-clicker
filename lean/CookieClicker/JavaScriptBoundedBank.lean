import CookieClicker.JavaScriptBoundedSubtraction

/-! Native first-hit and purchase bounds for the no-upgrade ladder. -/
namespace CookieClicker.JavaScript.BoundedBank
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge BoundedAddition BoundedSubtraction
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem rounded_le_power (n E : Nat) (bounded : n ≤ 2^E) : roundedInteger n ≤ 2^E := by
  by_cases large : 53 ≤ E
  · exact FractionalRoundingBridge.rounded_power_barrier n E large
      (Nat.le_trans bounded (Nat.le_add_right _ _))
  · have power : 2^E < 2^53 := Nat.pow_lt_pow_right (by decide) (by omega)
    have small : n < 2^53 := by omega
    simpa [roundedInteger,integerSpacing,small,unit_spacing_exact] using bounded

theorem scaled_fraction_bound (bits : UInt64) (D n B : Nat) (scale : D ≤ 1074)
    (value : ScaledNormal bits D n) (bounded : n ≤ B*2^D) :
    (Number.magnitudeFraction bits).1 ≤ B*(Number.magnitudeFraction bits).2 := by
  have cross := (normal_scaled_cross_product bits D n scale value).2.2
  have bound := Nat.mul_le_mul_right (Number.magnitudeFraction bits).2 bounded
  rw [← cross] at bound
  have rearrange : B*2^D*(Number.magnitudeFraction bits).2 =
      (B*(Number.magnitudeFraction bits).2)*2^D := by ac_rfl
  rw [rearrange] at bound
  exact Nat.le_of_mul_le_mul_right bound (Nat.two_pow_pos D)

theorem scaled_value_fraction_bound (bits : UInt64) (D n B : Nat) (scale : D ≤ 1074)
    (value : ScaledValue bits D n) (bounded : n ≤ B*2^D) :
    (Number.magnitudeFraction bits).1 ≤ B*(Number.magnitudeFraction bits).2 := by
  rcases value with ⟨rfl,_⟩ | normal
  · change 0 ≤ B * 2^1074
    omega
  · exact scaled_fraction_bound bits D n B scale normal bounded

theorem native_add_billion_bound (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 0)
    (bankBound : DyadicLE m₁ e₁ 1000000000)
    (creditBound : DyadicLE m₂ e₂ (2^11)) :
    let bits := Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    (Number.magnitudeFraction bits).1 ≤ 2^30*(Number.magnitudeFraction bits).2 := by
  let D := denominatorExponent e₁ e₂
  let n := alignedNumerator m₁ m₂ e₁ e₂
  have nonpositive : min e₁ e₂ ≤ 0 := by omega
  have scale : D ≤ 1074 := by dsimp [D,denominatorExponent]; omega
  have bank := aligned_dyadic_upper m₁ 1000000000 e₁ (min e₁ e₂)
    (Int.min_le_left _ _) nonpositive bankBound
  have credit := aligned_dyadic_upper m₂ (2^11) e₂ (min e₁ e₂)
    (Int.min_le_right _ _) nonpositive creditBound
  have margin : 1000000000+2^11 < 2^30 := by decide +kernel
  have multiplied := Nat.mul_lt_mul_of_pos_right margin (Nat.two_pow_pos D)
  have bounded : n < 2^(30+D) := by
    rw [Nat.pow_add]
    dsimp [n,alignedNumerator,D,denominatorExponent] at *
    omega
  have large : 2^52 ≤ n := by
    have term := Nat.mul_le_mul_left m₁ (Nat.one_le_two_pow (n := (e₁-min e₁ e₂).toNat))
    simp only [Nat.mul_one] at term
    dsimp [n,alignedNumerator]
    omega
  have powers : 2^(30+D) ≤ 2^(1023+D) := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨m,e,positive,lower,upper,lo,hi,shape,represented⟩ :=
    bounded_scaled_round_shape n D large (Nat.lt_of_lt_of_le bounded powers) scale
  have value : ScaledNormal
      (Float.Model.pack (round Format.binary64 .positive n (-(D:Int)))).toBits D (roundedInteger n) := by
    rw [shape]
    exact ⟨m,e,positive,lower,upper,lo,hi,rfl,represented⟩
  dsimp only
  rw [number_add_is_negative_dyadic_round m₁ m₂ e₁ e₂ positive₁ positive₂
    lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ (by omega) nonpositive]
  apply scaled_fraction_bound _ D (roundedInteger n) (2^30) scale value
  rw [← Nat.pow_add]
  exact rounded_le_power n (30+D) (Nat.le_of_lt bounded)

theorem native_sub_bank_bound (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expUpper₁ : e₁ ≤ 971) (expUpper₂ : e₂ ≤ 0)
    (bankLower : DyadicGE m₁ e₁ 64) (priceLower : DyadicGE m₂ e₂ 64)
    (bankUpper : DyadicLE m₁ e₁ (2^30))
    (affordable : m₂ * 2^(e₂-min e₁ e₂).toNat ≤ m₁ * 2^(e₁-min e₁ e₂).toNat) :
    let bits := Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits
    (Number.magnitudeFraction bits).1 ≤ 2^30*(Number.magnitudeFraction bits).2 := by
  let D := denominatorExponent e₁ e₂
  let difference := m₁ * 2^(e₁-min e₁ e₂).toNat - m₂ * 2^(e₂-min e₁ e₂).toNat
  obtain ⟨scale,value⟩ := native_bounded_purchase_value m₁ m₂ e₁ e₂ positive₁ positive₂
    lower₁ upper₁ lower₂ upper₂ expUpper₁ expUpper₂ bankLower priceLower bankUpper affordable
  have nonpositive : min e₁ e₂ ≤ 0 := by omega
  have bank := aligned_dyadic_upper m₁ (2^30) e₁ (min e₁ e₂)
    (Int.min_le_left _ _) nonpositive bankUpper
  have bounded : difference ≤ 2^(30+D) := by
    rw [Nat.pow_add]
    dsimp [difference,D,denominatorExponent] at *
    omega
  have rounded := rounded_le_power difference (30+D) bounded
  have multiplied := Nat.mul_le_mul_right (2^52) rounded
  have power : 2^(30+D)*2^52 = 2^30*2^(D+52) := by simp only [Nat.pow_add,Nat.mul_assoc]
  rw [power] at multiplied
  exact scaled_value_fraction_bound _ (D+52) (roundedInteger difference*2^52) (2^30)
    (by change D ≤ 46 at scale; omega) value multiplied

end CookieClicker.JavaScript.BoundedBank

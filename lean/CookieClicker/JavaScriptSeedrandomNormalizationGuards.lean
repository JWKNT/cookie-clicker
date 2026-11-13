import CookieClicker.JavaScriptSeedrandomNormalizationArithmetic

/-! The native growth and halving guards on canonical positive normal values. -/
namespace CookieClicker.JavaScript.SeedrandomNormalizationGuards
open Float.Model Float.Model.UnpackedFloat RoundingBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

theorem threshold52_unpack : (Number.model (Number.ofNat (2^52))).unpack =
    .finite .positive (2^52) 0 (by decide) := rfl

theorem threshold53_unpack : (Number.model (Number.ofNat (2^53))).unpack =
    .finite .positive (2^52) 1 (by decide) := rfl

theorem normal_growth_guard (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    Number.lessThan (Float.Model.pack (.finite .positive m e positive)).toBits
      (Number.ofNat (2^52)) = decide (e<0) := by
  simp only [Number.lessThan,Float.Model.lt,
    normal_model_unpack m e positive lower upper expLower expUpper,threshold52_unpack,
    UnpackedFloat.lt,UnpackedFloat.compare]
  by_cases less : e<0
  · rw [Int.compare_eq_lt.mpr less]
    simp [less]
  · by_cases same : e=0
    · subst e
      by_cases sameM : m=2^52
      · subst m; simp
      · rw [Nat.compare_eq_gt.mpr (show 2^52<m by omega)]
        rfl
    · rw [Int.compare_eq_gt.mpr (show 0<e by omega)]
      simp [less]

theorem normal_shrink_guard (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    Number.lessEqual (Number.ofNat (2^53))
      (Float.Model.pack (.finite .positive m e positive)).toBits = decide (1≤e) := by
  simp only [Number.lessEqual,Float.Model.le,
    normal_model_unpack m e positive lower upper expLower expUpper,threshold53_unpack,
    UnpackedFloat.le,UnpackedFloat.compare]
  by_cases less : e<1
  · rw [Int.compare_eq_gt.mpr less]
    simp [show ¬1≤e by omega]
  · by_cases same : e=1
    · subst e
      by_cases sameM : m=2^52
      · subst m; simp
      · rw [Nat.compare_eq_lt.mpr (show 2^52<m by omega)]
        rfl
    · rw [Int.compare_eq_lt.mpr (show 1<e by omega)]
      simp [show 1≤e by omega]

theorem zero_growth_guard : Number.lessThan Number.positiveZero (Number.ofNat (2^52)) = true := by
  decide +kernel

theorem zero_shrink_guard : Number.lessEqual (Number.ofNat (2^53)) Number.positiveZero = false := by
  decide +kernel

theorem natural_growth_guard (n : Nat) (bounded : n<2^1023) :
    Number.lessThan (Number.ofNat n) (Number.ofNat (2^52)) = decide (n<2^52) := by
  by_cases zero : n=0
  · subst n
    exact zero_growth_guard
  · by_cases small : n<2^52
    · obtain ⟨m,e,p,lo,hi,el,eu,shape,value⟩ :=
        SeedrandomNormalizationArithmetic.small_integer_shape n (by omega) (by omega)
      have negative : e<0 := by
        by_cases nonnegative : 0≤e
        · have same : e=0 := by omega
          subst e
          simp only [RepresentsNat,Int.le_refl,↓reduceIte,Int.toNat_zero,Nat.pow_zero,Nat.mul_one] at value
          omega
        · omega
      rw [shape,normal_growth_guard m e p lo hi el (by omega)]
      simp [negative,small]
    · obtain ⟨m,e,p,lo,hi,eu,shape⟩ := native_integer_round_shape n (by omega) bounded
      rw [NaturalArithmetic.ofNat_encoding,shape,normal_growth_guard m e p lo hi (by omega) (by omega)]
      simp [small]

end CookieClicker.JavaScript.SeedrandomNormalizationGuards

import CookieClicker.JavaScriptBoundedBank

/-! Order preservation of the integer projection of native dyadic rounding.
This is used to compare bank and earned-cookie additions with different
retained binary scales. Source-call composition is a separate theorem.
-/
namespace CookieClicker.JavaScript.RoundingOrder
open CookieClicker.FullGame.GodzamokRounding
open CookieClicker.FullGame.BootstrapArithmetic
open FractionalRoundingBridge
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

theorem round_multiple_monotone (spacing m n : Nat) (positive : 0 < spacing)
    (ordered : m ≤ n) : roundMultiple spacing m ≤ roundMultiple spacing n := by
  have qm := Nat.mod_add_div m spacing
  have qn := Nat.mod_add_div n spacing
  have rm := Nat.mod_lt m positive
  have rn := Nat.mod_lt n positive
  have quotient : m/spacing ≤ n/spacing := Nat.div_le_div_right ordered
  by_cases equal : m/spacing = n/spacing
  · have remainder : m%spacing ≤ n%spacing := by rw [equal] at qm; omega
    dsimp only [roundMultiple]
    rw [equal]
    apply Nat.mul_le_mul_right
    split <;> split <;> simp_all only [Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq, Nat.add_le_add_iff_left]
    · omega
    · omega
    · omega
    · omega
  · have gap : m/spacing+1 ≤ n/spacing := by omega
    have product := Nat.mul_le_mul_right spacing gap
    dsimp only [roundMultiple]
    split <;> split <;> simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul] at * <;> omega

theorem round_multiple_above_multiple (spacing n bound : Nat) (positive : 0 < spacing)
    (multiple : spacing ∣ bound) (within : bound ≤ n) : bound ≤ roundMultiple spacing n := by
  have quotient := Nat.div_le_div_right (c := spacing) within
  have product := Nat.mul_le_mul_right spacing quotient
  rw [Nat.div_mul_cancel multiple] at product
  dsimp only [roundMultiple]
  split <;> simp only [Nat.add_zero,Nat.add_mul,Nat.one_mul] <;> omega

theorem rounded_above_binade (n : Nat) (large : 2^53 ≤ n) :
    2^n.log2 ≤ roundedInteger n := by
  have nonzero : n ≠ 0 := by omega
  have logLower : 53 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have lower := (Nat.log2_eq_iff nonzero).mp (rfl : n.log2=n.log2) |>.1
  unfold roundedInteger integerSpacing
  rw [if_neg (by omega : ¬n<2^53)]
  exact round_multiple_above_multiple _ n _ (Nat.two_pow_pos _)
    (Nat.pow_dvd_pow 2 (by omega)) lower

theorem rounded_monotone (m n : Nat) (ordered : m ≤ n) : roundedInteger m ≤ roundedInteger n := by
  by_cases small : n < 2^53
  · have first : m < 2^53 := by omega
    simp only [roundedInteger,integerSpacing,if_pos small,if_pos first,unit_spacing_exact]
    exact ordered
  · have large : 2^53 ≤ n := by omega
    have nonzero : n ≠ 0 := by omega
    have logLower : 53 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
    by_cases before : m < 2^n.log2
    · exact Nat.le_trans (rounded_below_power m n.log2 before) (rounded_above_binade n large)
    · have mNonzero : m ≠ 0 := by have := Nat.two_pow_pos n.log2; omega
      have logUpper := (Nat.log2_eq_iff nonzero).mp (rfl : n.log2=n.log2) |>.2
      have sameLog : m.log2=n.log2 := (Nat.log2_eq_iff mNonzero).mpr ⟨by omega,by omega⟩
      have sameLarge : ¬m<2^53 := by
        have power := Nat.pow_le_pow_right (by decide : 0<2) logLower
        omega
      simp only [roundedInteger,integerSpacing,if_neg small,if_neg sameLarge,sameLog]
      exact round_multiple_monotone _ m n (Nat.two_pow_pos _) ordered

theorem round_multiple_scale (spacing n factor : Nat) (positive : 0 < factor) :
    roundMultiple (spacing*factor) (n*factor) = roundMultiple spacing n * factor := by
  simp only [roundMultiple, Nat.mul_div_mul_right _ _ positive,
    Nat.mul_mod_mul_right, ← Nat.mul_assoc]
  have comparison : decide (spacing*factor < 2*(n%spacing)*factor) = decide (spacing < 2*(n%spacing)) := by
    simp only [Nat.mul_lt_mul_right positive]
  have equal : (spacing*factor == 2*(n%spacing)*factor) = (spacing == 2*(n%spacing)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Nat.mul_right_cancel_iff positive]
  rw [comparison,equal]

theorem rounded_scale (n places : Nat) :
    roundedInteger (n*2^places) = roundedInteger n * 2^places := by
  by_cases zero : n=0
  · simp [zero,roundedInteger,integerSpacing,roundMultiple]
  · by_cases large : 2^52 ≤ n
    · have lower : 52 ≤ n.log2 := (Nat.le_log2 zero).mpr large
      have exponent : n.log2+places-52 = n.log2-52+places := by omega
      simp only [roundedInteger,RoundingBridge.integer_spacing_matches_native,
        DyadicArithmeticBridge.log2_scaled n places zero,exponent,Nat.pow_add]
      exact round_multiple_scale _ n _ (Nat.two_pow_pos _)
    · have small : n < 2^53 := by omega
      rw [DyadicArithmeticBridge.scaled_small_integer_exact n places (by omega) small]
      rw [integer_exact_through_cap n (by unfold unitCap; omega)]

end CookieClicker.JavaScript.RoundingOrder

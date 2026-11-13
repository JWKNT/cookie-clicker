import CookieClicker.JavaScriptScaledOrder
import CookieClicker.JavaScriptBankCycleBridge

/-! Actual binary64 resource bounds for the proposed fixed post-lump funding
profile. These statements do not supply source callback/profile reachability. -/
namespace CookieClicker.JavaScript.FundingEpisode
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge ScaledOrder BoundedAddition RoundingOrder
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.BootstrapArithmetic
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def S : Nat := 2^59

theorem integer_spacing_bounded (n k : Nat) (lower : 53 ≤ k) (bounded : n < 2^k) :
    0 < integerSpacing n ∧ integerSpacing n ≤ 2^(k-53) := by
  unfold integerSpacing
  split
  · exact ⟨by decide, Nat.one_le_two_pow⟩
  · rename_i large
    have logBound : n.log2 < k := (Nat.log2_lt (by omega)).mpr bounded
    exact ⟨Nat.two_pow_pos _, Nat.pow_le_pow_right (by decide) (by omega)⟩

theorem round_upper_spacing (spacing n : Nat) (positive : 0 < spacing) :
    roundMultiple spacing n ≤ n+spacing := by
  have decomp := Nat.mod_add_div n spacing
  rw [Nat.mul_comm spacing (n/spacing)] at decomp
  dsimp only [roundMultiple]
  split
  · simp only [Nat.add_mul,Nat.one_mul]
    omega
  · simp only [Nat.add_zero]
    omega

theorem small_bank_error (n : Nat) (bounded : n < 2^117) :
    n ≤ roundedInteger n + 16*S := by
  obtain ⟨positive,spacing⟩ := integer_spacing_bounded n 117 (by decide) bounded
  have error := roundMultiple_lower_error (integerSpacing n) n positive
  have half := Nat.div_le_div_right (c := 2) spacing
  change n ≤ roundMultiple (integerSpacing n) n + 16*S
  simp [S] at half ⊢
  omega

theorem bank_rounding_error (n : Nat) (bounded : n < 2^125) :
    n ≤ roundedInteger n + 8192*S ∧ roundedInteger n ≤ n+8192*S := by
  obtain ⟨positive,spacing⟩ := integer_spacing_bounded n 125 (by decide) bounded
  have low := roundMultiple_lower_error (integerSpacing n) n positive
  have high := round_upper_spacing (integerSpacing n) n positive
  change n ≤ roundMultiple (integerSpacing n) n + 8192*S ∧
    roundMultiple (integerSpacing n) n ≤ n+8192*S
  simp [S] at spacing ⊢
  omega

theorem spend_projection_lower (n : Nat) (bankLower : 2^79 ≤ n) (bankUpper : n < 2^117) :
    n ≤ roundedInteger (n-15*S)+32*S ∧ 2^78 ≤ roundedInteger (n-15*S) := by
  have affordable : 15*S ≤ n := by simp [S] at *; omega
  have error := small_bank_error (n-15*S) (by omega)
  have difference := Nat.sub_add_cancel affordable
  simp [S] at error difference ⊢
  omega

theorem normal_lower_scale (bits : UInt64) (n : Nat) (large : 2^53 ≤ n)
    (value : ScaledValue bits 111 (n*2^52)) : ScaledNormal bits 59 n := by
  rcases value with ⟨zero,eqZero⟩ | ⟨m,e,mp,lo,hi,elo,ehi,shape,represented⟩
  · have positive := Nat.mul_pos (by omega : 0<n) (Nat.two_pow_pos 52)
    omega
  · change m*2^(e+111).toNat = n*2^52 at represented
    have lower : -(59:Int) ≤ e := by
      by_cases inside : -(59:Int) ≤ e
      · exact inside
      have expBound : (e+111).toNat ≤ 51 := by omega
      have power := Nat.pow_le_pow_right (by decide : 0<2) expBound
      have product := Nat.mul_le_mul (show m ≤ 2^53 by omega) power
      have minimum := Nat.mul_le_mul_right (2^52) large
      rw [represented] at product
      simp only [Nat.reducePow] at product minimum
      omega
    refine ⟨m,e,mp,lo,hi,lower,ehi,shape,?_⟩
    change m*2^(e+59).toNat=n
    have exponents : (e+111).toNat=(e+59).toNat+52 := by omega
    rw [exponents,Nat.pow_add,← Nat.mul_assoc] at represented
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 52) represented

theorem fifteen_encoding : Number.ofNat 15 =
    (Float.Model.pack (.finite .positive (15*2^49) (-49) (by decide))).toBits := by
  decide +kernel

theorem native_small_spend (bank : UInt64) (n : Nat)
    (value : ScaledNormal bank 59 n) (bankLower : 2^79 ≤ n) (bankUpper : n < 2^117) :
    ∃ k, ScaledNormal (Number.sub bank (Number.ofNat 15)) 59 k ∧
      n ≤ k+32*S ∧ k≤n ∧ 2^78≤k := by
  have lower := spend_projection_lower n bankLower bankUpper
  have affordable : (15*2^49)*2^((-49:Int)+59).toNat ≤ n := by
    simp at *
    omega
  have bound : n+(0:Nat) < 2^(1023+59) := by
    have powBound : 2^117 < 2^(1023+59) := by decide +kernel
    omega
  obtain ⟨result,le⟩ := native_scaled_spend bank n (15*2^49) 59 (-49)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr value) affordable (by omega)
  rw [← fifteen_encoding] at result
  change ScaledValue (Number.sub bank (Number.ofNat 15)) 111
    (roundedInteger (n-15*S)*2^52) at result
  change roundedInteger (n-15*S)≤n at le
  exact ⟨_,normal_lower_scale _ _ (by omega) result,lower.1,le,lower.2⟩

end CookieClicker.JavaScript.FundingEpisode

import CookieClicker.JavaScriptFundingEpisode
namespace CookieClicker.JavaScript.FundingEpisode
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge ScaledOrder BoundedAddition RoundingOrder BankCycleBridge
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.BootstrapArithmetic
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The explicit bank range derives the canonical exponent required by the
already proved native absorption law. -/
theorem high_bank_exponent (m n : Nat) (e : Int)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -(59:Int)≤e)
    (represented : m*2^(e+59).toNat=n) (bankLower : 2^117≤n) (bankUpper : n<2^124) :
    6≤e ∧ e≤970 := by
  constructor
  · by_cases inside : 6≤e
    · exact inside
    have expBound : (e+59).toNat≤64 := by omega
    have bound := Nat.mul_lt_mul_of_pos_right upper (Nat.two_pow_pos (e+59).toNat)
    have power := Nat.mul_le_mul_left (2^53) (Nat.pow_le_pow_right (by decide : 0<2) expBound)
    rw [represented] at bound
    simp only [Nat.reducePow] at power bankLower
    omega
  · by_cases inside : e≤970
    · exact inside
    have expBound : 124≤(e+59).toNat := by omega
    have power := Nat.pow_le_pow_right (by decide : 0<2) expBound
    have product := Nat.le_mul_of_pos_left (2^(e+59).toNat) (by omega : 0<m)
    rw [represented] at product
    omega

theorem native_large_cycle (bank : UInt64) (n : Nat)
    (value : ScaledNormal bank 59 n) (bankLower : 2^117≤n) (bankUpper : n<2^124) :
    cycle 4 15 bank=bank := by
  obtain ⟨m,e,p,lo,hi,elo,ehi,shape,represented⟩ := value
  change m*2^(e+59).toNat=n at represented
  have bounds := high_bank_exponent m n e lo hi elo represented bankLower bankUpper
  have eNat : (e.toNat:Int)=e := Int.toNat_of_nonneg (by omega)
  rw [shape,← eNat]
  exact native_cycle_fixed m e.toNat 4 15 p lo hi (by omega) (by omega) (by decide) (by decide)

theorem native_bounded_spend (bank : UInt64) (n : Nat)
    (value : ScaledNormal bank 59 n) (bankLower : 2^79≤n) (bankUpper : n<2^124) :
    ∃ k, ScaledNormal (Number.sub bank (Number.ofNat 15)) 59 k ∧
      n≤k+32*S ∧ k≤n ∧ 2^78≤k := by
  by_cases small : n<2^117
  · exact native_small_spend bank n value bankLower small
  · obtain ⟨m,e,p,lo,hi,elo,ehi,shape,represented⟩ := value
    change m*2^(e+59).toNat=n at represented
    have bounds := high_bank_exponent m n e lo hi elo represented (by omega) bankUpper
    have eNat : (e.toNat:Int)=e := Int.toNat_of_nonneg (by omega)
    have fixed : Number.sub bank (Number.ofNat 15)=bank := by
      rw [shape,← eNat]
      exact native_debit_fixed m e.toNat 15 p lo hi (by omega) (by omega) (by decide)
    refine ⟨n,?_,by omega,by omega,by omega⟩
    rw [fixed]
    exact ⟨m,e,p,lo,hi,elo,ehi,shape,represented⟩

theorem four_encoding : Number.ofNat 4 =
    (Float.Model.pack (.finite .positive (2^52) (-50) (by decide))).toBits := by
  decide +kernel

theorem native_small_refund (bank : UInt64) (n : Nat)
    (value : ScaledNormal bank 59 n) (bankLower : 2^79≤n) (bankUpper : n<2^117) :
    ∃ k, ScaledNormal (Number.add bank (Number.ofNat 4)) 59 k ∧
      n≤k ∧ k≤n+128*S := by
  have exactBank := scaled_normal_exact bank 59 n value
  have result := native_scaled_credit_add bank n (2^52) 59 (-50) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr value)
    (by change n+4*S<2^1082; simp [S] at *; omega)
  rw [← four_encoding] at result
  change ScaledNormal (Number.add bank (Number.ofNat 4)) 59 (roundedInteger (n+4*S)) at result
  have lower := rounded_monotone n (n+4*S) (by omega)
  rw [exactBank] at lower
  obtain ⟨positive,spacing⟩ := integer_spacing_bounded (n+4*S) 118 (by decide)
    (by simp [S] at *; omega)
  have upper := round_upper_spacing (integerSpacing (n+4*S)) (n+4*S) positive
  change roundedInteger (n+4*S)≤n+4*S+integerSpacing (n+4*S) at upper
  refine ⟨_,result,lower,?_⟩
  simp [S] at spacing upper ⊢
  omega

/-- Exact native sale-refund then buy-debit order. Both bounds are derived
from Number.add/sub, not premises about the result of the cycle. -/
theorem native_bounded_cycle (bank : UInt64) (n : Nat)
    (value : ScaledNormal bank 59 n) (bankLower : 2^79≤n) (bankUpper : n<2^123) :
    ∃ k, ScaledNormal (cycle 4 15 bank) 59 k ∧
      n≤k+32*S ∧ k≤n+128*S ∧ 2^78≤k := by
  by_cases small : n<2^117
  · obtain ⟨r,refund,increase,upper⟩ := native_small_refund bank n value bankLower small
    obtain ⟨k,spend,loss,decrease,positive⟩ := native_bounded_spend _ r refund (by omega)
      (by simp [S] at upper; omega)
    exact ⟨k,spend,by omega,by omega,positive⟩
  · have fixed := native_large_cycle bank n value (by omega) (by omega)
    exact ⟨n,by simpa only [fixed] using value,by omega,by omega,by omega⟩

end CookieClicker.JavaScript.FundingEpisode

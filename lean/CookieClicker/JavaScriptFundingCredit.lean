import CookieClicker.JavaScriptFundingClick
namespace CookieClicker.JavaScript.FundingEpisode
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge ScaledArithmeticBridge ScaledOrder
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.BootstrapArithmetic
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

def stacked (count : Nat) : UInt64 :=
  nativeIterations Number.one (Number.ofScientific 1 (-2)) count

theorem stacked_normal (k : Nat) (bounded : k≤2^49) :
    ScaledNormal (stacked k) 59 (centIterations k) := by
  have lower := cent_episode_lower k bounded
  rcases native_cent_scaled k with ⟨_,zero⟩ | value
  · simp [S] at lower
    omega
  · exact value

/-- The native product output is brought back to the same exact scale as the
bank. This step retains all binary64 rounding in the product. -/
theorem product_scale59 (bits : UInt64) (r : Nat)
    (value : ScaledNormal bits 102 r) (large : 2^111≤r) :
    ∃ k, ScaledNormal bits 59 k ∧ r=k*2^43 := by
  obtain ⟨m,e,p,lo,hi,elo,ehi,shape,represented⟩ := value
  change m*2^(e+102).toNat=r at represented
  have expLower : -(59:Int)≤e := by
    by_cases yes : -(59:Int)≤e
    · exact yes
    have expBound : (e+102).toNat≤42 := by omega
    have power := Nat.pow_le_pow_right (by decide : 0<2) expBound
    have product := Nat.mul_le_mul (show m≤2^53 by omega) power
    rw [represented] at product
    simp only [Nat.reducePow] at product large
    omega
  refine ⟨m*2^(e+59).toNat,⟨m,e,p,lo,hi,expLower,ehi,shape,rfl⟩,?_⟩
  have exponent : (e+102).toNat=(e+59).toNat+43 := by omega
  rw [← represented,exponent,Nat.pow_add,← Nat.mul_assoc]

/-- A fresh finite cent stack and a native base click between512 and576 give
an actual click credit betweenN and10N. The control profile itself remains a
source reachability obligation; the product bound is proved here. -/
theorem native_episode_credit (base : UInt64) (a N : Nat)
    (baseLower : 2^52≤a) (baseUpper : a≤576*2^43)
    (baseShape : base=(Float.Model.pack (.finite .positive a (-43) (by omega))).toBits)
    (countLower : 2^22≤N) (countUpper : N≤2^49) :
    ∃ c, ScaledNormal (Number.mul (stacked N) base) 59 c ∧ N*S≤c ∧ c≤10*N*S := by
  have buff := stacked_normal N countUpper
  have low := cent_episode_lower N countUpper
  have high := cent_episode_upper N countUpper
  have count := Nat.mul_le_mul_right (2^53) countUpper
  have buffUpper : centIterations N<2^104 := by
    simp [S] at high count ⊢
    omega
  have product := native_profile_product base (stacked N) a (centIterations N)
    baseLower (by omega) baseShape buff buffUpper
  have bounds := profile_product_bounds base (stacked N) a (centIterations N)
    baseLower baseUpper baseShape buff buffUpper
  have large : 2^111≤roundedInteger (a*centIterations N) := by
    have h := Nat.mul_le_mul_right (2^52) low
    simp [S,Nat.add_mul] at h
    simp only [Nat.reducePow] at bounds
    omega
  obtain ⟨c,value,scaled⟩ := product_scale59 _ _ product large
  have cLower : centIterations N*512≤c := by
    have h := bounds.1
    rw [scaled,show (2:Nat)^52=512*2^43 by decide +kernel,← Nat.mul_assoc] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos 43)
  have cUpper : c≤576*centIterations N+4*S := by
    have h := bounds.2
    have rhs : 576*2^43*centIterations N+2^104=
        (576*centIterations N+4*S)*2^43 := by
      rw [Nat.add_mul]
      congr 1
      ac_rfl
    rw [scaled,rhs] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos 43)
  refine ⟨c,value,?_,?_⟩
  · have part : N*2^50≤centIterations N :=
      Nat.le_trans (Nat.le_add_left _ _) low
    have h := Nat.mul_le_mul_right 512 part
    have scale : N*S=(N*2^50)*512 := by
      rw [Nat.mul_assoc]
      rfl
    rw [← scale] at h
    exact Nat.le_trans h cLower
  · have h := Nat.mul_le_mul_left 576 high
    simp [S,Nat.mul_add,Nat.mul_assoc] at h cUpper ⊢
    omega

end CookieClicker.JavaScript.FundingEpisode

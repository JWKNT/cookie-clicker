import CookieClicker.JavaScriptFundingCycle
import CookieClicker.JavaScriptFundingCredit
namespace CookieClicker.JavaScript.FundingEpisode
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge ScaledArithmeticBridge ScaledOrder BankCycleBridge
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.BootstrapArithmetic
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

theorem native_credit_progress (bank credit : UInt64) (b c N : Nat)
    (bankValue : ScaledNormal bank 59 b) (creditValue : ScaledNormal credit 59 c)
    (bankUpper : b<2^123) (countLower : 2^22≤N) (countUpper : N≤2^49)
    (creditLower : N*S≤c) (creditUpper : c≤10*N*S) :
    ∃ r, ScaledNormal (Number.add bank credit) 59 r ∧
      2*b+N*S≤2*r ∧ r≤b+11*N*S := by
  obtain ⟨m,e,p,lo,hi,elo,ehi,shape,represented⟩ := creditValue
  change m*2^(e+59).toNat=c at represented
  have count := Nat.mul_le_mul_right (10*S) countUpper
  have cUpper : c<2^112 := by
    simp [S,Nat.mul_comm,Nat.mul_assoc] at count creditUpper
    omega
  have eUpper : e≤0 := by
    by_cases yes : e≤0
    · exact yes
    have power := Nat.pow_le_pow_right (by decide : 0<2)
      (show 60≤(e+59).toNat by omega)
    have product := Nat.mul_le_mul lo power
    rw [represented] at product
    simp only [Nat.reducePow] at product cUpper
    omega
  have bounded : b+c<2^125 := by omega
  have result := native_scaled_credit_add bank b m 59 e p lo hi elo eUpper (by decide)
    (Or.inr bankValue) (by
      change b+m*2^(e+59).toNat<2^1082
      rw [represented]
      exact Nat.lt_trans bounded (by decide +kernel : (2:Nat)^125<2^1082))
  rw [← shape] at result
  change ScaledNormal (Number.add bank credit) 59
    (roundedInteger (b+m*2^(e+59).toNat)) at result
  rw [represented] at result
  have errors := bank_rounding_error (b+c) bounded
  refine ⟨_,result,?_,?_⟩
  · simp [S] at creditLower errors countLower ⊢
    omega
  · simp [S] at creditUpper errors countLower ⊢
    omega

def cycles (bank : UInt64) : Nat → UInt64
  | 0 => bank
  | k+1 => cycle 4 15 (cycles bank k)

def clicks (credit bank : UInt64) : Nat → UInt64
  | 0 => bank
  | k+1 => Number.add (clicks credit bank k) credit

/-- Every intervening bank is derived from the actual native cycle function. -/
theorem finite_cycles (bank : UInt64) (n N k : Nat)
    (value : ScaledNormal bank 59 n) (countLower : 2^22≤N) (countUpper : N≤2^49)
    (funded : 256*N*S≤n) (bankUpper : n<2^118) (within : k≤N) :
    ∃ r, ScaledNormal (cycles bank k) 59 r ∧
      n≤r+32*k*S ∧ r≤n+128*k*S := by
  induction k with
  | zero => exact ⟨n,value,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨r,rValue,rLow,rHigh⟩ := ih (by omega)
    have used := Nat.mul_le_mul_right (32*S) (show k≤N by omega)
    have allocated := Nat.mul_le_mul_right (128*S) (show k≤N by omega)
    have maxCount := Nat.mul_le_mul_right (128*S) countUpper
    have rLower : 2^79≤r := by
      simp [S,Nat.mul_assoc,Nat.mul_comm] at used funded rLow countLower
      omega
    have rUpper : r<2^123 := by
      simp [S,Nat.mul_assoc,Nat.mul_comm] at allocated maxCount rHigh
      omega
    obtain ⟨q,qValue,qLow,qHigh,_⟩ := native_bounded_cycle _ r rValue rLower rUpper
    refine ⟨q,qValue,?_,?_⟩
    · simp [Nat.add_mul,Nat.mul_assoc] at *
      omega
    · simp [Nat.add_mul,Nat.mul_assoc] at *
      omega

/-- Four hundred accepted native additions; the source timing/acceptance
conditions are not hidden in this arithmetic theorem. -/
theorem finite_clicks (bank credit : UInt64) (b c N k : Nat)
    (bankValue : ScaledNormal bank 59 b) (creditValue : ScaledNormal credit 59 c)
    (bankUpper : b<2^119) (countLower : 2^22≤N) (countUpper : N≤2^49)
    (creditLower : N*S≤c) (creditUpper : c≤10*N*S) (within : k≤400) :
    ∃ r, ScaledNormal (clicks credit bank k) 59 r ∧
      2*b+k*N*S≤2*r ∧ r≤b+11*k*N*S := by
  induction k with
  | zero => exact ⟨b,bankValue,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨r,rValue,rLow,rHigh⟩ := ih (by omega)
    have kc := Nat.mul_le_mul (show k≤400 by omega) countUpper
    have maxGrowth := Nat.mul_le_mul_right (11*S) kc
    have rUpper : r<2^123 := by
      simp [S,Nat.mul_assoc,Nat.mul_comm] at maxGrowth rHigh
      omega
    obtain ⟨q,qValue,qLow,qHigh⟩ := native_credit_progress _ credit r c N rValue creditValue
      rUpper countLower countUpper creditLower creditUpper
    refine ⟨q,qValue,?_,?_⟩
    · simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at rLow qLow ⊢
      omega
    · simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc] at rHigh qHigh ⊢
      omega

/-- One finite native arithmetic episode: N refund/debit cycles, then400
accepted clicks using the actual freshly stacked binary64 multiplier. -/
theorem native_episode_gain (bank base : UInt64) (n a N : Nat)
    (bankValue : ScaledNormal bank 59 n) (baseLower : 2^52≤a) (baseUpper : a≤576*2^43)
    (baseShape : base=(Float.Model.pack (.finite .positive a (-43) (by omega))).toBits)
    (countLower : 2^22≤N) (countUpper : N≤2^49)
    (funded : 256*N*S≤n) (bankUpper : n<2^118) :
    ∃ r, ScaledNormal (clicks (Number.mul (stacked N) base) (cycles bank N) 400) 59 r ∧
      n+168*N*S≤r ∧ r≤n+4528*N*S := by
  obtain ⟨b,bValue,bLow,bHigh⟩ := finite_cycles bank n N N bankValue countLower countUpper
    funded bankUpper (Nat.le_refl _)
  obtain ⟨c,cValue,cLow,cHigh⟩ := native_episode_credit base a N baseLower baseUpper baseShape
    countLower countUpper
  have maxCount := Nat.mul_le_mul_right (128*S) countUpper
  have bUpper : b<2^119 := by
    simp [S,Nat.mul_assoc,Nat.mul_comm] at maxCount bHigh
    omega
  obtain ⟨r,rValue,rLow,rHigh⟩ := finite_clicks _ _ b c N 400 bValue cValue bUpper
    countLower countUpper cLow cHigh (Nat.le_refl _)
  refine ⟨r,rValue,?_,?_⟩
  · simp only [Nat.mul_assoc] at bLow rLow ⊢
    omega
  · simp only [Nat.mul_assoc] at bHigh rHigh ⊢
    omega


def episode (base : UInt64) (N : Nat) (bank : UInt64) : UInt64 :=
  clicks (Number.mul (stacked N) base) (cycles bank N) 400

/-- At most two explicit finite native arithmetic episodes cross a doubling
threshold256N→512N. This is an attaining finite arithmetic construction,
not a claim that its source profile or its elapsed schedule is optimal. -/
theorem two_episodes_double (bank base : UInt64) (n a N : Nat)
    (bankValue : ScaledNormal bank 59 n) (baseLower : 2^52≤a) (baseUpper : a≤576*2^43)
    (baseShape : base=(Float.Model.pack (.finite .positive a (-43) (by omega))).toBits)
    (countLower : 2^22≤N) (countUpper : N≤2^49)
    (funded : 256*N*S≤n) (below : n<512*N*S) :
    (∃ r, ScaledNormal (episode base N bank) 59 r ∧ 512*N*S≤r) ∨
    (∃ r, ScaledNormal (episode base N (episode base N bank)) 59 r ∧ 512*N*S≤r) := by
  have maximum := Nat.mul_le_mul_right (512*S) countUpper
  have bound : n<2^118 := by
    simp [S,Nat.mul_assoc,Nat.mul_comm] at maximum below
    omega
  obtain ⟨r,first,gain,_⟩ := native_episode_gain bank base n a N bankValue baseLower baseUpper
    baseShape countLower countUpper funded bound
  by_cases reached : 512*N*S≤r
  · exact Or.inl ⟨r,first,reached⟩
  · have rBound : r<2^118 := by
      simp [S,Nat.mul_assoc,Nat.mul_comm] at maximum reached
      omega
    obtain ⟨q,second,gain',_⟩ := native_episode_gain (episode base N bank) base r a N first
      baseLower baseUpper baseShape countLower countUpper (by omega) rBound
    refine Or.inr ⟨q,second,?_⟩
    simp only [Nat.mul_assoc] at funded gain gain' ⊢
    omega

end CookieClicker.JavaScript.FundingEpisode


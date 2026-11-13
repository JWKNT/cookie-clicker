import CookieClicker.JavaScriptFundingEpisode
namespace CookieClicker.JavaScript.FundingEpisode
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge ScaledOrder BoundedAddition RoundingOrder
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.BootstrapArithmetic
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-- The short finite funding episode stays well below the cent cap. -/
theorem cent_episode_upper (k : Nat) (bounded : k≤2^49) :
    centIterations k≤S+k*2^53 := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have previous := ih (by omega)
    have amount := Nat.mul_le_mul_right (2^53) (show k≤2^49 by omega)
    have small : centIterations k+centNumerator<2^104 := by
      simp [S,centNumerator] at previous amount ⊢
      omega
    obtain ⟨positive,spacing⟩ := integer_spacing_bounded _ 104 (by decide) small
    have upper := round_upper_spacing _ (centIterations k+centNumerator) positive
    change roundedInteger (centIterations k+centNumerator)≤
      centIterations k+centNumerator+integerSpacing (centIterations k+centNumerator) at upper
    change roundedInteger (centIterations k+centNumerator)≤S+(k+1)*2^53
    simp [Nat.add_mul,S,centNumerator] at previous spacing upper ⊢
    omega

theorem cent_episode_lower (k : Nat) (bounded : k≤2^49) :
    S+k*2^50≤centIterations k := by
  have lower := (cent_iterations_bounds k).1
  have amount := Nat.mul_le_mul_right (2^50) bounded
  have below : multiplierScale+k*centLowerStep≤centCap := by
    simp [multiplierScale,centLowerStep,centCap] at amount ⊢
    omega
  rw [Nat.min_eq_left below] at lower
  exact lower

theorem normal_round_same (n D : Nat) (large : 2^52≤n) (scaleBound : D≤1074) :
    round Format.binary64 .positive n (-(D:Int)) =
      roundWithAccuracy Format.binary64 .positive n (-(D:Int)) .exact := by
  have logLower : 52≤n.log2 := (Nat.le_log2 (by omega : n≠0)).mpr large
  have target : Format.binary64.targetExponent (totalExponent n (-(D:Int))) =
      (n.log2:Int)-D-52 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : (-(D:Int)-((n.log2:Int)-D-52)).toNat=0 := by omega
  have decrease : decreaseExponent n (-(D:Int)) ((n.log2:Int)-D-52)=(n,-(D:Int)) := by
    unfold decreaseExponent
    rw [gap]
    simp
  unfold round
  rw [target]
  dsimp only
  rw [decrease]

/-- An actual native positive product, not a real-number replacement. -/
theorem native_profile_product (base buff : UInt64) (a n : Nat)
    (baseLower : 2^52≤a) (baseUpper : a<2^53)
    (baseShape : base=(Float.Model.pack (.finite .positive a (-43) (by omega))).toBits)
    (buffValue : ScaledNormal buff 59 n) (buffUpper : n<2^104) :
    ScaledNormal (Number.mul buff base) 102 (roundedInteger (a*n)) := by
  obtain ⟨m,e,p,lo,hi,elo,ehi,buffShape,represented⟩ := buffValue
  change m*2^(e+59).toNat=n at represented
  have nonpositive : e≤0 := by
    by_cases yes : e≤0
    · exact yes
    have pow := Nat.pow_le_pow_right (by decide : 0<2)
      (show 52≤(e+59).toNat by omega)
    have product := Nat.mul_le_mul lo pow
    rw [represented] at product
    simp only [Nat.reducePow] at product buffUpper
    omega
  let d : Nat := (43-e).toNat
  have dBound : d≤102 := by dsimp [d]; omega
  have exponent : e+(-43)=-(d:Int) := by dsimp [d]; omega
  have shift : 102-d=(e+59).toNat := by dsimp [d]; omega
  have rawLower : 2^52≤a*m := by
    have h := Nat.le_mul_of_pos_right a p
    omega
  have rawUpper : a*m<2^106 := by
    have h := Nat.mul_lt_mul_of_pos_right baseUpper p
    have h' := Nat.mul_lt_mul_of_pos_left hi (Nat.two_pow_pos 53)
    simp only [Nat.reducePow] at h h' ⊢
    omega
  obtain ⟨v,ve,vp,vl,vu,vel,veu,shape,value⟩ :=
    bounded_scaled_round_shape (a*m) d rawLower
      (Nat.lt_of_lt_of_le rawUpper (Nat.pow_le_pow_right (by decide) (by omega)))
      (by omega)
  have result : ScaledNormal (Float.Model.pack (round Format.binary64 .positive
      (a*m) (-(d:Int)))).toBits d (roundedInteger (a*m)) := by
    rw [shape]
    exact ⟨v,ve,vp,vl,vu,vel,veu,rfl,value⟩
  have lift := scaled_normal_lift _ d 102 _ dBound result
  rw [← rounded_scale,shift,Nat.mul_assoc,represented] at lift
  rw [baseShape,buffShape]
  unfold Number.mul Float.Model.mul
  rw [normal_model_unpack a (-43) (by omega) baseLower baseUpper (by decide) (by decide),
    normal_model_unpack m e p lo hi (by omega) ehi]
  simp only [UnpackedFloat.mul]
  rw [show Sign.positive*Sign.positive=Sign.positive by rfl]
  rw [Nat.mul_comm m a,exponent,← normal_round_same (a*m) d rawLower (by omega)]
  exact lift

/-- Native product monotonicity here follows from the integer rounding bridge.
The exact power-of-two endpoint is retained, with no epsilon premise. -/
theorem profile_product_bounds (base buff : UInt64) (a n : Nat)
    (baseLower : 2^52≤a) (baseUpper : a≤576*2^43)
    (_baseShape : base=(Float.Model.pack (.finite .positive a (-43) (by omega))).toBits)
    (buffValue : ScaledNormal buff 59 n) (buffUpper : n<2^104) :
    n*2^52≤roundedInteger (a*n) ∧ roundedInteger (a*n)≤576*2^43*n+2^104 := by
  have exactBuff := scaled_normal_exact buff 59 n buffValue
  have low := rounded_monotone (n*2^52) (a*n)
    (by have h := Nat.mul_le_mul_right n baseLower; simpa only [Nat.mul_comm] using h)
  rw [rounded_scale,exactBuff] at low
  have aSmall : a<2^53 := by omega
  have nPositive : 0<n := by
    obtain ⟨m,e,p,_,_,_,_,_,r⟩ := buffValue
    change m*2^(e+59).toNat=n at r
    have h := Nat.mul_pos p (Nat.two_pow_pos (e+59).toNat)
    omega
  have productSmall : a*n<2^157 := by
    have h := Nat.mul_lt_mul_of_pos_right aSmall nPositive
    have h' := Nat.mul_lt_mul_of_pos_left buffUpper (Nat.two_pow_pos 53)
    simp only [Nat.reducePow] at h h' ⊢
    omega
  obtain ⟨positive,spacing⟩ := integer_spacing_bounded (a*n) 157 (by decide) productSmall
  have high := round_upper_spacing _ (a*n) positive
  change roundedInteger (a*n)≤a*n+integerSpacing (a*n) at high
  have baseBound := Nat.mul_le_mul_right n baseUpper
  exact ⟨low,by omega⟩

end CookieClicker.JavaScript.FundingEpisode

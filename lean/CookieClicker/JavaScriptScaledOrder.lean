import CookieClicker.JavaScriptRoundingOrder

/-! Native addition at a common exact dyadic scale. The input bank can have
a different canonical exponent from the production credit. -/
namespace CookieClicker.JavaScript.ScaledOrder
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open ScaledArithmeticBridge BoundedAddition RoundingOrder
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem scaled_normal_lift (bits : UInt64) (d D n : Nat) (scale : d ≤ D)
    (value : ScaledNormal bits d n) : ScaledNormal bits D (n*2^(D-d)) := by
  obtain ⟨m,e,positive,lower,upper,lo,hi,shape,represented⟩ := value
  refine ⟨m,e,positive,lower,upper,by omega,hi,shape,?_⟩
  have exponent : (e+D).toNat=(e+d).toNat+(D-d) := by omega
  rw [exponent,Nat.pow_add,← Nat.mul_assoc,represented]

theorem scaled_value_lift (bits : UInt64) (d D n : Nat) (scale : d ≤ D)
    (value : ScaledValue bits d n) : ScaledValue bits D (n*2^(D-d)) := by
  rcases value with ⟨rfl,rfl⟩ | normal
  · exact Or.inl ⟨rfl,by simp⟩
  · exact Or.inr (scaled_normal_lift bits d D n scale normal)

theorem scaled_normal_exact (bits : UInt64) (D n : Nat) (value : ScaledNormal bits D n) :
    roundedInteger n=n := by
  obtain ⟨m,e,positive,lower,upper,lo,hi,shape,represented⟩ := value
  rw [← represented]
  exact scaled_small_integer_exact m (e+D).toNat positive upper

theorem aligned_scale (m : Nat) (e common : Int) (D : Nat)
    (commonLower : -(D:Int) ≤ common) (commonUpper : common ≤ 0) (aligned : common ≤ e) :
    (m*2^(e-common).toNat)*2^(D-(-common).toNat) = m*2^(e+D).toNat := by
  have exponent : (e-common).toNat+(D-(-common).toNat)=(e+D).toNat := by omega
  rw [Nat.mul_assoc,← Nat.pow_add,exponent]

theorem native_normal_add_common_scale (m₁ m₂ D : Nat) (e₁ e₂ : Int)
    (positive₁ : 0<m₁) (positive₂ : 0<m₂)
    (lower₁ : 2^52≤m₁) (upper₁ : m₁<2^53)
    (lower₂ : 2^52≤m₂) (upper₂ : m₂<2^53)
    (expLower₁ : -(D:Int)≤e₁) (expUpper₁ : e₁≤971)
    (expLower₂ : -(D:Int)≤e₂) (expUpper₂ : e₂≤0)
    (scaleBound : D≤1074)
    (sumBound : m₁*2^(e₁+D).toNat+m₂*2^(e₂+D).toNat < 2^(1023+D)) :
    ScaledNormal (Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      D (roundedInteger (m₁*2^(e₁+D).toNat+m₂*2^(e₂+D).toNat)) := by
  let d := denominatorExponent e₁ e₂
  let a := alignedNumerator m₁ m₂ e₁ e₂
  have commonLower : -(D:Int)≤min e₁ e₂ := by omega
  have commonUpper : min e₁ e₂≤0 := by omega
  have dBound : d≤D := by dsimp [d,denominatorExponent]; omega
  have scaled : a*2^(D-d)=m₁*2^(e₁+D).toNat+m₂*2^(e₂+D).toNat := by
    dsimp [a,alignedNumerator,d,denominatorExponent]
    rw [Nat.add_mul,
      aligned_scale m₁ e₁ (min e₁ e₂) D commonLower commonUpper (Int.min_le_left _ _),
      aligned_scale m₂ e₂ (min e₁ e₂) D commonLower commonUpper (Int.min_le_right _ _)]
  have exponent : 1023+D=(1023+d)+(D-d) := by omega
  have rawBound : a < 2^(1023+d) := by
    rw [← scaled,exponent,Nat.pow_add] at sumBound
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mp sumBound
  have large : 2^52≤a := by
    have term := Nat.mul_le_mul_left m₁ (Nat.one_le_two_pow (n := (e₁-min e₁ e₂).toNat))
    simp only [Nat.mul_one] at term
    dsimp [a,alignedNumerator]
    omega
  obtain ⟨m,e,positive,lower,upper,lo,hi,shape,represented⟩ :=
    bounded_scaled_round_shape a d large rawBound (by omega)
  have value : ScaledNormal (Float.Model.pack
      (round Format.binary64 .positive a (-(d:Int)))).toBits d (roundedInteger a) := by
    rw [shape]
    exact ⟨m,e,positive,lower,upper,lo,hi,rfl,represented⟩
  rw [number_add_is_negative_dyadic_round m₁ m₂ e₁ e₂ positive₁ positive₂
    lower₁ upper₁ lower₂ upper₂ (by omega) expUpper₁ (by omega) (by omega) commonUpper]
  have lifted := scaled_normal_lift _ d D (roundedInteger a) dBound value
  rw [← rounded_scale,scaled] at lifted
  exact lifted

theorem native_scaled_credit_add (bits : UInt64) (n m D : Nat) (e : Int)
    (positive : 0<m) (lower : 2^52≤m) (upper : m<2^53)
    (expLower : -(D:Int)≤e) (expUpper : e≤0) (scaleBound : D≤1074)
    (bank : ScaledValue bits D n)
    (bounded : n+m*2^(e+D).toNat < 2^(1023+D)) :
    ScaledNormal (Number.add bits (Float.Model.pack (.finite .positive m e positive)).toBits)
      D (roundedInteger (n+m*2^(e+D).toNat)) := by
  rcases bank with ⟨rfl,rfl⟩ | ⟨b,be,bp,blo,bhi,beLo,beHi,rfl,represented⟩
  · rw [number_add_zero_left m e positive lower upper (by omega) (by omega),Nat.zero_add,
      scaled_small_integer_exact m (e+D).toNat positive upper]
    exact ⟨m,e,positive,lower,upper,expLower,by omega,rfl,rfl⟩
  · rw [← represented] at bounded ⊢
    exact native_normal_add_common_scale b m D be e bp positive blo bhi lower upper beLo beHi
      expLower expUpper scaleBound bounded

/-- Both sums are native Number.add results. Their common-scale numerators
retain the incoming order, including banks equal to positive zero. -/
theorem native_scaled_credit_order (a b : UInt64) (an bn m D : Nat) (e : Int)
    (positive : 0<m) (lower : 2^52≤m) (upper : m<2^53)
    (expLower : -(D:Int)≤e) (expUpper : e≤0) (scaleBound : D≤1074)
    (first : ScaledValue a D an) (second : ScaledValue b D bn) (order : an≤bn)
    (bounded : bn+m*2^(e+D).toNat < 2^(1023+D)) :
    let credit := (Float.Model.pack (.finite .positive m e positive)).toBits
    ∃ x y, ScaledNormal (Number.add a credit) D x ∧
      ScaledNormal (Number.add b credit) D y ∧ x≤y := by
  refine ⟨roundedInteger (an+m*2^(e+D).toNat),roundedInteger (bn+m*2^(e+D).toNat),?_,?_,?_⟩
  · exact native_scaled_credit_add a an m D e positive lower upper expLower expUpper scaleBound first (by omega)
  · exact native_scaled_credit_add b bn m D e positive lower upper expLower expUpper scaleBound second bounded
  · exact rounded_monotone _ _ (by omega)

theorem native_normal_sub_common_scale (m₁ m₂ D : Nat) (e₁ e₂ : Int)
    (positive₁ : 0<m₁) (positive₂ : 0<m₂)
    (lower₁ : 2^52≤m₁) (upper₁ : m₁<2^53)
    (lower₂ : 2^52≤m₂) (upper₂ : m₂<2^53)
    (expLower₁ : -(D:Int)≤e₁) (expUpper₁ : e₁≤971)
    (expLower₂ : -(D:Int)≤e₂) (expUpper₂ : e₂≤0)
    (scaleBound : D≤1022)
    (affordable : m₂*2^(e₂+D).toNat ≤ m₁*2^(e₁+D).toNat)
    (bankBound : m₁*2^(e₁+D).toNat < 2^(1023+D)) :
    ScaledValue (Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
      (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (D+52) (roundedInteger (m₁*2^(e₁+D).toNat-m₂*2^(e₂+D).toNat)*2^52) := by
  let d := denominatorExponent e₁ e₂
  let a := m₁*2^(e₁-min e₁ e₂).toNat
  let b := m₂*2^(e₂-min e₁ e₂).toNat
  have commonLower : -(D:Int)≤min e₁ e₂ := by omega
  have commonUpper : min e₁ e₂≤0 := by omega
  have dBound : d≤D := by dsimp [d,denominatorExponent]; omega
  have first : a*2^(D-d)=m₁*2^(e₁+D).toNat :=
    aligned_scale m₁ e₁ (min e₁ e₂) D commonLower commonUpper (Int.min_le_left _ _)
  have second : b*2^(D-d)=m₂*2^(e₂+D).toNat :=
    aligned_scale m₂ e₂ (min e₁ e₂) D commonLower commonUpper (Int.min_le_right _ _)
  have rawAffordable : b≤a := by
    rw [← first,← second] at affordable
    exact Nat.le_of_mul_le_mul_right affordable (Nat.two_pow_pos _)
  have scaledDifference : (a-b)*2^(D-d)=m₁*2^(e₁+D).toNat-m₂*2^(e₂+D).toNat := by
    rw [Nat.sub_mul,first,second]
  have exponent : 1023+D=(1023+d)+(D-d) := by omega
  have rawBound : a<2^(1023+d) := by
    rw [← first,exponent,Nat.pow_add] at bankBound
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mp bankBound
  have value := BoundedSubtraction.native_affordable_sub_value m₁ m₂ e₁ e₂ positive₁ positive₂
    lower₁ upper₁ lower₂ upper₂ (by omega) expUpper₁ (by omega) (by omega)
    (by omega) commonUpper rawAffordable rawBound
  change ScaledValue _ (d+52) (roundedInteger (a-b)*2^52) at value
  have lifted := scaled_value_lift _ (d+52) (D+52) (roundedInteger (a-b)*2^52) (by omega) value
  have gap : D+52-(d+52)=D-d := by omega
  have rearrange : (roundedInteger (a-b)*2^52)*2^(D-d) =
      (roundedInteger (a-b)*2^(D-d))*2^52 := by ac_rfl
  rw [gap,rearrange,← rounded_scale,scaledDifference] at lifted
  exact lifted

theorem native_scaled_spend (bits : UInt64) (n m D : Nat) (e : Int)
    (positive : 0<m) (lower : 2^52≤m) (upper : m<2^53)
    (expLower : -(D:Int)≤e) (expUpper : e≤0) (scaleBound : D≤1022)
    (bank : ScaledValue bits D n) (affordable : m*2^(e+D).toNat≤n)
    (bounded : n<2^(1023+D)) :
    ScaledValue (Number.sub bits (Float.Model.pack (.finite .positive m e positive)).toBits)
      (D+52) (roundedInteger (n-m*2^(e+D).toNat)*2^52) ∧
      roundedInteger (n-m*2^(e+D).toNat)≤n := by
  rcases bank with ⟨rfl,rfl⟩ | normal
  · have nonzero := Nat.mul_pos positive (Nat.two_pow_pos (e+D).toNat)
    omega
  · have exactBank := scaled_normal_exact bits D n normal
    have order := rounded_monotone (n-m*2^(e+D).toNat) n (Nat.sub_le _ _)
    rw [exactBank] at order
    refine ⟨?_,order⟩
    obtain ⟨b,be,bp,blo,bhi,beLo,beHi,rfl,represented⟩ := normal
    rw [← represented] at affordable bounded ⊢
    exact native_normal_sub_common_scale b m D be e bp positive blo bhi lower upper beLo beHi
      expLower expUpper scaleBound affordable bounded

theorem native_scaled_spend_order (a b : UInt64) (an bn m D : Nat) (e : Int)
    (positive : 0<m) (lower : 2^52≤m) (upper : m<2^53)
    (expLower : -(D:Int)≤e) (expUpper : e≤0) (scaleBound : D≤1022)
    (first : ScaledValue a D an) (second : ScaledValue b D bn) (order : an≤bn)
    (affordable : m*2^(e+D).toNat≤an) (bounded : an<2^(1023+D)) :
    let price := (Float.Model.pack (.finite .positive m e positive)).toBits
    ∃ x y, ScaledValue (Number.sub a price) (D+52) x ∧
      ScaledValue b (D+52) y ∧ x≤y := by
  obtain ⟨value,decrease⟩ := native_scaled_spend a an m D e positive lower upper
    expLower expUpper scaleBound first affordable bounded
  have lift := scaled_value_lift b D (D+52) bn (by omega) second
  rw [show D+52-D=52 by omega] at lift
  exact ⟨_,bn*2^52,value,lift,Nat.mul_le_mul_right _ (Nat.le_trans decrease order)⟩

end CookieClicker.JavaScript.ScaledOrder

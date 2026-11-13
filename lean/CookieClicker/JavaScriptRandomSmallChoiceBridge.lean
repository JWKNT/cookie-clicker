import CookieClicker.JavaScriptRandomChoiceBridge
import CookieClicker.StartupSeed
import CookieClicker.JavaScriptLumpSyntax

/-! Exact native binary64 indexing for the golden and meaty lump arrays.
The proof includes multiplication rounding, Math.floor, every IID53 bucket,
individual yield masses and the expectations. The pinned source literals are
checked against the existing complete harvest syntax. The active generator,
source call/array frame and whole harvest transition remain separate obligations.
-/
namespace CookieClicker.JavaScript.RandomSmallChoiceBridge
open Float.Model Float.Model.UnpackedFloat Number Random RoundingBridge DyadicArithmeticBridge RandomChoiceBridge
open CookieClicker.FullGame.GodzamokRounding CookieClicker.FullGame.UniformRandom
set_option exponentiation.threshold 4096
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem roundMultiple_scale (spacing n factor : Nat) (positive : 0 < factor) :
    roundMultiple (spacing*factor) (n*factor) = roundMultiple spacing n * factor := by
  have below : spacing*factor < 2*(n%spacing*factor) ↔ spacing < 2*(n%spacing) := by
    rw [←Nat.mul_assoc,Nat.mul_lt_mul_right positive]
  have tie : spacing*factor = 2*(n%spacing*factor) ↔ spacing = 2*(n%spacing) := by
    rw [←Nat.mul_assoc]
    exact Nat.mul_left_inj (by omega : factor ≠ 0)
  have tieBool : (spacing*factor == 2*(n%spacing*factor)) = (spacing == 2*(n%spacing)) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using tie
  simp only [roundMultiple,Nat.mul_div_mul_right _ _ positive,Nat.mul_mod_mul_right]
  simp only [below,tieBool]
  rw [Nat.mul_assoc]

theorem rounded_scale (n places : Nat) (positive : 0 < n) :
    roundedInteger (n*2^places) = roundedInteger n * 2^places := by
  by_cases small : n < 2^53
  · rw [scaled_small_integer_exact n places positive small]
    rw [integer_exact_through_cap n (by unfold unitCap; omega)]
  · have logLower : 52 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
    rw [roundedInteger,integer_spacing_matches_native,log2_scaled n places (by omega)]
    have exp : n.log2+places-52=(n.log2-52)+places := by omega
    rw [exp,Nat.pow_add,roundMultiple_scale _ _ _ (Nat.two_pow_pos _)]
    rw [←integer_spacing_matches_native]
    rfl

theorem normal_carry_shift_int (mantissa : Nat) (exponent : Int)
    (lower : 2^52 ≤ mantissa) (upper : mantissa ≤ 2^53) (finiteLow : -1074 ≤ exponent) :
    shiftToTargetExponent Format.binary64 mantissa exponent .exact =
      if mantissa=2^53 then (⟨2^52,false,false⟩,exponent+1)
      else (⟨mantissa,false,false⟩,exponent) := by
  by_cases same : mantissa=2^53
  · subst mantissa
    have logarithm : (2^53 : Nat).log2=53 := by decide +kernel
    have target : Format.binary64.targetExponent (totalExponent (2^53) exponent)=exponent+1 := by
      simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,logarithm]
      omega
    simp only [shiftToTargetExponent,target,shiftToExponent,show (exponent+1-exponent).toNat=1 by omega,↓reduceIte]
    rfl
  · have logarithm : mantissa.log2=52 :=
      (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower,by omega⟩
    have target : Format.binary64.targetExponent (totalExponent mantissa exponent)=exponent := by
      simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,logarithm]
      omega
    simp only [shiftToTargetExponent,target,shiftToExponent,Int.sub_self,Int.toNat_zero,
      Int.ofNat_zero,Int.add_zero,same,↓reduceIte]
    rfl


theorem normal_scaled_first_shift (n places : Nat) (e : Int)
    (large : 2^52 ≤ n) (finiteLow : -1074 ≤ e) :
    shiftToTargetExponent Format.binary64 (n*2^places) (e-places) .exact =
      (shifted n (n.log2-52),e+((n.log2-52 : Nat) : Int)) := by
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr large
  have target : Format.binary64.targetExponent (totalExponent (n*2^places) (e-places)) =
      e+((n.log2-52 : Nat) : Int) := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,
      log2_scaled n places (by omega),Int.natCast_add]
    omega
  have gap : (e+((n.log2-52 : Nat) : Int)-(e-places)).toNat=places+(n.log2-52) := by omega
  unfold shiftToTargetExponent
  rw [target]
  simp only [shiftToExponent,gap]
  change (shifted (n*2^places) (places+(n.log2-52)),
    e-places+((places+(n.log2-52) : Nat) : Int)) = _
  rw [shifted_scale]
  congr 1
  omega

theorem normal_scaled_round_shape (n places : Nat) (e : Int)
    (large : 2^52 ≤ n) (finiteLow : -1074 ≤ e) :
    ∃ (mantissa exponent : Nat) (positive : 0 < mantissa),
      2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ n.log2-52+1 ∧
      roundWithAccuracy Format.binary64 .positive (n*2^places) (e-places) .exact =
        .finite .positive mantissa (e+exponent) positive ∧
      mantissa*2^exponent = roundedInteger n := by
  let p := n.log2-52
  let m := (shifted n p).roundedMantissa
  have lower : 2^52 ≤ m := native_rounded_mantissa_lower n large
  have upper : m ≤ 2^53 := native_rounded_mantissa_bound n
  have value : m*2^p = roundedInteger n := by
    simpa only [m,p,roundedInteger,integer_spacing_matches_native] using shifted_rounding n p
  unfold roundWithAccuracy
  rw [normal_scaled_first_shift n places e large finiteLow]
  change ∃ (mantissa exponent : Nat) (positive : 0 < mantissa),
    2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ n.log2-52+1 ∧
    (let pair := shiftToTargetExponent Format.binary64 m (e+p) .exact
     if h : pair.1.mantissa=0 then UnpackedFloat.zero .positive
     else .finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) =
      .finite .positive mantissa (e+exponent) positive ∧ mantissa*2^exponent = roundedInteger n
  rw [normal_carry_shift_int m (e+p) lower upper (by omega)]
  by_cases carry : m=2^53
  · simp only [carry,↓reduceIte]
    refine ⟨2^52,p+1,by decide +kernel,by decide +kernel,by decide +kernel,by omega,?_,?_⟩
    · simp [Int.natCast_add,Int.add_assoc]
    · rw [carry] at value
      rw [Nat.pow_succ]
      have powers : (2^52 : Nat)*2=2^53 := by decide +kernel
      calc
        2^52*(2^p*2) = (2^52*2)*2^p := by ac_rfl
        _ = 2^53*2^p := by rw [powers]
        _ = roundedInteger n := value
  · simp only [carry,↓reduceIte]
    exact ⟨m,p,by omega,lower,by omega,by omega,by simp [show m ≠ 0 by omega],value⟩


theorem native_small_choice_unpack (c : Nat) (choice : c=5 ∨ c=6) :
    (Number.model (Number.ofNat c)).unpack =
      .finite .positive (c*2^50) (-50) (by rcases choice with rfl|rfl <;> decide) := by
  rcases choice with rfl|rfl <;> rfl

theorem multiply_small_choice_shape (draw : Draw 53) (c : Nat)
    (choice : c=5 ∨ c=6) (positive : 0 < draw.val) :
    ∃ (mantissa exponent : Nat) (positiveM : 0 < mantissa),
      2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ 4 ∧
      Number.mul (encode draw) (Number.ofNat c) =
        (Float.Model.pack (.finite .positive mantissa ((draw.val.log2 : Int)-105+exponent) positiveM)).toBits ∧
      mantissa*2^exponent = roundedInteger (draw.val*c)*2^(52-draw.val.log2) := by
  obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
  have log := logarithm_bound positive draw.isLt
  have cbounds : 4 ≤ c ∧ c ≤ 6 := by rcases choice with rfl|rfl <;> decide
  let n := significand draw.val*c
  have large : 2^52 ≤ n := Nat.le_trans lo (Nat.le_mul_of_pos_right _ (by omega))
  have bounded : n < 2^56 := by
    have upper := Nat.mul_le_mul_left (significand draw.val) cbounds.2
    dsimp [n]
    omega
  have logUpper : n.log2 < 56 := (Nat.log2_lt (by omega)).mpr bounded
  obtain ⟨m,p,pos,lower,upper,places,shape,value⟩ :=
    normal_scaled_round_shape n 50 ((draw.val.log2 : Int)-105) large (by omega)
  refine ⟨m,p,pos,lower,upper,by omega,?_,?_⟩
  · unfold Number.mul Float.Model.mul
    rw [encode_normal_pack draw positive,
      normal_model_unpack _ _ _ lo hi (by omega) (by omega),native_small_choice_unpack c choice]
    simp only [UnpackedFloat.mul]
    change (Float.Model.pack (roundWithAccuracy Format.binary64 .positive
      (significand draw.val*(c*2^50)) (((draw.val.log2 : Int)-105)+(-50)) .exact)).toBits = _
    rw [←Nat.mul_assoc,show ((draw.val.log2 : Int)-105)+(-50) = (draw.val.log2 : Int)-105-(50 : Nat) by omega]
    exact congrArg (fun value => (Float.Model.pack value).toBits) shape
  · have scaled : n=(draw.val*c)*2^(52-draw.val.log2) := by dsimp [n,significand]; ac_rfl
    rw [scaled,rounded_scale _ _ (Nat.mul_pos positive (by omega))] at value
    exact value


theorem normal_negative_magnitude (m d : Nat) (pos : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (dpos : 0 < d) (dbound : d ≤ 1074) :
    magnitudeFraction (Float.Model.pack (.finite .positive m (-(d : Int)) pos)).toBits = (m,2^d) := by
  obtain ⟨ef,ff⟩ := normal_pack_fields_int m (-(d : Int)) pos lower upper (by omega) (by omega)
  unfold magnitudeFraction dyadic
  rw [ef,ff]
  have nonzero : (-(d : Int)+1075).toNat ≠ 0 := by omega
  have e : (((-(d : Int)+1075).toNat : Nat) : Int)-1075 = -(d : Int) := by omega
  simp only [beq_iff_eq,nonzero,↓reduceIte,Nat.add_sub_of_le lower,e,
    show ¬(0 : Int) ≤ -(d : Int) by omega,Int.neg_neg,Int.toNat_natCast]

theorem normal_negative_floor (m d : Nat) (pos : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (dpos : 0 < d) (dbound : d ≤ 1074) :
    Number.floor (Float.Model.pack (.finite .positive m (-(d : Int)) pos)).toBits =
      Number.ofNat (m/2^d) := by
  obtain ⟨finite,sign⟩ := normal_pack_finite_nonnegative_int m (-(d : Int)) pos lower upper (by omega) (by omega)
  have nonzero : isZero (Float.Model.pack (.finite .positive m (-(d : Int)) pos)).toBits = false := by
    unfold isZero
    rw [normal_pack_toNat_int _ _ _ lower upper (by omega) (by omega)]
    have exp : 1 ≤ (-(d : Int)+1075).toNat ∧ (-(d : Int)+1075).toNat ≤ 1074 := by omega
    have bound : (-(d : Int)+1075).toNat*2^52+(m-2^52) < 2^63 := by omega
    rw [Nat.mod_eq_of_lt bound]
    simp only [beq_eq_false_iff_ne]
    omega
  unfold Number.floor
  rw [finite,nonzero]
  simp only [Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte,sign,Bool.false_and,Nat.add_zero]
  rw [normal_negative_magnitude m d pos lower upper dpos dbound]
  exact signed_nonnegative_integer _

theorem native_small_choice (draw : Draw 53) (c : Nat) (choice : c=5 ∨ c=6) :
    Number.floor (Number.mul (encode draw) (Number.ofNat c)) =
      Number.ofNat (roundedInteger (draw.val*c)/2^53) := by
  by_cases zero : draw.val=0
  · have enc : encode draw=0 := by simp [encode,packed,zero]
    rw [enc,zero]
    rcases choice with rfl|rfl <;> rfl
  · have positive : 0 < draw.val := by omega
    have log := logarithm_bound positive draw.isLt
    obtain ⟨m,p,pos,lower,upper,pbound,shape,value⟩ := multiply_small_choice_shape draw c choice positive
    let d := 105-draw.val.log2-p
    have dpos : 0 < d := by dsimp [d]; omega
    have dbound : d ≤ 1074 := by dsimp [d]; omega
    have exponent : (draw.val.log2 : Int)-105+p = -(d : Int) := by dsimp [d]; omega
    rw [shape,exponent,normal_negative_floor m d pos lower upper dpos dbound]
    apply congrArg Number.ofNat
    have denominator : 2^d*2^p = 2^53*2^(52-draw.val.log2) := by
      rw [←Nat.pow_add,←Nat.pow_add]
      congr 1
      dsimp [d]
      omega
    calc
      m/2^d = (m*2^p)/(2^d*2^p) := (Nat.mul_div_mul_right _ _ (Nat.two_pow_pos p)).symm
      _ = (roundedInteger (draw.val*c)*2^(52-draw.val.log2))/(2^53*2^(52-draw.val.log2)) := by rw [value,denominator]
      _ = roundedInteger (draw.val*c)/2^53 := Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)


def denominator : Nat := 2^53
def projection (c index : Nat) : Nat := roundedInteger (index*c)/denominator

def boundary (c j : Nat) : Nat :=
  if c=5 ∧ j=0 then 0 else
  if c=5 ∧ j=1 then 1801439850948199 else
  if c=5 ∧ j=2 then 3602879701896397 else
  if c=5 ∧ j=3 then 5404319552844595 else
  if c=5 ∧ j=4 then 7205759403792794 else
  if c=5 ∧ j=5 then 9007199254740992 else
  if c=6 ∧ j=0 then 0 else
  if c=6 ∧ j=1 then 1501199875790166 else
  if c=6 ∧ j=2 then 3002399751580331 else
  if c=6 ∧ j=3 then 4503599627370496 else
  if c=6 ∧ j=4 then 6004799503160661 else
  if c=6 ∧ j=5 then 7505999378950826 else
  if c=6 ∧ j=6 then 9007199254740992 else
  0

theorem small_spacing (c index : Nat) (choice : c=5 ∨ c=6) (valid : index < denominator) :
    0 < integerSpacing (index*c) ∧ integerSpacing (index*c) ≤ 8 := by
  unfold integerSpacing
  split
  · decide +kernel
  · have nonzero : index*c ≠ 0 := by omega
    have bounded : index*c < 2^56 := by rcases choice with rfl|rfl <;> unfold denominator at valid <;> omega
    have log := (Nat.log2_lt nonzero).mpr bounded
    have exponent : (index*c).log2-52 ≤ 3 := by omega
    exact ⟨Nat.two_pow_pos _,Nat.pow_le_pow_right (by decide) exponent⟩

theorem small_rounding_error (c index : Nat) (choice : c=5 ∨ c=6) (valid : index < denominator) :
    roundedInteger (index*c) ≤ index*c+8 ∧ index*c ≤ roundedInteger (index*c)+8 := by
  have bound := small_spacing c index choice valid
  have error := CookieClicker.FullGame.StartupSeed.round_multiple_error (integerSpacing (index*c)) (index*c) bound.1
  unfold roundedInteger
  omega

private theorem threshold5_0 (index : Nat) (_valid : index < denominator) :
    projection 5 index < 0 ↔ index < boundary 5 0 := by
  simp [boundary]

private theorem threshold5_1 (index : Nat) (valid : index < denominator) :
    projection 5 index < 1 ↔ index < boundary 5 1 := by
  have error := small_rounding_error 5 index (by decide) valid
  rw [show boundary 5 1 = 1801439850948199 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*5) < 9007199254740992 ↔ index < 1801439850948199
  by_cases below : index*5+8 < 9007199254740992
  · omega
  by_cases above : 9007199254740992+8 < index*5
  · omega
  have choices : index=1801439850948197 ∨ index=1801439850948198 ∨ index=1801439850948199 ∨ index=1801439850948200 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 | h3 <;> subst index <;> decide +kernel

private theorem threshold5_2 (index : Nat) (valid : index < denominator) :
    projection 5 index < 2 ↔ index < boundary 5 2 := by
  have error := small_rounding_error 5 index (by decide) valid
  rw [show boundary 5 2 = 3602879701896397 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*5) < 18014398509481984 ↔ index < 3602879701896397
  by_cases below : index*5+8 < 18014398509481984
  · omega
  by_cases above : 18014398509481984+8 < index*5
  · omega
  have choices : index=3602879701896396 ∨ index=3602879701896397 ∨ index=3602879701896398 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold5_3 (index : Nat) (valid : index < denominator) :
    projection 5 index < 3 ↔ index < boundary 5 3 := by
  have error := small_rounding_error 5 index (by decide) valid
  rw [show boundary 5 3 = 5404319552844595 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*5) < 27021597764222976 ↔ index < 5404319552844595
  by_cases below : index*5+8 < 27021597764222976
  · omega
  by_cases above : 27021597764222976+8 < index*5
  · omega
  have choices : index=5404319552844594 ∨ index=5404319552844595 ∨ index=5404319552844596 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold5_4 (index : Nat) (valid : index < denominator) :
    projection 5 index < 4 ↔ index < boundary 5 4 := by
  have error := small_rounding_error 5 index (by decide) valid
  rw [show boundary 5 4 = 7205759403792794 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*5) < 36028797018963968 ↔ index < 7205759403792794
  by_cases below : index*5+8 < 36028797018963968
  · omega
  by_cases above : 36028797018963968+8 < index*5
  · omega
  have choices : index=7205759403792792 ∨ index=7205759403792793 ∨ index=7205759403792794 ∨ index=7205759403792795 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 | h3 <;> subst index <;> decide +kernel

private theorem threshold5_5 (index : Nat) (valid : index < denominator) :
    projection 5 index < 5 ↔ index < boundary 5 5 := by
  have error := small_rounding_error 5 index (by decide) valid
  rw [show boundary 5 5 = 9007199254740992 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*5) < 45035996273704960 ↔ index < 9007199254740992
  by_cases below : index*5+8 < 45035996273704960
  · omega
  by_cases above : 45035996273704960+8 < index*5
  · omega
  have choices : index=9007199254740991 := by unfold denominator at valid; omega
  rcases choices with h0 <;> subst index <;> decide +kernel

private theorem threshold6_0 (index : Nat) (_valid : index < denominator) :
    projection 6 index < 0 ↔ index < boundary 6 0 := by
  simp [boundary]

private theorem threshold6_1 (index : Nat) (valid : index < denominator) :
    projection 6 index < 1 ↔ index < boundary 6 1 := by
  have error := small_rounding_error 6 index (by decide) valid
  rw [show boundary 6 1 = 1501199875790166 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*6) < 9007199254740992 ↔ index < 1501199875790166
  by_cases below : index*6+8 < 9007199254740992
  · omega
  by_cases above : 9007199254740992+8 < index*6
  · omega
  have choices : index=1501199875790164 ∨ index=1501199875790165 ∨ index=1501199875790166 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold6_2 (index : Nat) (valid : index < denominator) :
    projection 6 index < 2 ↔ index < boundary 6 2 := by
  have error := small_rounding_error 6 index (by decide) valid
  rw [show boundary 6 2 = 3002399751580331 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*6) < 18014398509481984 ↔ index < 3002399751580331
  by_cases below : index*6+8 < 18014398509481984
  · omega
  by_cases above : 18014398509481984+8 < index*6
  · omega
  have choices : index=3002399751580330 ∨ index=3002399751580331 ∨ index=3002399751580332 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold6_3 (index : Nat) (valid : index < denominator) :
    projection 6 index < 3 ↔ index < boundary 6 3 := by
  have error := small_rounding_error 6 index (by decide) valid
  rw [show boundary 6 3 = 4503599627370496 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*6) < 27021597764222976 ↔ index < 4503599627370496
  by_cases below : index*6+8 < 27021597764222976
  · omega
  by_cases above : 27021597764222976+8 < index*6
  · omega
  have choices : index=4503599627370495 ∨ index=4503599627370496 ∨ index=4503599627370497 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold6_4 (index : Nat) (valid : index < denominator) :
    projection 6 index < 4 ↔ index < boundary 6 4 := by
  have error := small_rounding_error 6 index (by decide) valid
  rw [show boundary 6 4 = 6004799503160661 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*6) < 36028797018963968 ↔ index < 6004799503160661
  by_cases below : index*6+8 < 36028797018963968
  · omega
  by_cases above : 36028797018963968+8 < index*6
  · omega
  have choices : index=6004799503160660 ∨ index=6004799503160661 ∨ index=6004799503160662 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold6_5 (index : Nat) (valid : index < denominator) :
    projection 6 index < 5 ↔ index < boundary 6 5 := by
  have error := small_rounding_error 6 index (by decide) valid
  rw [show boundary 6 5 = 7505999378950826 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*6) < 45035996273704960 ↔ index < 7505999378950826
  by_cases below : index*6+8 < 45035996273704960
  · omega
  by_cases above : 45035996273704960+8 < index*6
  · omega
  have choices : index=7505999378950826 ∨ index=7505999378950827 ∨ index=7505999378950828 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold6_6 (index : Nat) (valid : index < denominator) :
    projection 6 index < 6 ↔ index < boundary 6 6 := by
  have error := small_rounding_error 6 index (by decide) valid
  rw [show boundary 6 6 = 9007199254740992 by decide +kernel]
  unfold projection
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (index*6) < 54043195528445952 ↔ index < 9007199254740992
  by_cases below : index*6+8 < 54043195528445952
  · omega
  by_cases above : 54043195528445952+8 < index*6
  · omega
  have choices : index=9007199254740991 := by unfold denominator at valid; omega
  rcases choices with h0 <;> subst index <;> decide +kernel

theorem threshold (c index j : Nat) (choice : c=5 ∨ c=6)
    (valid : index < denominator) (jbound : j ≤ c) :
    projection c index < j ↔ index < boundary c j := by
  rcases choice with rfl|rfl
  · have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
    rcases cases with h0 | h1 | h2 | h3 | h4 | h5
    · subst j; exact threshold5_0 index valid
    · subst j; exact threshold5_1 index valid
    · subst j; exact threshold5_2 index valid
    · subst j; exact threshold5_3 index valid
    · subst j; exact threshold5_4 index valid
    · subst j; exact threshold5_5 index valid
  · have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
    rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · subst j; exact threshold6_0 index valid
    · subst j; exact threshold6_1 index valid
    · subst j; exact threshold6_2 index valid
    · subst j; exact threshold6_3 index valid
    · subst j; exact threshold6_4 index valid
    · subst j; exact threshold6_5 index valid
    · subst j; exact threshold6_6 index valid

theorem projection_support (c index : Nat) (choice : c=5 ∨ c=6) (valid : index < denominator) :
    projection c index < c := by
  have endpoint : boundary c c=denominator := by rcases choice with rfl|rfl <;> decide +kernel
  have final := threshold c index c choice valid (by omega)
  exact final.mpr (by simpa [endpoint] using valid)

theorem projection_interval (c index j : Nat) (choice : c=5 ∨ c=6)
    (valid : index < denominator) (jbound : j < c) :
    projection c index = j ↔ boundary c j ≤ index ∧ index < boundary c (j+1) := by
  have lo := threshold c index j choice valid (by omega)
  have hi := threshold c index (j+1) choice valid (by omega)
  omega

theorem boundaries_ordered (c : Nat) (choice : c=5 ∨ c=6) :
    ∀ j : Fin c, boundary c j.val ≤ boundary c (j.val+1) ∧ boundary c (j.val+1) ≤ denominator := by
  rcases choice with rfl|rfl <;> decide +kernel

def bucketCount (c j : Nat) : Nat := boundary c (j+1)-boundary c j
def bucketMass (c j : Nat) : Rat := (bucketCount c j : Rat)/(denominator : Rat)
def projectionEvent (c j : Nat) (index : Nat) : Bool := decide (projection c index=j)

theorem projection_mass (c : Nat) (choice : c=5 ∨ c=6) (j : Fin c) :
    eventMass 53 (projectionEvent c j.val) = bucketMass c j.val := by
  have counts : (List.range (size 53)).countP (projectionEvent c j.val) =
      (List.range (size 53)).countP (interval (boundary c j.val) (boundary c (j.val+1))) := by
    apply List.countP_congr
    intro index member
    have valid : index < denominator := by simpa [size,denominator] using member
    simp only [projectionEvent,interval,projection_interval c index j.val choice valid j.isLt]
  unfold eventMass
  rw [counts]
  have bounds := boundaries_ordered c choice j
  rw [count_interval _ _ _ bounds.1]
  have upper : boundary c (j.val+1) ≤ size 53 := by simpa [size,denominator] using bounds.2
  rw [Nat.min_eq_right upper,Nat.min_eq_right (Nat.le_trans bounds.1 upper)]
  rfl

theorem golden_bucket_counts :
    (List.range 6).map (bucketCount 6) =
      [1501199875790166,1501199875790165,1501199875790165,1501199875790165,1501199875790165,1501199875790166] := by decide +kernel

theorem meaty_bucket_counts :
    (List.range 5).map (bucketCount 5) =
      [1801439850948199,1801439850948198,1801439850948198,1801439850948199,1801439850948198] := by decide +kernel

theorem golden_normalized : ((List.range 6).map (bucketMass 6)).foldl (· + ·) 0=1 := by decide +kernel
theorem meaty_normalized : ((List.range 5).map (bucketMass 5)).foldl (· + ·) 0=1 := by decide +kernel

def goldenExpectation : Rat := ((List.range 6).map (fun j => (j+2 : Nat)*bucketMass 6 j)).foldl (· + ·) 0
def meatyYield (j : Nat) : Nat := if j<2 then 0 else if j=2 then 1 else 2
def meatyExpectation : Rat := ((List.range 5).map (fun j => (meatyYield j : Rat)*bucketMass 5 j)).foldl (· + ·) 0

theorem golden_expectation : goldenExpectation=9/2 := by decide +kernel
theorem meaty_expectation : meatyExpectation=1 := by decide +kernel


theorem small_ofNat_injective (a b : Nat) (aBound : a<8) (bBound : b<8) :
    Number.ofNat a=Number.ofNat b ↔ a=b := by
  have all : ∀ x y : Fin 8, Number.ofNat x.val=Number.ofNat y.val ↔ x.val=y.val := by decide +kernel
  exact all ⟨a,aBound⟩ ⟨b,bBound⟩

def nativeBucketEvent (c j index : Nat) : Bool :=
  if valid : index < size 53 then
    decide (Number.floor (Number.mul (encode ⟨index,valid⟩) (Number.ofNat c))=Number.ofNat j)
  else false

theorem native_bucket_event (c j index : Nat) (choice : c=5 ∨ c=6)
    (jbound : j<c) (valid : index<denominator) :
    nativeBucketEvent c j index = projectionEvent c j index := by
  have cBound : c<8 := by rcases choice with rfl|rfl <;> decide
  have support := projection_support c index choice valid
  have bound : index < size 53 := valid
  simp only [nativeBucketEvent,bound,↓reduceDIte,native_small_choice _ c choice]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,projectionEvent,projection,denominator] at *
  have equivalent := small_ofNat_injective _ _ (Nat.lt_trans support cBound) (Nat.lt_trans jbound cBound)
  constructor
  · intro same
    exact decide_eq_true (equivalent.mp same)
  · intro same
    exact equivalent.mpr (of_decide_eq_true same)

theorem native_bucket_mass (c : Nat) (choice : c=5 ∨ c=6) (j : Fin c) :
    eventMass 53 (nativeBucketEvent c j.val) = bucketMass c j.val := by
  have counts : (List.range (size 53)).countP (nativeBucketEvent c j.val) =
      (List.range (size 53)).countP (projectionEvent c j.val) := by
    apply List.countP_congr
    intro index member
    have valid : index<denominator := by simpa [size,denominator] using member
    exact congrArg (· = true) (native_bucket_event c j.val index choice j.isLt valid) |>.to_iff
  unfold eventMass
  rw [counts]
  exact projection_mass c choice j

def nativeGoldenExpectation : Rat :=
  ((List.finRange 6).map (fun j => (j.val+2 : Nat)*eventMass 53 (nativeBucketEvent 6 j.val))).foldl (· + ·) 0

def nativeMeatyExpectation : Rat :=
  ((List.finRange 5).map (fun j => (meatyYield j.val : Rat)*eventMass 53 (nativeBucketEvent 5 j.val))).foldl (· + ·) 0

theorem native_golden_expectation : nativeGoldenExpectation=9/2 := by
  unfold nativeGoldenExpectation
  simp only [native_bucket_mass 6 (by decide)]
  decide +kernel

theorem native_meaty_expectation : nativeMeatyExpectation=1 := by
  unfold nativeMeatyExpectation
  simp only [native_bucket_mass 5 (by decide)]
  decide +kernel

theorem golden_native_masses :
    ((List.finRange 6).map (fun j => eventMass 53 (nativeBucketEvent 6 j.val))) =
      [1501199875790166/9007199254740992,1501199875790165/9007199254740992,
       1501199875790165/9007199254740992,1501199875790165/9007199254740992,
       1501199875790165/9007199254740992,1501199875790166/9007199254740992] := by
  simp only [native_bucket_mass 6 (by decide)]
  decide +kernel

theorem meaty_native_masses :
    ((List.finRange 5).map (fun j => eventMass 53 (nativeBucketEvent 5 j.val))) =
      [1801439850948199/9007199254740992,1801439850948198/9007199254740992,
       1801439850948198/9007199254740992,1801439850948199/9007199254740992,
       1801439850948198/9007199254740992] := by
  simp only [native_bucket_mass 5 (by decide)]
  decide +kernel


def nativeMeatyZero (index : Nat) : Bool := nativeBucketEvent 5 0 index || nativeBucketEvent 5 1 index
def nativeMeatyOne (index : Nat) : Bool := nativeBucketEvent 5 2 index
def nativeMeatyTwo (index : Nat) : Bool := nativeBucketEvent 5 3 index || nativeBucketEvent 5 4 index

theorem native_meaty_zero_event : nativeMeatyZero=interval 0 3602879701896397 := by
  funext index
  by_cases valid : index<denominator
  · rw [nativeMeatyZero,native_bucket_event 5 0 index (by decide) (by decide) valid,
      native_bucket_event 5 1 index (by decide) (by decide) valid]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,projectionEvent,interval,decide_eq_true_eq]
    have cut := threshold5_2 index valid
    have boundaryValue : boundary 5 2=3602879701896397 := by decide +kernel
    rw [boundaryValue] at cut
    omega
  · have invalid : ¬index<size 53 := valid
    have above : 3602879701896397 ≤ index := by unfold denominator at valid; omega
    simp [nativeMeatyZero,nativeBucketEvent,invalid,interval,show ¬index<3602879701896397 by omega]

theorem native_meaty_one_event : nativeMeatyOne=interval 3602879701896397 5404319552844595 := by
  funext index
  by_cases valid : index<denominator
  · rw [nativeMeatyOne,native_bucket_event 5 2 index (by decide) (by decide) valid]
    apply Bool.eq_iff_iff.mpr
    simp only [projectionEvent,interval,decide_eq_true_eq]
    have cut := projection_interval 5 index 2 (by decide) valid (by decide)
    have lo : boundary 5 2=3602879701896397 := by decide +kernel
    have hi : boundary 5 3=5404319552844595 := by decide +kernel
    simpa only [lo,hi] using cut
  · have invalid : ¬index<size 53 := valid
    have above : 5404319552844595 ≤ index := by unfold denominator at valid; omega
    simp [nativeMeatyOne,nativeBucketEvent,invalid,interval,show ¬index<5404319552844595 by omega]

theorem native_meaty_two_event : nativeMeatyTwo=interval 5404319552844595 9007199254740992 := by
  funext index
  by_cases valid : index<denominator
  · rw [nativeMeatyTwo,native_bucket_event 5 3 index (by decide) (by decide) valid,
      native_bucket_event 5 4 index (by decide) (by decide) valid]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,projectionEvent,interval,decide_eq_true_eq]
    have cut := threshold5_3 index valid
    have support := projection_support 5 index (by decide) valid
    have boundaryValue : boundary 5 3=5404319552844595 := by decide +kernel
    rw [boundaryValue] at cut
    unfold denominator at valid
    omega
  · have invalid : ¬index<size 53 := valid
    have above : 9007199254740992 ≤ index := by unfold denominator at valid; omega
    simp [nativeMeatyTwo,nativeBucketEvent,invalid,interval,show ¬index<9007199254740992 by omega]

theorem native_meaty_yield_masses :
    eventMass 53 nativeMeatyZero = 3602879701896397/9007199254740992 ∧
    eventMass 53 nativeMeatyOne = 1801439850948198/9007199254740992 ∧
    eventMass 53 nativeMeatyTwo = 3602879701896397/9007199254740992 := by
  rw [native_meaty_zero_event,native_meaty_one_event,native_meaty_two_event]
  rw [interval_mass 53 0 3602879701896397 (by decide +kernel) (by decide +kernel),
    interval_mass 53 3602879701896397 5404319552844595 (by decide +kernel) (by decide +kernel),
    interval_mass 53 5404319552844595 9007199254740992 (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem golden_not_uniform : bucketMass 6 0 ≠ 1/6 := by decide +kernel

theorem meaty_zero_not_two_fifths : eventMass 53 nativeMeatyZero ≠ 2/5 := by
  rw [native_meaty_yield_masses.1]
  decide +kernel


def payoutBranch : Stmt := match LumpSyntax.harvestLumpsBody with
  | .block body => (body[3]?).getD .empty
  | _ => .empty

def uncommonBranch : Stmt := match payoutBranch with
  | .ifThenElse _ _ (some (.ifThenElse _ _ (some tail))) => tail
  | _ => .empty

def multipliedChoice : Stmt → Expr
  | .expression (.assignment .multiply (.identifier "total") expression) => expression
  | _ => .literal .null

def goldenSourceChoice : Expr := match uncommonBranch with
  | .ifThenElse _ (.block body) _ => multipliedChoice ((body[0]?).getD .empty)
  | _ => .literal .null

def meatySourceChoice : Expr := match uncommonBranch with
  | .ifThenElse _ _ (some (.ifThenElse _ body _)) => multipliedChoice body
  | _ => .literal .null

def goldenSourceValues : List Nat := [2,3,4,5,6,7]
def meatySourceValues : List Nat := [0,0,1,2,2]

theorem golden_source_choices : goldenSourceChoice = .call (.identifier "choose")
    [.array (goldenSourceValues.map (fun value => some (.literal (.number (Number.ofNat value)))))] := rfl

theorem meaty_source_choices : meatySourceChoice = .call (.identifier "choose")
    [.array (meatySourceValues.map (fun value => some (.literal (.number (Number.ofNat value)))))] := rfl

theorem golden_source_values : ∀ j : Fin 6, goldenSourceValues[j.val]?=some (j.val+2) := by decide +kernel

theorem meaty_source_values : ∀ j : Fin 5, meatySourceValues[j.val]?=some (meatyYield j.val) := by decide +kernel

end CookieClicker.JavaScript.RandomSmallChoiceBridge

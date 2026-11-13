import CookieClicker.JavaScriptNaturalArithmetic

/-! Exact JavaScript remainder on natural operands below 2^52.
The proof follows the actual bit-level remainder and logical binary64 rounding.
It does not enumerate operand pairs. -/
namespace CookieClicker.JavaScript.NaturalRemainder
open Float.Model Float.Model.UnpackedFloat RoundingBridge NaturalArithmetic
open DyadicArithmeticBridge CookieClicker.FullGame.GodzamokRounding
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096

theorem normal_dyadic (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53)
    (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    Number.dyadic (Float.Model.pack (.finite .positive m e positive)).toBits = (m,e) := by
  obtain ⟨exponentField,fraction⟩ :=
    normal_pack_fields_int m e positive lower upper expLower expUpper
  have nonzero : (e+1075).toNat ≠ 0 := by omega
  have cancel : ((e+1075).toNat : Int)-1075=e := by omega
  simp only [Number.dyadic,exponentField,fraction,beq_iff_eq,nonzero,↓reduceIte,
    cancel,Nat.add_sub_of_le lower]

theorem normal_flags (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53)
    (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    let bits := (Float.Model.pack (.finite .positive m e positive)).toBits
    Number.isNaN bits=false ∧ Number.isInfinite bits=false ∧
      Number.isZero bits=false ∧ Number.signBit bits=false := by
  obtain ⟨exponentField,_⟩ :=
    normal_pack_fields_int m e positive lower upper expLower expUpper
  have finiteExponent : (e+1075).toNat ≠ 2047 := by omega
  have value := normal_pack_toNat_int m e positive lower upper expLower expUpper
  have positiveBits : 0 < (Float.Model.pack (.finite .positive m e positive)).toBits.toNat := by
    rw [value]; omega
  have smallBits : (Float.Model.pack (.finite .positive m e positive)).toBits.toNat < 2^63 := by
    rw [value]; omega
  dsimp only
  refine ⟨?_,?_,?_,(normal_pack_finite_nonnegative_int m e positive lower upper expLower expUpper).2⟩
  · simp [Number.isNaN,exponentField,finiteExponent]
  · simp [Number.isInfinite,exponentField,finiteExponent]
  · simp [Number.isZero,Nat.mod_eq_of_lt smallBits,Nat.ne_of_gt positiveBits]

theorem shifted_zero (places : Nat) :
    Nat.repeat ExtendedMantissa.shiftRightOne places ⟨0,false,false⟩ = ⟨0,false,false⟩ := by
  induction places with
  | zero => rfl
  | succ places ih => rw [Nat.repeat,ih]; rfl

theorem shift_zero (e target : Int) :
    (shiftToExponent 0 e .exact target).1=⟨0,false,false⟩ := by
  change Nat.repeat ExtendedMantissa.shiftRightOne _ ⟨0,false,false⟩ = _
  exact shifted_zero _

theorem round_zero (spec : Format) (sign : Sign) (e : Int) :
    round spec sign 0 e = .zero sign := by
  simp only [round,decreaseExponent,Nat.zero_shiftLeft]
  unfold roundWithAccuracy
  simp only [shiftToTargetExponent,shift_zero,ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy,Accuracy.roundToNearestEven,↓reduceDIte]

theorem scaled_round (n k : Nat) :
    round Format.binary64 .positive (n*2^k) (-(k:Int)) =
      round Format.binary64 .positive n 0 := by
  by_cases zero : n=0
  · subst n; simp [round_zero]
  · exact native_negative_scaled_round_is_integer_round n k (by omega)

theorem native_remainder_positive (a b : Nat) (aPos : 0<a) (bPos : 0<b)
    (aSmall : a<2^52) (bSmall : b<2^52) :
    Number.remainder (Number.ofNat a) (Number.ofNat b)=Number.ofNat (a%b) := by
  obtain ⟨ma,ea,pa,la,ua,ela,eua,sha,ra⟩ := native_small_integer_round_shape a aPos aSmall
  obtain ⟨mb,eb,pb,lb,ub,elb,eub,shb,rb⟩ := native_small_integer_round_shape b bPos bSmall
  obtain ⟨na,ia,za,sa⟩ := normal_flags ma ea pa la ua ela (by omega)
  obtain ⟨nb,ib,zb,_⟩ := normal_flags mb eb pb lb ub elb (by omega)
  let common := min ea eb
  have nonpositive : common ≤ 0 := by dsimp only [common]; omega
  have first := aligned_integer_value ma a ea common pa (Int.min_le_left _ _) nonpositive ra
  have second := aligned_integer_value mb b eb common pb (Int.min_le_right _ _) nonpositive rb
  have exponent : common = -((-common).toNat : Int) := by omega
  rw [ofNat_encoding a,ofNat_encoding b,sha,shb]
  simp only [Number.remainder,na,nb,ia,ib,za,zb,Bool.false_or,Bool.false_eq_true,↓reduceIte,
    normal_dyadic ma ea pa la ua ela (by omega),
    normal_dyadic mb eb pb lb ub elb (by omega)]
  change Number.ofDyadic _ ((ma*2^(ea-common).toNat)%(mb*2^(eb-common).toNat)) common = _
  rw [first,second,Nat.mul_mod_mul_right]
  simp only [Number.ofDyadic,sa,Bool.false_eq_true,↓reduceIte]
  have native := scaled_round (a%b) (-common).toNat
  rw [← exponent] at native
  rw [native,← ofNat_encoding]

theorem native_remainder_zero (b : Nat) (bPos : 0<b) (bSmall : b<2^52) :
    Number.remainder (Number.ofNat 0) (Number.ofNat b)=Number.ofNat 0 := by
  obtain ⟨mb,eb,pb,lb,ub,elb,eub,shb,_⟩ := native_small_integer_round_shape b bPos bSmall
  obtain ⟨nb,ib,zb,_⟩ := normal_flags mb eb pb lb ub elb (by omega)
  rw [ofNat_encoding b,shb]
  simp only [Number.remainder,nb,ib,zb]
  rfl

theorem native_remainder (a b : Nat) (aSmall : a<2^52)
    (bPos : 0<b) (bSmall : b<2^52) :
    Number.remainder (Number.ofNat a) (Number.ofNat b)=Number.ofNat (a%b) := by
  by_cases zero : a=0
  · subst a; simpa using native_remainder_zero b bPos bSmall
  · exact native_remainder_positive a b (by omega) bPos aSmall bSmall

theorem byte_remainder (a b : Nat) (aSmall : a<256) (bPos : 0<b) (bSmall : b≤256) :
    Number.remainder (Number.ofNat a) (Number.ofNat b)=Number.ofNat (a%b) :=
  native_remainder a b (by omega) bPos (by omega)

end CookieClicker.JavaScript.NaturalRemainder

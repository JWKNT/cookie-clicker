import CookieClicker.JavaScriptNumber
import CookieClicker.JavaScriptRandom
import CookieClicker.GodzamokRounding

/-! Correspondence between the actual logical Float residual-bit operations
and the integer nearest-even projection. Packing, normalization, arithmetic
composition and source-counter invariants require their own bridge results.
-/
namespace CookieClicker.JavaScript.RoundingBridge
open Float.Model.UnpackedFloat CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

def shifted (n places : Nat) : ExtendedMantissa :=
  Nat.repeat ExtendedMantissa.shiftRightOne places ⟨n,false,false⟩

theorem shifted_is_native (n places : Nat) :
    shifted n places = (ExtendedMantissa.ofMantissaAndAccuracy n .exact >>> places) := rfl

theorem shifted_fields (n places : Nat) :
    (shifted n (places + 1)).mantissa = n / 2^(places + 1) ∧
    (shifted n (places + 1)).roundBit = (n / 2^places % 2 != 0) ∧
    (shifted n (places + 1)).stickyBit = (n % 2^places != 0) := by
  induction places with
  | zero => simp [shifted, Nat.repeat, ExtendedMantissa.shiftRightOne, Nat.mod_one]
  | succ places ih =>
    change (shifted n (places + 1)).mantissa / 2 = n / 2^(places + 1 + 1) ∧
      ((shifted n (places + 1)).mantissa % 2 != 0) = (n / 2^(places + 1) % 2 != 0) ∧
      ((shifted n (places + 1)).roundBit || (shifted n (places + 1)).stickyBit) =
        (n % 2^(places + 1) != 0)
    rw [ih.1, ih.2.1, ih.2.2]
    constructor
    · simp only [Nat.div_div_eq_div_mul, Nat.pow_succ]
    · refine ⟨rfl, ?_⟩
      have positive := Nat.two_pow_pos places
      have highBound := Nat.mod_lt (n / 2^places) (by decide : 0 < 2)
      rw [Nat.mod_pow_succ]
      by_cases high : n / 2^places % 2 = 0
      · simp [high]
      · have highOne : n / 2^places % 2 = 1 := by omega
        simp [highOne]

theorem shifted_rounding_zero (n : Nat) :
    (shifted n 0).roundedMantissa = n := rfl

theorem shifted_rounding (n places : Nat) :
    (shifted n places).roundedMantissa * 2^places = roundMultiple (2^places) n := by
  cases places with
  | zero => simp [shifted_rounding_zero, unit_spacing_exact]
  | succ places =>
    obtain ⟨mantissa,roundBit,stickyBit⟩ := shifted_fields n places
    have positive := Nat.two_pow_pos places
    have lowBound := Nat.mod_lt n positive
    have highBound := Nat.mod_lt (n / 2^places) (by decide : 0 < 2)
    have remainder := Nat.mod_pow_succ (x := n) (b := 2) (k := places)
    have shape : shifted n (places + 1) =
        ⟨n / 2^(places+1), n / 2^places % 2 != 0, n % 2^places != 0⟩ := by
      cases h : shifted n (places + 1) with
      | mk m r s =>
        simp only [h] at mantissa roundBit stickyBit
        cases mantissa
        cases roundBit
        cases stickyBit
        rfl
    rw [shape]
    unfold ExtendedMantissa.roundedMantissa ExtendedMantissa.accuracy
    unfold roundMultiple
    by_cases high : n / 2^places % 2 = 0
    · have smaller : 2 * (n % 2^(places+1)) < 2^(places+1) := by
        rw [remainder, high, Nat.mul_zero, Nat.add_zero, Nat.pow_succ]
        omega
      have highBit : (n / 2^places % 2 != 0) = false := by simp [high]
      rw [highBit]
      cases lowBit : (n % 2^places != 0) <;>
        simp [Accuracy.roundToNearestEven,
          show ¬2^(places+1) < 2*(n % 2^(places+1)) by omega,
          show 2^(places+1) ≠ 2*(n % 2^(places+1)) by omega]
    · have highOne : n / 2^places % 2 = 1 := by omega
      have highBit : (n / 2^places % 2 != 0) = true := by simp [highOne]
      rw [highBit]
      by_cases low : n % 2^places = 0
      · have halfway : 2 * (n % 2^(places+1)) = 2^(places+1) := by
          rw [remainder, highOne, low, Nat.zero_add, Nat.mul_one, Nat.pow_succ]
          omega
        have parity := Nat.mod_lt (n / 2^(places+1)) (by decide : 0 < 2)
        by_cases odd : n / 2^(places+1) % 2 = 1
        · simp [low,Accuracy.roundToNearestEven,halfway,odd]
        · have even : n / 2^(places+1) % 2 = 0 := by omega
          simp [low,Accuracy.roundToNearestEven,halfway,even]
      · have above : 2^(places+1) < 2 * (n % 2^(places+1)) := by
          rw [remainder,highOne,Nat.mul_one,Nat.pow_succ]
          omega
        have lowBit : (n % 2^places != 0) = true := by exact bne_iff_ne.mpr low
        rw [lowBit]
        simp [Accuracy.roundToNearestEven,above]

theorem native_integer_target_exponent (n : Nat) :
    Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent n 0) =
      (n.log2 : Int) - 52 := by
  simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
    Float.Model.Format.mantissaBits, Float.Model.Format.minExponent]
  omega

theorem native_integer_shift (n : Nat) :
    shiftToTargetExponent Float.Model.Format.binary64 n 0 .exact =
      (shifted n (n.log2 - 52), ((n.log2 - 52 : Nat) : Int)) := by
  unfold shiftToTargetExponent
  rw [native_integer_target_exponent]
  have gap : ((n.log2 : Int) - 52 - 0).toNat = n.log2 - 52 := by omega
  simp only [shiftToExponent, gap, Int.zero_add]
  rfl

theorem integer_spacing_matches_native (n : Nat) :
    integerSpacing n = 2^(n.log2 - 52) := by
  unfold integerSpacing
  split
  · rename_i below
    by_cases zero : n = 0
    · subst n; decide
    · have logarithm : n.log2 < 53 := (Nat.log2_lt zero).mpr below
      have small : n.log2 - 52 = 0 := by omega
      simp [small]
  · rfl

/-- The first rounding phase used by Float.Model is exactly the nearest-even
integer projection, for every natural input and every bit length. -/
theorem native_first_rounding_equals_projection (n : Nat) :
    let pair := shiftToTargetExponent Float.Model.Format.binary64 n 0 .exact
    pair.1.roundedMantissa * 2^pair.2.toNat = roundedInteger n := by
  rw [native_integer_shift]
  simpa [roundedInteger, integer_spacing_matches_native] using shifted_rounding n (n.log2 - 52)

theorem residual_rounding_bound (em : ExtendedMantissa) :
    em.roundedMantissa ≤ em.mantissa + 1 := by
  cases em with
  | mk mantissa roundBit stickyBit =>
    have parity := Nat.mod_lt mantissa (by decide : 0 < 2)
    cases roundBit <;> cases stickyBit <;>
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
        Accuracy.roundToNearestEven] <;> omega

theorem shifted_mantissa (n places : Nat) :
    (shifted n places).mantissa = n / 2^places := by
  cases places with
  | zero => simp [shifted, Nat.repeat]
  | succ places => exact (shifted_fields n places).1

theorem native_rounded_mantissa_bound (n : Nat) :
    (shifted n (n.log2 - 52)).roundedMantissa ≤ 2^53 := by
  by_cases below : n < 2^53
  · have logarithm : n.log2 ≤ 52 := by
      by_cases zero : n = 0
      · subst n; decide
      · have h := (Nat.log2_lt zero).mpr below
        omega
    have places : n.log2 - 52 = 0 := by omega
    rw [places, shifted_rounding_zero]
    omega
  · have nonzero : n ≠ 0 := by omega
    have logLower : 53 ≤ n.log2 := by
      apply Nat.le_of_not_gt
      intro hlog
      exact below ((Nat.log2_lt nonzero).mp hlog)
    have upper : n < 2^(n.log2+1) := ((Nat.log2_eq_iff nonzero).mp rfl).2
    have power : 2^(n.log2-52) * 2^53 = 2^(n.log2+1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have quotient : n / 2^(n.log2-52) < 2^53 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by simpa [Nat.mul_comm, power] using upper)
    have rounded := residual_rounding_bound (shifted n (n.log2-52))
    rw [shifted_mantissa] at rounded
    omega

/-- The second native shift only normalizes a possible carry. It changes no
integer value once the first rounded mantissa has at most 54 bits. -/
theorem native_carry_shift (mantissa exponent : Nat) (bounded : mantissa ≤ 2^53) :
    let pair := shiftToTargetExponent Float.Model.Format.binary64 mantissa exponent .exact
    0 ≤ pair.2 ∧ pair.1.mantissa * 2^pair.2.toNat = mantissa * 2^exponent := by
  by_cases below : mantissa < 2^53
  · have logarithm : mantissa.log2 ≤ 52 := by
      by_cases zero : mantissa = 0
      · subst mantissa; decide
      · have h := (Nat.log2_lt zero).mpr below
        omega
    have target : Float.Model.Format.binary64.targetExponent
        (Float.Model.totalExponent mantissa exponent) ≤ (exponent : Int) := by
      simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
        Float.Model.Format.mantissaBits, Float.Model.Format.minExponent]
      omega
    have shift : (Float.Model.Format.binary64.targetExponent
        (Float.Model.totalExponent mantissa exponent) - (exponent : Int)).toNat = 0 := by omega
    simp [shiftToTargetExponent, shiftToExponent, shift,
      ExtendedMantissa.ofMantissaAndAccuracy, HShiftRight.hShiftRight, Nat.repeat]
  · have same : mantissa = 2^53 := by omega
    subst mantissa
    have logarithm : (2^53 : Nat).log2 = 53 := by decide +kernel
    have target : Float.Model.Format.binary64.targetExponent
        (Float.Model.totalExponent (2^53) exponent) = (exponent : Int) + 1 := by
      simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
        Float.Model.Format.mantissaBits, Float.Model.Format.minExponent, logarithm]
      omega
    simp only [shiftToTargetExponent, target, shiftToExponent]
    have shift : ((exponent : Int) + 1 - exponent).toNat = 1 := by omega
    rw [shift]
    change 0 ≤ (exponent : Int) + 1 ∧ 2^52 * 2^((exponent : Int)+1).toNat = 2^53 * 2^exponent
    have cast : ((exponent : Int)+1).toNat = exponent+1 := by omega
    rw [cast]
    constructor
    · omega
    · rw [Nat.pow_succ]
      omega

/-- Exact dyadic interpretation of a nonnegative unpacked integer. -/
def RepresentsNat : Float.Model.UnpackedFloat → Nat → Prop
  | .zero .positive, n => n = 0
  | .finite .positive mantissa exponent _, n =>
    if 0 ≤ exponent then mantissa * 2^exponent.toNat = n
    else mantissa = n * 2^(-exponent).toNat
  | _, _ => False

theorem native_integer_roundWithAccuracy (n : Nat) :
    RepresentsNat (roundWithAccuracy Float.Model.Format.binary64 .positive n 0 .exact)
      (roundedInteger n) := by
  let places := n.log2 - 52
  let mantissa := (shifted n places).roundedMantissa
  let pair := shiftToTargetExponent Float.Model.Format.binary64 mantissa places .exact
  have bound : mantissa ≤ 2^53 := native_rounded_mantissa_bound n
  have carry := native_carry_shift mantissa places bound
  change 0 ≤ pair.2 ∧ pair.1.mantissa * 2^pair.2.toNat = mantissa * 2^places at carry
  have first : mantissa * 2^places = roundedInteger n := by
    simpa [mantissa, places, roundedInteger, integer_spacing_matches_native] using shifted_rounding n places
  have value : pair.1.mantissa * 2^pair.2.toNat = roundedInteger n := carry.2.trans first
  unfold roundWithAccuracy
  rw [native_integer_shift]
  change RepresentsNat
    (if h : pair.1.mantissa = 0 then .zero .positive
      else .finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) (roundedInteger n)
  split
  · rename_i zero
    change roundedInteger n = 0
    simpa [zero] using value.symm
  · simp only [RepresentsNat, if_pos carry.1]
    exact value

/-- For integer inputs in these binades, native normalization has no left
shift. This result covers the counter barriers, before packing to 64 bits. -/
theorem native_normal_integer_round (n : Nat) (large : 2^52 ≤ n) :
    RepresentsNat (round Float.Model.Format.binary64 .positive n 0) (roundedInteger n) := by
  have nonzero : n ≠ 0 := by omega
  have lower : 52 ≤ n.log2 := by
    apply Nat.le_of_not_gt
    intro small
    have h := (Nat.log2_lt nonzero).mp small
    omega
  have shift : (0 - ((n.log2 : Int) - 52)).toNat = 0 := by omega
  have decrease : decreaseExponent n 0 ((n.log2 : Int) - 52) = (n,0) := by
    unfold decreaseExponent
    rw [shift]
    simp
  unfold round
  rw [native_integer_target_exponent]
  dsimp only
  rw [decrease]
  exact native_integer_roundWithAccuracy n

theorem native_large_integer_round (n : Nat) (large : 2^53 ≤ n) :
    RepresentsNat (round Float.Model.Format.binary64 .positive n 0) (roundedInteger n) :=
  native_normal_integer_round n (by omega)

/-- Packing a positive normal integer does not change its dyadic value, as
long as its exponent is below the binary64 overflow boundary. -/
theorem normal_pack_toNat (mantissa exponent : Nat) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53) (finite : exponent ≤ 971) :
    (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits.toNat =
      (exponent + 1075) * 2^52 + (mantissa - 2^52) := by
  have logarithm : mantissa.log2 = 52 :=
    (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower,upper⟩
  have biased : ((exponent : Int) + 1023 + 52).toNat = exponent + 1075 := by omega
  have safe : ¬ 2^11 ≤ exponent + 1075 + 1 := by omega
  have exponentSmall : exponent + 1075 < 2^11 := by omega
  have remainder : mantissa % 2^52 = mantissa - 2^52 := by omega
  change (pack Float.Model.Format.binary64
    (.finite .positive mantissa exponent positive)).toNat = _
  change (if 2^11 ≤ ((exponent : Int)+1023+52).toNat + 1 then
      packedInfinity Float.Model.Format.binary64 .positive
    else if mantissa.log2+1=53 then
      packComponents Float.Model.Format.binary64 .positive
        (BitVec.ofNat 11 ((exponent : Int)+1023+52).toNat) (BitVec.ofNat 52 mantissa)
    else packComponents Float.Model.Format.binary64 .positive 0 (BitVec.ofNat 52 mantissa)).toNat = _
  rw [biased, if_neg safe, logarithm]
  simp only [↓reduceIte, packComponents, Sign.toBitVec, BitVec.toNat_append,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt exponentSmall, remainder]
  simp only [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : mantissa - 2^52 < 2^52), Nat.shiftLeft_eq]

theorem normal_pack_fields (mantissa exponent : Nat) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53) (finite : exponent ≤ 971) :
    let bits := (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits
    Number.exponentField bits = exponent + 1075 ∧
      Number.fraction bits = mantissa - 2^52 := by
  have rem : mantissa - 2^52 < 2^52 := by omega
  dsimp only
  simp only [Number.exponentField, Number.fraction,
    normal_pack_toNat mantissa exponent positive lower upper finite]
  constructor
  · rw [Nat.add_comm ((exponent+1075)*2^52),
      Nat.add_mul_div_right _ _ (by decide : 0 < 2^52),
      Nat.div_eq_of_lt rem, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · simp [Nat.add_mod, Nat.mod_eq_of_lt rem]

theorem normal_pack_finite_nonnegative (mantissa exponent : Nat) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53) (finite : exponent ≤ 971) :
    let bits := (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false := by
  dsimp only
  constructor
  · rw [Number.isFinite, (normal_pack_fields mantissa exponent positive lower upper finite).1]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [Number.signBit, normal_pack_toNat mantissa exponent positive lower upper finite]
    simp only [decide_eq_false_iff_not]
    omega

theorem normal_pack_magnitude (mantissa exponent : Nat) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53) (finite : exponent ≤ 971) :
    Number.magnitudeFraction
      (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits =
        (mantissa * 2^exponent, 1) := by
  obtain ⟨exponentField,fraction⟩ := normal_pack_fields mantissa exponent positive lower upper finite
  have nonzero : exponent + 1075 ≠ 0 := by omega
  have cancel : (((exponent+1075 : Nat) : Int) - 1075) = exponent := by omega
  simp only [Number.magnitudeFraction, Number.dyadic, exponentField, fraction,
    beq_iff_eq, nonzero, ↓reduceIte, cancel, Int.natCast_nonneg,
    Int.toNat_natCast, Nat.add_sub_of_le lower]

theorem unpackSign_components {spec : Float.Model.Format} {sign exponent mantissa} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have zero : i = 0 := by omega
  subst i
  have first : ¬ spec.mantissaBitsWithoutImplicit + spec.exponentBits < spec.mantissaBitsWithoutImplicit := by omega
  simp [unpackSign, packComponents, BitVec.getLsbD_append, first,
    BitVec.getLsbD_eq_getElem, BitVec.getElem_append]

theorem normal_pack_components (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    pack Float.Model.Format.binary64 (.finite .positive mantissa exponent positive) =
      packComponents Float.Model.Format.binary64 .positive
        (BitVec.ofNat 11 (exponent + 1075).toNat) (BitVec.ofNat 52 mantissa) := by
  have logarithm : mantissa.log2 = 52 :=
    (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower,upper⟩
  have biased : (exponent + 1023 + 52).toNat = (exponent + 1075).toNat := by omega
  have safe : ¬ 2^11 ≤ (exponent + 1075).toNat + 1 := by omega
  change (if 2^11 ≤ (exponent + 1023 + 52).toNat + 1 then
      packedInfinity Float.Model.Format.binary64 .positive
    else if mantissa.log2+1=53 then
      packComponents Float.Model.Format.binary64 .positive
        (BitVec.ofNat 11 (exponent + 1023 + 52).toNat) (BitVec.ofNat 52 mantissa)
    else packComponents Float.Model.Format.binary64 .positive 0 (BitVec.ofNat 52 mantissa)) = _
  rw [biased, if_neg safe, logarithm]
  rfl

theorem normal_unpack_pack (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    (Float.Model.pack (.finite .positive mantissa exponent positive)).unpack =
      .finite .positive mantissa exponent positive := by
  have biasedBound : (exponent + 1075).toNat < 2^11 := by omega
  have biasedPositive : 0 < (exponent + 1075).toNat := by omega
  have biasedNotAll : (exponent + 1075).toNat ≠ 2047 := by omega
  have exponentNotZero : BitVec.ofNat 11 (exponent + 1075).toNat ≠ 0#11 := by
    intro h
    have v := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt biasedBound] at v
    change (exponent + 1075).toNat = 0 at v
    omega
  have exponentNotAll : BitVec.ofNat 11 (exponent + 1075).toNat ≠ -1#11 := by
    intro h
    have v := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt biasedBound] at v
    have allBits : ((-1#11).toNat) = 2047 := by decide +kernel
    rw [allBits] at v
    exact biasedNotAll v
  have remainder : mantissa % 2^52 = mantissa - 2^52 := by omega
  change unpack Float.Model.Format.binary64
    (pack Float.Model.Format.binary64 (.finite .positive mantissa exponent positive)) = _
  rw [normal_pack_components mantissa exponent positive lower upper expLower expUpper]
  simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_components, Sign.ofBitVec, Sign.toBitVec, ↓reduceIte,
    exponentNotAll, exponentNotZero, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt biasedBound]
  have expCancel : ((exponent + 1075).toNat : Int) - (1023 + 52) = exponent := by omega
  have mantissaRecover : ((1#1 ++ BitVec.ofNat 52 mantissa) : BitVec 53).toNat = mantissa := by
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat, remainder]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : mantissa - 2^52 < 2^52)]
    simp only [Nat.shiftLeft_eq]
    omega
  simp only [mantissaRecover]
  change Float.Model.UnpackedFloat.finite .positive mantissa
    (((exponent + 1075).toNat : Int) - (1023+52)) _ = _
  simp only [expCancel]

theorem normal_model_pack (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    Number.model (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits =
      Float.Model.pack (.finite .positive mantissa exponent positive) := by
  change Float.Model.pack (Float.Model.pack (.finite .positive mantissa exponent positive)).unpack = _
  rw [normal_unpack_pack mantissa exponent positive lower upper expLower expUpper]

theorem normal_model_unpack (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    (Number.model (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits).unpack =
      .finite .positive mantissa exponent positive := by
  rw [normal_model_pack mantissa exponent positive lower upper expLower expUpper,
    normal_unpack_pack mantissa exponent positive lower upper expLower expUpper]

theorem normal_pack_toNat_int (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits.toNat =
      (exponent + 1075).toNat * 2^52 + (mantissa - 2^52) := by
  have biasedBound : (exponent + 1075).toNat < 2^11 := by omega
  have remainder : mantissa % 2^52 = mantissa - 2^52 := by omega
  change (pack Float.Model.Format.binary64 (.finite .positive mantissa exponent positive)).toNat = _
  rw [normal_pack_components mantissa exponent positive lower upper expLower expUpper]
  simp only [packComponents, Sign.toBitVec, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt biasedBound, remainder, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : mantissa - 2^52 < 2^52), Nat.shiftLeft_eq]

theorem normal_pack_fields_int (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    let bits := (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits
    Number.exponentField bits = (exponent + 1075).toNat ∧
      Number.fraction bits = mantissa - 2^52 := by
  have rem : mantissa - 2^52 < 2^52 := by omega
  dsimp only
  simp only [Number.exponentField, Number.fraction,
    normal_pack_toNat_int mantissa exponent positive lower upper expLower expUpper]
  constructor
  · rw [Nat.add_comm ((exponent+1075).toNat*2^52),
      Nat.add_mul_div_right _ _ (by decide : 0 < 2^52),
      Nat.div_eq_of_lt rem, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · simp [Nat.add_mod, Nat.mod_eq_of_lt rem]

theorem normal_pack_finite_nonnegative_int (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    let bits := (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false := by
  dsimp only
  constructor
  · rw [Number.isFinite,
      (normal_pack_fields_int mantissa exponent positive lower upper expLower expUpper).1]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [Number.signBit, normal_pack_toNat_int mantissa exponent positive lower upper expLower expUpper]
    simp only [decide_eq_false_iff_not]
    omega

theorem normal_pack_cross_product (mantissa n : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971)
    (represented : RepresentsNat (.finite .positive mantissa exponent positive) n) :
    let bits := (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits
    (Number.magnitudeFraction bits).1 = n * (Number.magnitudeFraction bits).2 := by
  obtain ⟨exponentField,fraction⟩ :=
    normal_pack_fields_int mantissa exponent positive lower upper expLower expUpper
  have nonzero : (exponent + 1075).toNat ≠ 0 := by omega
  have cancel : (((exponent+1075).toNat : Int) - 1075) = exponent := by omega
  dsimp only
  simp only [Number.magnitudeFraction, Number.dyadic, exponentField, fraction,
    beq_iff_eq, nonzero, ↓reduceIte, cancel, Nat.add_sub_of_le lower]
  simp only [RepresentsNat] at represented
  by_cases nonnegative : 0 ≤ exponent
  · simp only [if_pos nonnegative] at represented ⊢
    simpa using represented
  · simp only [if_neg nonnegative] at represented ⊢
    exact represented

/-- The bit-level value relation does not assume the unreduced dyadic fraction
has denominator one. Small exact integers use negative canonical exponents. -/
def RepresentsNatBits (bits : Number.Bits) (n : Nat) : Prop :=
  Number.isFinite bits = true ∧ Number.signBit bits = false ∧
    (Number.magnitudeFraction bits).1 = n * (Number.magnitudeFraction bits).2

theorem normal_pack_represents (mantissa n : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971)
    (represented : RepresentsNat (.finite .positive mantissa exponent positive) n) :
    RepresentsNatBits (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits n := by
  obtain ⟨finite,sign⟩ := normal_pack_finite_nonnegative_int mantissa exponent positive lower upper expLower expUpper
  exact ⟨finite,sign,normal_pack_cross_product mantissa n exponent positive lower upper expLower expUpper represented⟩

theorem zero_pack_represents : RepresentsNatBits (Float.Model.pack (.zero .positive)).toBits 0 := by
  unfold RepresentsNatBits
  decide +kernel

theorem residual_rounding_lower (em : ExtendedMantissa) :
    em.mantissa ≤ em.roundedMantissa := by
  cases em with
  | mk mantissa roundBit stickyBit =>
    cases roundBit <;> cases stickyBit <;>
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
        Accuracy.roundToNearestEven]

theorem native_rounded_mantissa_lower (n : Nat) (large : 2^52 ≤ n) :
    2^52 ≤ (shifted n (n.log2 - 52)).roundedMantissa := by
  have nonzero : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have lower := ((Nat.log2_eq_iff nonzero).mp rfl).1
  have power : 2^52 * 2^(n.log2-52) = 2^n.log2 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have quotient : 2^52 ≤ n / 2^(n.log2-52) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [power]; exact lower)
  have rounded := residual_rounding_lower (shifted n (n.log2-52))
  rw [shifted_mantissa] at rounded
  omega

theorem native_normal_carry_shift (mantissa exponent : Nat)
    (lower : 2^52 ≤ mantissa) (upper : mantissa ≤ 2^53) :
    shiftToTargetExponent Float.Model.Format.binary64 mantissa exponent .exact =
      if mantissa = 2^53 then (⟨2^52,false,false⟩, (exponent : Int)+1)
      else (⟨mantissa,false,false⟩, exponent) := by
  by_cases same : mantissa = 2^53
  · subst mantissa
    have logarithm : (2^53 : Nat).log2 = 53 := by decide +kernel
    have target : Float.Model.Format.binary64.targetExponent
        (Float.Model.totalExponent (2^53) exponent) = (exponent : Int) + 1 := by
      simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
        Float.Model.Format.mantissaBits, Float.Model.Format.minExponent, logarithm]
      omega
    have shift : ((exponent : Int)+1-exponent).toNat = 1 := by omega
    simp only [shiftToTargetExponent, target, shiftToExponent, shift, ↓reduceIte]
    rfl
  · have logarithm : mantissa.log2 = 52 :=
      (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower,by omega⟩
    have target : Float.Model.Format.binary64.targetExponent
        (Float.Model.totalExponent mantissa exponent) = exponent := by
      simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
        Float.Model.Format.mantissaBits, Float.Model.Format.minExponent, logarithm]
      omega
    simp only [shiftToTargetExponent, target, shiftToExponent, Int.sub_self,
      Int.toNat_zero, Int.ofNat_zero, Int.add_zero, same, ↓reduceIte]
    rfl

theorem native_integer_round_shape (n : Nat) (large : 2^52 ≤ n) (bounded : n < 2^1023) :
    ∃ (mantissa exponent : Nat) (positive : 0 < mantissa),
      2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ 971 ∧
      round Float.Model.Format.binary64 .positive n 0 =
        .finite .positive mantissa exponent positive := by
  have nonzero : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have logUpper : n.log2 < 1023 := (Nat.log2_lt nonzero).mpr bounded
  let places := n.log2 - 52
  let m := (shifted n places).roundedMantissa
  have mLower : 2^52 ≤ m := native_rounded_mantissa_lower n large
  have mUpper : m ≤ 2^53 := native_rounded_mantissa_bound n
  have shift : (0-((n.log2 : Int)-52)).toNat = 0 := by omega
  have decrease : decreaseExponent n 0 ((n.log2 : Int)-52) = (n,0) := by
    unfold decreaseExponent
    rw [shift]
    simp
  have sameRound : round Float.Model.Format.binary64 .positive n 0 =
      roundWithAccuracy Float.Model.Format.binary64 .positive n 0 .exact := by
    unfold round
    rw [native_integer_target_exponent]
    dsimp only
    rw [decrease]
  rw [sameRound]
  unfold roundWithAccuracy
  rw [native_integer_shift]
  change ∃ (mantissa exponent : Nat) (positive : 0 < mantissa),
    2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ exponent ≤ 971 ∧
    (let pair := shiftToTargetExponent Float.Model.Format.binary64 m places .exact
     if h : pair.1.mantissa = 0 then Float.Model.UnpackedFloat.zero .positive
     else Float.Model.UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) =
      Float.Model.UnpackedFloat.finite .positive mantissa exponent positive
  rw [native_normal_carry_shift m places mLower mUpper]
  by_cases carry : m = 2^53
  · simp only [carry, ↓reduceIte]
    refine ⟨2^52,places+1,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_⟩
    · dsimp [places]; omega
    · simp
  · simp only [carry, ↓reduceIte]
    refine ⟨m,places,by omega,mLower,by omega,?_,?_⟩
    · dsimp [places]; omega
    · simp [show m ≠ 0 by omega]

theorem packed_integer_round_projection (n : Nat) (large : 2^52 ≤ n) (bounded : n < 2^1023) :
    let bits := (Float.Model.pack (round Float.Model.Format.binary64 .positive n 0)).toBits
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      Number.magnitudeFraction bits = (roundedInteger n, 1) := by
  obtain ⟨m,e,positive,lower,upper,finite,shape⟩ := native_integer_round_shape n large bounded
  have represented := native_normal_integer_round n large
  rw [shape] at represented
  simp only [RepresentsNat, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast] at represented
  dsimp only
  rw [shape]
  obtain ⟨finiteBits,sign⟩ := normal_pack_finite_nonnegative m e positive lower upper finite
  refine ⟨finiteBits,sign,?_⟩
  rw [normal_pack_magnitude m e positive lower upper finite,represented]

theorem native_small_integer_round_shape (n : Nat) (positive : 0 < n) (small : n < 2^52) :
    ∃ (mantissa : Nat) (exponent : Int) (mantissaPositive : 0 < mantissa),
      2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ -1074 ≤ exponent ∧ exponent ≤ 0 ∧
      round Float.Model.Format.binary64 .positive n 0 =
        .finite .positive mantissa exponent mantissaPositive ∧
      RepresentsNat (.finite .positive mantissa exponent mantissaPositive) n := by
  have logarithm : n.log2 < 52 := (Nat.log2_lt (by omega)).mpr small
  let places := 52-n.log2
  let enlarged := n*2^places
  let exponent : Int := -(places : Int)
  have placesBound : places ≤ 52 := by dsimp [places]; omega
  have placesPositive : 0 < places := by dsimp [places]; omega
  obtain ⟨lower,upper⟩ := Random.significand_bounds positive (by omega : n < 2^53)
  change 2^52 ≤ enlarged at lower
  change enlarged < 2^53 at upper
  have enlargedPositive : 0 < enlarged := by omega
  have enlargedLog : enlarged.log2 = 52 :=
    (Nat.log2_eq_iff (by omega : enlarged ≠ 0)).mpr ⟨lower,upper⟩
  have expLower : -1074 ≤ exponent := by dsimp [exponent]; omega
  have expUpper : exponent ≤ 0 := by dsimp [exponent]; omega
  have gap : (0-((n.log2 : Int)-52)).toNat = places := by dsimp [places]; omega
  have target : Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent enlarged exponent) = exponent := by
    simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
      Float.Model.Format.mantissaBits, Float.Model.Format.minExponent, enlargedLog]
    omega
  have shiftedExact : shiftToTargetExponent Float.Model.Format.binary64 enlarged exponent .exact =
      (⟨enlarged,false,false⟩,exponent) := by
    simp [shiftToTargetExponent,target,shiftToExponent,
      ExtendedMantissa.ofMantissaAndAccuracy,HShiftRight.hShiftRight,Nat.repeat]
  have roundExact : roundWithAccuracy Float.Model.Format.binary64 .positive enlarged exponent .exact =
      .finite .positive enlarged exponent enlargedPositive := by
    unfold roundWithAccuracy
    rw [shiftedExact]
    change (let pair := shiftToTargetExponent Float.Model.Format.binary64 enlarged exponent .exact
      if h : pair.1.mantissa = 0 then Float.Model.UnpackedFloat.zero .positive
      else Float.Model.UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) = _
    rw [shiftedExact]
    simp [show enlarged ≠ 0 by omega]
  refine ⟨enlarged,exponent,enlargedPositive,lower,upper,expLower,expUpper,?_,?_⟩
  · unfold round
    rw [native_integer_target_exponent]
    simp only [decreaseExponent,gap,Nat.shiftLeft_eq]
    simpa only [Int.zero_sub] using roundExact
  · have negative : ¬ 0 ≤ exponent := by dsimp [exponent]; omega
    simp only [RepresentsNat,if_neg negative]
    change enlarged = n*2^(-(-(places : Int))).toNat
    simp only [Int.neg_neg,Int.toNat_natCast]
    rfl

/-- Every nonnegative integer below the stated overflow margin is connected
to the packed native rounding operation, including zero and cancellation into
small integers with a negative canonical exponent. -/
theorem packed_integer_round_represents (n : Nat) (bounded : n < 2^1023) :
    RepresentsNatBits (Float.Model.pack (round Float.Model.Format.binary64 .positive n 0)).toBits
      (roundedInteger n) := by
  by_cases zero : n = 0
  · subst n
    have roundZero : round Float.Model.Format.binary64 .positive 0 0 = .zero .positive := by rfl
    have projectedZero : roundedInteger 0 = 0 := by decide +kernel
    rw [roundZero,projectedZero]
    exact zero_pack_represents
  · by_cases small : n < 2^52
    · obtain ⟨m,e,positive,lower,upper,expLower,expUpper,shape,represented⟩ :=
        native_small_integer_round_shape n (by omega) small
      rw [shape,integer_exact_through_cap n (by unfold unitCap; omega)]
      exact normal_pack_represents m n e positive lower upper expLower (by omega) represented
    · obtain ⟨finite,sign,magnitude⟩ := packed_integer_round_projection n (by omega) bounded
      refine ⟨finite,sign,?_⟩
      rw [magnitude]
      simp

end CookieClicker.JavaScript.RoundingBridge

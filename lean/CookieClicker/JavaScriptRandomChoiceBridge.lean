import CookieClicker.JavaScriptRandom
import CookieClicker.JavaScriptDyadicArithmeticBridge

/-! Actual binary64 multiplication and floor for the native two-item choice.
The proof covers every IID53 index without enumerating the sample space.
It does not establish which generator is active at a native harvest callback,
or that the source array/Math bindings have the required initialized meaning.
-/
namespace CookieClicker.JavaScript.RandomChoiceBridge
open Float.Model Float.Model.UnpackedFloat Number Random RoundingBridge DyadicArithmeticBridge
open CookieClicker.FullGame.UniformRandom
set_option exponentiation.threshold 4096
set_option maxHeartbeats 3000000

theorem scaled_normal_shift (m k : Nat) (e : Int) (_positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) :
    shiftToTargetExponent Format.binary64 (m * 2^k) (e-k) .exact =
      (⟨m,false,false⟩,e) := by
  have log : m.log2 = 52 := (Nat.log2_eq_iff (by omega : m ≠ 0)).mpr ⟨lower,upper⟩
  have target : Format.binary64.targetExponent (totalExponent (m*2^k) (e-k)) = e := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,
      log2_scaled m k (by omega),log]
    omega
  have gap : (e-(e-k)).toNat = k := by omega
  unfold shiftToTargetExponent
  rw [target]
  simp only [shiftToExponent,gap,ExtendedMantissa.ofMantissaAndAccuracy]
  have shift : (ExtendedMantissa.mk (m*2^k) false false >>> k) = ⟨m,false,false⟩ := by
    have h := shifted_scale m k 0
    simpa [shifted,HShiftRight.hShiftRight,Nat.repeat] using h
  rw [shift]
  congr 1
  omega

theorem scaled_normal_round (m k : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) :
    roundWithAccuracy Format.binary64 .positive (m*2^k) (e-k) .exact =
      .finite .positive m e positive := by
  have shift := scaled_normal_shift m k e positive lower upper expLower
  have plain : shiftToTargetExponent Format.binary64 m e .exact = (⟨m,false,false⟩,e) := by
    simpa using scaled_normal_shift m 0 e positive lower upper expLower
  unfold roundWithAccuracy
  rw [shift]
  change (let pair := shiftToTargetExponent Format.binary64 m e .exact
    if h : pair.1.mantissa = 0 then UnpackedFloat.zero .positive
    else UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) = _
  rw [plain]
  simp only [Nat.ne_of_gt positive,↓reduceDIte]

theorem encode_normal_pack (draw : Draw 53) (positive : 0 < draw.val) :
    encode draw =
      (Float.Model.pack (.finite .positive (significand draw.val) ((draw.val.log2 : Int)-105)
        (by have h := (significand_bounds positive draw.isLt).1; omega))).toBits := by
  obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
  have log := logarithm_bound positive draw.isLt
  apply UInt64.toNat_inj.mp
  rw [encode_toNat,normal_pack_toNat_int _ _ _ lo hi (by omega) (by omega)]
  simp only [packed,beq_iff_eq,show draw.val ≠ 0 by omega,↓reduceIte]
  have exp : (((draw.val.log2 : Int)-105)+1075).toNat = draw.val.log2+970 := by omega
  rw [exp]

theorem native_two_unpack : (Number.model (Number.ofNat 2)).unpack =
    .finite .positive (2^52) (-51) (by decide) := by rfl

theorem multiply_draw_by_two (draw : Draw 53) (positive : 0 < draw.val) :
    Number.mul (encode draw) (Number.ofNat 2) =
      (Float.Model.pack (.finite .positive (significand draw.val) ((draw.val.log2 : Int)-104)
        (by have h := (significand_bounds positive draw.isLt).1; omega))).toBits := by
  obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
  have log := logarithm_bound positive draw.isLt
  unfold Number.mul Float.Model.mul
  rw [encode_normal_pack draw positive,
    normal_model_unpack _ _ _ lo hi (by omega) (by omega),native_two_unpack]
  simp only [UnpackedFloat.mul]
  change (Float.Model.pack (roundWithAccuracy Format.binary64 .positive
    (significand draw.val * 2^52) (((draw.val.log2 : Int)-105)+(-51)) .exact)).toBits = _
  rw [show ((draw.val.log2 : Int)-105)+(-51) = ((draw.val.log2 : Int)-104)-(52:Nat) by omega]
  rw [scaled_normal_round _ _ _ (by omega) lo hi (by omega)]


theorem doubled_draw_magnitude (draw : Draw 53) (positive : 0 < draw.val) :
    magnitudeFraction (Number.mul (encode draw) (Number.ofNat 2)) =
      (significand draw.val,2^(104-draw.val.log2)) := by
  obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
  have log := logarithm_bound positive draw.isLt
  rw [multiply_draw_by_two draw positive]
  obtain ⟨ef,ff⟩ := normal_pack_fields_int (significand draw.val) ((draw.val.log2 : Int)-104)
    (by omega) lo hi (by omega) (by omega)
  unfold magnitudeFraction dyadic
  rw [ef,ff]
  have nonzero : (((draw.val.log2 : Int)-104)+1075).toNat ≠ 0 := by omega
  have e : ((((draw.val.log2 : Int)-104)+1075).toNat : Int)-1075 = (draw.val.log2 : Int)-104 := by omega
  have neg : ¬(0:Int) ≤ (draw.val.log2 : Int)-104 := by omega
  have nat : (-((draw.val.log2 : Int)-104)).toNat = 104-draw.val.log2 := by omega
  simp only [beq_iff_eq,nonzero,↓reduceIte,Nat.add_sub_of_le lo,e,neg,nat]

theorem doubled_draw_quotient (draw : Draw 53) (positive : 0 < draw.val) :
    (magnitudeFraction (Number.mul (encode draw) (Number.ofNat 2))).1 /
      (magnitudeFraction (Number.mul (encode draw) (Number.ofNat 2))).2 = draw.val / 2^52 := by
  rw [doubled_draw_magnitude draw positive]
  dsimp only
  have log := logarithm_bound positive draw.isLt
  have exp : 104-draw.val.log2 = 52+(52-draw.val.log2) := by omega
  rw [significand,exp,Nat.pow_add]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)


theorem doubled_draw_properties (draw : Draw 53) (positive : 0 < draw.val) :
    isFinite (Number.mul (encode draw) (Number.ofNat 2)) = true ∧
    signBit (Number.mul (encode draw) (Number.ofNat 2)) = false ∧
    isZero (Number.mul (encode draw) (Number.ofNat 2)) = false := by
  obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
  have log := logarithm_bound positive draw.isLt
  rw [multiply_draw_by_two draw positive]
  obtain ⟨finite,sign⟩ := normal_pack_finite_nonnegative_int (significand draw.val)
    ((draw.val.log2 : Int)-104) (by omega) lo hi (by omega) (by omega)
  refine ⟨finite,sign,?_⟩
  unfold isZero
  rw [normal_pack_toNat_int _ _ _ lo hi (by omega) (by omega)]
  have eb : 971 ≤ (((draw.val.log2 : Int)-104)+1075).toNat ∧
      (((draw.val.log2 : Int)-104)+1075).toNat ≤ 1023 := by omega
  have bounds : 0 < (((draw.val.log2 : Int)-104)+1075).toNat * 2^52 + (significand draw.val-2^52) ∧
      (((draw.val.log2 : Int)-104)+1075).toNat * 2^52 + (significand draw.val-2^52) < 2^63 := by omega
  rw [Nat.mod_eq_of_lt bounds.2]
  simp only [beq_eq_false_iff_ne]
  omega

theorem signed_nonnegative_integer (n : Nat) : signedInteger false n = Number.ofNat n := by
  unfold signedInteger
  by_cases zero : n=0
  · subst n; rfl
  · simp [zero]

/-- Actual binary64 multiplication and the interpreter's Math.floor, for all
2^53 possible free draw indices. This does not assert that a particular source
callback uses the free generator. -/
theorem native_choose_two (draw : Draw 53) :
    Number.floor (Number.mul (encode draw) (Number.ofNat 2)) = Number.ofNat (chooseTwo draw) := by
  by_cases zero : draw.val=0
  · have bits : encode draw = positiveZero := by simp [encode,packed,zero,positiveZero]
    rw [bits]
    have chosen : chooseTwo draw=0 := by simp [chooseTwo,zero]
    rw [chosen]
    rfl
  · have positive : 0<draw.val := by omega
    obtain ⟨finite,sign,nonzero⟩ := doubled_draw_properties draw positive
    unfold Number.floor
    rw [finite,nonzero]
    simp only [Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte,sign,Bool.false_and]
    simp only [Nat.add_zero]
    rw [doubled_draw_quotient draw positive,signed_nonnegative_integer]
    rfl

theorem native_choose_two_success (draw : Draw 53) :
    Number.floor (Number.mul (encode draw) (Number.ofNat 2)) = Number.one ↔ 2^52 ≤ draw.val := by
  rw [native_choose_two]
  have support := choose_two_support draw
  have choice := choose_two_success_iff draw
  change _ ↔ size 52 ≤ draw.val
  rw [← choice]
  have cases : chooseTwo draw=0 ∨ chooseTwo draw=1 := by omega
  rcases cases with h | h <;> rw [h] <;> decide +kernel


def nativeSuccess (index : Nat) : Bool :=
  if h : index < size 53 then
    decide (Number.floor (Number.mul (encode ⟨index,h⟩) (Number.ofNat 2)) = Number.one)
  else false

theorem native_success_event : nativeSuccess = interval (size 52) (size 53) := by
  funext index
  by_cases bound : index < size 53
  · simp only [nativeSuccess,bound,↓reduceDIte,native_choose_two_success,
      interval,decide_eq_decide, and_true]
    rfl
  · simp [nativeSuccess,interval,bound]

theorem native_unripe_success_mass : eventMass 53 nativeSuccess = 1/2 := by
  rw [native_success_event]
  exact uniform53_unripe_success_mass

end CookieClicker.JavaScript.RandomChoiceBridge

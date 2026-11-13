import CookieClicker.JavaScriptNumber
import CookieClicker.UniformRandom

/-! Exact binary64 encoding of the selected IID53 environment draws. This
encoding constructs the bits directly. Its proof covers every draw index,
without testing or enumerating all 2^53 possibilities. Independence belongs to
the stochastic transition kernel, not to this deterministic encoding function.
-/
namespace CookieClicker.JavaScript.Random
open Number
open CookieClicker.FullGame.UniformRandom
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

def significand (n : Nat) : Nat := n * 2 ^ (52 - n.log2)

def packed (n : Nat) : Nat :=
  if n == 0 then 0
  else (n.log2 + 970) * 2 ^ 52 + (significand n - 2 ^ 52)

def encode (draw : Draw 53) : Bits := UInt64.ofNat (packed draw.val)

theorem logarithm_bound {n : Nat} (positive : 0 < n) (bound : n < 2 ^ 53) :
    n.log2 ≤ 52 := by
  have := (Nat.log2_lt (show n ≠ 0 by omega)).mpr bound
  omega

theorem significand_bounds {n : Nat} (positive : 0 < n) (bound : n < 2 ^ 53) :
    2 ^ 52 ≤ significand n ∧ significand n < 2 ^ 53 := by
  have e := logarithm_bound positive bound
  obtain ⟨lower,upper⟩ := (Nat.log2_eq_iff (show n ≠ 0 by omega)).mp (rfl : n.log2 = n.log2)
  have lo := Nat.mul_le_mul_right (2 ^ (52-n.log2)) lower
  have hi := Nat.mul_lt_mul_of_pos_right upper (Nat.two_pow_pos (52-n.log2))
  rw [← Nat.pow_add] at lo hi
  have lowExponent : n.log2 + (52-n.log2) = 52 := by omega
  have highExponent : n.log2 + 1 + (52-n.log2) = 53 := by omega
  rw [lowExponent] at lo
  rw [highExponent] at hi
  exact ⟨lo,hi⟩

theorem packed_bound (draw : Draw 53) : packed draw.val < 2 ^ 63 := by
  have bound : draw.val < 2 ^ 53 := draw.isLt
  by_cases zero : draw.val = 0
  · simp [packed,zero]
  · have positive : 0 < draw.val := by omega
    have e := logarithm_bound positive bound
    obtain ⟨lo,hi⟩ := significand_bounds positive bound
    unfold packed
    simp only [beq_iff_eq,zero,↓reduceIte]
    omega

theorem encode_toNat (draw : Draw 53) : (encode draw).toNat = packed draw.val := by
  have bound := packed_bound draw
  unfold encode
  apply UInt64.toNat_ofNat_of_lt'
  change packed draw.val < 2 ^ 64
  omega

theorem fields_nonzero (draw : Draw 53) (positive : 0 < draw.val) :
    exponentField (encode draw) = draw.val.log2 + 970 ∧
    fraction (encode draw) = significand draw.val - 2 ^ 52 := by
  have e := logarithm_bound positive draw.isLt
  obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
  have rem : significand draw.val - 2 ^ 52 < 2 ^ 52 := by omega
  have notZero : draw.val ≠ 0 := by omega
  simp only [exponentField,fraction,encode_toNat,packed,beq_iff_eq,notZero,↓reduceIte]
  constructor
  · rw [Nat.add_comm ((draw.val.log2+970)*2^52),
      Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 52), Nat.div_eq_of_lt rem, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · simp [Nat.add_mod,Nat.mod_eq_of_lt rem]

theorem finite_nonnegative (draw : Draw 53) :
    isFinite (encode draw) = true ∧ signBit (encode draw) = false := by
  have bound := packed_bound draw
  have sign : signBit (encode draw) = false := by simp [signBit,encode_toNat]; omega
  refine ⟨?_,sign⟩
  by_cases zero : draw.val = 0
  · simp [isFinite,exponentField,encode_toNat,packed,zero]
  · have positive : 0 < draw.val := by omega
    have e := logarithm_bound positive draw.isLt
    rw [isFinite,(fields_nonzero draw positive).1]
    simp only [bne_iff_ne,ne_eq]
    omega

theorem magnitude_cross_product (draw : Draw 53) :
    (magnitudeFraction (encode draw)).1 * 2 ^ 53 =
      draw.val * (magnitudeFraction (encode draw)).2 := by
  by_cases zero : draw.val = 0
  · simp [magnitudeFraction,dyadic,exponentField,fraction,encode_toNat,packed,zero]
  · have positive : 0 < draw.val := by omega
    obtain ⟨exponent,fraction⟩ := fields_nonzero draw positive
    have e := logarithm_bound positive draw.isLt
    obtain ⟨lo,hi⟩ := significand_bounds positive draw.isLt
    have expNonzero : draw.val.log2 + 970 ≠ 0 := by omega
    have expNegative : ¬ (0 : Int) ≤ ((draw.val.log2 + 970 : Nat) : Int) - 1075 := by omega
    have expMagnitude : (-(((draw.val.log2 + 970 : Nat) : Int) - 1075)).toNat = 105 - draw.val.log2 := by omega
    unfold magnitudeFraction dyadic
    simp only [exponent,beq_iff_eq,expNonzero,↓reduceIte,fraction,expNegative,expMagnitude]
    rw [Nat.add_sub_of_le lo]
    unfold significand
    rw [Nat.mul_assoc,← Nat.pow_add]
    congr 2
    omega

theorem magnitude_denominator_positive (draw : Draw 53) :
    0 < (magnitudeFraction (encode draw)).2 := by
  unfold magnitudeFraction
  split
  split <;> simp [Nat.pow_pos]

private theorem fraction_eq_of_cross (a b c d : Rat) (hb : b ≠ 0) (hd : d ≠ 0)
    (cross : a*d = c*b) : a/b = c/d := by
  have product := congrArg (fun x : Rat => x * (d⁻¹ * b⁻¹)) cross
  have cancelB := Rat.mul_inv_cancel b hb
  have cancelD := Rat.mul_inv_cancel d hd
  change a * b⁻¹ = c * d⁻¹
  grind

/-- The actual Number bits have exactly the intended rational draw value. -/
theorem exact_value (draw : Draw 53) :
    ((magnitudeFraction (encode draw)).1 : Rat) / (magnitudeFraction (encode draw)).2 =
      value draw := by
  have npos := Rat.natCast_pos.mpr (magnitude_denominator_positive draw)
  have dpos : (0 : Rat) < (2 ^ 53 : Nat) := by decide +kernel
  have nzero : ((magnitudeFraction (encode draw)).2 : Rat) ≠ 0 := by grind
  have dzero : ((2 ^ 53 : Nat) : Rat) ≠ 0 := by grind
  have cross := congrArg (fun n : Nat => (n : Rat)) (magnitude_cross_product draw)
  simp only [Rat.natCast_mul] at cross
  exact fraction_eq_of_cross _ _ _ _ nzero dzero cross

theorem encode_injective (left right : Draw 53) (same : encode left = encode right) : left = right := by
  have values : value left = value right := by
    rw [← exact_value left, ← exact_value right, same]
  have nonzero : ((size 53 : Nat) : Rat) ≠ 0 := by decide +kernel
  have multiplied := congrArg (fun x : Rat => x * (size 53 : Nat)) values
  simp only [value,Rat.div_mul_cancel nonzero] at multiplied
  exact Fin.ext (Rat.natCast_inj.mp multiplied)

theorem zero_encoding : encode ⟨0,size_positive 53⟩ = positiveZero := by decide +kernel

theorem largest_encoding : encode ⟨2^53-1,by decide +kernel⟩ = 4607182418800017407 := by
  decide +kernel

end CookieClicker.JavaScript.Random

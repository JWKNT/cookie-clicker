import CookieClicker.GodzamokRounding
import CookieClicker.UniformRandom

/-! Startup letters from the exact 53-bit free grid and normal binary64
significand rounding. This uses a scaled-integer representation of 26*u;
source parsing and the native floating-point implementation remain external.
-/
namespace CookieClicker.FullGame.StartupSeed
open GodzamokRounding UniformRandom

def denominator : Nat := 2 ^ 53
def letter (index : Nat) : Nat := roundedInteger (26 * index) / denominator

def boundary (j : Nat) : Nat :=
  if j = 0 then 0 else if 26 ≤ j then denominator else
  let correction := if j.isPowerOfTwo then 2 ^ j.log2 else 2 ^ (j.log2 + 1)
  (2 * j * denominator - correction + 51) / 52

def bucketCount (j : Nat) : Nat := boundary (j + 1) - boundary j

theorem round_multiple_error (spacing n : Nat) (positive : 0 < spacing) :
    roundMultiple spacing n ≤ n + spacing ∧ n ≤ roundMultiple spacing n + spacing := by
  have division := Nat.div_add_mod n spacing
  have remainder := Nat.mod_lt n positive
  rw [Nat.mul_comm spacing (n / spacing)] at division
  unfold roundMultiple
  dsimp only
  split <;> simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul] <;> omega

theorem letter_spacing_bound (index : Nat) (valid : index < denominator) :
    0 < integerSpacing (26 * index) ∧ integerSpacing (26 * index) ≤ 32 := by
  unfold integerSpacing
  split
  · decide +kernel
  · rename_i large
    have nonzero : 26 * index ≠ 0 := by omega
    have upper : 26 * index < 2 ^ 58 := by unfold denominator at valid; omega
    have logBound : (26 * index).log2 < 58 := (Nat.log2_lt nonzero).mpr upper
    have exponent : (26 * index).log2 - 52 ≤ 5 := by omega
    constructor
    · exact Nat.pow_pos (by decide)
    · exact Nat.pow_le_pow_right (by decide) exponent

theorem letter_rounding_error (index : Nat) (valid : index < denominator) :
    roundedInteger (26 * index) ≤ 26 * index + 32 ∧
    26 * index ≤ roundedInteger (26 * index) + 32 := by
  obtain ⟨positive, bounded⟩ := letter_spacing_bound index valid
  have error := round_multiple_error (integerSpacing (26 * index)) (26 * index) positive
  unfold roundedInteger
  omega


private theorem threshold1 (index : Nat) (valid : index < denominator) :
    letter index < 1 ↔ index < boundary 1 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 1 = 346430740566962 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 9007199254740992 ↔ index < 346430740566962
  by_cases below : 26 * index + 32 < 9007199254740992
  · omega
  by_cases above : 9007199254740992 + 32 < 26 * index
  · omega
  have choices : index = 346430740566960 ∨ index = 346430740566961 ∨ index = 346430740566962 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold2 (index : Nat) (valid : index < denominator) :
    letter index < 2 ↔ index < boundary 2 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 2 = 692861481133923 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 18014398509481984 ↔ index < 692861481133923
  by_cases below : 26 * index + 32 < 18014398509481984
  · omega
  by_cases above : 18014398509481984 + 32 < 26 * index
  · omega
  have choices : index = 692861481133922 ∨ index = 692861481133923 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold3 (index : Nat) (valid : index < denominator) :
    letter index < 3 ↔ index < boundary 3 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 3 = 1039292221700884 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 27021597764222976 ↔ index < 1039292221700884
  by_cases below : 26 * index + 32 < 27021597764222976
  · omega
  by_cases above : 27021597764222976 + 32 < 26 * index
  · omega
  have choices : index = 1039292221700883 ∨ index = 1039292221700884 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold4 (index : Nat) (valid : index < denominator) :
    letter index < 4 ↔ index < boundary 4 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 4 = 1385722962267845 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 36028797018963968 ↔ index < 1385722962267845
  by_cases below : 26 * index + 32 < 36028797018963968
  · omega
  by_cases above : 36028797018963968 + 32 < 26 * index
  · omega
  have choices : index = 1385722962267844 ∨ index = 1385722962267845 ∨ index = 1385722962267846 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold5 (index : Nat) (valid : index < denominator) :
    letter index < 5 ↔ index < boundary 5 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 5 = 1732153702834806 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 45035996273704960 ↔ index < 1732153702834806
  by_cases below : 26 * index + 32 < 45035996273704960
  · omega
  by_cases above : 45035996273704960 + 32 < 26 * index
  · omega
  have choices : index = 1732153702834805 ∨ index = 1732153702834806 ∨ index = 1732153702834807 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold6 (index : Nat) (valid : index < denominator) :
    letter index < 6 ↔ index < boundary 6 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 6 = 2078584443401768 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 54043195528445952 ↔ index < 2078584443401768
  by_cases below : 26 * index + 32 < 54043195528445952
  · omega
  by_cases above : 54043195528445952 + 32 < 26 * index
  · omega
  have choices : index = 2078584443401767 ∨ index = 2078584443401768 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold7 (index : Nat) (valid : index < denominator) :
    letter index < 7 ↔ index < boundary 7 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 7 = 2425015183968729 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 63050394783186944 ↔ index < 2425015183968729
  by_cases below : 26 * index + 32 < 63050394783186944
  · omega
  by_cases above : 63050394783186944 + 32 < 26 * index
  · omega
  have choices : index = 2425015183968728 ∨ index = 2425015183968729 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold8 (index : Nat) (valid : index < denominator) :
    letter index < 8 ↔ index < boundary 8 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 8 = 2771445924535690 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 72057594037927936 ↔ index < 2771445924535690
  by_cases below : 26 * index + 32 < 72057594037927936
  · omega
  by_cases above : 72057594037927936 + 32 < 26 * index
  · omega
  have choices : index = 2771445924535689 ∨ index = 2771445924535690 ∨ index = 2771445924535691 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold9 (index : Nat) (valid : index < denominator) :
    letter index < 9 ↔ index < boundary 9 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 9 = 3117876665102651 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 81064793292668928 ↔ index < 3117876665102651
  by_cases below : 26 * index + 32 < 81064793292668928
  · omega
  by_cases above : 81064793292668928 + 32 < 26 * index
  · omega
  have choices : index = 3117876665102650 ∨ index = 3117876665102651 ∨ index = 3117876665102652 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold10 (index : Nat) (valid : index < denominator) :
    letter index < 10 ↔ index < boundary 10 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 10 = 3464307405669612 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 90071992547409920 ↔ index < 3464307405669612
  by_cases below : 26 * index + 32 < 90071992547409920
  · omega
  by_cases above : 90071992547409920 + 32 < 26 * index
  · omega
  have choices : index = 3464307405669612 ∨ index = 3464307405669613 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold11 (index : Nat) (valid : index < denominator) :
    letter index < 11 ↔ index < boundary 11 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 11 = 3810738146236574 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 99079191802150912 ↔ index < 3810738146236574
  by_cases below : 26 * index + 32 < 99079191802150912
  · omega
  by_cases above : 99079191802150912 + 32 < 26 * index
  · omega
  have choices : index = 3810738146236573 ∨ index = 3810738146236574 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold12 (index : Nat) (valid : index < denominator) :
    letter index < 12 ↔ index < boundary 12 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 12 = 4157168886803535 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 108086391056891904 ↔ index < 4157168886803535
  by_cases below : 26 * index + 32 < 108086391056891904
  · omega
  by_cases above : 108086391056891904 + 32 < 26 * index
  · omega
  have choices : index = 4157168886803534 ∨ index = 4157168886803535 ∨ index = 4157168886803536 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold13 (index : Nat) (valid : index < denominator) :
    letter index < 13 ↔ index < boundary 13 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 13 = 4503599627370496 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 117093590311632896 ↔ index < 4503599627370496
  by_cases below : 26 * index + 32 < 117093590311632896
  · omega
  by_cases above : 117093590311632896 + 32 < 26 * index
  · omega
  have choices : index = 4503599627370495 ∨ index = 4503599627370496 ∨ index = 4503599627370497 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold14 (index : Nat) (valid : index < denominator) :
    letter index < 14 ↔ index < boundary 14 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 14 = 4850030367937457 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 126100789566373888 ↔ index < 4850030367937457
  by_cases below : 26 * index + 32 < 126100789566373888
  · omega
  by_cases above : 126100789566373888 + 32 < 26 * index
  · omega
  have choices : index = 4850030367937456 ∨ index = 4850030367937457 ∨ index = 4850030367937458 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold15 (index : Nat) (valid : index < denominator) :
    letter index < 15 ↔ index < boundary 15 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 15 = 5196461108504419 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 135107988821114880 ↔ index < 5196461108504419
  by_cases below : 26 * index + 32 < 135107988821114880
  · omega
  by_cases above : 135107988821114880 + 32 < 26 * index
  · omega
  have choices : index = 5196461108504418 ∨ index = 5196461108504419 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold16 (index : Nat) (valid : index < denominator) :
    letter index < 16 ↔ index < boundary 16 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 16 = 5542891849071380 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 144115188075855872 ↔ index < 5542891849071380
  by_cases below : 26 * index + 32 < 144115188075855872
  · omega
  by_cases above : 144115188075855872 + 32 < 26 * index
  · omega
  have choices : index = 5542891849071379 ∨ index = 5542891849071380 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold17 (index : Nat) (valid : index < denominator) :
    letter index < 17 ↔ index < boundary 17 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 17 = 5889322589638341 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 153122387330596864 ↔ index < 5889322589638341
  by_cases below : 26 * index + 32 < 153122387330596864
  · omega
  by_cases above : 153122387330596864 + 32 < 26 * index
  · omega
  have choices : index = 5889322589638340 ∨ index = 5889322589638341 ∨ index = 5889322589638342 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold18 (index : Nat) (valid : index < denominator) :
    letter index < 18 ↔ index < boundary 18 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 18 = 6235753330205302 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 162129586585337856 ↔ index < 6235753330205302
  by_cases below : 26 * index + 32 < 162129586585337856
  · omega
  by_cases above : 162129586585337856 + 32 < 26 * index
  · omega
  have choices : index = 6235753330205301 ∨ index = 6235753330205302 ∨ index = 6235753330205303 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold19 (index : Nat) (valid : index < denominator) :
    letter index < 19 ↔ index < boundary 19 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 19 = 6582184070772263 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 171136785840078848 ↔ index < 6582184070772263
  by_cases below : 26 * index + 32 < 171136785840078848
  · omega
  by_cases above : 171136785840078848 + 32 < 26 * index
  · omega
  have choices : index = 6582184070772263 ∨ index = 6582184070772264 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold20 (index : Nat) (valid : index < denominator) :
    letter index < 20 ↔ index < boundary 20 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 20 = 6928614811339224 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 180143985094819840 ↔ index < 6928614811339224
  by_cases below : 26 * index + 32 < 180143985094819840
  · omega
  by_cases above : 180143985094819840 + 32 < 26 * index
  · omega
  have choices : index = 6928614811339224 ∨ index = 6928614811339225 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold21 (index : Nat) (valid : index < denominator) :
    letter index < 21 ↔ index < boundary 21 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 21 = 7275045551906186 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 189151184349560832 ↔ index < 7275045551906186
  by_cases below : 26 * index + 32 < 189151184349560832
  · omega
  by_cases above : 189151184349560832 + 32 < 26 * index
  · omega
  have choices : index = 7275045551906185 ∨ index = 7275045551906186 ∨ index = 7275045551906187 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold22 (index : Nat) (valid : index < denominator) :
    letter index < 22 ↔ index < boundary 22 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 22 = 7621476292473147 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 198158383604301824 ↔ index < 7621476292473147
  by_cases below : 26 * index + 32 < 198158383604301824
  · omega
  by_cases above : 198158383604301824 + 32 < 26 * index
  · omega
  have choices : index = 7621476292473146 ∨ index = 7621476292473147 ∨ index = 7621476292473148 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold23 (index : Nat) (valid : index < denominator) :
    letter index < 23 ↔ index < boundary 23 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 23 = 7967907033040108 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 207165582859042816 ↔ index < 7967907033040108
  by_cases below : 26 * index + 32 < 207165582859042816
  · omega
  by_cases above : 207165582859042816 + 32 < 26 * index
  · omega
  have choices : index = 7967907033040108 ∨ index = 7967907033040109 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold24 (index : Nat) (valid : index < denominator) :
    letter index < 24 ↔ index < boundary 24 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 24 = 8314337773607069 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 216172782113783808 ↔ index < 8314337773607069
  by_cases below : 26 * index + 32 < 216172782113783808
  · omega
  by_cases above : 216172782113783808 + 32 < 26 * index
  · omega
  have choices : index = 8314337773607069 ∨ index = 8314337773607070 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 <;> subst index <;> decide +kernel

private theorem threshold25 (index : Nat) (valid : index < denominator) :
    letter index < 25 ↔ index < boundary 25 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 25 = 8660768514174031 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 225179981368524800 ↔ index < 8660768514174031
  by_cases below : 26 * index + 32 < 225179981368524800
  · omega
  by_cases above : 225179981368524800 + 32 < 26 * index
  · omega
  have choices : index = 8660768514174030 ∨ index = 8660768514174031 ∨ index = 8660768514174032 := by unfold denominator at valid; omega
  rcases choices with h0 | h1 | h2 <;> subst index <;> decide +kernel

private theorem threshold26 (index : Nat) (valid : index < denominator) :
    letter index < 26 ↔ index < boundary 26 := by
  have error := letter_rounding_error index valid
  have exactBoundary : boundary 26 = 9007199254740992 := by decide +kernel
  rw [exactBoundary]
  unfold letter
  rw [Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < denominator)]
  change roundedInteger (26 * index) < 234187180623265792 ↔ index < 9007199254740992
  by_cases below : 26 * index + 32 < 234187180623265792
  · omega
  by_cases above : 234187180623265792 + 32 < 26 * index
  · omega
  have choices : index = 9007199254740991 := by unfold denominator at valid; omega
  rcases choices with h0 <;> subst index <;> decide +kernel


theorem letter_lt_boundary (index j : Nat) (valid : index < denominator) (range : j ≤ 26) :
    letter index < j ↔ index < boundary j := by
  have choices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 := by omega
  rcases choices with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26
  · subst j; simp [boundary]
  · subst j; exact threshold1 index valid
  · subst j; exact threshold2 index valid
  · subst j; exact threshold3 index valid
  · subst j; exact threshold4 index valid
  · subst j; exact threshold5 index valid
  · subst j; exact threshold6 index valid
  · subst j; exact threshold7 index valid
  · subst j; exact threshold8 index valid
  · subst j; exact threshold9 index valid
  · subst j; exact threshold10 index valid
  · subst j; exact threshold11 index valid
  · subst j; exact threshold12 index valid
  · subst j; exact threshold13 index valid
  · subst j; exact threshold14 index valid
  · subst j; exact threshold15 index valid
  · subst j; exact threshold16 index valid
  · subst j; exact threshold17 index valid
  · subst j; exact threshold18 index valid
  · subst j; exact threshold19 index valid
  · subst j; exact threshold20 index valid
  · subst j; exact threshold21 index valid
  · subst j; exact threshold22 index valid
  · subst j; exact threshold23 index valid
  · subst j; exact threshold24 index valid
  · subst j; exact threshold25 index valid
  · subst j; exact threshold26 index valid


theorem letter_support (index : Nat) (valid : index < denominator) : letter index < 26 := by
  have endPoint : boundary 26 = denominator := by decide +kernel
  exact (letter_lt_boundary index 26 valid (by decide)).mpr (by simpa [endPoint] using valid)

theorem letter_eq_interval (index : Nat) (j : Fin 26) (valid : index < denominator) :
    letter index = j.val ↔ boundary j.val ≤ index ∧ index < boundary (j.val + 1) := by
  have lower := letter_lt_boundary index j.val valid (by omega)
  have upper := letter_lt_boundary index (j.val + 1) valid (by omega)
  omega

theorem boundaries_ordered : ∀ j : Fin 26,
    boundary j.val ≤ boundary (j.val + 1) ∧ boundary (j.val + 1) ≤ denominator := by decide +kernel

theorem all_bucket_counts_positive : ∀ j : Fin 26, 0 < bucketCount j.val := by decide +kernel

theorem bucket_counts_partition : ((List.range 26).map bucketCount).sum = denominator := by decide +kernel

theorem exact_bucket_sizes : ∀ j : Fin 26,
    bucketCount j.val = 346430740566961 +
      if j.val ∈ [0, 5, 10, 14, 20, 24] then 1 else 0 := by decide +kernel

def letterEvent (j : Fin 26) (index : Nat) : Bool := decide (letter index = j.val)
def prior (j : Fin 26) : Rat := (bucketCount j.val : Rat) / (denominator : Rat)

theorem letter_mass (j : Fin 26) : eventMass 53 (letterEvent j) = prior j := by
  have counts : (List.range (size 53)).countP (letterEvent j) =
      (List.range (size 53)).countP (interval (boundary j.val) (boundary (j.val + 1))) := by
    apply List.countP_congr
    intro index member
    have valid : index < denominator := by simpa [size, denominator] using member
    simpa [letterEvent, interval] using letter_eq_interval index j valid
  unfold eventMass
  rw [counts]
  have bounds := boundaries_ordered j
  rw [count_interval _ _ _ bounds.1]
  have upper : boundary (j.val + 1) ≤ size 53 := by simpa [size, denominator] using bounds.2
  have lower : boundary j.val ≤ size 53 := Nat.le_trans bounds.1 upper
  rw [Nat.min_eq_right upper, Nat.min_eq_right lower]
  rfl

theorem prior_positive (j : Fin 26) : 0 < prior j := by
  unfold prior
  apply (Rat.lt_div_iff (by decide +kernel : 0 < (denominator : Rat))).mpr
  simpa only [Rat.zero_mul] using Rat.natCast_pos.mpr (all_bucket_counts_positive j)

theorem priors_normalized : ((List.finRange 26).map prior).foldl (· + ·) 0 = 1 := by decide +kernel

theorem letters_are_not_uniform : prior ⟨0, by decide⟩ ≠ 1 / 26 := by decide +kernel

theorem seed_mass_five (a b c d e : Fin 26) :
    cylinderMass 53 [letterEvent a, letterEvent b, letterEvent c, letterEvent d, letterEvent e] =
      (bucketCount a.val * bucketCount b.val * bucketCount c.val * bucketCount d.val * bucketCount e.val : Nat) /
        (denominator : Rat)^5 := by
  simp only [cylinderMass, letter_mass, prior, Rat.mul_one, Rat.natCast_mul]
  simp only [denominator]
  grind

theorem seed_mass_five_positive (a b c d e : Fin 26) :
    0 < cylinderMass 53 [letterEvent a, letterEvent b, letterEvent c, letterEvent d, letterEvent e] := by
  simp only [cylinderMass, letter_mass, Rat.mul_one]
  exact Rat.mul_pos (prior_positive a) (Rat.mul_pos (prior_positive b)
    (Rat.mul_pos (prior_positive c) (Rat.mul_pos (prior_positive d) (prior_positive e))))

end CookieClicker.FullGame.StartupSeed

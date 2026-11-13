import CookieClicker.JavaScriptDyadicArithmeticBridge
/-! Actual logical binary64 addition and subtraction of natural-number encodings.
For operands below2^52, addition agrees with encoding the mathematical sum;
affordable subtraction agrees with encoding the mathematical difference.
The proof uses the general dyadic bridge. No finite operand enumeration or
unchecked native evaluation is used. Source heap and caller invariants are separate.
-/
namespace CookieClicker.JavaScript.NaturalArithmetic
open Float.Model Float.Model.UnpackedFloat RoundingBridge DyadicArithmeticBridge
open CookieClicker.FullGame.GodzamokRounding
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

theorem native_ofNat_round (n : Nat) :
    UnpackedFloat.ofNat Format.binary64 n = round Format.binary64 .positive n 0 := by
  by_cases zero : n = 0
  · subst n; rfl
  · exact native_positive_normalize n 0 (by omega)

theorem ofNat_encoding (n : Nat) :
    Number.ofNat n = (Float.Model.pack (round Format.binary64 .positive n 0)).toBits := by
  simp only [Number.ofNat, Float.Model.ofNat, native_ofNat_round]

theorem positive_small_add_round (m₁ m₂ n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) n₁)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) n₂)
    (nonpositive : min e₁ e₂ ≤ 0) (positiveSum : 0 < n₁+n₂) :
    UnpackedFloat.add Format.binary64
      (.finite .positive m₁ e₁ positive₁) (.finite .positive m₂ e₂ positive₂) =
      round Format.binary64 .positive (n₁+n₂) 0 := by
  let common := min e₁ e₂
  have first := aligned_integer_value m₁ n₁ e₁ common positive₁ (Int.min_le_left _ _) nonpositive represents₁
  have second := aligned_integer_value m₂ n₂ e₂ common positive₂ (Int.min_le_right _ _) nonpositive represents₂
  have exponent : common = -((-common).toNat : Int) := by dsimp only [common]; omega
  have scaledPositive : 0 < (n₁+n₂) * 2^(-common).toNat := Nat.mul_pos positiveSum (Nat.two_pow_pos _)
  rw [native_positive_add_alignment_int, first, second, ← Nat.add_mul]
  change normalize Format.binary64 (((n₁+n₂) * 2^(-common).toNat : Nat) : Int) common .positive = _
  have comparison : compare (((n₁+n₂) * 2^(-common).toNat : Nat) : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp only [normalize, comparison, Int.toNat_natCast]
  have native := native_negative_scaled_round_is_integer_round (n₁+n₂) (-common).toNat positiveSum
  rw [← exponent] at native
  exact native

theorem native_add_small_positive (a b : Nat) (aPos : 0 < a) (bPos : 0 < b)
    (aSmall : a < 2^52) (bSmall : b < 2^52) :
    Number.add (Number.ofNat a) (Number.ofNat b) = Number.ofNat (a+b) := by
  obtain ⟨ma,ea,pa,la,ua,ela,eua,sha,ra⟩ := native_small_integer_round_shape a aPos aSmall
  obtain ⟨mb,eb,pb,lb,ub,elb,eub,shb,rb⟩ := native_small_integer_round_shape b bPos bSmall
  rw [ofNat_encoding a, ofNat_encoding b, sha, shb, ofNat_encoding (a+b)]
  simp only [Number.add, Float.Model.add,
    normal_model_unpack ma ea pa la ua ela (by omega),
    normal_model_unpack mb eb pb lb ub elb (by omega)]
  rw [positive_small_add_round ma mb a b ea eb pa pb ra rb (by omega) (by omega)]

private theorem zero_unpack : (Number.model (Number.ofNat 0)).unpack = .zero .positive := rfl

theorem native_add_zero_left (b : Nat) (bSmall : b < 2^52) :
    Number.add (Number.ofNat 0) (Number.ofNat b) = Number.ofNat b := by
  by_cases zero : b = 0
  · subst b; rfl
  · obtain ⟨mb,eb,pb,lb,ub,elb,eub,shb,_⟩ := native_small_integer_round_shape b (by omega) bSmall
    rw [ofNat_encoding b, shb]
    simp only [Number.add, Float.Model.add, zero_unpack,
      normal_model_unpack mb eb pb lb ub elb (by omega), UnpackedFloat.add]

theorem native_add_zero_right (a : Nat) (aSmall : a < 2^52) :
    Number.add (Number.ofNat a) (Number.ofNat 0) = Number.ofNat a := by
  by_cases zero : a = 0
  · subst a; rfl
  · obtain ⟨ma,ea,pa,la,ua,ela,eua,sha,_⟩ := native_small_integer_round_shape a (by omega) aSmall
    rw [ofNat_encoding a, sha]
    simp only [Number.add, Float.Model.add, zero_unpack,
      normal_model_unpack ma ea pa la ua ela (by omega), UnpackedFloat.add]

theorem native_add_small (a b : Nat) (aSmall : a < 2^52) (bSmall : b < 2^52) :
    Number.add (Number.ofNat a) (Number.ofNat b) = Number.ofNat (a+b) := by
  by_cases az : a = 0
  · subst a; simpa using native_add_zero_left b bSmall
  · by_cases bz : b = 0
    · subst b; simpa using native_add_zero_right a aSmall
    · exact native_add_small_positive a b (by omega) (by omega) aSmall bSmall

theorem native_sub_small_positive (a b : Nat) (aPos : 0 < a) (bPos : 0 < b)
    (aSmall : a < 2^52) (bSmall : b < 2^52) (affordable : b ≤ a) :
    Number.sub (Number.ofNat a) (Number.ofNat b) = Number.ofNat (a-b) := by
  obtain ⟨ma,ea,pa,la,ua,ela,eua,sha,ra⟩ := native_small_integer_round_shape a aPos aSmall
  obtain ⟨mb,eb,pb,lb,ub,elb,eub,shb,rb⟩ := native_small_integer_round_shape b bPos bSmall
  rw [ofNat_encoding a, ofNat_encoding b, sha, shb, ofNat_encoding (a-b)]
  simp only [Number.sub, Float.Model.sub,
    normal_model_unpack ma ea pa la ua ela (by omega),
    normal_model_unpack mb eb pb lb ub elb (by omega)]
  rw [native_integer_sub_is_round ma mb a b ea eb pa pb ra rb affordable]

theorem native_sub_zero_right (a : Nat) (aSmall : a < 2^52) :
    Number.sub (Number.ofNat a) (Number.ofNat 0) = Number.ofNat a := by
  by_cases zero : a = 0
  · subst a; rfl
  · obtain ⟨ma,ea,pa,la,ua,ela,eua,sha,_⟩ := native_small_integer_round_shape a (by omega) aSmall
    rw [ofNat_encoding a, sha]
    simp only [Number.sub, Float.Model.sub, zero_unpack,
      normal_model_unpack ma ea pa la ua ela (by omega), UnpackedFloat.sub]

theorem native_sub_small (a b : Nat) (aSmall : a < 2^52) (bSmall : b < 2^52)
    (affordable : b ≤ a) :
    Number.sub (Number.ofNat a) (Number.ofNat b) = Number.ofNat (a-b) := by
  by_cases bz : b = 0
  · subst b; simpa using native_sub_zero_right a aSmall
  · exact native_sub_small_positive a b (by omega) (by omega) aSmall bSmall affordable

end CookieClicker.JavaScript.NaturalArithmetic

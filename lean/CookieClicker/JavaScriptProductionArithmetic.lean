import CookieClicker.JavaScriptRandomChoiceBridge
import CookieClicker.JavaScriptNaturalArithmetic

/-! Neutral native production multipliers, with explicit finite operands.
These statements preserve binary64 encodings rather than using real arithmetic. -/
namespace CookieClicker.JavaScript.ProductionArithmetic
open Float.Model Float.Model.UnpackedFloat RoundingBridge RandomChoiceBridge NaturalArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem native_one_unpack : (Number.model Number.one).unpack=
    .finite .positive (2^52) (-52) (by decide) := rfl

theorem normal_times_one (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971) :
    let bits:=(Float.Model.pack (.finite .positive m e positive)).toBits
    Number.mul bits Number.one=bits := by
  dsimp only
  unfold Number.mul Float.Model.mul
  rw [normal_model_unpack m e positive lower upper expLower expUpper,native_one_unpack]
  simp only [UnpackedFloat.mul]
  change (Float.Model.pack (roundWithAccuracy Format.binary64 .positive
    (m*2^52) (e+(-52)) .exact)).toBits=_
  rw [show e+(-52)=e-(52:Nat) by omega,
    scaled_normal_round m 52 e positive lower upper expLower]

theorem zero_times_normal (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971) :
    Number.mul Number.positiveZero (Float.Model.pack (.finite .positive m e positive)).toBits=
      Number.positiveZero := by
  unfold Number.mul Float.Model.mul
  rw [normal_model_unpack m e positive lower upper expLower expUpper]
  rfl

theorem zero_times_small_natural (n : Nat) (small : n<2^52) :
    Number.mul Number.positiveZero (Number.ofNat n)=Number.positiveZero := by
  by_cases zero : n=0
  · subst n; rfl
  · obtain ⟨m,e,p,lo,hi,el,eu,shape,_⟩ := native_small_integer_round_shape n (by omega) small
    rw [ofNat_encoding,shape]
    exact zero_times_normal m e p lo hi el (by omega)

theorem small_natural_times_one (n : Nat) (small : n<2^52) :
    Number.mul (Number.ofNat n) Number.one=Number.ofNat n := by
  by_cases zero : n=0
  · subst n; rfl
  · obtain ⟨m,e,p,lo,hi,el,eu,shape,_⟩ := native_small_integer_round_shape n (by omega) small
    rw [ofNat_encoding,shape]
    exact normal_times_one m e p lo hi el (by omega)

end CookieClicker.JavaScript.ProductionArithmetic

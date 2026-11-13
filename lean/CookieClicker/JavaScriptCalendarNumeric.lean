import CookieClicker.JavaScriptIntegerDivision
namespace CookieClicker.JavaScript.CalendarNumeric
open Float.Model Float.Model.UnpackedFloat RoundingBridge NaturalArithmetic DyadicArithmeticBridge
open SeedrandomNormalizationArithmetic IntegerDivision
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-- Affordable subtraction of any two exactly encoded nonnegative native Date
milliseconds below2^53, including cancellation and zero. -/
theorem native_sub_u53 (a b : Nat) (aSmall : a<2^53) (bSmall : b<2^53)
    (affordable : b≤a) : Number.sub (Number.ofNat a) (Number.ofNat b)=Number.ofNat (a-b) := by
  by_cases zero : b=0
  · subst b
    by_cases az : a=0
    · subst a;decide +kernel
    · obtain ⟨m,e,p,lo,hi,el,eu,sh,_⟩:=small_integer_shape a (by omega) aSmall
      rw [sh,Nat.sub_zero]
      simp only [Number.sub,Float.Model.sub,
        normal_model_unpack m e p lo hi el (by omega),
        show (Number.model (Number.ofNat 0)).unpack=.zero .positive from rfl,
        UnpackedFloat.sub]
      exact sh.symm
  · obtain ⟨ma,ea,pa,la,ua,ela,eua,sha,ra⟩:=small_integer_shape a (by omega) aSmall
    obtain ⟨mb,eb,pb,lb,ub,elb,eub,shb,rb⟩:=small_integer_shape b (by omega) bSmall
    rw [sha,shb,ofNat_encoding (a-b)]
    simp only [Number.sub,Float.Model.sub,
      normal_model_unpack ma ea pa la ua ela (by omega),
      normal_model_unpack mb eb pb lb ub elb (by omega)]
    rw [native_integer_sub_is_round ma mb a b ea eb pa pb ra rb affordable]

/-- The native left-associated multiplication tree, not a replacement literal. -/
def sourceDayDenominator : UInt64 :=
  Number.mul (Number.mul (Number.mul (Number.ofNat 1000) (Number.ofNat 60)) (Number.ofNat 60)) (Number.ofNat 24)

theorem source_day_denominator : sourceDayDenominator=Number.ofNat 86400000 := by decide +kernel

/-- Complete native arithmetic tree for the ordinary nonnegative Date-prefix
ordinal. Source Date construction, extraction of the integer milliseconds, and
lexical/heap/Math bindings are separate from this arithmetic statement. -/
theorem source_prefix_ordinal (current januaryZero : Nat)
    (currentBound : current≤8640000000000000)
    (januaryBound : januaryZero≤8640000000000000)
    (ordered : januaryZero≤current) (withinYear : current-januaryZero<367*86400000) :
    Number.floor (Number.div (Number.sub (Number.ofNat current) (Number.ofNat januaryZero)) sourceDayDenominator)=
      Number.ofNat ((current-januaryZero)/86400000) := by
  rw [native_sub_u53 current januaryZero (by omega) (by omega) ordered,source_day_denominator]
  exact native_ordinal_div_floor (current-januaryZero) withinYear

end CookieClicker.JavaScript.CalendarNumeric

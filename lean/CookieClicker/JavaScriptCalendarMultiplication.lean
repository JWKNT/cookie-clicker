import CookieClicker.JavaScriptCalendarNumeric
namespace CookieClicker.JavaScript.CalendarMultiplication
open Float.Model Float.Model.UnpackedFloat RoundingBridge NaturalArithmetic DyadicArithmeticBridge
open IntegerDivisionCore
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

theorem round_large_exact (n : Nat) (e : Int) (large : 2^52≤n) :
    round Format.binary64 .positive n e = roundWithAccuracy Format.binary64 .positive n e .exact := by
  have log : 52≤n.log2 := (Nat.le_log2 (by omega)).mpr large
  have target : e≤Format.binary64.targetExponent (totalExponent n e) := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : (e-Format.binary64.targetExponent (totalExponent n e)).toNat=0 := by omega
  simp only [round,decreaseExponent,gap,Nat.shiftLeft_zero,Int.natCast_zero,Int.sub_zero]

theorem native_positive_mul (a b : Nat) (ap : 0<a) (bp : 0<b) (as : a<2^40) (bs : b<2^40) :
    Number.mul (Number.ofNat a) (Number.ofNat b)=Number.ofNat (a*b) := by
  have ha:=small_shape a ap as
  have hb:=small_shape b bp bs
  have lo:=Nat.mul_le_mul ha.2.2.1 hb.2.2.1
  have large : 2^52≤mantissa a*mantissa b := by omega
  have product : mantissa a*mantissa b=(a*b)*2^(places a+places b) := by
    simp only [mantissa,Nat.pow_add]
    ac_rfl
  rw [ha.2.2.2.2,hb.2.2.2.2,ofNat_encoding (a*b)]
  simp only [Number.mul,Float.Model.mul,
    normal_model_unpack (mantissa a) (-(places a : Int)) (Nat.mul_pos ap (Nat.two_pow_pos _)) ha.2.2.1 ha.2.2.2.1 (by omega) (by omega),
    normal_model_unpack (mantissa b) (-(places b : Int)) (Nat.mul_pos bp (Nat.two_pow_pos _)) hb.2.2.1 hb.2.2.2.1 (by omega) (by omega),
    UnpackedFloat.mul]
  rw [show Sign.positive*Sign.positive=Sign.positive from rfl,←round_large_exact _ _ large,product,
    show -(places a : Int)+(-(places b : Int))= -((places a+places b : Nat):Int) by omega,
    native_negative_scaled_round_is_integer_round (a*b) (places a+places b) (Nat.mul_pos ap bp)]

theorem native_mul_zero_left (b : Nat) (bs : b<2^40) :
    Number.mul (Number.ofNat 0) (Number.ofNat b)=Number.ofNat 0 := by
  by_cases bz : b=0
  · subst b;decide +kernel
  · have h:=small_shape b (by omega) bs
    rw [h.2.2.2.2]
    simp only [Number.mul,Float.Model.mul,
      normal_model_unpack (mantissa b) (-(places b : Int)) (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) h.2.2.1 h.2.2.2.1 (by omega) (by omega),
      show (Number.model (Number.ofNat 0)).unpack=.zero .positive from rfl,
      UnpackedFloat.mul]
    decide +kernel

theorem native_mul_zero_right (a : Nat) (as : a<2^40) :
    Number.mul (Number.ofNat a) (Number.ofNat 0)=Number.ofNat 0 := by
  by_cases az : a=0
  · subst a;decide +kernel
  · have h:=small_shape a (by omega) as
    rw [h.2.2.2.2]
    simp only [Number.mul,Float.Model.mul,
      normal_model_unpack (mantissa a) (-(places a : Int)) (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) h.2.2.1 h.2.2.2.1 (by omega) (by omega),
      show (Number.model (Number.ofNat 0)).unpack=.zero .positive from rfl,
      UnpackedFloat.mul]
    decide +kernel

theorem native_mul (a b : Nat) (as : a<2^40) (bs : b<2^40) :
    Number.mul (Number.ofNat a) (Number.ofNat b)=Number.ofNat (a*b) := by
  by_cases az : a=0
  · subst a;simpa using native_mul_zero_left b bs
  · by_cases bz : b=0
    · subst b;simpa using native_mul_zero_right a as
    · exact native_positive_mul a b (by omega) (by omega) as bs

end CookieClicker.JavaScript.CalendarMultiplication

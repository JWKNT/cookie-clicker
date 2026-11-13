import CookieClicker.JavaScriptRandomChoiceBridge
import CookieClicker.JavaScriptNaturalArithmetic

/-! Native binary64 facts for the retained seeded random normalization loops. -/
namespace CookieClicker.JavaScript.SeedrandomNormalizationArithmetic
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge NaturalArithmetic RandomChoiceBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false

theorem normal_round_exact (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) :
    round Format.binary64 .positive m e = .finite .positive m e positive := by
  unfold round
  rw [normal_target_exact m e lower upper expLower]
  simp only [decreaseExponent,Int.sub_self,Int.toNat_zero,Nat.shiftLeft_zero,Int.natCast_zero,Int.sub_zero]
  exact native_exact_normal_roundWithAccuracy m e positive lower upper expLower

theorem normal_integer_encoding (m n : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e)
    (represents : RepresentsNat (.finite .positive m e positive) n) :
    (Float.Model.pack (.finite .positive m e positive)).toBits = Number.ofNat n := by
  rw [ofNat_encoding]
  apply congrArg (fun value => (Float.Model.pack value).toBits)
  rw [←normal_round_exact m e positive lower upper expLower]
  by_cases nonnegative : 0 ≤ e
  · have value : m*2^e.toNat=n := by simpa only [RepresentsNat,if_pos nonnegative] using represents
    have cast : (e.toNat : Int)=e := Int.toNat_of_nonneg nonnegative
    rw [←cast,native_dyadic_round_is_integer_round m e.toNat positive,value]
  · have value : m=n*2^(-e).toNat := by simpa only [RepresentsNat,if_neg nonnegative] using represents
    have nPositive : 0<n := by
      apply Nat.pos_of_ne_zero
      intro zero
      simp [zero] at value
      omega
    have exponent : e=-((-e).toNat : Int) := by omega
    have same := native_negative_scaled_round_is_integer_round n (-e).toNat nPositive
    rw [←value,←exponent] at same
    exact same

theorem native_256_unpack : (Number.model (Number.ofNat 256)).unpack =
    .finite .positive (2^52) (-44) (by decide) := rfl

theorem multiply_normal_256 (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    Number.mul (Float.Model.pack (.finite .positive m e positive)).toBits (Number.ofNat 256) =
      (Float.Model.pack (.finite .positive m (e+8) positive)).toBits := by
  simp only [Number.mul,Float.Model.mul,
    normal_model_unpack m e positive lower upper expLower expUpper,native_256_unpack,UnpackedFloat.mul]
  change (Float.Model.pack (roundWithAccuracy Format.binary64 .positive (m*2^52) (e+(-44)) .exact)).toBits = _
  rw [show e+(-44)=(e+8)-(52:Nat) by omega]
  rw [scaled_normal_round m 52 (e+8) positive lower upper (by omega)]

theorem divide_normal_two (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1072 ≤ e) (expUpper : e ≤ 971) :
    Number.div (Float.Model.pack (.finite .positive m e positive)).toBits (Number.ofNat 2) =
      (Float.Model.pack (.finite .positive m (e-1) positive)).toBits := by
  have logarithm : m.log2=52 := (Nat.log2_eq_iff (by omega : m≠0)).mpr ⟨lower,upper⟩
  have constantLog : (2^52 : Nat).log2=52 := by decide +kernel
  have target : Format.binary64.targetExponent (totalExponent m e - totalExponent (2^52) (-51)) = e-2 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,logarithm,constantLog]
    omega
  have minimum : min (e-(-51)) (e-2)=e-2 := by omega
  have gap : (e-(-51)-(e-2)).toNat=53 := by omega
  have quotient : (m*2^53)/(2^52)=m*2 := by
    rw [show (2^53 : Nat)=2*2^52 by decide,←Nat.mul_assoc,Nat.mul_div_left _ (Nat.two_pow_pos 52)]
  have remainder : (m*2^53)%(2^52)=0 := by
    rw [show (2^53 : Nat)=2*2^52 by decide,←Nat.mul_assoc,Nat.mul_mod_left]
  have core : divCore Format.binary64 m e (2^52) (-51) = (m*2,e-2,.exact) := by
    simp only [divCore,target,minimum,gap,Nat.shiftLeft_eq,quotient,remainder,accuracyOfFraction,↓reduceIte]
  simp only [Number.div,Float.Model.div,
    normal_model_unpack m e positive lower upper (by omega) expUpper,native_two_unpack,UnpackedFloat.div,
    core]
  have same := scaled_normal_round m 1 (e-1) positive lower upper (by omega)
  simp only [Nat.pow_one,show (e-1)-(1:Nat)=e-2 by omega] at same
  simpa only [show Sign.positive / Sign.positive = Sign.positive from rfl] using
    congrArg (fun value => (Float.Model.pack value).toBits) same

theorem infinity_multiply_256 : Number.mul Number.positiveInfinity (Number.ofNat 256) =
    Number.positiveInfinity := by decide +kernel

theorem infinity_divide_two : Number.div Number.positiveInfinity (Number.ofNat 2) =
    Number.positiveInfinity := by decide +kernel

theorem normal_divide_infinity (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    Number.div (Float.Model.pack (.finite .positive m e positive)).toBits Number.positiveInfinity =
      Number.positiveZero := by
  simp only [Number.div,Float.Model.div,normal_model_unpack m e positive lower upper expLower expUpper]
  rfl

theorem represented_scale (m n places : Nat) (e : Int) (positive : 0 < m)
    (represents : RepresentsNat (.finite .positive m e positive) n) :
    RepresentsNat (.finite .positive m (e+places) positive) (n*2^places) := by
  by_cases oldPositive : 0≤e
  · have old : m*2^e.toNat=n := by simpa only [RepresentsNat,if_pos oldPositive] using represents
    have newPositive : 0≤e+places := by omega
    have exponent : (e+places).toNat=e.toNat+places := by omega
    simp only [RepresentsNat,if_pos newPositive,exponent,Nat.pow_add,←Nat.mul_assoc,old]
  · have old : m=n*2^(-e).toNat := by simpa only [RepresentsNat,if_neg oldPositive] using represents
    by_cases newPositive : 0≤e+places
    · have exponent : (-e).toNat+(e+places).toNat=places := by omega
      simp only [RepresentsNat,if_pos newPositive,old,Nat.mul_assoc,←Nat.pow_add,exponent]
    · have exponent : places+(-(e+places)).toNat=(-e).toNat := by omega
      simp only [RepresentsNat,if_neg newPositive,Nat.mul_assoc,←Nat.pow_add,exponent,old]

theorem small_integer_shape (n : Nat) (positive : 0<n) (small : n<2^53) :
    ∃ (m : Nat) (e : Int) (p : 0<m),
      2^52≤m ∧ m<2^53 ∧ -1074≤e ∧ e≤0 ∧
      Number.ofNat n=(Float.Model.pack (.finite .positive m e p)).toBits ∧
      RepresentsNat (.finite .positive m e p) n := by
  by_cases tiny : n<2^52
  · obtain ⟨m,e,p,lo,hi,el,eu,shape,value⟩ := native_small_integer_round_shape n positive tiny
    refine ⟨m,e,p,lo,hi,el,eu,?_,value⟩
    rw [ofNat_encoding,shape]
  · refine ⟨n,0,positive,by omega,small,by omega,by omega,?_,?_⟩
    · rw [ofNat_encoding,normal_round_exact n 0 positive (by omega) small (by omega)]
    · simp [RepresentsNat]

theorem multiply_small_nat_256 (n : Nat) (small : n<2^53) :
    Number.mul (Number.ofNat n) (Number.ofNat 256) = Number.ofNat (n*256) := by
  by_cases zero : n=0
  · subst n; rfl
  · obtain ⟨m,e,p,lo,hi,el,eu,shape,value⟩ := small_integer_shape n (by omega) small
    rw [shape,multiply_normal_256 m e p lo hi el (by omega)]
    exact normal_integer_encoding m (n*256) (e+8) p lo hi (by omega)
      (represented_scale m n 8 e p value)

end CookieClicker.JavaScript.SeedrandomNormalizationArithmetic

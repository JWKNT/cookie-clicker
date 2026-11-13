import CookieClicker.JavaScriptIntegerDivisionFloor
namespace CookieClicker.JavaScript.IntegerDivision
open Float.Model Float.Model.UnpackedFloat RoundingBridge RandomChoiceBridge
open IntegerDivisionRound IntegerDivisionCore IntegerDivisionFloor
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

theorem exact_scaled_quotient (n d S : Nat) (dp : 0<d) (exact : n%d=0) :
    (n*S)/d=(n/d)*S := by
  have base : n=(n/d)*d := by
    have h:=Nat.mod_add_div n d
    rw [exact,Nat.zero_add,Nat.mul_comm] at h
    exact h.symm
  have expanded : n*S=((n/d)*S)*d := by
    calc
      _ = ((n/d)*d)*S := congrArg (fun x : Nat => x*S) base
      _ = _ := by ac_rfl
  rw [expanded,Nat.mul_div_left _ dp]

theorem native_positive_div_floor (n d : Nat) (np : 0<n) (ns : n<2^40)
    (dp : 0<d) (ds : d<2^40) :
    Number.floor (Number.div (Number.ofNat n) (Number.ofNat d)) = Number.ofNat (n/d) := by
  have hn:=small_shape n np ns
  have hd:=small_shape d dp ds
  have sb:=scale_bounds n d np ns dp ds
  let D:=scale n d
  let m:=(n*2^D)/d
  let a:=accuracyOfFraction ((mantissa n*2^53)%(mantissa d)) (mantissa d)
  have bounds : 2^52≤m ∧ m<2^54 := by
    have h:=divided_mantissa_bounds (mantissa n) (mantissa d) hn.2.2.1 hn.2.2.2.1 hd.2.2.1 hd.2.2.2.1
    rw [quotient_alignment n d np ns dp ds] at h
    exact h
  obtain ⟨N,shape,lo,hi,exactRound⟩ := native_round_bounded m (-(D:Int)) a bounds.1 bounds.2 (by dsimp [D];omega)
  have exact : n%d=0 → N=(n/d)*2^D := by
    intro divexact
    have ae : a=.exact := exact_remainder n d np ns dp ds divexact
    have me : m=(n/d)*2^D := exact_scaled_quotient n d (2^D) dp divexact
    have even : m%2=0 := by
      have Dpos : 0<D := by dsimp [D];omega
      have pow : 2^D=2^(D-1)*2 := by rw [←Nat.pow_succ];congr;omega
      rw [me,pow,←Nat.mul_assoc,Nat.mul_mod_left]
    exact (exactRound ae even).trans me
  have quotient : N/2^D=n/d := quotient_stable n d (2^D) m N dp (scale_gap n d np ns dp ds) rfl lo hi exact
  have result:=shape_floor (roundWithAccuracy Format.binary64 .positive m (-(D:Int)) a) D N (by dsimp [D];omega) (by dsimp [D];omega) shape
  rw [quotient] at result
  rw [hn.2.2.2.2,hd.2.2.2.2]
  simp only [Number.div,Float.Model.div,
    normal_model_unpack (mantissa n) (-(places n : Int)) (Nat.mul_pos np (Nat.two_pow_pos _)) hn.2.2.1 hn.2.2.2.1 (by omega) (by omega),
    normal_model_unpack (mantissa d) (-(places d : Int)) (Nat.mul_pos dp (Nat.two_pow_pos _)) hd.2.2.1 hd.2.2.2.1 (by omega) (by omega),
    UnpackedFloat.div,actual_div_core n d np ns dp ds]
  exact result

/-- Native binary64 division followed by the actual Number.floor agrees with
integer division for every numerator and positive denominator below2^40.
This covers all within-year millisecond numerators and the ordinary Date-prefix
computus quotients, without enumerating years or possible milliseconds. -/
theorem native_div_floor (n d : Nat) (ns : n<2^40) (dp : 0<d) (ds : d<2^40) :
    Number.floor (Number.div (Number.ofNat n) (Number.ofNat d)) = Number.ofNat (n/d) := by
  by_cases zero : n=0
  · subst n
    have hd:=small_shape d dp ds
    rw [hd.2.2.2.2]
    simp only [Number.div,Float.Model.div,
      normal_model_unpack (mantissa d) (-(places d : Int)) (Nat.mul_pos dp (Nat.two_pow_pos _)) hd.2.2.1 hd.2.2.2.1 (by omega) (by omega)]
    rw [Nat.zero_div,show (Number.model (Number.ofNat 0)).unpack=.zero .positive from rfl]
    simp only [UnpackedFloat.div]
    decide +kernel
  · exact native_positive_div_floor n d (by omega) ns dp ds

theorem native_ordinal_div_floor (n : Nat) (bound : n<367*86400000) :
    Number.floor (Number.div (Number.ofNat n) (Number.ofNat 86400000)) = Number.ofNat (n/86400000) :=
  native_div_floor n 86400000 (by omega) (by decide) (by decide)

end CookieClicker.JavaScript.IntegerDivision

import CookieClicker.JavaScriptIntegerDivisionRound
namespace CookieClicker.JavaScript.IntegerDivisionCore
open Float.Model Float.Model.UnpackedFloat RoundingBridge DyadicArithmeticBridge NaturalArithmetic
open SeedrandomNormalizationArithmetic IntegerDivisionRound
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

def places (n : Nat) := 52-n.log2
def mantissa (n : Nat) := n*2^(places n)
def scale (n d : Nat) := 53+places n-places d

theorem small_shape (n : Nat) (positive : 0<n) (small : n<2^40) :
    13≤places n ∧ places n≤52 ∧ 2^52≤mantissa n ∧ mantissa n<2^53 ∧
    Number.ofNat n=(Float.Model.pack (.finite .positive (mantissa n) (-(places n : Int))
      (Nat.mul_pos positive (Nat.two_pow_pos _)))).toBits := by
  have log : n.log2<40 := (Nat.log2_lt (by omega)).mpr small
  obtain ⟨lo,hi⟩ := Random.significand_bounds positive (by omega : n<2^53)
  have sh := native_small_negative_scaled_round_shape n 0 positive (by omega)
  simp only [Nat.pow_zero,Nat.mul_one,Int.natCast_zero,Int.neg_zero] at sh
  refine ⟨by unfold places;omega,by unfold places;omega,lo,hi,?_⟩
  rw [ofNat_encoding,sh]
  rfl

theorem scale_bounds (n d : Nat) (np : 0<n) (ns : n<2^40) (dp : 0<d) (ds : d<2^40) :
    14≤scale n d ∧ scale n d≤92 ∧ scale n d+places d=53+places n := by
  have hn:=small_shape n np ns
  have hd:=small_shape d dp ds
  unfold scale
  omega

theorem divided_mantissa_bounds (m₁ m₂ : Nat)
    (lo₁ : 2^52≤m₁) (hi₁ : m₁<2^53) (lo₂ : 2^52≤m₂) (hi₂ : m₂<2^53) :
    2^52≤(m₁*2^53)/m₂ ∧ (m₁*2^53)/m₂<2^54 := by
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).mpr
    omega
  · apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    omega

theorem numerator_alignment (n d : Nat) (np : 0<n) (ns : n<2^40) (dp : 0<d) (ds : d<2^40) :
    mantissa n*2^53=(n*2^(scale n d))*2^(places d) := by
  have e:=(scale_bounds n d np ns dp ds).2.2
  simp only [mantissa,Nat.mul_assoc,←Nat.pow_add]
  congr 2
  omega

theorem quotient_alignment (n d : Nat) (np : 0<n) (ns : n<2^40) (dp : 0<d) (ds : d<2^40) :
    (mantissa n*2^53)/(mantissa d)=(n*2^(scale n d))/d := by
  rw [numerator_alignment n d np ns dp ds]
  unfold mantissa
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)

theorem scale_gap (n d : Nat) (np : 0<n) (ns : n<2^40) (dp : 0<d) (ds : d<2^40) :
    4*d<2^(scale n d) := by
  have hn:=small_shape n np ns
  have hd:=small_shape d dp ds
  have e:=(scale_bounds n d np ns dp ds).2.2
  have pp : 2^55≤(2 : Nat)^(scale n d+places d) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add] at pp
  have mm : d*2^(places d)<2^53 := hd.2.2.2.1
  have bound : (4*d)*2^(places d)<2^(scale n d)*2^(places d) := by
    rw [show (4*d)*2^(places d)=4*(d*2^(places d)) by ac_rfl]
    omega
  exact Nat.lt_of_mul_lt_mul_right bound

theorem actual_div_core (n d : Nat) (np : 0<n) (ns : n<2^40) (dp : 0<d) (ds : d<2^40) :
    divCore Format.binary64 (mantissa n) (-(places n : Int)) (mantissa d) (-(places d : Int)) =
      ((n*2^(scale n d))/d,-(scale n d : Int),
        accuracyOfFraction ((mantissa n*2^53)%(mantissa d)) (mantissa d)) := by
  have hn:=small_shape n np ns
  have hd:=small_shape d dp ds
  have sb:=scale_bounds n d np ns dp ds
  have logn : (mantissa n).log2=52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hn.2.2.1,hn.2.2.2.1⟩
  have logd : (mantissa d).log2=52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hd.2.2.1,hd.2.2.2.1⟩
  have target : Format.binary64.targetExponent
      (totalExponent (mantissa n) (-(places n : Int))-totalExponent (mantissa d) (-(places d : Int)))=
        -(scale n d : Int) := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,logn,logd]
    omega
  have min : min (-(places n : Int)-(-(places d : Int))) (-(scale n d : Int))= -(scale n d : Int) := by omega
  have gap : (-(places n : Int)-(-(places d : Int))-(-(scale n d : Int))).toNat=53 := by omega
  simp only [divCore,target,min,gap,Nat.shiftLeft_eq,quotient_alignment n d np ns dp ds]

theorem exact_remainder (n d : Nat) (np : 0<n) (ns : n<2^40) (dp : 0<d) (ds : d<2^40)
    (exact : n%d=0) :
    accuracyOfFraction ((mantissa n*2^53)%(mantissa d)) (mantissa d)=.exact := by
  have multiple : n=(n/d)*d := by
    have h:=Nat.mod_add_div n d
    rw [exact,Nat.zero_add,Nat.mul_comm] at h
    exact h.symm
  rw [numerator_alignment n d np ns dp ds]
  unfold mantissa
  have reordered : n*2^(scale n d)=(n/d*2^(scale n d))*d := by
    calc
      _ = (n/d*d)*2^(scale n d) := congrArg (fun x : Nat => x*2^(scale n d)) multiple
      _ = _ := by ac_rfl
  rw [Nat.mul_mod_mul_right,reordered,Nat.mul_mod_left]
  simp [accuracyOfFraction]

end CookieClicker.JavaScript.IntegerDivisionCore

import CookieClicker.JavaScriptSeedrandomNormalizationArithmetic
namespace CookieClicker.JavaScript.IntegerDivisionRound
open Float.Model Float.Model.UnpackedFloat RoundingBridge RandomChoiceBridge
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

theorem accuracy_bounds (m : Nat) (a : Accuracy) :
    m ≤ a.roundToNearestEven m ∧ a.roundToNearestEven m ≤ m+1 := by
  cases a with
  | exact => simp [Accuracy.roundToNearestEven]
  | inexact order => cases order <;> simp [Accuracy.roundToNearestEven] <;> omega

theorem normal_shift_accuracy (m : Nat) (e : Int) (a : Accuracy)
    (lower : 2^52≤m) (upper : m<2^53) (lowE : -1074≤e) :
    shiftToTargetExponent Format.binary64 m e a =
      (ExtendedMantissa.ofMantissaAndAccuracy m a,e) := by
  have log : m.log2=52 := (Nat.log2_eq_iff (by omega : m≠0)).mpr ⟨lower,upper⟩
  have target : Format.binary64.targetExponent (totalExponent m e)=e := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,log]
    omega
  simp [shiftToTargetExponent,target,shiftToExponent,HShiftRight.hShiftRight,Nat.repeat]

theorem round_initial (m : Nat) (a : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m a).roundedMantissa = a.roundToNearestEven m := by
  cases a with
  | exact => rfl
  | inexact o => cases o <;> rfl

/-- The final native carry shift retains the rounded dyadic value. -/
theorem carry_shape (m : Nat) (e : Int) (lower : 2^52≤m) (upper : m≤2^53)
    (lowE : -1074≤e) :
    ∃ (r k : Nat), k≤1 ∧ 2^52≤r ∧ r<2^53 ∧
      shiftToTargetExponent Format.binary64 m e .exact = (⟨r,false,false⟩,e+k) ∧
      r*2^k=m := by
  by_cases small : m<2^53
  · refine ⟨m,0,by omega,lower,small,?_,by simp⟩
    simpa [ExtendedMantissa.ofMantissaAndAccuracy] using normal_shift_accuracy m e .exact lower small lowE
  · have eq : m=2^53 := by omega
    subst m
    refine ⟨2^52,1,by omega,by omega,by decide,?_,by decide⟩
    have h := scaled_normal_shift (2^52) 1 (e+1) (by decide) (by decide) (by decide) (by omega)
    simpa only [Int.natCast_one, Int.add_sub_cancel, show (2^52)*(2^1)=(2^53 : Nat) by decide,
      show e+1-(1:Nat)=e by omega] using h

/-- Result at a fixed denominator before the native carry normalization. -/
def Shape (value : UnpackedFloat) (e : Int) (n : Nat) : Prop :=
  ∃ (m k : Nat) (positive : 0<m), k≤2 ∧ 2^52≤m ∧ m<2^53 ∧
    value=.finite .positive m (e+k) positive ∧ m*2^k=n

theorem finish_round (em : ExtendedMantissa) (e : Int)
    (lower : 2^52≤em.roundedMantissa) (upper : em.roundedMantissa≤2^53)
    (lowE : -1074≤e) :
    ∃ (m k : Nat) (positive : 0<m), k≤1 ∧ 2^52≤m ∧ m<2^53 ∧
      (let pair := shiftToTargetExponent Format.binary64 em.roundedMantissa e .exact
       if h : pair.1.mantissa=0 then UnpackedFloat.zero .positive
       else .finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h))
        = .finite .positive m (e+k) positive ∧ m*2^k=em.roundedMantissa := by
  obtain ⟨m,k,kb,lo,hi,sh,v⟩ := carry_shape em.roundedMantissa e lower upper lowE
  refine ⟨m,k,by omega,kb,lo,hi,?_,v⟩
  rw [sh]
  simp only [show m≠0 by omega,↓reduceDIte]

theorem round_small_shape (m : Nat) (e : Int) (a : Accuracy)
    (lower : 2^52≤m) (upper : m<2^53) (lowE : -1074≤e) :
    Shape (roundWithAccuracy Format.binary64 .positive m e a) e (a.roundToNearestEven m) := by
  have bounds := accuracy_bounds m a
  have lo : 2^52≤(ExtendedMantissa.ofMantissaAndAccuracy m a).roundedMantissa := by
    rw [round_initial]; omega
  have hi : (ExtendedMantissa.ofMantissaAndAccuracy m a).roundedMantissa≤2^53 := by
    rw [round_initial]; omega
  obtain ⟨r,k,p,kb,l,u,sh,v⟩ := finish_round _ e lo hi lowE
  refine ⟨r,k,p,by omega,l,u,?_,?_⟩
  · unfold roundWithAccuracy
    rw [normal_shift_accuracy m e a lower upper lowE]
    exact sh
  · simpa only [round_initial] using v

theorem wide_shift (m : Nat) (e : Int) (a : Accuracy)
    (lower : 2^53≤m) (upper : m<2^54) (lowE : -1074≤e) :
    shiftToTargetExponent Format.binary64 m e a =
      ((ExtendedMantissa.ofMantissaAndAccuracy m a).shiftRightOne,e+1) := by
  have log : m.log2=53 := (Nat.log2_eq_iff (by omega : m≠0)).mpr ⟨lower,upper⟩
  have target : Format.binary64.targetExponent (totalExponent m e)=e+1 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,log]
    omega
  simp only [shiftToTargetExponent,target,shiftToExponent,show (e+1-e).toNat=1 by omega]
  rfl

theorem shifted_round_bounds (m : Nat) (a : Accuracy) :
    m/2 ≤ ((ExtendedMantissa.ofMantissaAndAccuracy m a).shiftRightOne).roundedMantissa ∧
    ((ExtendedMantissa.ofMantissaAndAccuracy m a).shiftRightOne).roundedMantissa ≤ m/2+1 := by
  have h := accuracy_bounds m
  cases a with
  | exact => simp [ExtendedMantissa.shiftRightOne,ExtendedMantissa.ofMantissaAndAccuracy,
      ExtendedMantissa.roundedMantissa,ExtendedMantissa.accuracy,Accuracy.roundToNearestEven] <;> split <;> omega
  | inexact o => cases o <;> simp [ExtendedMantissa.shiftRightOne,ExtendedMantissa.ofMantissaAndAccuracy,
      ExtendedMantissa.roundedMantissa,ExtendedMantissa.accuracy,Accuracy.roundToNearestEven] <;> split <;> omega

theorem round_wide_shape (m : Nat) (e : Int) (a : Accuracy)
    (lower : 2^53≤m) (upper : m<2^54) (lowE : -1074≤e) :
    Shape (roundWithAccuracy Format.binary64 .positive m e a) e
      (2*((ExtendedMantissa.ofMantissaAndAccuracy m a).shiftRightOne).roundedMantissa) := by
  let em := (ExtendedMantissa.ofMantissaAndAccuracy m a).shiftRightOne
  have bounds := shifted_round_bounds m a
  have lo : 2^52≤em.roundedMantissa := by dsimp [em]; omega
  have hi : em.roundedMantissa≤2^53 := by dsimp [em]; omega
  obtain ⟨r,k,p,kb,l,u,sh,v⟩ := finish_round em (e+1) lo hi (by omega)
  refine ⟨r,k+1,p,by omega,l,u,?_,?_⟩
  · unfold roundWithAccuracy
    rw [wide_shift m e a lower upper lowE]
    simpa only [show e+(k+1:Nat)=e+1+k by omega] using sh
  · rw [Nat.pow_succ, ←Nat.mul_assoc]
    simpa only [em,Nat.mul_comm] using congrArg (fun x : Nat => x*2) v

theorem native_round_error (m : Nat) (e : Int) (a : Accuracy)
    (lower : 2^52≤m) (upper : m<2^54) (lowE : -1074≤e) :
    ∃ n : Nat, Shape (roundWithAccuracy Format.binary64 .positive m e a) e n ∧
      m≤n+1 ∧ n≤m+2 := by
  by_cases small : m<2^53
  · refine ⟨a.roundToNearestEven m,round_small_shape m e a lower small lowE,?_⟩
    have h := accuracy_bounds m a
    omega
  · refine ⟨2*((ExtendedMantissa.ofMantissaAndAccuracy m a).shiftRightOne).roundedMantissa,
      round_wide_shape m e a (by omega) upper lowE,?_⟩
    have h := shifted_round_bounds m a
    omega

theorem round_exact_even_shape (m : Nat) (e : Int)
    (lower : 2^52≤m) (upper : m<2^54) (lowE : -1074≤e) (even : m%2=0) :
    Shape (roundWithAccuracy Format.binary64 .positive m e .exact) e m := by
  by_cases small : m<2^53
  · exact round_small_shape m e .exact lower small lowE
  · have shifted : ((ExtendedMantissa.ofMantissaAndAccuracy m .exact).shiftRightOne).roundedMantissa=m/2 := by
      simp [ExtendedMantissa.shiftRightOne,ExtendedMantissa.ofMantissaAndAccuracy,even,
        ExtendedMantissa.roundedMantissa,ExtendedMantissa.accuracy,Accuracy.roundToNearestEven]
    have h := round_wide_shape m e .exact (by omega) upper lowE
    rw [shifted,show 2*(m/2)=m by omega] at h
    exact h

theorem native_round_bounded (m : Nat) (e : Int) (a : Accuracy)
    (lower : 2^52≤m) (upper : m<2^54) (lowE : -1074≤e) :
    ∃ n : Nat, Shape (roundWithAccuracy Format.binary64 .positive m e a) e n ∧
      m≤n+1 ∧ n≤m+2 ∧ (a=.exact → m%2=0 → n=m) := by
  by_cases exactEven : a=.exact ∧ m%2=0
  · obtain ⟨rfl,even⟩ := exactEven
    exact ⟨m,round_exact_even_shape m e lower upper lowE even,by omega,by omega,by simp⟩
  · obtain ⟨n,sh,lo,hi⟩ := native_round_error m e a lower upper lowE
    exact ⟨n,sh,lo,hi,by intro h e; exact False.elim (exactEven ⟨h,e⟩)⟩

end CookieClicker.JavaScript.IntegerDivisionRound

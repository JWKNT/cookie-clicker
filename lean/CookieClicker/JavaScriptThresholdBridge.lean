import CookieClicker.JavaScriptScaledArithmeticBridge
import CookieClicker.JavaScriptLumpSource

/-! Native comparisons and the source sugar-lump activation guard.
Canonical scaled positive values preserve their mathematical order under the
actual Float.Model comparison. This is composed with the intact canLumps body,
then with the earned15 passive recurrence. The source guard runs in its explicit
field layout; the complete startup/production/Logic frame invariant is separate.
-/
namespace CookieClicker.JavaScript.ThresholdBridge
open Float.Model Float.Model.UnpackedFloat RoundingBridge ScaledArithmeticBridge
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem canonical_scaled_exponent_order (m₁ m₂ D : Nat) (e₁ e₂ : Int)
    (lower₁ : 2^52 ≤ m₁) (upper₂ : m₂ < 2^53)
    (scale₁ : -(D:Int) ≤ e₁) (scale₂ : -(D:Int) ≤ e₂)
    (ordered : m₁*2^(e₁+D).toNat ≤ m₂*2^(e₂+D).toNat) : e₁ ≤ e₂ := by
  by_cases order : e₁ ≤ e₂
  · exact order
  · have exponentOrder : (e₂+D).toNat+1 ≤ (e₁+D).toNat := by omega
    have powerOrder := Nat.pow_le_pow_right (by decide : 0 < 2) exponentOrder
    have productLower := Nat.mul_le_mul lower₁ powerOrder
    have productUpper := Nat.mul_lt_mul_of_pos_right upper₂ (Nat.two_pow_pos (e₂+D).toNat)
    have nextPower : 2^((e₂+D).toNat+1) = 2^(e₂+D).toNat*2 := by rw [Nat.pow_succ]
    rw [nextPower] at productLower
    have rearrange : 2^52*(2^(e₂+D).toNat*2) = 2^53*2^(e₂+D).toNat := by omega
    rw [rearrange] at productLower
    omega

theorem native_scaled_less_equal (left right : UInt64) (D a b : Nat)
    (scaleBound : D ≤ 1074) (leftValue : ScaledNormal left D a)
    (rightValue : ScaledNormal right D b) (ordered : a ≤ b) :
    Number.lessEqual left right = true := by
  obtain ⟨m₁,e₁,p₁,l₁,u₁,s₁,f₁,sh₁,v₁⟩ := leftValue
  obtain ⟨m₂,e₂,p₂,l₂,u₂,s₂,f₂,sh₂,v₂⟩ := rightValue
  have values : m₁*2^(e₁+D).toNat ≤ m₂*2^(e₂+D).toNat := by rw [v₁,v₂]; exact ordered
  have exponents := canonical_scaled_exponent_order m₁ m₂ D e₁ e₂ l₁ u₂ s₁ s₂ values
  rw [sh₁,sh₂]
  simp only [Number.lessEqual,Float.Model.le,
    normal_model_unpack m₁ e₁ p₁ l₁ u₁ (by omega) f₁,
    normal_model_unpack m₂ e₂ p₂ l₂ u₂ (by omega) f₂,
    UnpackedFloat.le,UnpackedFloat.compare]
  by_cases same : e₁ = e₂
  · subst e₂
    have mantissas : m₁ ≤ m₂ := Nat.le_of_mul_le_mul_right values (Nat.two_pow_pos _)
    have comparison : compare e₁ e₁ = .eq := by simp
    rw [comparison]
    by_cases equalM : m₁ = m₂
    · subst m₂; simp
    · have lessM : m₁ < m₂ := by omega
      rw [Nat.compare_eq_lt.mpr lessM]
      rfl
  · have lessE : e₁ < e₂ := by omega
    rw [Int.compare_eq_lt.mpr lessE]
    rfl

theorem billion_scaled : ScaledNormal (Number.ofNat 1000000000) 61 (1000000000*2^61) := by
  exact ⟨1000000000*2^23,-23,by decide,by decide,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel⟩

theorem native_billion_threshold (bits : UInt64) (n : Nat)
    (value : ScaledValue bits 61 n) (large : 1000000000*2^61 ≤ n) :
    Number.lessEqual (Number.ofNat 1000000000) bits = true := by
  rcases value with ⟨_,zero⟩ | normal
  · omega
  · exact native_scaled_less_equal _ bits 61 _ n (by decide) billion_scaled normal large

private theorem neg_one_less_self : Number.lessThan 13830554455654793216 13830554455654793216 = false := by decide +kernel
private theorem zero_equal_one : Number.equal 0 4607182418800017408 = false := by decide +kernel
private theorem neg_one_bits : Number.neg 4607182418800017408 = 13830554455654793216 := by decide +kernel
attribute [local cbv_opaque] Number.add Number.lessEqual Number.lessThan Number.equal Number.ofNat Number.neg
attribute [local cbv_eval] neg_one_less_self zero_equal_one neg_one_bits


def eligibility (earned : UInt64) := LumpSource.eligibilityState
  (Number.neg Number.one) Number.positiveZero earned Number.positiveZero

theorem actual_canLumps_test (earned : UInt64) :
    (run 57 (eligibility earned)).control =
      .expressionResult (.value (.boolean
        (Number.lessEqual 4741671816366391296 (Number.add earned Number.positiveZero)))) := by
  cbv

theorem actual_canLumps_true_tail (earned : UInt64) :
    status (run 13 {run 57 (eligibility earned) with
      control := .expressionResult (.value (.boolean true))}) = .value (.boolean true) := by
  cbv

theorem run_stopped (fuel : Nat) (machine : Machine) (stopped : status machine ≠ .running) :
    run fuel machine = machine := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [run,beq_iff_eq,if_neg stopped]

theorem run_add (first more : Nat) (machine : Machine) :
    run (first+more) machine = run more (run first machine) := by
  induction first generalizing machine with
  | zero => simp only [Nat.zero_add,run]
  | succ first ih =>
    rw [show first+1+more = (first+more)+1 by omega]
    by_cases running : status machine = .running
    · simp only [run,beq_iff_eq,if_pos running]
      exact ih (step machine)
    · rw [run_stopped _ machine running,run_stopped _ machine running,run_stopped _ machine running]

theorem actual_canLumps_true (earned : UInt64)
    (threshold : Number.lessEqual 4741671816366391296 (Number.add earned Number.positiveZero) = true) :
    status (run 70 (eligibility earned)) = .value (.boolean true) := by
  have control := actual_canLumps_test earned
  rw [threshold] at control
  have update : {run 57 (eligibility earned) with control := .expressionResult (.value (.boolean true))} =
      run 57 (eligibility earned) := by rw [← control]
  change status (run (57+13) (eligibility earned)) = _
  rw [run_add,← update]
  exact actual_canLumps_true_tail earned

private theorem billion_literal : (4741671816366391296 : UInt64) = Number.ofNat 1000000000 := by
  decide +kernel

theorem native_canLumps_above_billion (earned : UInt64) (n : Nat)
    (value : ScaledValue earned 61 n) (large : 1000000000*2^61 ≤ n) :
    status (run 70 (eligibility earned)) = .value (.boolean true) := by
  have threshold := native_billion_threshold earned n value large
  have normal : ScaledNormal earned 61 n := by
    rcases value with ⟨_,zero⟩ | normal
    · omega
    · exact normal
  obtain ⟨m,e,positive,lower,upper,scaleLower,expUpper,shape,_⟩ := normal
  have addZero : Number.add earned Number.positiveZero = earned := by
    rw [shape]
    exact FractionalArithmeticBridge.number_add_zero_right m e positive lower upper (by omega) expUpper
  apply actual_canLumps_true
  rw [addZero,billion_literal]
  exact threshold

/-- The actual canLumps callback accepts at a finite prefix of the native
passive earned recurrence starting from the fifteen initial cookie clicks.
The full-game invariant that supplies these periodic source credits is separate. -/
theorem earned15_native_canLumps_finite_prefix :
    ∃ k ≤ 512*1000000000,
      status (run 70 (eligibility (nativeIterations (Number.ofNat 15)
        (Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30)) k))) =
          .value (.boolean true) := by
  open CookieClicker.FullGame.BootstrapArithmetic in
  obtain ⟨k,bound,reached⟩ := passive_numerator_hits_target_from (15*2^61)
  refine ⟨k,bound,?_⟩
  have value := native_iterations_scaled (Number.ofNat 15) (15*2^61)
    CookieClicker.FullGame.BootstrapArithmetic.passiveIncrement 61 k (by decide)
    (Or.inr native_fifteen_scaled) (by decide) (by decide) (by decide) (by decide)
  rw [← passive_credit_encoding] at value
  exact native_canLumps_above_billion _ _ value reached

end CookieClicker.JavaScript.ThresholdBridge

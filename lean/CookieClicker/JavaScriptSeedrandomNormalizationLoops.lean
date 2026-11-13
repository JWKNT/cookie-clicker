import CookieClicker.JavaScriptSeedrandomNormalizationGuards
import CookieClicker.Arc4Orbit

/-! The normalization recurrence uses the interpreter's native Number operations.
A separate source loop refinement is still required for these finite checks. -/
namespace CookieClicker.JavaScript.SeedrandomNormalizationLoops
open Float.Model Float.Model.UnpackedFloat
open SeedrandomNormalizationArithmetic SeedrandomNormalizationGuards
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

structure State where
  numerator : UInt64
  denominator : UInt64
  extra : UInt64
  generator : CookieClicker.Arc4Orbit.State

def growthStep (state : State) : State := {
  numerator := Number.mul (Number.add state.numerator state.extra) (Number.ofNat 256)
  denominator := Number.mul state.denominator (Number.ofNat 256)
  extra := Number.ofNat (CookieClicker.Arc4Orbit.output state.generator).toNat
  generator := CookieClicker.Arc4Orbit.next state.generator }

def shrinkStep (state : State) : State := { state with
  numerator := Number.div state.numerator (Number.ofNat 2)
  denominator := Number.div state.denominator (Number.ofNat 2)
  extra := Number.unsignedShiftRight state.extra Number.one }

def fill : Nat → State → Option State
  | 0, _ => none
  | fuel+1, state =>
    if Number.lessThan state.numerator (Number.ofNat (2^52)) then fill fuel (growthStep state)
    else some state

def shrink : Nat → State → Option State
  | 0, _ => none
  | fuel+1, state =>
    if Number.lessEqual (Number.ofNat (2^53)) state.numerator then shrink fuel (shrinkStep state)
    else some state

def returned (state : State) : UInt64 := Number.div (Number.add state.numerator state.extra) state.denominator

theorem shrink_normal (m k : Nat) (positive : 0<m) (lower : 2^52≤m) (upper : m<2^53)
    (small : k≤971) (denominator extra : UInt64) (generator : CookieClicker.Arc4Orbit.State) :
    ∃ final : State,
      shrink (k+1) ⟨(Float.Model.pack (.finite .positive m k positive)).toBits,denominator,extra,generator⟩ = some final ∧
      final.numerator=(Float.Model.pack (.finite .positive m 0 positive)).toBits ∧
      final.generator=generator := by
  induction k generalizing denominator extra with
  | zero =>
    refine ⟨⟨(Float.Model.pack (.finite .positive m 0 positive)).toBits,denominator,extra,generator⟩,?_,rfl,rfl⟩
    simp only [shrink,Int.natCast_zero,normal_shrink_guard m 0 positive lower upper (by omega) (by omega)]
    rfl
  | succ k induction =>
    have guard := normal_shrink_guard m (k+1) positive lower upper (by omega) (by omega)
    have divided := divide_normal_two m (k+1) positive lower upper (by omega) (by omega)
    have reduced : (k+1 : Int)-1=k := by omega
    rw [reduced] at divided
    obtain ⟨final,done,value,retained⟩ := induction (by omega)
      (Number.div denominator (Number.ofNat 2)) (Number.unsignedShiftRight extra Number.one)
    refine ⟨final,?_,value,retained⟩
    rw [shrink]
    simp only [Int.natCast_add,Int.natCast_one,guard,
      show decide (1≤(k:Int)+1)=true by simp only [decide_eq_true_eq]; omega,↓reduceIte]
    simp only [shrinkStep,divided]
    exact done

theorem growth_numerator (n c : Nat) (small : n<2^52) (byte : c<256) :
    Number.mul (Number.add (Number.ofNat n) (Number.ofNat c)) (Number.ofNat 256) =
      Number.ofNat ((n+c)*256) := by
  rw [NaturalArithmetic.native_add_small n c small (by omega),multiply_small_nat_256 (n+c) (by omega)]

theorem growth_numerator_bound (n c : Nat) (small : n<2^52) (byte : c<256) :
    (n+c)*256 ≤ 2^60+65024 := by omega

theorem zero_growth_arithmetic :
    Number.mul (Number.add Number.positiveZero Number.positiveZero) (Number.ofNat 256) =
      Number.positiveZero := by decide +kernel

theorem fill_all_zero (fuel : Nat) (generator : CookieClicker.Arc4Orbit.State)
    (zero : ∀ n, CookieClicker.Arc4Orbit.output
      (CookieClicker.FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next n generator)=0)
    (denominator : UInt64) :
    fill fuel ⟨Number.positiveZero,denominator,Number.positiveZero,generator⟩ = none := by
  induction fuel generalizing generator denominator with
  | zero => rfl
  | succ fuel induction =>
    have first : CookieClicker.Arc4Orbit.output generator=0 := zero 0
    have later : ∀ n, CookieClicker.Arc4Orbit.output
        (CookieClicker.FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next n
          (CookieClicker.Arc4Orbit.next generator))=0 := by
      intro n
      simpa only [CookieClicker.FiniteInvertibleOrbit.run_succ_start] using zero (n+1)
    rw [fill]
    simp only [zero_growth_guard,↓reduceIte]
    have next : growthStep ⟨Number.positiveZero,denominator,Number.positiveZero,generator⟩ =
        ⟨Number.positiveZero,Number.mul denominator (Number.ofNat 256),Number.positiveZero,
          CookieClicker.Arc4Orbit.next generator⟩ := by
      simp only [growthStep,zero_growth_arithmetic,first]
      rfl
    rw [next]
    exact induction _ later _

def encoded (n : Nat) (denominator : UInt64) (extra : UInt8)
    (generator : CookieClicker.Arc4Orbit.State) : State :=
  ⟨Number.ofNat n,denominator,Number.ofNat extra.toNat,generator⟩

theorem growth_encoded (n : Nat) (small : n<2^52) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State) :
    growthStep (encoded n denominator extra generator) =
      encoded ((n+extra.toNat)*256) (Number.mul denominator (Number.ofNat 256))
        (CookieClicker.Arc4Orbit.output generator) (CookieClicker.Arc4Orbit.next generator) := by
  simp only [growthStep,encoded,growth_numerator n extra.toNat small extra.toNat_lt]

theorem fill_encoded_step (fuel n : Nat) (small : n<2^52) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State) :
    fill (fuel+1) (encoded n denominator extra generator) =
      fill fuel (encoded ((n+extra.toNat)*256) (Number.mul denominator (Number.ofNat 256))
        (CookieClicker.Arc4Orbit.output generator) (CookieClicker.Arc4Orbit.next generator)) := by
  rw [fill]
  rw [show (encoded n denominator extra generator).numerator=Number.ofNat n from rfl,
    natural_growth_guard n (by omega)]
  simp only [small,decide_true,↓reduceIte]
  rw [growth_encoded n small]

theorem fill_encoded_exit (fuel n : Nat) (bounded : n<2^61) (large : 2^52≤n)
    (denominator : UInt64) (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State) :
    fill (fuel+1) (encoded n denominator extra generator) = some (encoded n denominator extra generator) := by
  rw [fill]
  rw [show (encoded n denominator extra generator).numerator=Number.ofNat n from rfl,
    natural_growth_guard n (by omega)]
  simp only [show ¬n<2^52 by omega,decide_false,Bool.false_eq_true,↓reduceIte]

theorem positive_fill (fuel n : Nat) (positive : 0<n) (bounded : n<2^61)
    (cover : 2^52≤n+fuel) (denominator : UInt64) (extra : UInt8)
    (generator : CookieClicker.Arc4Orbit.State) :
    ∃ final, fill (fuel+1) (encoded n denominator extra generator)=some final := by
  induction fuel generalizing n denominator extra generator with
  | zero =>
    exact ⟨_,fill_encoded_exit 0 n bounded (by omega) denominator extra generator⟩
  | succ fuel induction =>
    by_cases small : n<2^52
    · have byte := extra.toNat_lt
      have nextBound : (n+extra.toNat)*256<2^61 := by omega
      obtain ⟨final,done⟩ := induction ((n+extra.toNat)*256) (by omega) nextBound (by omega)
        (Number.mul denominator (Number.ofNat 256)) (CookieClicker.Arc4Orbit.output generator)
        (CookieClicker.Arc4Orbit.next generator)
      exact ⟨final,(fill_encoded_step (fuel+1) n small denominator extra generator).trans done⟩
    · exact ⟨_,fill_encoded_exit (fuel+1) n bounded (by omega) denominator extra generator⟩

theorem fill_sum_positive (n : Nat) (bounded : n<2^61) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State) (positive : 0<n+extra.toNat) :
    ∃ fuel final, fill fuel (encoded n denominator extra generator)=some final := by
  by_cases small : n<2^52
  · have byte := extra.toNat_lt
    have nextBound : (n+extra.toNat)*256<2^61 := by omega
    obtain ⟨final,done⟩ := positive_fill (2^52) ((n+extra.toNat)*256) (by omega) nextBound (by omega)
      (Number.mul denominator (Number.ofNat 256)) (CookieClicker.Arc4Orbit.output generator)
      (CookieClicker.Arc4Orbit.next generator)
    exact ⟨2^52+2,final,(fill_encoded_step (2^52+1) n small denominator extra generator).trans done⟩
  · exact ⟨1,_,fill_encoded_exit 0 n bounded (by omega) denominator extra generator⟩

theorem fill_from_nonzero (index n : Nat) (bounded : n<2^61) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State)
    (witness : CookieClicker.Arc4Orbit.output
      (CookieClicker.FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index generator)≠0) :
    ∃ fuel final, fill fuel (encoded n denominator extra generator)=some final := by
  induction index generalizing n denominator extra generator with
  | zero =>
    by_cases positive : 0<n+extra.toNat
    · exact fill_sum_positive n bounded denominator extra generator positive
    · have nZero : n=0 := by omega
      have extraZero : extra.toNat=0 := by omega
      have outputPositive : 0<(CookieClicker.Arc4Orbit.output generator).toNat := by
        apply Nat.pos_of_ne_zero
        intro equal
        apply witness
        apply UInt8.toNat_inj.mp
        exact equal
      obtain ⟨fuel,final,done⟩ := fill_sum_positive 0 (by omega)
        (Number.mul denominator (Number.ofNat 256)) (CookieClicker.Arc4Orbit.output generator)
        (CookieClicker.Arc4Orbit.next generator) (by omega)
      refine ⟨fuel+1,final,?_⟩
      rw [fill_encoded_step fuel n (by omega),nZero,extraZero]
      exact done
  | succ index induction =>
    by_cases positive : 0<n+extra.toNat
    · exact fill_sum_positive n bounded denominator extra generator positive
    · have nZero : n=0 := by omega
      have extraZero : extra.toNat=0 := by omega
      have later : CookieClicker.Arc4Orbit.output
          (CookieClicker.FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index
            (CookieClicker.Arc4Orbit.next generator))≠0 := by
        simpa only [CookieClicker.FiniteInvertibleOrbit.run_succ_start] using witness
      obtain ⟨fuel,final,done⟩ := induction 0 (by omega)
        (Number.mul denominator (Number.ofNat 256)) (CookieClicker.Arc4Orbit.output generator)
        (CookieClicker.Arc4Orbit.next generator) later
      refine ⟨fuel+1,final,?_⟩
      rw [fill_encoded_step fuel n (by omega),nZero,extraZero]
      exact done

theorem fill_return_bounds (fuel n : Nat) (bounded : n<2^61) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State) (final : State)
    (done : fill fuel (encoded n denominator extra generator)=some final) :
    ∃ finalN finalD finalC finalG,
      final=encoded finalN finalD finalC finalG ∧ finalN<2^61 ∧ 2^52≤finalN := by
  induction fuel generalizing n denominator extra generator with
  | zero => simp [fill] at done
  | succ fuel induction =>
    by_cases small : n<2^52
    · have byte := extra.toNat_lt
      rw [fill_encoded_step fuel n small] at done
      exact induction ((n+extra.toNat)*256) (by omega) _ _ _ done
    · rw [fill_encoded_exit fuel n bounded (by omega)] at done
      have same := Option.some.inj done
      exact ⟨n,denominator,extra,generator,same.symm,bounded,by omega⟩

theorem shrink_natural (n : Nat) (bounded : n<2^61) (large : 2^52≤n) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State) :
    ∃ fuel final, shrink fuel (encoded n denominator extra generator)=some final := by
  obtain ⟨m,e,p,lo,hi,eu,shape⟩ := RoundingBridge.native_integer_round_shape n large (by omega)
  obtain ⟨final,done,_,_⟩ := shrink_normal m e p lo hi eu denominator (Number.ofNat extra.toNat) generator
  refine ⟨e+1,final,?_⟩
  unfold encoded
  rw [NaturalArithmetic.ofNat_encoding,shape]
  exact done

def normalize (fillFuel shrinkFuel : Nat) (state : State) : Option (UInt64 × CookieClicker.Arc4Orbit.State) := do
  let filled ← fill fillFuel state
  let shrunk ← shrink shrinkFuel filled
  pure (returned shrunk,shrunk.generator)

theorem normalize_from_nonzero (index n : Nat) (bounded : n<2^61) (denominator : UInt64)
    (extra : UInt8) (generator : CookieClicker.Arc4Orbit.State)
    (witness : CookieClicker.Arc4Orbit.output
      (CookieClicker.FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index generator)≠0) :
    ∃ fillFuel shrinkFuel result,
      normalize fillFuel shrinkFuel (encoded n denominator extra generator)=some result := by
  obtain ⟨fuel,filled,done⟩ := fill_from_nonzero index n bounded denominator extra generator witness
  obtain ⟨nextN,nextD,nextC,nextG,shape,nextBound,nextLarge⟩ :=
    fill_return_bounds fuel n bounded denominator extra generator filled done
  obtain ⟨shrinkFuel,shrunk,shrunkDone⟩ := shrink_natural nextN nextBound nextLarge nextD nextC nextG
  refine ⟨fuel,shrinkFuel,(returned shrunk,shrunk.generator),?_⟩
  simp only [normalize,done,bind,Option.bind,shape,shrunkDone,pure]

theorem normalize_all_zero (fillFuel shrinkFuel : Nat) (generator : CookieClicker.Arc4Orbit.State)
    (zero : ∀ n, CookieClicker.Arc4Orbit.output
      (CookieClicker.FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next n generator)=0)
    (denominator : UInt64) :
    normalize fillFuel shrinkFuel ⟨Number.positiveZero,denominator,Number.positiveZero,generator⟩=none := by
  simp only [normalize,fill_all_zero fillFuel generator zero denominator,bind,Option.bind]

end CookieClicker.JavaScript.SeedrandomNormalizationLoops

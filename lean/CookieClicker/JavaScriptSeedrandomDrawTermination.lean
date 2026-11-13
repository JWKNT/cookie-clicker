import CookieClicker.JavaScriptSeedrandomDrawComplete
import CookieClicker.JavaScriptRetainedArc4Accumulator

/-! A nonzero byte on the retained orbit suffices for complete source-body
termination. No denominator finiteness condition is imposed. -/
namespace CookieClicker.JavaScript.SeedrandomDrawTermination
open SeedrandomDrawLocals SeedrandomDrawBacking SeedrandomDrawGenerator SeedrandomDrawCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

attribute [local irreducible] RetainedArc4GenerateComplete.finished

theorem initial_natural (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId) :
    ∃ n, n<2^48 ∧ (initial i objects g argument).frame.a=Number.ofNat n := by
  obtain ⟨n,bounded,encoded⟩ := RetainedArc4Accumulator.natural_call
    (Call i objects g argument {} #[] 6 (by decide)) (by change 6≤6;decide)
  exact ⟨n,bounded,encoded⟩

theorem initial_project (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (n : Nat) (encoded : (initial i objects g argument).frame.a=Number.ofNat n) :
    project (initial i objects g argument)=
      SeedrandomNormalizationLoops.encoded n (Number.ofNat (2^48)) 0
        (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next 6 (projectGenerator g)) := by
  have generator := returned_project i objects g argument {} #[] 6 (by decide)
  change SeedrandomNormalizationLoops.State.mk (initial i objects g argument).frame.a _ _ _=_
  rw [encoded]
  have projected : projectGenerator (initial i objects g argument).generator=
      FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next 6 (projectGenerator g) := by
    exact generator
  rw [projected]
  rfl

theorem actual_body_from_nonzero (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (witness : ∃ index, CookieClicker.Arc4Orbit.output
      (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index (projectGenerator g))≠0)
    (caller : ExecutionContext) (rest : List Frame) :
    ∃ steps value final,
      (∀ remaining, Builtins.run (steps+remaining)
        (SeedrandomDrawCalls.initialStart i objects argument (.callBoundary caller none :: rest))=
        Builtins.run remaining final) ∧
      final.control=.expressionResult (.value (.number value)) ∧
      final.context=caller ∧ final.continuation=rest ∧
      final.elapsed=i.base.elapsed ∧ final.freeDrawCount=i.base.freeDrawCount := by
  obtain ⟨n,bounded,encoded⟩ := initial_natural i objects g argument
  obtain ⟨index,_,later⟩ := CookieClicker.Arc4Orbit.nonzero_recurring (projectGenerator g) witness 6
  have afterSix : CookieClicker.Arc4Orbit.output
      (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index
        (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next 6 (projectGenerator g)))≠0 := by
    rw [←FiniteInvertibleOrbit.run_add,show index+6=6+index by omega]
    exact later
  have small : n<2^61 := by omega
  obtain ⟨fillFuel,filled,fillDone⟩ := SeedrandomNormalizationLoops.fill_from_nonzero index n small
    (Number.ofNat (2^48)) 0 (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next 6 (projectGenerator g)) afterSix
  obtain ⟨nextN,nextD,nextC,nextG,shape,nextBound,nextLarge⟩ :=
    SeedrandomNormalizationLoops.fill_return_bounds fillFuel n small (Number.ofNat (2^48)) 0
      (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next 6 (projectGenerator g)) filled fillDone
  obtain ⟨shrinkFuel,shifted,shrinkDone⟩ := SeedrandomNormalizationLoops.shrink_natural nextN nextBound nextLarge nextD nextC nextG
  have sourceFill : SeedrandomNormalizationLoops.fill fillFuel (project (initial i objects g argument))=some filled := by
    rw [initial_project i objects g argument n encoded]
    exact fillDone
  have sourceShrink : SeedrandomNormalizationLoops.shrink shrinkFuel filled=some shifted := by
    rw [shape]
    exact shrinkDone
  obtain ⟨steps,final,run,control,context,continuation,elapsed,freeDraws⟩ :=
    SeedrandomDrawComplete.actual_normalization fillFuel shrinkFuel ⟨initial i objects g argument,none⟩
      filled shifted sourceFill sourceShrink caller rest
  refine ⟨939+steps,SeedrandomNormalizationLoops.returned shifted,final,?_,control,context,continuation,?_,?_⟩
  · intro remaining
    rw [show 939+steps+remaining=939+(steps+remaining) by omega,actual_initial_six]
    exact run remaining
  · simpa only [initial,initial_source] using elapsed
  · simpa only [initial,initial_source] using freeDraws

end CookieClicker.JavaScript.SeedrandomDrawTermination

import CookieClicker.JavaScriptSeedrandomDrawSource

/-! The native shrink recurrence composes with its retained source loop and
actual caller return. The heap and random activation come from the source frame. -/
namespace CookieClicker.JavaScript.SeedrandomDrawShrinkComplete
open SeedrandomDrawSource
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def project (f : SeedrandomDrawSource.Frame) (generator : CookieClicker.Arc4Orbit.State) : SeedrandomNormalizationLoops.State :=
  ⟨f.a,f.b,f.c,generator⟩
def replace (f : SeedrandomDrawSource.Frame) (s : SeedrandomNormalizationLoops.State) : SeedrandomDrawSource.Frame :=
  {f with a := s.numerator,b := s.denominator,c := s.extra}
def tail (inherited : Option Value) (caller : ExecutionContext) (rest : List JavaScript.Frame) : List JavaScript.Frame :=
  .statementList [returnStatement] inherited :: .callBoundary caller none :: rest

theorem replace_project (f : SeedrandomDrawSource.Frame) (generator : CookieClicker.Arc4Orbit.State) : replace f (project f generator)=f := rfl

theorem project_shrunk (f : SeedrandomDrawSource.Frame) (generator : CookieClicker.Arc4Orbit.State) :
    project (shrunk f) generator=SeedrandomNormalizationLoops.shrinkStep (project f generator) := rfl

theorem replace_shrunk (f : SeedrandomDrawSource.Frame) (s : SeedrandomNormalizationLoops.State) :
    replace (shrunk f) s=replace f s := rfl

theorem actual_complete (fuel : Nat) (f : SeedrandomDrawSource.Frame) (generator : CookieClicker.Arc4Orbit.State)
    (s : SeedrandomNormalizationLoops.State)
    (finished : SeedrandomNormalizationLoops.shrink fuel (project f generator)=some s)
    (previous inherited : Option Value) (caller : ExecutionContext) (rest : List JavaScript.Frame) :
    ∃ steps, ∀ remaining,
      Builtins.run (steps+remaining) (shrinkStart f previous (tail inherited caller rest))=
        Builtins.run remaining (returned (replace f s) caller rest) := by
  induction fuel generalizing f previous with
  | zero => simp [SeedrandomNormalizationLoops.shrink] at finished
  | succ fuel ih =>
    rw [SeedrandomNormalizationLoops.shrink] at finished
    split at finished
    next guard =>
      have continued : SeedrandomNormalizationLoops.shrink fuel (project (shrunk f) generator)=some s := finished
      obtain ⟨steps,run⟩ := ih (shrunk f) continued (shrinkPrevious f)
      refine ⟨44+steps,?_⟩
      intro remaining
      rw [show 44+steps+remaining=9+((34+(steps+remaining))+1) by omega,actual_shrink_test]
      change Builtins.run (34+(steps+remaining)) (Builtins.builtinStep (shrinkAtTest f previous (tail inherited caller rest)))=_
      rw [actual_shrink_branch]
      have native : Number.lessEqual (Number.ofNat (2^53)) f.a=true := guard
      rw [native]
      simp only [↓reduceIte]
      rw [actual_shrink_assignments,run,replace_shrunk]
    next guard =>
      have same : project f generator=s := Option.some.inj finished
      subst s
      refine ⟨30,?_⟩
      intro remaining
      rw [show 30+remaining=9+((20+remaining)+1) by omega,actual_shrink_test]
      change Builtins.run (20+remaining) (Builtins.builtinStep (shrinkAtTest f previous (tail inherited caller rest)))=_
      rw [actual_shrink_branch]
      have native : Number.lessEqual (Number.ofNat (2^53)) f.a=false := by
        exact Bool.eq_false_iff.mpr guard
      rw [native]
      simp only [↓reduceIte,replace_project]
      exact actual_return_inherited f previous inherited caller rest remaining

theorem returned_value (f : SeedrandomDrawSource.Frame) (s : SeedrandomNormalizationLoops.State)
    (caller : ExecutionContext) (rest : List JavaScript.Frame) :
    (returned (replace f s) caller rest).control=
      .expressionResult (.value (.number (SeedrandomNormalizationLoops.returned s))) := rfl

theorem retained_elapsed (f : SeedrandomDrawSource.Frame) (s : SeedrandomNormalizationLoops.State)
    (caller : ExecutionContext) (rest : List JavaScript.Frame) :
    (returned (replace f s) caller rest).elapsed=f.source.base.elapsed := rfl

theorem retained_free_draws (f : SeedrandomDrawSource.Frame) (s : SeedrandomNormalizationLoops.State)
    (caller : ExecutionContext) (rest : List JavaScript.Frame) :
    (returned (replace f s) caller rest).freeDrawCount=f.source.base.freeDrawCount := rfl

end CookieClicker.JavaScript.SeedrandomDrawShrinkComplete

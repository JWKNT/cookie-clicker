import CookieClicker.JavaScriptSeedrandomDrawCursor
import CookieClicker.JavaScriptSeedrandomDrawShrinkComplete

/-! Composition of the exact growth loop, shrink loop and caller return.
A successful native recurrence determines the same returned Number bits. -/
namespace CookieClicker.JavaScript.SeedrandomDrawComplete
open SeedrandomDrawCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Stage where
  cursor : Cursor
  previous : Option Value

def advance (stage : Stage) : Stage := ⟨next stage.cursor,some (.number (byte stage.cursor))⟩
def fill : Nat → Stage → Option Stage
  | 0,_ => none
  | fuel+1,stage =>
    if Number.lessThan stage.cursor.frame.a (Number.ofNat (2^52)) then fill fuel (advance stage)
    else some stage

theorem fill_project (fuel : Nat) (stage : Stage) :
    (fill fuel stage).map (fun stop => project stop.cursor)=
      SeedrandomNormalizationLoops.fill fuel (project stage.cursor) := by
  induction fuel generalizing stage with
  | zero => rfl
  | succ fuel ih =>
    rw [fill,SeedrandomNormalizationLoops.fill]
    cases guard : Number.lessThan stage.cursor.frame.a (Number.ofNat (2^52)) <;>
      simp only [project,guard,Bool.false_eq_true,↓reduceIte,Option.map_some]
    have next := ih (advance stage)
    rw [show project (advance stage).cursor=SeedrandomNormalizationLoops.growthStep (project stage.cursor) from project_next stage.cursor] at next
    exact next

theorem fill_source (fuel : Nat) (stage stop : Stage) (done : fill fuel stage=some stop) :
    stop.cursor.frame.source=stage.cursor.frame.source := by
  induction fuel generalizing stage with
  | zero => simp [fill] at done
  | succ fuel ih =>
    rw [fill] at done
    split at done
    · exact ih (advance stage) done
    · exact congrArg (fun stage : Stage => stage.cursor.frame.source) (Option.some.inj done).symm

theorem actual_fill (fuel : Nat) (stage stop : Stage) (done : fill fuel stage=some stop) (tail : List Frame) :
    ∃ steps, ∀ remaining,
      Builtins.run (steps+remaining) (SeedrandomDrawSource.growthStart stage.cursor.frame stage.previous tail)=
        Builtins.run remaining (SeedrandomDrawSource.exit stop.cursor.frame stop.previous tail) := by
  induction fuel generalizing stage with
  | zero => simp [fill] at done
  | succ fuel ih =>
    rw [fill] at done
    split at done
    next guard =>
      obtain ⟨steps,run⟩ := ih (advance stage) done
      refine ⟨293+steps,?_⟩
      intro remaining
      rw [show 293+steps+remaining=9+((283+(steps+remaining))+1) by omega,SeedrandomDrawSource.actual_growth_test]
      change Builtins.run (283+(steps+remaining))
        (Builtins.builtinStep (SeedrandomDrawSource.growthAtTest stage.cursor.frame stage.previous tail))=_
      rw [SeedrandomDrawSource.actual_growth_branch,guard]
      simp only [↓reduceIte]
      rw [actual_growth_body]
      exact run remaining
    next guard =>
      have same : stage=stop := Option.some.inj done
      subst stop
      refine ⟨10,?_⟩
      intro remaining
      rw [show 10+remaining=9+(remaining+1) by omega,SeedrandomDrawSource.actual_growth_test]
      change Builtins.run remaining
        (Builtins.builtinStep (SeedrandomDrawSource.growthAtTest stage.cursor.frame stage.previous tail))=_
      rw [SeedrandomDrawSource.actual_growth_branch]
      have native : Number.lessThan stage.cursor.frame.a (Number.ofNat (2^52))=false := Bool.eq_false_iff.mpr guard
      rw [native]
      rfl

def tail (caller : ExecutionContext) (rest : List Frame) : List Frame :=
  .statementList [SeedrandomDrawSource.shrink,SeedrandomDrawSource.returnStatement] none ::
    .callBoundary caller none :: rest

attribute [local cbv_opaque] SeedrandomDrawLocals.heap SeedrandomDrawLocals.localIndex Number.ofNat
  checkedEnvironment readBinding setBinding Array.size List.length Environment.identifier

theorem actual_between (stage : Stage) (caller : ExecutionContext) (rest : List Frame) (remaining : Nat) :
    Builtins.run (2+remaining) (SeedrandomDrawSource.exit stage.cursor.frame stage.previous (tail caller rest))=
      Builtins.run remaining (SeedrandomDrawSource.shrinkStart stage.cursor.frame none
        (SeedrandomDrawShrinkComplete.tail stage.previous caller rest)) := by
  rw [Nat.add_comm 2 remaining]
  cases previous : stage.previous <;> cbv <;> rw [previous]

theorem actual_normalization (fillFuel shrinkFuel : Nat) (stage : Stage)
    (filled shifted : SeedrandomNormalizationLoops.State)
    (fillDone : SeedrandomNormalizationLoops.fill fillFuel (project stage.cursor)=some filled)
    (shrinkDone : SeedrandomNormalizationLoops.shrink shrinkFuel filled=some shifted)
    (caller : ExecutionContext) (rest : List Frame) :
    ∃ steps final,
      (∀ remaining, Builtins.run (steps+remaining)
        (SeedrandomDrawSource.growthStart stage.cursor.frame stage.previous (tail caller rest))=
        Builtins.run remaining final) ∧
      final.control=.expressionResult (.value (.number (SeedrandomNormalizationLoops.returned shifted))) ∧
      final.context=caller ∧ final.continuation=rest ∧
      final.elapsed=stage.cursor.frame.source.base.elapsed ∧
      final.freeDrawCount=stage.cursor.frame.source.base.freeDrawCount := by
  have mapped := fill_project fillFuel stage
  rw [fillDone] at mapped
  cases sourceDone : fill fillFuel stage with
  | none => simp [sourceDone] at mapped
  | some stop =>
    have projected : project stop.cursor=filled := by simpa [sourceDone] using mapped
    obtain ⟨fillSteps,fillRun⟩ := actual_fill fillFuel stage stop sourceDone (tail caller rest)
    have shrinkNative : SeedrandomNormalizationLoops.shrink shrinkFuel
      (SeedrandomDrawShrinkComplete.project stop.cursor.frame (projectGenerator stop.cursor.generator))=some shifted := by
      change SeedrandomNormalizationLoops.shrink shrinkFuel (project stop.cursor)=some shifted
      rw [projected]
      exact shrinkDone
    obtain ⟨shrinkSteps,shrinkRun⟩ := SeedrandomDrawShrinkComplete.actual_complete shrinkFuel stop.cursor.frame
      (projectGenerator stop.cursor.generator) shifted shrinkNative none stop.previous caller rest
    refine ⟨fillSteps+2+shrinkSteps,SeedrandomDrawSource.returned
      (SeedrandomDrawShrinkComplete.replace stop.cursor.frame shifted) caller rest,?_,rfl,rfl,rfl,?_,?_⟩
    · intro remaining
      rw [show fillSteps+2+shrinkSteps+remaining=fillSteps+(2+(shrinkSteps+remaining)) by omega,
        fillRun,actual_between,shrinkRun]
    · change stop.cursor.frame.source.base.elapsed=stage.cursor.frame.source.base.elapsed
      rw [fill_source fillFuel stage stop sourceDone]
    · change stop.cursor.frame.source.base.freeDrawCount=stage.cursor.frame.source.base.freeDrawCount
      rw [fill_source fillFuel stage stop sourceDone]

end CookieClicker.JavaScript.SeedrandomDrawComplete

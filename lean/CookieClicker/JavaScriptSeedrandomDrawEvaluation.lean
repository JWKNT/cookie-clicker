import CookieClicker.JavaScriptSeedrandomDrawFactory
import CookieClicker.Arc4NonzeroPrefix

/-! Checked finite execution of the retained source frames returns a concrete
machine and Number bits, with the complete source-run equation as a proof. -/
namespace CookieClicker.JavaScript.SeedrandomDrawEvaluation
open SeedrandomDrawLocals SeedrandomDrawBacking SeedrandomDrawCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] RetainedArc4GenerateComplete.finished

def initialStage (i : Inputs) (callee : ObjectId) (g : Generator i i.base.heap.objects) : SeedrandomDrawComplete.Stage :=
  ⟨initial i (SeedrandomDrawInvocation.objects i callee) (SeedrandomDrawInvocation.generator i callee g)
    i.base.heap.objects.size,none⟩

def finished (stop : SeedrandomDrawComplete.Stage) (shifted : SeedrandomNormalizationLoops.State)
    (caller : ExecutionContext) (rest : List Frame) : Machine :=
  SeedrandomDrawSource.returned (SeedrandomDrawShrinkComplete.replace stop.cursor.frame shifted) caller rest

theorem actual_checked (i : Inputs) (callee : ObjectId) (object : JSObject)
    (present : checkedObject i.base.heap callee=.ok object)
    (kind : object.kind=.function (SeedrandomRandomClosure.closure i.capture))
    (g : Generator i i.base.heap.objects) (fillFuel shrinkFuel : Nat)
    (stop : SeedrandomDrawComplete.Stage) (shifted : SeedrandomNormalizationLoops.State)
    (fillDone : SeedrandomDrawComplete.fill fillFuel (initialStage i callee g)=some stop)
    (shrinkDone : SeedrandomNormalizationLoops.shrink shrinkFuel (project stop.cursor)=some shifted) :
    ∃ steps,
      (∀ remaining, Builtins.run (steps+remaining) (SeedrandomDrawInvocation.start i callee)=
        Builtins.run remaining (finished stop shifted i.base.context i.base.continuation)) ∧
      (finished stop shifted i.base.context i.base.continuation).elapsed=i.base.elapsed ∧
      (finished stop shifted i.base.context i.base.continuation).freeDrawCount=i.base.freeDrawCount := by
  obtain ⟨fillSteps,fillRun⟩ := SeedrandomDrawComplete.actual_fill fillFuel (initialStage i callee g) stop fillDone
    (SeedrandomDrawComplete.tail i.base.context i.base.continuation)
  obtain ⟨shrinkSteps,shrinkRun⟩ := SeedrandomDrawShrinkComplete.actual_complete shrinkFuel stop.cursor.frame
    (projectGenerator stop.cursor.generator) shifted shrinkDone none stop.previous i.base.context i.base.continuation
  have source := SeedrandomDrawComplete.fill_source fillFuel (initialStage i callee g) stop fillDone
  refine ⟨11+939+fillSteps+2+shrinkSteps,?_,?_,?_⟩
  · intro remaining
    rw [show 11+939+fillSteps+2+shrinkSteps+remaining=11+(939+(fillSteps+(2+(shrinkSteps+remaining)))) by omega,
      SeedrandomDrawInvocation.actual_prefix i callee object present kind,
      SeedrandomDrawGenerator.actual_initial_six i (SeedrandomDrawInvocation.objects i callee)
        (SeedrandomDrawInvocation.generator i callee g) i.base.heap.objects.size]
    change Builtins.run (fillSteps+(2+(shrinkSteps+remaining)))
      (SeedrandomDrawSource.growthStart (initialStage i callee g).cursor.frame (initialStage i callee g).previous
        (SeedrandomDrawComplete.tail i.base.context i.base.continuation))=_
    rw [fillRun,SeedrandomDrawComplete.actual_between,shrinkRun]
    rfl
  · change stop.cursor.frame.source.base.elapsed=i.base.elapsed
    rw [source]
    rfl
  · change stop.cursor.frame.source.base.freeDrawCount=i.base.freeDrawCount
    rw [source]
    rfl

structure Result {base : Machine} {math : ObjectId} (ready : SeedrandomDrawFactory.Ready base math) where
  witness : CookieClicker.Arc4NonzeroPrefix.Witness (projectGenerator ready.generator)
  bits : UInt64
  machine : Machine
  source : ∃ steps, ∀ remaining,
    Builtins.run (steps+remaining) (SeedrandomDrawFactory.propertyStart base math)=Builtins.run remaining machine
  control : machine.control=.expressionResult (.value (.number bits))
  context : machine.context=base.context
  continuation : machine.continuation=base.continuation
  elapsed : machine.elapsed=base.elapsed
  freeDraws : machine.freeDrawCount=base.freeDrawCount

def inspectNonzero {base : Machine} {math : ObjectId} (ready : SeedrandomDrawFactory.Ready base math)
    (fuel : Nat) : Option (CookieClicker.Arc4NonzeroPrefix.Witness (projectGenerator ready.generator)) :=
  CookieClicker.Arc4NonzeroPrefix.search fuel (projectGenerator ready.generator)

def inspect {base : Machine} {math : ObjectId} (ready : SeedrandomDrawFactory.Ready base math)
    (byteFuel fillFuel shrinkFuel : Nat) : Except String (Result ready) := do
  let some witness := inspectNonzero ready byteFuel | throw "No nonzero byte was certified within the prefix budget"
  let stage := initialStage ready.locals ready.callee ready.generator
  match fillDone : SeedrandomDrawComplete.fill fillFuel stage with
  | none => throw "Growth source frame exceeded the finite evaluation budget"
  | some stop =>
    match shrinkDone : SeedrandomNormalizationLoops.shrink shrinkFuel (project stop.cursor) with
    | none => throw "Shrink source frame exceeded the finite evaluation budget"
    | some shifted => do
      have present : checkedObject ready.locals.base.heap ready.callee=.ok ready.object := by
        rw [ready.baseSame]
        exact ready.present
      have run := actual_checked ready.locals ready.callee ready.object present ready.kind ready.generator
        fillFuel shrinkFuel stop shifted fillDone shrinkDone
      let final := finished stop shifted ready.locals.base.context ready.locals.base.continuation
      pure {
        witness := witness,bits := SeedrandomNormalizationLoops.returned shifted,machine := final
        source := by
          obtain ⟨steps,run,_,_⟩ := run
          refine ⟨4+steps,?_⟩
          intro remaining
          rw [show 4+steps+remaining=4+(steps+remaining) by omega,
            SeedrandomDrawFactory.property_invocation base math ready,
            ←SeedrandomDrawFactory.invocation_same base math ready,run]
        control := rfl
        context := by change ready.locals.base.context=base.context; rw [ready.baseSame]
        continuation := by change ready.locals.base.continuation=base.continuation; rw [ready.baseSame]
        elapsed := by rw [←ready.baseSame]; exact run.choose_spec.2.1
        freeDraws := by rw [←ready.baseSame]; exact run.choose_spec.2.2 }

theorem result_nonzero {base : Machine} {math : ObjectId} (ready : SeedrandomDrawFactory.Ready base math)
    (result : Result ready) : SeedrandomDrawFactory.Nonzero ready :=
  CookieClicker.Arc4NonzeroPrefix.sound _ result.witness

end CookieClicker.JavaScript.SeedrandomDrawEvaluation

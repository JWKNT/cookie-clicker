import CookieClicker.JavaScriptSeedrandomDrawFactory
import CookieClicker.JavaScriptSeedrandomCapturedRuntime

/-! The complete captured setup supplies the exact machine inspected for the
next retained random invocation. The byte-orbit condition remains explicit. -/
namespace CookieClicker.JavaScript.SeedrandomCapturedDraw
open SeedrandomCapturedFrame SeedrandomCapturedRuntime
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

abbrev Ready {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) :=
  SeedrandomDrawFactory.Ready complete.machine frame.inputs.source.math

def inspect {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) :
    Except String (Ready frame complete) := SeedrandomDrawFactory.inspect complete.machine frame.inputs.source.math

theorem native_receiver {state : Browser.State} {seed : JSString} (frame : Captured state seed)
    (complete : Complete frame) (ready : Ready frame complete) :
    state.mathObject=some ready.locals.thisObject := by
  rw [ready.receiverSame]
  exact frame.mathSame

theorem exact_setup_machine {state : Browser.State} {seed : JSString} (frame : Captured state seed)
    (complete : Complete frame) (ready : Ready frame complete) :
    ready.locals.base=setupResult frame := ready.baseSame.trans complete.sourceResult

theorem captured_setup_and_draw {state : Browser.State} {seed : JSString} (frame : Captured state seed)
    (complete : Complete frame) (ready : Ready frame complete) (witness : SeedrandomDrawFactory.Nonzero ready) :
    BrowserRuntime.run (129+steps frame) (prepared frame)=returned frame complete.machine ∧
    ∃ drawSteps value final,
      (∀ remaining, Builtins.run (drawSteps+remaining)
        (SeedrandomDrawFactory.propertyStart complete.machine frame.inputs.source.math)=Builtins.run remaining final) ∧
      final.control=.expressionResult (.value (.number value)) ∧
      final.context=complete.machine.context ∧ final.continuation=complete.machine.continuation ∧
      final.elapsed=state.machine.elapsed ∧ final.freeDrawCount=state.machine.freeDrawCount := by
  refine ⟨complete.runtime,?_⟩
  obtain ⟨drawSteps,value,final,run,control,context,continuation,elapsed,draws⟩ :=
    SeedrandomDrawFactory.actual_property_complete complete.machine frame.inputs.source.math ready witness
  exact ⟨drawSteps,value,final,run,control,context,continuation,
    elapsed.trans (SeedrandomCapturedRuntime.returned_elapsed frame complete),
    draws.trans (SeedrandomCapturedRuntime.returned_free_draws frame complete)⟩

def report {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) : Lean.Json :=
  match inspect frame complete with
  | .error reason => Lean.Json.mkObj [
    ("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
    ("drawFrameConstructed",Lean.toJson false),("error",Lean.toJson reason)]
  | .ok ready => Lean.Json.mkObj [
    ("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
    ("drawFrameConstructed",Lean.toJson true),("drawExecuted",Lean.toJson false),
    ("nonzeroOrbitRequired",Lean.toJson true),
    ("nativeMath",Lean.toJson frame.inputs.source.math),
    ("randomClosure",Lean.toJson ready.callee),("randomScope",Lean.toJson ready.locals.capture),
    ("generator",Lean.toJson ready.locals.generator),("generatorMethod",Lean.toJson ready.generator.callee),
    ("constructorScope",Lean.toJson ready.generator.backing.prefixEnvironments.size),
    ("stateArray",Lean.toJson ready.generator.array),("stateLength",Lean.toJson ready.generator.arrayFrame.length),
    ("counterI",Lean.toJson ready.generator.oldF.toNat),("counterJ",Lean.toJson ready.generator.oldG.toNat)]

def captureReport (state : Browser.State) (seed : JSString) : Lean.Json :=
  match SeedrandomCapturedFrame.inspect state seed with
  | .error reason => Lean.Json.mkObj [
    ("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
    ("proofFrameConstructed",Lean.toJson false),("error",Lean.toJson reason),
    ("seedUnits",Lean.toJson (seed.map UInt16.toNat))]
  | .ok frame => match SeedrandomCapturedRuntime.inspect frame with
    | .error reason => Lean.Json.mkObj [
      ("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
      ("proofFrameConstructed",Lean.toJson true),("runtimeProofConstructed",Lean.toJson false),
      ("seedUnits",Lean.toJson (seed.map UInt16.toNat)),
      ("error",Lean.toJson reason),("coreSteps",Lean.toJson (steps frame))]
    | .ok complete => Lean.Json.mkObj [
      ("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
      ("proofFrameConstructed",Lean.toJson true),("runtimeProofConstructed",Lean.toJson true),
      ("seedUnits",Lean.toJson (seed.map UInt16.toNat)),
      ("returnedPUnits",Lean.toJson ((returnedPUnits complete.machine).map (List.map UInt16.toNat))),
      ("runtimeSteps",Lean.toJson (129+steps frame)),("poolLength",Lean.toJson frame.inputs.pool.length),
      ("objectsBefore",Lean.toJson state.machine.heap.objects.size),("objectsAfter",Lean.toJson complete.machine.heap.objects.size),
      ("environmentsBefore",Lean.toJson state.machine.heap.environments.size),
      ("environmentsAfter",Lean.toJson complete.machine.heap.environments.size),
      ("freeDrawsBefore",Lean.toJson state.machine.freeDrawCount),("freeDrawsAfter",Lean.toJson complete.machine.freeDrawCount),
      ("retainedDraw",report frame complete)]

end CookieClicker.JavaScript.SeedrandomCapturedDraw

import CookieClicker.JavaScriptSeedrandomCapturedFrame
import CookieClicker.JavaScriptBrowserCoreTrace
import CookieClicker.JavaScriptTimestampSeedRuntimeEntry

/-! An accepted finite native trace closes the browser runtime through the
complete captured source setup, including its installed random closure. -/
namespace CookieClicker.JavaScript.SeedrandomCapturedRuntime
open SeedrandomCapturedFrame
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def sourceInputs {state : Browser.State} {seed : JSString} (frame : Captured state seed) :=
  frame.inputs.source.constructor.prelude.mixing

def steps {state : Browser.State} {seed : JSString} (frame : Captured state seed) : Nat :=
  88+93*(sourceInputs frame).seed.toArray.size+
    2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing (sourceInputs frame))).length+
    TimestampSeedArc4Complete.steps frame.inputs.source.constructor+25003

def prepared {state : Browser.State} {seed : JSString} (frame : Captured state seed) : Browser.State :=
  {state with machine := (SeedrandomInvocation.preparedText (sourceInputs frame).globals.base
    (sourceInputs frame).globals.scope (sourceInputs frame).receiver (sourceInputs frame).seed (sourceInputs frame).seedrandom)}

def captured {state : Browser.State} {seed : JSString} (frame : Captured state seed) : Browser.State :=
  {state with
    machine := TimestampSeedMixingCapture.prepared (sourceInputs frame)
    timestampMixkeyActivations := state.timestampMixkeyActivations+1}

def returned {state : Browser.State} {seed : JSString} (_frame : Captured state seed) (machine : Machine) : Browser.State :=
  {state with machine := machine, timestampMixkeyActivations := state.timestampMixkeyActivations+1}

structure Complete {state : Browser.State} {seed : JSString} (frame : Captured state seed) where
  machine : Machine
  sourceResult : machine=setupResult frame
  runtime : BrowserRuntime.run (129+steps frame) (prepared frame)=returned frame machine

theorem runtime_return {state : Browser.State} {seed : JSString} (frame : Captured state seed)
    (complete : Complete frame) :
    BrowserRuntime.run (129+steps frame) (prepared frame)=returned frame (setupResult frame) := by
  rw [complete.runtime,complete.sourceResult]

def inspect {state : Browser.State} {seed : JSString} (frame : Captured state seed) : Except String (Complete frame) := do
  let trace ← BrowserCoreTrace.inspect (steps frame) (captured frame)
  have result : trace.machine=setupResult frame :=
    trace.source.symm.trans (captured_source_return frame 0)
  pure ⟨trace.machine,result,by
    change BrowserRuntime.run (129+steps frame)
      {state with machine := (SeedrandomInvocation.preparedText (sourceInputs frame).globals.base
        (sourceInputs frame).globals.scope (sourceInputs frame).receiver (sourceInputs frame).seed (sourceInputs frame).seedrandom)} = _
    rw [TimestampSeedRuntimeEntry.actual_setup_and_capture state (sourceInputs frame) frame.mixkeySame]
    exact trace.runtime⟩

theorem returned_p {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) :
    complete.machine.control=.expressionResult (.value (.string (TimestampSeedMixing.text (sourceInputs frame)))) := by
  rw [complete.sourceResult]
  exact SeedrandomCapturedFrame.returned_p frame

theorem returned_elapsed {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) :
    complete.machine.elapsed=state.machine.elapsed := by
  rw [complete.sourceResult]
  exact SeedrandomCapturedFrame.returned_elapsed frame

theorem returned_free_draws {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) :
    complete.machine.freeDrawCount=state.machine.freeDrawCount := by
  rw [complete.sourceResult]
  exact SeedrandomCapturedFrame.returned_free_draws frame

def returnedPUnits (machine : Machine) : Option JSString :=
  match machine.control with
  | .expressionResult (.value (.string units)) => some units
  | _ => none

theorem returned_p_units {state : Browser.State} {seed : JSString} (frame : Captured state seed) (complete : Complete frame) :
    returnedPUnits complete.machine=some (TimestampSeedMixing.text (sourceInputs frame)) := by
  unfold returnedPUnits
  rw [returned_p frame complete]

def report (state : Browser.State) (seed : JSString) : Lean.Json :=
  match SeedrandomCapturedFrame.inspect state seed with
  | .error reason => Lean.Json.mkObj [("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
    ("proofFrameConstructed",Lean.toJson false),("error",Lean.toJson reason),("seedUnits",Lean.toJson (seed.map UInt16.toNat))]
  | .ok frame =>
    match inspect frame with
    | .error reason => Lean.Json.mkObj [("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
      ("proofFrameConstructed",Lean.toJson true),("runtimeProofConstructed",Lean.toJson false),
      ("seedUnits",Lean.toJson (seed.map UInt16.toNat)),
      ("error",Lean.toJson reason),("coreSteps",Lean.toJson (steps frame))]
    | .ok complete => Lean.Json.mkObj [("privatePureDiagnostic",Lean.toJson true),("playerObserved",Lean.toJson false),
      ("proofFrameConstructed",Lean.toJson true),("runtimeProofConstructed",Lean.toJson true),
      ("seedUnits",Lean.toJson (seed.map UInt16.toNat)),
      ("returnedPUnits",Lean.toJson ((returnedPUnits complete.machine).map (List.map UInt16.toNat))),
      ("runtimeSteps",Lean.toJson (129+steps frame)),("poolLength",Lean.toJson frame.inputs.pool.length),
      ("objectsBefore",Lean.toJson state.machine.heap.objects.size),("objectsAfter",Lean.toJson complete.machine.heap.objects.size),
      ("environmentsBefore",Lean.toJson state.machine.heap.environments.size),
      ("environmentsAfter",Lean.toJson complete.machine.heap.environments.size),
      ("freeDrawsBefore",Lean.toJson state.machine.freeDrawCount),("freeDrawsAfter",Lean.toJson complete.machine.freeDrawCount)]

end CookieClicker.JavaScript.SeedrandomCapturedRuntime

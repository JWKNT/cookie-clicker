import CookieClicker.JavaScriptSeedrandomCapturedDraw
import CookieClicker.JavaScriptSeedrandomDrawEvaluation

/-! Finite private diagnostics evaluate theorem-linked retained source draws.
Selected extended timestamp text is rendered before native-library comparison. -/
namespace CookieClicker.JavaScript.SeedrandomCapturedDrawEvaluation
open Lean SeedrandomCapturedFrame SeedrandomCapturedRuntime
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def report (state : Browser.State) (seed : JSString) : Json :=
  match SeedrandomCapturedFrame.inspect state seed with
  | .error reason => Json.mkObj [("proofFrameConstructed",toJson false),("error",toJson reason)]
  | .ok frame => match SeedrandomCapturedRuntime.inspect frame with
    | .error reason => Json.mkObj [("runtimeProofConstructed",toJson false),("error",toJson reason)]
    | .ok complete => match SeedrandomCapturedDraw.inspect frame complete with
      | .error reason => Json.mkObj [("drawFrameConstructed",toJson false),("error",toJson reason)]
      | .ok ready => match SeedrandomDrawEvaluation.inspect ready 64 64 16 with
        | .error reason => Json.mkObj [
          ("privatePureDiagnostic",toJson true),("playerObserved",toJson false),
          ("drawFrameConstructed",toJson true),("completeDrawProofConstructed",toJson false),("error",toJson reason)]
        | .ok evaluated =>
          let retained := match SeedrandomDrawFactory.inspect evaluated.machine frame.inputs.source.math with
            | .error reason => Json.mkObj [("constructed",toJson false),("error",toJson reason)]
            | .ok next => Json.mkObj [("constructed",toJson true),
              ("counterI",toJson next.generator.oldF.toNat),("counterJ",toJson next.generator.oldG.toNat)]
          Json.mkObj [
            ("privatePureDiagnostic",toJson true),("playerObserved",toJson false),
            ("proofFrameConstructed",toJson true),("runtimeProofConstructed",toJson true),
            ("drawFrameConstructed",toJson true),("completeDrawProofConstructed",toJson true),
            ("selectedSourceFrameExecution",toJson true),("universalSeedLivenessProved",toJson false),
            ("seedUnits",toJson (seed.map UInt16.toNat)),
            ("returnedPUnits",toJson ((returnedPUnits complete.machine).map (List.map UInt16.toNat))),
            ("runtimeSetupSteps",toJson (129+steps frame)),
            ("nonzeroByteIndex",toJson evaluated.witness.index),
            ("numberBits",toJson (toString evaluated.bits.toNat)),
            ("freeDrawsBefore",toJson state.machine.freeDrawCount),
            ("freeDrawsAfter",toJson evaluated.machine.freeDrawCount),
            ("objectsAfterSetup",toJson complete.machine.heap.objects.size),
            ("objectsAfterDraw",toJson evaluated.machine.heap.objects.size),
            ("environmentsAfterSetup",toJson complete.machine.heap.environments.size),
            ("environmentsAfterDraw",toJson evaluated.machine.heap.environments.size),
            ("retainedAfterDraw",retained)]

def selectedExtended (state : Browser.State) (label : String) (value : ClockValue.Dyadic) : Json :=
  Json.mkObj [("label",toJson label),("seedOrigin",toJson "selected-extended-timestamp-rendering"),
    ("numerator",toJson (toString value.numerator)),("scale",toJson value.scale),
    ("result",report state (ClockValue.Codec.renderExtended value))]

def samples (state : Browser.State) (ordinary : JSString) : Json :=
  Json.arr #[
    Json.mkObj [("label",toJson "ordinary"),("seedOrigin",toJson "ordinary-string"),("result",report state ordinary)],
    selectedExtended state "past-native-date" ⟨8640000000000001,0⟩,
    selectedExtended state "large-exact-half" ⟨2*(10^40)+1,1⟩]

end CookieClicker.JavaScript.SeedrandomCapturedDrawEvaluation

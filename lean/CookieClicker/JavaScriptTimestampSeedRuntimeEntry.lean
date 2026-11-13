import CookieClicker.JavaScriptSeedRuntimeCapture

/-! The actual browser seed path reaches the captured tagged activation.
Flatten and mixkey identities are separated by their retained source bodies. -/
namespace CookieClicker.JavaScript.TimestampSeedRuntimeEntry
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open TimestampSeedMixing

theorem flatten_different (i : Inputs) : i.mixkey≠i.flatten := by
  intro same
  have objects : (Except.ok i.mixkeyObject : Checked JSObject)=Except.ok i.flattenObject := by
    rw [←i.mixkeyPresent,←i.flattenPresent,same]
  have kinds := congrArg JSObject.kind (Except.ok.inj objects)
  rw [i.mixkeyKind,i.flattenKind] at kinds
  have length := congrArg (fun kind => match kind with
    | .function closure => closure.body.length
    | _ => 0) kinds
  have impossible : (2:Nat)=3 := length
  omega

theorem actual_prefix (state : Browser.State) (i : Inputs)
    (captured : state.nativeTimestampMixkey=some i.mixkey) (fuel : Nat) :
    BrowserRuntime.run (128+fuel)
      {state with machine := SeedrandomInvocation.preparedText i.globals.base i.globals.scope i.receiver i.seed i.seedrandom} =
      BrowserRuntime.run fuel {state with machine := beforeMixing i} := by
  apply SeedRuntimeCapture.actual_seedrandom_to_mixkey state (setup i) _ i.flattenObject i.flattenPresent i.flattenKind fuel
  rw [captured]
  exact fun same => flatten_different i (Option.some.inj same)

theorem actual_capture (state : Browser.State) (i : Inputs)
    (captured : state.nativeTimestampMixkey=some i.mixkey) :
    BrowserRuntime.step {state with machine := beforeMixing i} =
      {state with
        machine := TimestampSeedMixingCapture.prepared i
        timestampMixkeyActivations := state.timestampMixkeyActivations+1} := by
  rw [show beforeMixing i={beforeMixing i with control := .invoke (.object i.mixkey) .undefined [.timestampText i.seed.toArray,.object (key i)] false} from rfl,SeedRuntimeCapture.invocation_step]
  exact TimestampSeedMixingCapture.actual_browser_step i _ rfl captured

theorem actual_setup_and_capture (state : Browser.State) (i : Inputs)
    (captured : state.nativeTimestampMixkey=some i.mixkey) (fuel : Nat) :
    BrowserRuntime.run (129+fuel)
      {state with machine := SeedrandomInvocation.preparedText i.globals.base i.globals.scope i.receiver i.seed i.seedrandom} =
      BrowserRuntime.run fuel {state with
        machine := TimestampSeedMixingCapture.prepared i
        timestampMixkeyActivations := state.timestampMixkeyActivations+1} := by
  rw [show 129+fuel=128+(fuel+1) by omega,actual_prefix state i captured]
  change BrowserRuntime.run fuel (BrowserRuntime.step {state with machine := beforeMixing i}) = _
  rw [actual_capture state i captured]

end CookieClicker.JavaScript.TimestampSeedRuntimeEntry

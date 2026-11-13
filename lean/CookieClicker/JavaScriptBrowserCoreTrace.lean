import CookieClicker.JavaScriptBrowserCoreStep
import CookieClicker.JavaScriptSeedrandomNativeInspect

/-! Finite checked traces connect exact core execution to the browser runtime.
Each accepted transition retains its dispatch and run-equation proofs. -/
namespace CookieClicker.JavaScript.BrowserCoreTrace
open SeedrandomNativeInspect
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def ordinaryInvoke (state : Browser.State) (function : Value) (arguments : List Value) (construct : Bool) : Bool :=
  match function,arguments,construct with
  | .object id,[],false => state.nativeSeedrandom != some id
  | .object id,.timestampText _ :: _,false => state.nativeTimestampMixkey != some id
  | _,_,_ => true

theorem invoke_step (state : Browser.State) (function receiver : Value) (arguments : List Value) (construct : Bool)
    (accepted : ordinaryInvoke state function arguments construct=true) :
    BrowserRuntime.step {state with machine := {state.machine with control := .invoke function receiver arguments construct}} =
      {state with machine := {Builtins.builtinStep {state.machine with control := .invoke function receiver arguments construct}
        with elapsed := state.machine.elapsed}} := by
  cases construct with
  | true =>
    cases function <;> try rfl
    case object id =>
      cases arguments with
      | nil => rfl
      | cons first rest => cases first <;> rfl
  | false =>
    cases function <;> try rfl
    case object id =>
      cases arguments with
      | nil =>
        apply BrowserCoreStep.invoke_empty
        simpa [ordinaryInvoke] using accepted
      | cons first rest =>
        cases first <;> try rfl
        case timestampText text =>
          have no : (state.nativeTimestampMixkey == some id)=false := by
            simpa [ordinaryInvoke] using accepted
          change Browser.step {state with machine := {state.machine with control := .invoke (.object id) receiver (.timestampText text::rest) false}} = _
          simp only [Browser.step,Browser.internalStep,no,Bool.false_eq_true,↓reduceIte]

structure Transition (state : Browser.State) where
  machine : Machine
  step : BrowserRuntime.step state={state with machine := machine}
  source : ∀ fuel, Builtins.run (fuel+1) state.machine=Builtins.run fuel machine
  runtime : ∀ fuel, BrowserRuntime.run (fuel+1) state=BrowserRuntime.run fuel {state with machine := machine}

private instance (name : String) : Decidable (BrowserCoreStep.nativeNamespace name) :=
  inferInstanceAs (Decidable (name="String" ∨ name="String.prototype" ∨ name="Function.prototype"))

def dispatch (state : Browser.State) : Except String (PLift (BrowserRuntime.step state=
    {state with machine := {Builtins.builtinStep state.machine with elapsed := state.machine.elapsed}})) := do
  match control : state.machine.control with
  | .invoke function receiver arguments construct =>
    let ⟨accepted⟩ ← require (ordinaryInvoke state function arguments construct=true) "Invocation selects captured browser dispatch"
    pure ⟨by simpa only [←control] using (invoke_step state function receiver arguments construct accepted)⟩
  | .unresolved (.builtin id receiver arguments construct) =>
    let ⟨supported⟩ ← require (BrowserCoreStep.nativeNamespace id.namespaceName) "Builtin namespace is not in the checked core set"
    pure ⟨by simpa only [←control] using
      (BrowserCoreStep.builtin_step state state.machine id receiver arguments construct supported)⟩
  | .resumeBuiltin continuation value =>
    let ⟨supported⟩ ← require (BrowserCoreStep.nativeNamespace continuation.id.namespaceName) "Builtin continuation is not in the checked core set"
    pure ⟨by simpa only [←control] using
      (BrowserCoreStep.resume_step state state.machine continuation value supported)⟩
  | _ =>
    let ⟨plain⟩ ← require (BrowserCoreStep.plain state.machine.control=true) "Control is not a checked core transition"
    match running : status state.machine with
    | .running => pure ⟨BrowserCoreStep.plain_step state plain running⟩
    | _ => throw "Plain control is not running"

def transition (state : Browser.State) : Except String (Transition state) := do
  let ⟨step⟩ ← dispatch state
  let next := Builtins.builtinStep state.machine
  have nextDef : Builtins.builtinStep state.machine=next := rfl
  let ⟨elapsed⟩ ← require (next.elapsed=state.machine.elapsed) "Core transition changes elapsed time"
  have stepExact : BrowserRuntime.step state={state with machine := next} := by
    rw [step,←elapsed]
  match running : status state.machine with
  | .running =>
    pure ⟨next,stepExact,
      by intro fuel; simp only [Builtins.run,running,nextDef],
      by intro fuel; simp only [BrowserRuntime.run,running,stepExact]⟩
  | .unresolved (.builtin id receiver arguments construct) =>
    match nextRunning : status next with
    | .running =>
      pure ⟨next,stepExact,
        by intro fuel; simp only [Builtins.run,running,nextDef,nextRunning],
        by intro fuel; simp only [BrowserRuntime.run,running,stepExact,nextRunning]⟩
    | _ => throw "Builtin transition does not resume the core"
  | _ => throw "Transition has no checked run equation"

structure Trace (count : Nat) (state : Browser.State) where
  machine : Machine
  source : Builtins.run count state.machine=machine
  runtime : BrowserRuntime.run count state={state with machine := machine}

def inspect : (count : Nat) → (state : Browser.State) → Except String (Trace count state)
  | 0,state => .ok ⟨state.machine,rfl,rfl⟩
  | count+1,state => do
    let first ← transition state
    let rest ← inspect count {state with machine := first.machine}
    pure ⟨rest.machine,
      (first.source count).trans rest.source,
      by rw [first.runtime count,rest.runtime]⟩

end CookieClicker.JavaScript.BrowserCoreTrace

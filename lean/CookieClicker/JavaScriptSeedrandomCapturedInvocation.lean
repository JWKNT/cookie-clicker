import CookieClicker.JavaScriptSeedrandomCapturedRuntime

/-! The retained captured seedrandom object supplies the actual runtime call
entry. Its source parameters separate it from captured timestamp mixkey. -/
namespace CookieClicker.JavaScript.SeedrandomCapturedInvocation
open SeedrandomCapturedFrame SeedrandomCapturedRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem seed_mix_different {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    (sourceInputs frame).seedrandom≠(sourceInputs frame).mixkey := by
  intro same
  have seedRead : checkedObject (sourceInputs frame).globals.base.heap (sourceInputs frame).seedrandom=.ok frame.seedObject :=
    (congrArg (fun machine : Machine => checkedObject machine.heap (sourceInputs frame).seedrandom) frame.baseSame).trans frame.seedRead
  have readSame := congrArg (checkedObject (sourceInputs frame).globals.base.heap) same
  have objects := Except.ok.inj (seedRead.symm.trans (readSame.trans (sourceInputs frame).mixkeyPresent))
  have kinds := frame.seedKind.symm.trans ((congrArg JSObject.kind objects).trans (sourceInputs frame).mixkeyKind)
  have parameters := congrArg (fun kind => match kind with | .function closure => closure.parameters | _ => []) kinds
  have impossible : (["a","f"] : List String)=["a","b"] := parameters
  exact (by decide : (["a","f"] : List String)≠["a","b"]) impossible

def invocation {state : Browser.State} {seed : JSString} (frame : Captured state seed) : Browser.State :=
  {state with machine := {state.machine with control := (.invoke (.object (sourceInputs frame).seedrandom)
    (.object (sourceInputs frame).receiver) [.timestampText (sourceInputs frame).seed.toArray] false)}}

theorem native_math_receiver {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    state.mathObject=some (sourceInputs frame).receiver :=
  frame.mathSame.trans (congrArg some frame.receiverSame.symm)

theorem invocation_eq_native {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    invocation frame={state with machine := {state.machine with control := (.invoke (.object (sourceInputs frame).seedrandom) (.object frame.inputs.source.math) [.timestampText seed.toArray] false)}} := by
  unfold invocation sourceInputs
  rw [frame.receiverSame,frame.seedSame]

theorem actual_invocation {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    BrowserRuntime.step (invocation frame)=prepared frame := by
  have separate : state.nativeTimestampMixkey≠some (sourceInputs frame).seedrandom := by
    rw [frame.mixkeySame]
    intro same
    exact seed_mix_different frame (Option.some.inj same).symm
  have accepted : BrowserCoreTrace.ordinaryInvoke state (.object (sourceInputs frame).seedrandom)
      [.timestampText (sourceInputs frame).seed.toArray] false=true := by
    simpa [BrowserCoreTrace.ordinaryInvoke] using separate
  rw [invocation,BrowserCoreTrace.invoke_step _ _ _ _ _ accepted]
  change {state with machine := {invoke (invocation frame).machine
    (.object (sourceInputs frame).seedrandom) (.object (sourceInputs frame).receiver)
    [.timestampText (sourceInputs frame).seed.toArray] false with elapsed := state.machine.elapsed}} = _
  rw [SeedrandomInvocation.actual_invokeText (invocation frame).machine (sourceInputs frame).globals.scope
    (sourceInputs frame).receiver (sourceInputs frame).seed (sourceInputs frame).seedrandom frame.seedObject frame.seedRead frame.seedKind]
  unfold invocation prepared sourceInputs
  rw [frame.baseSame]
  rfl

attribute [local irreducible] SeedrandomCapturedRuntime.steps SeedrandomCapturedFrame.setupResult
  SeedrandomCapturedRuntime.returned

theorem actual_complete_return {state : Browser.State} {seed : JSString} (frame : Captured state seed)
    (complete : Complete frame) :
    BrowserRuntime.run (130+steps frame) (invocation frame)=returned frame (setupResult frame) := by
  rw [show 130+steps frame=(129+steps frame)+1 by omega]
  change BrowserRuntime.run (129+steps frame) (BrowserRuntime.step (invocation frame))= _
  rw [actual_invocation,runtime_return frame complete]

theorem actual_native_math_return {state : Browser.State} {seed : JSString} (frame : Captured state seed)
    (complete : Complete frame) :
    BrowserRuntime.run (130+steps frame)
      {state with machine := {state.machine with control := (.invoke (.object (sourceInputs frame).seedrandom) (.object frame.inputs.source.math) [.timestampText seed.toArray] false)}} =
      returned frame (setupResult frame) := by
  rw [←invocation_eq_native frame]
  exact actual_complete_return frame complete

end CookieClicker.JavaScript.SeedrandomCapturedInvocation

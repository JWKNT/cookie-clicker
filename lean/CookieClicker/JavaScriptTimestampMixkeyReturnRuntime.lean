import CookieClicker.JavaScriptTimestampMixkeyReturn
import CookieClicker.JavaScriptBrowserCoreStep

/-! Retained source return operations under actual browser dispatch. -/
namespace CookieClicker.JavaScript.TimestampMixkeyReturnRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkeyReturn
open TimestampMixkey TimestampMixkeyLoop

attribute [local cbv_opaque] source callee objects smear index base scope seed key libraryBindings libraryOuter
  sourceHeap heap localIndex bodyHeap checkedEnvironment readBinding Array.size List.length JSString.ofString

attribute [local cbv_eval] contains_o read_o checked_library checked_local environment_size local_read_b

attribute [local cbv_eval] local_environment library_environment size read_b

theorem actual_return_prefix (state : Browser.State) (i : TimestampMixkeyReturn.Inputs) (fuel : Nat) :
    BrowserRuntime.run (11+fuel) {state with machine := (start i)} = BrowserRuntime.run fuel {state with machine := (beforeCall i)} := by
  change BrowserRuntime.run (11+fuel) {state with machine := {start i with heap := sourceHeap i}} = _
  rw [Nat.add_comm 11 fuel]
  cases previous : i.previous <;> cbv <;> simp only [previous] <;> cbv
  all_goals simp only [size]
  all_goals cbv



theorem actual_invocation (state : Browser.State) (i : TimestampMixkeyReturn.Inputs) :
    BrowserRuntime.step {state with machine := beforeCall i}={state with machine := prepared i} := by
  have passthrough : BrowserRuntime.step {state with machine := beforeCall i}=
      {state with machine := {Builtins.builtinStep (beforeCall i) with elapsed := (base (source i)).elapsed}} := rfl
  rw [passthrough,TimestampMixkeyReturn.actual_invocation]
  rfl

theorem actual_return_call (state : Browser.State) (i : TimestampMixkeyReturn.Inputs) (fuel : Nat) :
    BrowserRuntime.run (12+fuel) {state with machine := TimestampMixkeyReturn.start i}=
      BrowserRuntime.run fuel {state with machine := prepared i} := by
  rw [show 12+fuel=11+(fuel+1) by omega,actual_return_prefix]
  change BrowserRuntime.run fuel (BrowserRuntime.step {state with machine := beforeCall i}) = _
  rw [actual_invocation]

end CookieClicker.JavaScript.TimestampMixkeyReturnRuntime

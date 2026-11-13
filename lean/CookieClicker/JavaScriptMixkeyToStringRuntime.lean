import CookieClicker.JavaScriptMixkeyToString
import CookieClicker.JavaScriptMixkeyApplyRuntime

/-! Retained source return operations under actual browser dispatch. -/
namespace CookieClicker.JavaScript.MixkeyToStringRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open MixkeyToString

attribute [local cbv_opaque] base scope callee array globalScope constructorId codes applyId heap localIndex argumentIndex List.length Array.size allocatedHeap JSString.ofString Environment.identifier readProperty checkedEnvironment readBinding

attribute [local cbv_eval] local_read global_read environment_size read_a identifier_string_explicit read_string_explicit read_codes_explicit read_apply_explicit

theorem actual_prefix (state : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (8+fuel) {state with machine := (start i)} = BrowserRuntime.run fuel {state with machine := (beforeString i)} := by
  change BrowserRuntime.run (8+fuel) {state with machine := {start i with heap := heap i}} = _
  rw [Nat.add_comm 8 fuel]
  cbv



theorem actual_call_prefix (state : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (16+fuel) {state with machine := (beforeString i)} = BrowserRuntime.run fuel {state with machine := (beforeApply i)} := by
  rw [Nat.add_comm 16 fuel]
  cbv
  simp only [identifier_string_explicit]
  cbv
  simp only [read_string_explicit,read_codes_explicit,read_apply_explicit,environment_size]
  cbv
  simp only [read_string_explicit,read_codes_explicit,read_apply_explicit,environment_size]
  cbv
  simp only [read_string_explicit,read_codes_explicit,read_apply_explicit,identifier_a_explicit,environment_size]
  cbv
  simp only [identifier_a_explicit,environment_size]
  cbv


attribute [local cbv_opaque] text

theorem actual_source_return (state : Browser.State) (i : Inputs) (data : ArrayData i) (fuel : Nat) :
    BrowserRuntime.run (3+fuel) {state with machine := (afterApply i data)} = BrowserRuntime.run fuel {state with machine := (returned i data)} := by
  rw [Nat.add_comm 3 fuel]
  cbv



theorem actual_apply_invoke (state : Browser.State) (i : Inputs) :
    BrowserRuntime.step {state with machine := beforeApply i}={state with machine := applyRequest i} := by
  have passthrough : BrowserRuntime.step {state with machine := beforeApply i}=
      {state with machine := {Builtins.builtinStep (beforeApply i) with elapsed := (base i).elapsed}} := rfl
  rw [passthrough,MixkeyToString.actual_apply_invoke]
  rfl

theorem actual_native_apply (state : Browser.State) (i : Inputs) (data : ArrayData i)
    (notSeed : state.nativeSeedrandom≠some (codes i)) (fuel : Nat) :
    BrowserRuntime.run (5+2*data.length+fuel) {state with machine := applyRequest i}=
      BrowserRuntime.run fuel {state with machine := afterApply i data} :=
  MixkeyApplyRuntime.actual_apply_request state (applyInput i data) rfl notSeed fuel

theorem actual_source_helper (state : Browser.State) (i : Inputs) (data : ArrayData i)
    (notSeed : state.nativeSeedrandom≠some (codes i)) (fuel : Nat) :
    BrowserRuntime.run (33+2*data.length+fuel) {state with machine := start i}=
      BrowserRuntime.run fuel {state with machine := returned i data} := by
  rw [show 33+2*data.length+fuel=8+(16+((5+2*data.length+(3+fuel))+1)) by omega,actual_prefix,actual_call_prefix]
  change BrowserRuntime.run (5+2*data.length+(3+fuel)) (BrowserRuntime.step {state with machine := beforeApply i}) = _
  rw [actual_apply_invoke,actual_native_apply state i data notSeed,actual_source_return]

end CookieClicker.JavaScript.MixkeyToStringRuntime

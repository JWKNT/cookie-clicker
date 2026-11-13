import CookieClicker.JavaScriptTimestampMixkeyCode
import CookieClicker.JavaScriptBrowserCoreStep

/-! Retained source prefixes under the composed browser handlers. -/
namespace CookieClicker.JavaScript.TimestampMixkeyCodeRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkeyCode
open TimestampMixkey TimestampMixkeyLoop

attribute [local cbv_opaque] base scope seed key libraryBindings libraryOuter heap localIndex bodyHeap
  checkedEnvironment binary toJSString readBinding MixkeyIndex.key Nat.mod Number.ofNat Array.size List.length readProperty

attribute [local cbv_eval] checked_library checked_local environment_size contains_mask read_mask
  local_read_a local_read_b local_read_c local_read_d local_read_e slot_ofNat key_mod

theorem actual_method_prefix (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (fuel : Nat) :
    BrowserRuntime.run (8+fuel) {state with machine := (startCode i objects d index previous)} =
      BrowserRuntime.run fuel {state with machine := (atMethod i objects d index previous)} := by
  change BrowserRuntime.run (8+fuel) {state with machine := {startCode i objects d index previous with heap := heap i objects (.number d) index}} = _
  rw [Nat.add_comm 8 fuel]
  cbv


attribute [local cbv_opaque] setBinding

attribute [local cbv_eval] write_index write_index_succ

theorem actual_postincrement (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (9+fuel) {state with machine := {atMethod i objects d index previous with control := .expressionResult (.value (.object method))}} =
      BrowserRuntime.run fuel {state with machine := (atInvoke i objects d index previous method)} := by
  change BrowserRuntime.run (9+fuel) {state with machine := {atMethod i objects d index previous with
    heap := heap i objects (.number d) index, control := .expressionResult (.value (.object method))}} = _
  rw [Nat.add_comm 9 fuel]
  cbv
  all_goals (try simp only [write_index_succ]; cbv)
  all_goals rfl



theorem actual_method_lookup (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (frame : MixkeyString.PrototypeFrame (atMethod i objects d index previous)) :
    BrowserRuntime.step {state with machine := atMethod i objects d index previous} =
      {state with machine := afterMethod i objects d index previous frame.method} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,TimestampMixkeyCode.actual_method_lookup i objects d index previous frame]
  rfl

theorem actual_builtin_request (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (object : JSObject)
    (present : checkedObject (heap i objects (.number d) (index+1)) method = .ok object)
    (kind : object.kind = .builtin MixkeyString.methodId) :
    BrowserRuntime.step {state with machine := atInvoke i objects d index previous method} =
      {state with machine := atBuiltin i objects d index previous method} := by
  have passthrough : BrowserRuntime.step {state with machine := atInvoke i objects d index previous method} =
      {state with machine := {Builtins.builtinStep (atInvoke i objects d index previous method) with elapsed := (base i).elapsed}} := rfl
  rw [passthrough,TimestampMixkeyCode.actual_builtin_request i objects d index previous method object present kind]
  rfl

theorem actual_builtin_response (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size) :
    BrowserRuntime.step {state with machine := atBuiltin i objects d index previous method} =
      {state with machine := afterCode i objects d index previous method bound} := by
  have passthrough : BrowserRuntime.step {state with machine := atBuiltin i objects d index previous method} =
      {state with machine := {Builtins.builtinStep (atBuiltin i objects d index previous method) with elapsed := (base i).elapsed}} :=
    BrowserCoreStep.builtin_step state (atInvoke i objects d index previous method) MixkeyString.methodId
      (.timestampText (seed i)) [.textIndex (Int.ofNat index)] false (Or.inr (Or.inl rfl))
  rw [passthrough,TimestampMixkeyCode.actual_builtin_response i objects d index previous method bound]
  rfl

theorem actual_builtin_call (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (object : JSObject)
    (present : checkedObject (heap i objects (.number d) (index+1)) method = .ok object)
    (kind : object.kind = .builtin MixkeyString.methodId) (bound : index < (seed i).size) (fuel : Nat) :
    BrowserRuntime.run (2+fuel) {state with machine := atInvoke i objects d index previous method} =
      BrowserRuntime.run fuel {state with machine := afterCode i objects d index previous method bound} := by
  rw [show 2+fuel=(fuel+1)+1 by omega]
  change BrowserRuntime.run (fuel+1) (BrowserRuntime.step {state with machine := atInvoke i objects d index previous method}) = _
  rw [actual_builtin_request state i objects d index previous method object present kind]
  simp only [BrowserRuntime.run]
  change (match status (BrowserRuntime.step {state with machine := atBuiltin i objects d index previous method}).machine with
    | .unresolved nextRequest => _
    | .fault _ => _
    | _ => _) = _
  rw [actual_builtin_response state i objects d index previous method bound]
  rfl

end CookieClicker.JavaScript.TimestampMixkeyCodeRuntime

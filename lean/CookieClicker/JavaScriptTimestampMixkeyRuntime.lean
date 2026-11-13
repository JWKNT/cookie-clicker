import CookieClicker.JavaScriptTimestampMixkey
import CookieClicker.JavaScriptBrowserCoreStep

/-! Retained source prefixes under the composed browser handlers. -/
namespace CookieClicker.JavaScript.TimestampMixkeyRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey
open SeedrandomMixkeySyntax

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withD withC withE defineBinding

attribute [local cbv_eval] hoist_d hoist_c hoist_e

theorem actual_hoist (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (8+fuel) {state with machine := (prepared base scope seed key callee)} =
      BrowserRuntime.run fuel {state with machine := (hoisted base scope seed key callee)} := by
  rw [Nat.add_comm 8 fuel]
  cbv



attribute [local cbv_opaque] bodyHeap objectsWithArgument setBinding checkedEnvironment binary

attribute [local cbv_eval] checked_body_local body_environment_size write_c write_e append_empty initial_scope

theorem actual_initializers (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (18+fuel) {state with machine := (hoisted base scope seed key callee)} =
      BrowserRuntime.run fuel {state with machine := (atGuard base scope seed key (objectsWithArgument base seed key callee) .undefined 0 none)} := by
  change BrowserRuntime.run (18+fuel) {state with machine := {hoisted base scope seed key callee with
    heap := bodyHeap base scope seed key (objectsWithArgument base seed key callee) .undefined .undefined .undefined}} = _
  rw [Nat.add_comm 18 fuel]
  cbv



attribute [local cbv_opaque] Array.push Array.size readProperty

attribute [local cbv_eval] Array.size_push read_length body_allocate loop_compare

theorem actual_guard_prefix (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    BrowserRuntime.run (7+fuel) {state with machine := (atGuard base scope seed key objects d index previous)} =
      BrowserRuntime.run fuel {state with machine := (atLength base scope seed key objects d index previous)} := by
  rw [Nat.add_comm 7 fuel]
  cbv


theorem actual_guard_right (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    BrowserRuntime.run (4+fuel) {state with machine := (afterLength base scope seed key objects d index previous)} =
      BrowserRuntime.run fuel {state with machine := (atComparison base scope seed key objects d index previous)} := by
  rw [Nat.add_comm 4 fuel]
  cbv



theorem actual_length_step (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :
    BrowserRuntime.step {state with machine := atLength base scope seed key objects d index previous} =
      {state with machine := afterLength base scope seed key objects d index previous} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,TimestampMixkey.actual_length_step]
  rfl

theorem actual_compare_step (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :
    BrowserRuntime.step {state with machine := atComparison base scope seed key objects d index previous} =
      {state with machine := atBranch base scope seed key objects d index previous} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,TimestampMixkey.actual_compare_step]
  rfl

theorem actual_branch_step (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :
    BrowserRuntime.step {state with machine := atBranch base scope seed key objects d index previous} =
      {state with machine := (if index<seed.size then atBody base scope seed key (objects.push (stringWrapper base seed)) d index previous
        else atExit base scope seed key (objects.push (stringWrapper base seed)) d index previous)} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,TimestampMixkey.actual_branch_step]
  split <;> rfl

theorem actual_guard (state : Browser.State) (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    BrowserRuntime.run (14+fuel) {state with machine := atGuard base scope seed key objects d index previous} =
      BrowserRuntime.run fuel {state with machine := (if index<seed.size then
        atBody base scope seed key (objects.push (stringWrapper base seed)) d index previous
        else atExit base scope seed key (objects.push (stringWrapper base seed)) d index previous)} := by
  rw [show 14+fuel=7+((4+((fuel+1)+1))+1) by omega,actual_guard_prefix]
  change BrowserRuntime.run (4+((fuel+1)+1)) (BrowserRuntime.step {state with machine := atLength base scope seed key objects d index previous}) = _
  rw [actual_length_step,actual_guard_right]
  change BrowserRuntime.run (fuel+1) (BrowserRuntime.step {state with machine := atComparison base scope seed key objects d index previous}) = _
  rw [actual_compare_step]
  change BrowserRuntime.run fuel (BrowserRuntime.step {state with machine := atBranch base scope seed key objects d index previous}) = _
  rw [actual_branch_step]

end CookieClicker.JavaScript.TimestampMixkeyRuntime

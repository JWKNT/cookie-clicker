import CookieClicker.JavaScriptTimestampSeedRuntime
import CookieClicker.JavaScriptBrowserCoreStep

/-! The complete tagged flatten source runs through the browser composition. -/
namespace CookieClicker.JavaScript.TimestampFlattenRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open TimestampSeedFlatten

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withE withC withD defineBinding
attribute [local cbv_eval] hoist_e hoist_c hoist_d
attribute [local cbv_opaque] Array.push Array.size
attribute [local cbv_eval] Array.size_push
attribute [local cbv_opaque] bodyHeap objectsWithArgument setBinding Heap.allocateObject checkedEnvironment checkedObject lookupProperty readProperty
attribute [local cbv_eval] read_type_zero checked_body_local body_environment_size body_allocate write_c write_d
attribute [local cbv_eval] checked_array array_length_zero

theorem actual_hoist (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (13+fuel) {state with machine := prepared base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := hoisted base scope receiver seed callee} := by
  rw [Nat.add_comm 13 fuel]
  cbv

attribute [local cbv_eval] initial_locals

theorem actual_type_prefix (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (16+fuel) {state with machine := hoisted base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := atType base scope receiver seed callee} := by
  change BrowserRuntime.run (16+fuel) {state with machine := {hoisted base scope receiver seed callee with
    heap := bodyHeap base scope seed (objectsWithArgument base seed callee) .undefined .undefined}} = _
  rw [Nat.add_comm 16 fuel]
  cbv


theorem actual_type_step (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) :
    BrowserRuntime.step {state with machine := atType base scope receiver seed callee} =
      {state with machine := afterType base scope receiver seed callee} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,TimestampSeedFlatten.actual_type_step]
  rfl


theorem actual_branch_prefix (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (28+fuel) {state with machine := afterType base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := atLength base scope receiver seed callee} := by
  rw [Nat.add_comm 28 fuel]
  cbv


theorem actual_length_step (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) :
    BrowserRuntime.step {state with machine := atLength base scope receiver seed callee} =
      {state with machine := afterLength base scope receiver seed callee} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,TimestampSeedFlatten.actual_length_step]
  rfl


theorem actual_return_suffix (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (16+fuel) {state with machine := afterLength base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := afterBody base scope receiver seed callee} := by
  rw [Nat.add_comm 16 fuel]
  cbv


theorem actual_restore_caller (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (2+fuel) {state with machine := afterBody base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := returned base scope seed callee} := by
  rw [Nat.add_comm 2 fuel]
  cbv


theorem actual_prepared_return (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (77+fuel) {state with machine := prepared base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := returned base scope seed callee} := by
  rw [show 77+fuel=13+(16+(1+(28+(1+(16+(2+fuel)))))) by omega,actual_hoist,actual_type_prefix]
  rw [Nat.add_comm 1 (28+(1+(16+(2+fuel))))]
  change BrowserRuntime.run (28+(1+(16+(2+fuel)))) (BrowserRuntime.step {state with machine := atType base scope receiver seed callee}) = _
  rw [actual_type_step,actual_branch_prefix]
  rw [Nat.add_comm 1 (16+(2+fuel))]
  change BrowserRuntime.run (16+(2+fuel)) (BrowserRuntime.step {state with machine := atLength base scope receiver seed callee}) = _
  rw [actual_length_step,actual_return_suffix,actual_restore_caller]


end CookieClicker.JavaScript.TimestampFlattenRuntime

import CookieClicker.JavaScriptTimestampSeedMixingCapture
import CookieClicker.JavaScriptBrowserRuntime

/-! Retained seed-library statements execute in the composed browser runtime.
The concrete browser handlers remain part of every represented transition. -/
namespace CookieClicker.JavaScript.TimestampSeedRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampSeedSetup
open SeedrandomInvocation (allocatedHeapText localIndex argumentIndex preparedText)

attribute [local cbv_opaque] allocatedHeapText localIndex argumentIndex SeedrandomInvocation.localsText withJ withP withQ defineBinding
attribute [local cbv_eval] hoist_j hoist_p hoist_q

theorem actual_hoist (state : Browser.State) (base : Machine) (scope receiver : EnvId)
    (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (7+fuel) {state with machine := preparedText base scope receiver seed callee} =
      BrowserRuntime.run fuel {state with machine := hoisted base scope receiver seed callee} := by
  rw [Nat.add_comm 7 fuel]
  cbv


attribute [local cbv_opaque] base scope receiver callee seed mixkey flatten libraryBindings libraryOuter
attribute [local cbv_opaque] sourceHeap initialObjects checkedEnvironment readBinding setBinding Heap.allocateObject binaryWithHeap
attribute [local cbv_opaque] Array.push Array.size
attribute [local cbv_eval] Array.size_push source_locals
attribute [local cbv_eval] checked_local checked_library library_contains_m library_contains_l library_read_m library_read_l
attribute [local cbv_eval] read_a read_f read_arguments read_j write_j source_environment_size source_allocate arguments_present arguments_present_literal

theorem actual_flatten_prefix (state : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (38+fuel) {state with machine := sourceStart i} =
      BrowserRuntime.run fuel {state with machine := atFlatten i} := by
  change BrowserRuntime.run (38+fuel) {state with machine := {sourceStart i with heap := sourceHeap i (initialObjects i) .undefined}} = _
  rw [Nat.add_comm 38 fuel]
  cbv
  simp only [source_environment_size]
  cbv
  all_goals (simp only [source_environment_size]; cbv)
  all_goals (simp only [arguments_present_literal]; cbv)

end CookieClicker.JavaScript.TimestampSeedRuntime

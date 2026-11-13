import CookieClicker.JavaScriptTimestampMixkeyTraversal
import CookieClicker.JavaScriptTimestampMixkeyRuntime
import CookieClicker.JavaScriptTimestampIterationRuntime

/-! Complete finite UTF16 traversal through the actual browser composition. -/
namespace CookieClicker.JavaScript.TimestampTraversalRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey TimestampMixkeyLoop TimestampMixkeyCode TimestampMixkeyFinish TimestampMixkeyFrame
open TimestampMixkeyTraversal

theorem actual_advance (browser : Browser.State) (i : Inputs) (state : State i) (bound : state.index < (seed i).size) (fuel : Nat) :
    BrowserRuntime.run (93+fuel) {browser with machine := (machine i state)} = BrowserRuntime.run fuel {browser with machine := (machine i (advance i state bound))} := by
  unfold machine
  rw [show 93+fuel=14+(79+fuel) by omega,TimestampMixkeyRuntime.actual_guard]
  simp only [bound,↓reduceIte]
  change BrowserRuntime.run (79+fuel) {browser with machine := (TimestampMixkeyIteration.start (iteration i state bound))} = _
  rw [TimestampIterationRuntime.actual_iteration]
  rfl


theorem actual_traverse (browser : Browser.State) (i : Inputs) (count : Nat) (state : State i) (fits : state.index+count ≤ (seed i).size) (fuel : Nat) :
    BrowserRuntime.run (93*count+fuel) {browser with machine := (machine i state)} = BrowserRuntime.run fuel {browser with machine := (machine i (traverse i count state fits))} := by
  induction count generalizing state with
  | zero => simp [traverse]
  | succ count ih =>
    rw [show 93*(count+1)+fuel=93+(93*count+fuel) by omega]
    rw [actual_advance browser i state (by omega)]
    exact ih _ _


theorem actual_exit (browser : Browser.State) (i : Inputs) (state : State i) (atEnd : state.index = (seed i).size) (fuel : Nat) :
    BrowserRuntime.run (14+fuel) {browser with machine := (machine i state)} = BrowserRuntime.run fuel {browser with machine := (exited i state)} := by
  unfold machine
  rw [TimestampMixkeyRuntime.actual_guard]
  simp [exited,atEnd]


theorem complete_source_loop (browser : Browser.State) (i : Inputs) (state : State i) (within : state.index ≤ (seed i).size) (fuel : Nat) :
    BrowserRuntime.run (93*((seed i).size-state.index)+14+fuel) {browser with machine := (machine i state)} =
      BrowserRuntime.run fuel {browser with machine := (exited i (traverse i ((seed i).size-state.index) state (by omega)))} := by
  rw [Nat.add_assoc,actual_traverse browser i ((seed i).size-state.index) state (by omega)]
  apply actual_exit
  rw [traverse_index]
  omega


theorem actual_source_loop (browser : Browser.State) (i : Inputs) (frame : TimestampMixkeyFrame.Frame i (base i).heap.objects)
    (empty : frame.length = 0) (callee : ObjectId) (fuel : Nat) :
    BrowserRuntime.run (26+93*(seed i).size+14+fuel) {browser with machine := (prepared (base i) (scope i) (seed i) (key i) callee)} =
      BrowserRuntime.run fuel {browser with machine := (exited i (traversed i frame empty callee))} := by
  rw [show 26+93*(seed i).size+14+fuel = 8+(18+(93*(seed i).size+14+fuel)) by omega,
    TimestampMixkeyRuntime.actual_hoist,TimestampMixkeyRuntime.actual_initializers]
  change BrowserRuntime.run (93*(seed i).size+14+fuel) {browser with machine := (machine i (initial i frame empty callee))} = _
  have loop := complete_source_loop browser i (initial i frame empty callee) (by change 0≤(seed i).size; omega) fuel
  simpa only [initial,traversed,Nat.sub_zero] using loop


end CookieClicker.JavaScript.TimestampTraversalRuntime

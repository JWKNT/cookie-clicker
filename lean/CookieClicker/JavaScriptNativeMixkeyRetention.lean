import CookieClicker.JavaScriptNativeMixkeyTraversal
import CookieClicker.JavaScriptMixkeyRetention

/-! The real mixing traversal changes only its key object among existing
objects. Source lexical environments and the captured intrinsic paths persist. -/
namespace CookieClicker.JavaScript.NativeMixkeyRetention
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open NativeMixkey NativeMixkeyLoop NativeMixkeyFrame NativeMixkeyTraversal

open MixkeyRetention

theorem advance_preserves (i : Inputs) (state : State i) (bound : state.index < (seed i).size) :
    Preserves (key i) (referenceHeap i state.objects) (referenceHeap i (advance i state bound).objects) := by
  let first := stringWrapper (base i) (seed i)
  let added := (state.objects.push first).push first
  have allocated := HeapExtension.trans (NativeMixkeyFrame.append_extends i state.objects first)
    (NativeMixkeyFrame.append_extends i (state.objects.push first) first)
  apply trans (from_extension (key i) allocated)
  constructor
  · change added.size ≤ (added.set! (key i) _).size
    simp
  · intro id object different read
    change checkedObject (MixkeyArray.writtenHeap (referenceHeap i added) (key i)
      state.frame.object state.frame.length (Nat.mod state.index 256) (newByte i state bound)) id = .ok object
    rw [MixkeyArray.written_heap_other _ _ _ _ _ _ _ different]
    exact read

theorem traverse_preserves (i : Inputs) (count : Nat) (state : State i)
    (fits : state.index+count ≤ (seed i).size) :
    Preserves (key i) (referenceHeap i state.objects) (referenceHeap i (traverse i count state fits).objects) := by
  induction count generalizing state with
  | zero => exact refl _ _
  | succ count ih =>
    exact trans (advance_preserves i state (by omega)) (ih _ _)

theorem initial_preserves (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) :
    Preserves (key i) (base i).heap (referenceHeap i (initial i frame callee).objects) :=
  from_extension (key i) (HeapExtension.trans (HeapExtension.append_object _ (argumentObject (base i) (seed i) (key i) callee))
    (HeapExtension.same_objects (before := ((base i).heap.allocateObject (argumentObject (base i) (seed i) (key i) callee)).2)
      (after := referenceHeap i (initial i frame callee).objects) rfl))

theorem complete_preserves (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) :
    Preserves (key i) (base i).heap (exited i (traversed i frame callee)).heap := by
  let state := traversed i frame callee
  have first := trans (initial_preserves i frame callee)
    (traverse_preserves i (seed i).size (initial i frame callee) (by change 0+(seed i).size≤(seed i).size; omega))
  exact trans first (from_extension (key i) (HeapExtension.trans
    (NativeMixkeyFrame.append_extends i state.objects (stringWrapper (base i) (seed i)))
    (HeapExtension.same_objects (before := referenceHeap i (state.objects.push (stringWrapper (base i) (seed i))))
      (after := (exited i state).heap) rfl)))

end CookieClicker.JavaScript.NativeMixkeyRetention

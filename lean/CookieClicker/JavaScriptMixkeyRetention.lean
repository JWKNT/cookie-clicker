import CookieClicker.JavaScriptTimestampMixkeyTraversal
import CookieClicker.JavaScriptDataPropertyPath

/-! The real mixing traversal changes only its key object among existing
objects. Source lexical environments and the captured intrinsic paths persist. -/
namespace CookieClicker.JavaScript.MixkeyRetention
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey TimestampMixkeyLoop TimestampMixkeyFrame TimestampMixkeyTraversal

structure Preserves (key : ObjectId) (before after : Heap) : Prop where
  size : before.objects.size ≤ after.objects.size
  read : ∀ id object, key ≠ id → checkedObject before id = .ok object → checkedObject after id = .ok object

theorem refl (key : ObjectId) (heap : Heap) : Preserves key heap heap := ⟨Nat.le_refl _,fun _ _ _ h => h⟩

theorem trans {key : ObjectId} {first second third : Heap}
    (a : Preserves key first second) (b : Preserves key second third) : Preserves key first third :=
  ⟨Nat.le_trans a.size b.size,fun id object different read => b.read id object different (a.read id object different read)⟩

theorem from_extension (key : ObjectId) {before after : Heap} (extension : HeapExtension.Extends before after) :
    Preserves key before after := ⟨extension.size,fun id object _ read => HeapExtension.checked_object extension id object read⟩

inductive SafePath (key : ObjectId) (heap : Heap) (name : JSString) (value : Value) : ObjectId → Nat → Prop where
  | own (id : ObjectId) (object : JSObject) (writable enumerable configurable : Bool)
      (different : key ≠ id)
      (read : checkedObject heap id = .ok object)
      (inspected : object.unresolvedOwnNames.contains name = false)
      (data : ownProperty object name = some (.data value writable enumerable configurable)) : SafePath key heap name value id 0
  | parent (id next depth : Nat) (object : JSObject)
      (different : key ≠ id)
      (read : checkedObject heap id = .ok object)
      (inspected : object.unresolvedOwnNames.contains name = false)
      (absent : ownProperty object name = none)
      (complete : object.propertiesComplete = true)
      (link : object.prototype = some next)
      (rest : SafePath key heap name value next depth) : SafePath key heap name value id (depth+1)

theorem path {key : ObjectId} {before after : Heap} (retained : Preserves key before after)
    {name : JSString} {value : Value} {id depth : Nat} (original : SafePath key before name value id depth) :
    DataPropertyPath.Path after name value id depth := by
  induction original with
  | own id object w e c different read inspected data =>
    exact .own id object w e c (retained.read id object different read) inspected data
  | parent id next depth object different read inspected absent complete link rest ih =>
    exact .parent id next depth object (retained.read id object different read) inspected absent complete link ih

theorem advance_preserves (i : Inputs) (state : State i) (bound : state.index < (seed i).size) :
    Preserves (key i) (referenceHeap i state.objects) (referenceHeap i (advance i state bound).objects) := by
  let first := stringWrapper (base i) (seed i)
  let added := (state.objects.push first).push first
  have allocated := HeapExtension.trans (TimestampMixkeyFrame.append_extends i state.objects first)
    (TimestampMixkeyFrame.append_extends i (state.objects.push first) first)
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

theorem initial_preserves (i : Inputs) (frame : TimestampMixkeyFrame.Frame i (base i).heap.objects)
    (empty : frame.length=0) (callee : ObjectId) :
    Preserves (key i) (base i).heap (referenceHeap i (initial i frame empty callee).objects) :=
  from_extension (key i) (HeapExtension.trans (HeapExtension.append_object _ (argumentObject (base i) (seed i) (key i) callee))
    (HeapExtension.same_objects (before := ((base i).heap.allocateObject (argumentObject (base i) (seed i) (key i) callee)).2)
      (after := referenceHeap i (initial i frame empty callee).objects) rfl))

theorem complete_preserves (i : Inputs) (frame : TimestampMixkeyFrame.Frame i (base i).heap.objects)
    (empty : frame.length=0) (callee : ObjectId) :
    Preserves (key i) (base i).heap (exited i (traversed i frame empty callee)).heap := by
  let state := traversed i frame empty callee
  have first := trans (initial_preserves i frame empty callee)
    (traverse_preserves i (seed i).size (initial i frame empty callee) (by change 0+(seed i).size≤(seed i).size; omega))
  exact trans first (from_extension (key i) (HeapExtension.trans
    (TimestampMixkeyFrame.append_extends i state.objects (stringWrapper (base i) (seed i)))
    (HeapExtension.same_objects (before := referenceHeap i (state.objects.push (stringWrapper (base i) (seed i))))
      (after := (exited i state).heap) rfl)))

end CookieClicker.JavaScript.MixkeyRetention

import CookieClicker.JavaScriptRetainedArc4GeneratorReturn

/-! The generator's array writes preserve every other heap object, including
the captured instance whose index fields are written only at return. -/
namespace CookieClicker.JavaScript.RetainedArc4GenerateRetained
open RetainedArc4GenerateCursor RetainedArc4GenerateComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

theorem next_source (cursor : Cursor) : (next cursor).source=cursor.source := rfl
theorem next_array (cursor : Cursor) : (next cursor).array=cursor.array := rfl
theorem next_argument (cursor : Cursor) : (next cursor).argument=cursor.argument := rfl

theorem next_other (cursor : Cursor) (id : ObjectId) (different : cursor.array≠id) :
    (next cursor).objects[id]?=cursor.objects[id]? := by
  simp [next,inputs,RetainedArc4GenerateWrites.secondObjects,RetainedArc4GenerateWrites.firstObjects,
    RetainedArc4Generate.array,RetainedArc4Generate.objects,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different]

theorem traversal_source (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining) :
    (traverse count stage bound).cursor.source=stage.cursor.source := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    rfl

theorem traversal_array (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining) :
    (traverse count stage bound).cursor.array=stage.cursor.array := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    rfl

theorem traversal_argument (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining) :
    (traverse count stage bound).cursor.argument=stage.cursor.argument := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    rfl

theorem traversal_other (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining)
    (id : ObjectId) (different : stage.cursor.array≠id) :
    (traverse count stage bound).cursor.objects[id]?=stage.cursor.objects[id]? := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction (advance stage) _ (show (advance stage).cursor.array≠id from different)]
    exact next_other stage.cursor id different

theorem finished_source (stage : Stage) : (finished stage).cursor.source=stage.cursor.source :=
  traversal_source _ _ _
theorem finished_array (stage : Stage) : (finished stage).cursor.array=stage.cursor.array :=
  traversal_array _ _ _
theorem finished_argument (stage : Stage) : (finished stage).cursor.argument=stage.cursor.argument :=
  traversal_argument _ _ _

theorem checked_other (stage : Stage) (id : ObjectId) (object : JSObject)
    (different : stage.cursor.array≠id)
    (present : checkedObject (RetainedArc4Generate.objectHeap stage.cursor.source stage.cursor.objects) id=.ok object) :
    checkedObject (RetainedArc4Generate.objectHeap (finished stage).cursor.source (finished stage).cursor.objects) id=.ok object := by
  simp only [checkedObject,Heap.object?,RetainedArc4Generate.objectHeap] at present ⊢
  rw [finished,traversal_other _ _ _ _ different]
  exact present

end CookieClicker.JavaScript.RetainedArc4GenerateRetained

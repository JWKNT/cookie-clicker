import CookieClicker.JavaScriptArc4LoopInterlude

/-! The identity initialization changes only its native S array. The actual
input key and its native prototype objects survive all256 assignments. -/
namespace CookieClicker.JavaScript.Arc4IdentityRetained
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals Arc4IdentityLoop Arc4IdentityComplete

theorem next_other {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (small : cursor.index<256) (other : ObjectId) (different : array≠other) :
    (next cursor small).objects[other]? = cursor.objects[other]? := by
  simp [next,written,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different]

theorem traversal_other {i : Inputs} {argument array : Nat} {v : Values}
    (count : Nat) (stage : Stage i argument array v) (bound : stage.cursor.index+count≤256)
    (other : ObjectId) (different : array≠other) :
    (traverse count stage bound).cursor.objects[other]? = stage.cursor.objects[other]? := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    exact next_other stage.cursor _ other different

theorem finished_other {i : Inputs} {argument array : Nat} {v : Values}
    (stage : Stage i argument array v) (other : ObjectId) (different : array≠other) :
    (finished stage).cursor.objects[other]? = stage.cursor.objects[other]? :=
  traversal_other _ stage _ other different

theorem checked_other {i : Inputs} {argument array : Nat} {v : Values}
    (stage : Stage i argument array v) (other : ObjectId) (different : array≠other) :
    checkedObject (Arc4Schedule.objectHeap i (finished stage).cursor.objects) other =
      checkedObject (Arc4Schedule.objectHeap i stage.cursor.objects) other := by
  simp only [checkedObject,Heap.object?,Arc4Schedule.objectHeap]
  rw [finished_other stage other different]

theorem same_size {i : Inputs} {argument array : Nat} {v : Values}
    (count : Nat) (stage : Stage i argument array v) (bound : stage.cursor.index+count≤256) :
    (traverse count stage bound).cursor.objects.size = stage.cursor.objects.size := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    simp [advance,next,written]

def keyFrame {i : Inputs} {argument array : Nat} {v : Values}
    (stage : Stage i argument array v) (key : ObjectId)
    (frame : Arc4Bytes.Frame (Arc4Schedule.objectHeap i stage.cursor.objects) key)
    (different : array≠key) (arrayDifferent : array≠frame.prototype.arrayId)
    (rootDifferent : array≠frame.prototype.rootId) :
    Arc4Bytes.Frame (Arc4Schedule.objectHeap i (finished stage).cursor.objects) key := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := by rw [checked_other stage key different]; exact frame.present
  prototype := frame.prototype.transport rfl
    (by rw [checked_other stage _ arrayDifferent]; exact frame.prototype.arrayRead)
    (by rw [checked_other stage _ rootDifferent]; exact frame.prototype.rootRead)
  room := by simpa only [Arc4Schedule.objectHeap,finished,same_size] using frame.room
  bound := by simpa only [Arc4Schedule.objectHeap,finished,same_size] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

end CookieClicker.JavaScript.Arc4IdentityRetained

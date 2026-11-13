import CookieClicker.JavaScriptArc4Initializers

/-! The array and prototype frames obtained from the source initializers.
These frames are derived from the writes and fresh allocation, rather than
supplied as an independent loop-entry heap. -/
namespace CookieClicker.JavaScript.Arc4Initialized
open Arc4Initializers
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

theorem checked_present {heap : Heap} {id : ObjectId} {object : JSObject}
    (found : checkedObject heap id=.ok object) : heap.object? id=some object := by
  unfold checkedObject at found
  cases read : heap.object? id with
  | none => simp [read] at found
  | some original => simp only [read,Except.ok.injEq] at found; simpa [found] using read

theorem fresh_different (q : Setup) (id : ObjectId) (object : JSObject)
    (found : checkedObject (objectHeap q.source q.objects) id=.ok object)
    (different : object≠freshObject q.prototype) : q.receiver≠id := by
  intro equal
  have original := checked_present found
  change q.objects[id]?=some object at original
  rw [←equal,q.fresh] at original
  exact different (Option.some.inj original).symm

theorem receiver_key (q : Setup) : q.receiver≠q.key := by
  apply fresh_different q _ _ q.keyFrame.present
  intro same
  have shape := q.keyFrame.shape.kind
  rw [same] at shape
  contradiction

theorem receiver_array (q : Setup) : q.receiver≠q.keyFrame.prototype.arrayId := by
  apply fresh_different q _ _ q.keyFrame.prototype.arrayRead
  intro same
  have shape := q.keyFrame.prototype.arrayKind
  rw [same] at shape
  contradiction

theorem receiver_root (q : Setup) : q.receiver≠q.keyFrame.prototype.rootId := by
  apply fresh_different q _ _ q.keyFrame.prototype.rootRead
  intro same
  have shape := q.keyFrame.prototype.rootParent
  rw [same] at shape
  contradiction

theorem sizes (q : Setup) : (jObjects q).size=q.objects.size ∧
    (iObjects q).size=q.objects.size ∧ sIndex q=q.objects.size ∧
    (sObjects q).size=q.objects.size+1 := by
  simp [jObjects,iObjects,sIndex,sObjects,allocatedObjects]

theorem retained_checked (q : Setup) (id : ObjectId) (object : JSObject)
    (different : q.receiver≠id)
    (found : checkedObject (objectHeap q.source q.objects) id=.ok object) :
    checkedObject (objectHeap q.source (sObjects q)) id=.ok object := by
  have raw := checked_present found
  have bound : id<q.objects.size := (Array.getElem?_eq_some_iff.mp raw).1
  change q.objects[id]?=some object at raw
  have after : (sObjects q)[id]?=some object := by
    simpa only [sObjects,allocatedObjects,iObjects,jObjects,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different,↓reduceIte,
      Array.getElem?_push,Array.size_setIfInBounds,if_neg (Nat.ne_of_lt bound)] using raw
  simp [checkedObject,Heap.object?,objectHeap,after]

def retainedKey (q : Setup) : Arc4Bytes.Frame (objectHeap q.source (sObjects q)) q.key := {
  object := q.keyFrame.object, length := q.keyFrame.length, bytes := q.keyFrame.bytes, shape := q.keyFrame.shape
  present := retained_checked q _ _ (receiver_key q) q.keyFrame.present
  prototype := q.keyFrame.prototype.transport rfl
    (retained_checked q _ _ (receiver_array q) q.keyFrame.prototype.arrayRead)
    (retained_checked q _ _ (receiver_root q) q.keyFrame.prototype.rootRead)
  room := by
    change 2≤(sObjects q).size
    rw [(sizes q).2.2.2]
    have bound : 2≤q.objects.size := q.keyFrame.room
    omega
  bound := by
    change q.key<(sObjects q).size
    rw [(sizes q).2.2.2]
    exact Nat.lt_trans q.keyFrame.bound (Nat.lt_succ_self _)
  arrayDifferent := q.keyFrame.arrayDifferent
  rootDifferent := q.keyFrame.rootDifferent }

theorem empty_shape (prototype : Option ObjectId) :
    DenseArray.Shape (emptyArray prototype) 0 (fun _ => .undefined) := by
  refine ⟨rfl,rfl,rfl,rfl,by decide,rfl,?_⟩
  intro index small
  have different := DenseArray.length_not_key index small
  simp [emptyArray,ownProperty,different]

theorem empty_present (q : Setup) :
    checkedObject (objectHeap q.source (sObjects q)) (sIndex q)=.ok (emptyArray (Arc4Locals.base q.source).arrayPrototype) := by
  have bound := receiver_bound q
  have different : q.receiver≠(iObjects q).size := by simpa only [(sizes q).2.1] using Nat.ne_of_lt bound
  simp only [checkedObject,Heap.object?,objectHeap,sObjects,allocatedObjects,sIndex,
    Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different,↓reduceIte,
    Array.getElem?_push_size]

theorem prototype_bound (q : Setup) (id : ObjectId) (object : JSObject)
    (found : checkedObject (objectHeap q.source q.objects) id=.ok object) : id<q.objects.size :=
  (Array.getElem?_eq_some_iff.mp (checked_present found)).1

def emptyFrame (q : Setup)
    (matching : (Arc4Locals.base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId) :
    DenseArrayState.Frame (Arc4Locals.heap q.source (sObjects q) q.argument (finalValues q)) (sIndex q) := {
  object := emptyArray (Arc4Locals.base q.source).arrayPrototype
  length := 0, values := fun _ => .undefined
  shape := empty_shape _
  present := by simpa only [checkedObject,Heap.object?,objectHeap,Arc4Locals.heap] using empty_present q
  prototype := (retainedKey q).prototype.transport (matching.trans q.keyFrame.prototype.parent.symm)
    (by simpa only [checkedObject,Heap.object?,objectHeap,Arc4Locals.heap] using (retainedKey q).prototype.arrayRead)
    (by simpa only [checkedObject,Heap.object?,objectHeap,Arc4Locals.heap] using (retainedKey q).prototype.rootRead)
  room := by have := (retainedKey q).room; exact this
  bound := by
    change sIndex q<(sObjects q).size
    rw [(sizes q).2.2.1,(sizes q).2.2.2]
    exact Nat.lt_succ_self _
  arrayDifferent := by
    have bounded := prototype_bound q _ _ q.keyFrame.prototype.arrayRead
    change sIndex q≠q.keyFrame.prototype.arrayId
    rw [(sizes q).2.2.1]
    exact Nat.ne_of_gt bounded
  rootDifferent := by
    have bounded := prototype_bound q _ _ q.keyFrame.prototype.rootRead
    change sIndex q≠q.keyFrame.prototype.rootId
    rw [(sizes q).2.2.1]
    exact Nat.ne_of_gt bounded }

end CookieClicker.JavaScript.Arc4Initialized

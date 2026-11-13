import CookieClicker.JavaScriptEval

/-! Allocation preserves successful reads of the existing object graph.
An extension may add objects and change environments; it cannot replace an
existing object. Missing-object errors are not covered: an allocation can make
a formerly dangling reference valid. Successful reads have no such dependency.
-/
namespace CookieClicker.JavaScript.HeapExtension

structure Extends (before after : Heap) : Prop where
  size : before.objects.size ≤ after.objects.size
  read : ∀ id object, before.object? id = some object → after.object? id = some object

theorem refl (heap : Heap) : Extends heap heap := ⟨Nat.le_refl _,fun _ _ h => h⟩

theorem trans {first second third : Heap} (left : Extends first second) (right : Extends second third) :
    Extends first third := ⟨Nat.le_trans left.size right.size,fun id object h => right.read id object (left.read id object h)⟩

theorem append_object (heap : Heap) (object : JSObject) :
    Extends heap (heap.allocateObject object).2 := by
  constructor
  · simp [Heap.allocateObject]
  · intro id previous found
    have bounded : id < heap.objects.size := by
      exact Array.getElem?_eq_some_iff.mp found |>.1
    have same : (heap.objects.push object)[id]? = heap.objects[id]? := by
      simp only [Array.getElem?_push,Nat.ne_of_lt bounded,↓reduceIte]
    simpa only [Heap.allocateObject,Heap.object?,same] using found

theorem same_objects {before after : Heap} (same : before.objects = after.objects) : Extends before after := by
  constructor
  · simp [same]
  · intro id object found
    simpa [Heap.object?,←same] using found

theorem checked_object {before after : Heap} (extension : Extends before after)
    (id : ObjectId) (object : JSObject) (found : checkedObject before id = .ok object) :
    checkedObject after id = .ok object := by
  cases h : before.object? id with
  | none => simp [checkedObject,h] at found
  | some original =>
    have eq : original = object := by simpa [checkedObject,h] using found
    simp [checkedObject,extension.read id original h,eq]

theorem find_property {before after : Heap} (extension : Extends before after)
    (fuel more : Nat) (enough : fuel ≤ more) (id : ObjectId) (name : JSString)
    (value : Option PropertyDescriptor) (found : findProperty before fuel id name = .ok value) :
    findProperty after more id name = .ok value := by
  induction fuel generalizing more id value with
  | zero => simp [findProperty] at found
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      have room : fuel ≤ more := Nat.le_of_succ_le_succ enough
      cases read : before.object? id with
      | none => simp [findProperty,checkedObject,read,Except.bind,bind] at found
      | some object =>
        have later := extension.read id object read
        simp only [findProperty,checkedObject,read,later,Except.bind,bind] at found ⊢
        by_cases unknown : object.unresolvedOwnNames.contains name = true
        · simp only [unknown,↓reduceIte] at found
          cases found
        · simp only [unknown, Bool.false_eq_true, ↓reduceIte] at found ⊢
          cases own : ownProperty object name with
          | some descriptor => simpa [own,pure,Except.pure] using found
          | none =>
            simp only [own] at found ⊢
            by_cases complete : object.propertiesComplete = true
            · simp only [complete,Bool.not_true,Bool.false_eq_true,↓reduceIte] at found ⊢
              cases parent : object.prototype with
              | none => simpa [parent,Except.bind,bind] using found
              | some parentId =>
                cases inherited : findProperty before fuel parentId name with
                | error failure => simp [parent,inherited] at found
                | ok inheritedValue =>
                  have next := ih more room parentId inheritedValue inherited
                  simpa [parent,inherited,next,Except.bind,bind] using found
            · have incomplete : object.propertiesComplete = false := by cases h : object.propertiesComplete <;> simp_all
              simp [incomplete] at found

theorem lookup_property {before after : Heap} (extension : Extends before after)
    (id : ObjectId) (name : JSString) (value : Option PropertyDescriptor)
    (found : lookupProperty before id name = .ok value) :
    lookupProperty after id name = .ok value :=
  find_property extension _ _ (Nat.add_le_add_right extension.size 1) id name value found

theorem allocated_lookup (heap : Heap) (object : JSObject) (id : ObjectId)
    (name : JSString) (value : Option PropertyDescriptor)
    (found : lookupProperty heap id name = .ok value) :
    lookupProperty (heap.allocateObject object).2 id name = .ok value :=
  lookup_property (append_object heap object) id name value found

end CookieClicker.JavaScript.HeapExtension

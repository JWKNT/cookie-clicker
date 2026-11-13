import CookieClicker.JavaScriptHeapExtension

/-! Finite source-heap paths ending in an actual data descriptor.
Every intermediate native prototype and own-property check is retained. -/
namespace CookieClicker.JavaScript.DataPropertyPath
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

inductive Path (heap : Heap) (name : JSString) (value : Value) : ObjectId → Nat → Prop where
  | own (id : ObjectId) (object : JSObject) (writable enumerable configurable : Bool)
      (read : checkedObject heap id = .ok object)
      (inspected : object.unresolvedOwnNames.contains name = false)
      (data : ownProperty object name = some (.data value writable enumerable configurable)) : Path heap name value id 0
  | parent (id next depth : Nat) (object : JSObject)
      (read : checkedObject heap id = .ok object)
      (inspected : object.unresolvedOwnNames.contains name = false)
      (absent : ownProperty object name = none)
      (complete : object.propertiesComplete = true)
      (link : object.prototype = some next)
      (rest : Path heap name value next depth) : Path heap name value id (depth+1)

theorem found {heap : Heap} {name : JSString} {value : Value} {id depth : Nat}
    (path : Path heap name value id depth) (fuel : Nat) :
    ∃ writable enumerable configurable,
      findProperty heap (depth+fuel+1) id name = .ok (some (.data value writable enumerable configurable)) := by
  induction path with
  | own id object writable enumerable configurable read inspected data =>
    exact ⟨writable,enumerable,configurable,by simp only [findProperty,read,inspected,data,Bool.false_eq_true,↓reduceIte,Except.bind,bind,Except.pure,pure]⟩
  | parent id next depth object read inspected absent complete link rest ih =>
    obtain ⟨writable,enumerable,configurable,found⟩ := ih
    refine ⟨writable,enumerable,configurable,?_⟩
    rw [show depth+1+fuel+1=(depth+fuel+1)+1 by omega]
    rw [findProperty]
    simp only [read,inspected,absent,complete,link,found,Bool.false_eq_true,Bool.not_true,↓reduceIte,Except.bind,bind,Except.pure,pure]

theorem lookup {heap : Heap} {name : JSString} {value : Value} {id depth : Nat}
    (path : Path heap name value id depth) (enough : depth ≤ heap.objects.size) :
    ∃ writable enumerable configurable,
      lookupProperty heap id name = .ok (some (.data value writable enumerable configurable)) := by
  unfold lookupProperty
  rw [show heap.objects.size+1=depth+(heap.objects.size-depth)+1 by omega]
  exact found path _

theorem extend {before after : Heap} (extension : HeapExtension.Extends before after)
    {name : JSString} {value : Value} {id depth : Nat} (path : Path before name value id depth) :
    Path after name value id depth := by
  induction path with
  | own id object writable enumerable configurable read inspected data =>
    exact .own id object writable enumerable configurable (HeapExtension.checked_object extension id object read) inspected data
  | parent id next depth object read inspected absent complete link rest ih =>
    exact .parent id next depth object (HeapExtension.checked_object extension id object read) inspected absent complete link ih

theorem native_read (machine : Machine) (id : ObjectId) (object : JSObject) (name : JSString) (value : Value)
    (depth : Nat) (path : Path machine.heap name value id depth) (enough : depth ≤ machine.heap.objects.size)
    (read : checkedObject machine.heap id = .ok object)
    (notArguments : ∀ mappings, object.kind ≠ .arguments mappings) :
    readProperty machine (.object id) name = result machine value := by
  obtain ⟨writable,enumerable,configurable,found⟩ := lookup path enough
  simp only [readProperty,toObject,checked,readObjectProperty,read,found]

end CookieClicker.JavaScript.DataPropertyPath

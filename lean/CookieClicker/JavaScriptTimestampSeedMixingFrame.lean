import CookieClicker.JavaScriptTimestampMixkeyComplete
import CookieClicker.JavaScriptTimestampSeedSetup

/-! Allocation and lexical-scope preservation from native seedrandom setup
through the tagged flatten helper, before the actual mixing invocation. -/
namespace CookieClicker.JavaScript.TimestampSeedMixingFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampSeedSetup

def key (i : Inputs) := (initialObjects i).size

theorem key_fresh (i : Inputs) : (base i).heap.objects.size < key i := by
  simp [key,initialObjects]

theorem environment_size (i : Inputs) : (atMixkey i).heap.environments.size = (base i).heap.environments.size+2 := by
  simp [atMixkey,afterFlattenView,retainedHeap,afterFlatten,TimestampSeedFlatten.returned,
    TimestampSeedFlatten.bodyHeap,atFlatten,sourceHeap]

theorem original_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (base i).heap id = .ok environment) :
    checkedEnvironment (atMixkey i).heap id = .ok environment := by
  have first := EnvironmentAppend.checked_old (base i).heap
    ((initialObjects i).push (TimestampSeedFlatten.emptyArray (base i)))
    ⟨.declarative (localBindings i (.object (initialObjects i).size)),some (scope i)⟩ environment id read
  have next := EnvironmentAppend.checked_old (atFlatten i).heap
    (TimestampSeedFlatten.resultObjects (atFlatten i) (seed i) (flatten i))
    ⟨.declarative (TimestampSeedFlatten.scopeLocals (atFlatten i) (seed i)
        (.object (TimestampSeedFlatten.objectsWithArgument (atFlatten i) (seed i) (flatten i)).size)
        (.string (JSString.ofString "s"))),some (scope i)⟩ environment id first
  exact next

theorem original_binding (i : Inputs) (id : EnvId) (name : String) (value : Value)
    (environment : LexicalEnvironment)
    (read : checkedEnvironment (base i).heap id = .ok environment)
    (binding : readBinding (base i).heap id name = .ok value) :
    readBinding (atMixkey i).heap id name = .ok value := by
  unfold readBinding at binding ⊢
  rw [read] at binding
  rw [original_environment i id environment read]
  exact binding

theorem original_path (i : Inputs) (name : String) (first last depth : Nat)
    (path : HasEnvironment.DeclarativePath (base i).heap.environments name first last depth) :
    HasEnvironment.DeclarativePath (atMixkey i).heap.environments name first last depth := by
  apply HasEnvironment.append_path
  exact HasEnvironment.append_path _ _ _ _ _ _ path

theorem key_present (i : Inputs) :
    checkedObject (atMixkey i).heap (key i) = .ok (TimestampSeedFlatten.emptyArray (base i)) := by
  have bound : key i < (atFlatten i).heap.objects.size := by simp [key,atFlatten,sourceHeap]
  have old := TimestampSeedFlatten.returned_original_object (atFlatten i) (scope i) (seed i) (flatten i) (key i) bound
  change checkedObject (TimestampSeedFlatten.returned (atFlatten i) (scope i) (seed i) (flatten i)).heap _ = _
  unfold checkedObject Heap.object?
  rw [old]
  simp [key,atFlatten,sourceHeap]

theorem empty_shape (base : Machine) :
    MixkeyArray.Shape (TimestampSeedFlatten.emptyArray base) 0 (fun _ => 0) := by
  constructor <;> try rfl
  · decide
  · intro index small
    have distinct := MixkeyArray.length_not_key index small
    simp [TimestampSeedFlatten.emptyArray,ownProperty,distinct]

theorem safe_fresh_path {heap : Heap} {name : JSString} {value : Value} {id depth : Nat}
    (path : DataPropertyPath.Path heap name value id depth) (fresh : Nat) (bound : heap.objects.size ≤ fresh) :
    MixkeyRetention.SafePath fresh heap name value id depth := by
  induction path with
  | own id object w e c read inspected data =>
    have less : id < heap.objects.size := by
      unfold checkedObject Heap.object? at read
      cases found : heap.objects[id]? with
      | none => simp [found] at read
      | some object => exact Array.getElem?_eq_some_iff.mp found |>.1
    exact .own id object w e c (Nat.ne_of_gt (Nat.lt_of_lt_of_le less bound)) read inspected data
  | parent id next depth object read inspected absent complete link rest ih =>
    have less : id < heap.objects.size := by
      unfold checkedObject Heap.object? at read
      cases found : heap.objects[id]? with
      | none => simp [found] at read
      | some object => exact Array.getElem?_eq_some_iff.mp found |>.1
    exact .parent id next depth object (Nat.ne_of_gt (Nat.lt_of_lt_of_le less bound)) read inspected absent complete link ih

theorem safe_extend {key : ObjectId} {before after : Heap} (extension : HeapExtension.Extends before after)
    {name : JSString} {value : Value} {id depth : Nat}
    (path : MixkeyRetention.SafePath key before name value id depth) :
    MixkeyRetention.SafePath key after name value id depth := by
  induction path with
  | own id object w e c different read inspected data =>
    exact .own id object w e c different (HeapExtension.checked_object extension id object read) inspected data
  | parent id next depth object different read inspected absent complete link rest ih =>
    exact .parent id next depth object different (HeapExtension.checked_object extension id object read) inspected absent complete link ih

theorem key_different (i : Inputs) (id : ObjectId) (object : JSObject)
    (read : checkedObject (base i).heap id = .ok object) : key i ≠ id := by
  have less : id < (base i).heap.objects.size := by
    unfold checkedObject Heap.object? at read
    cases found : (base i).heap.objects[id]? with
    | none => simp [found] at read
    | some object => exact Array.getElem?_eq_some_iff.mp found |>.1
  exact Nat.ne_of_gt (Nat.lt_trans less (key_fresh i))

end CookieClicker.JavaScript.TimestampSeedMixingFrame

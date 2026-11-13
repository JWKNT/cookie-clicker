import CookieClicker.JavaScriptArrayIndexBound

/-! Native last-slot deletion and shrinking length for a dense valid array. -/
namespace CookieClicker.JavaScript.ArrayPopData
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open MixkeyArray (stored)

def removed (object : JSObject) (name : JSString) : JSObject :=
  {object with properties := object.properties.filter (fun p => p.name != name)}

theorem stored_removed_same (properties : List OwnProperty) (name : JSString) :
    stored (properties.filter (fun p => p.name != name)) name = none := by
  induction properties with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first.name = name <;> simp [stored,List.filter_cons,same,ih,stored] at *

theorem stored_removed_other (properties : List OwnProperty) (name other : JSString) (different : name≠other) :
    stored (properties.filter (fun p => p.name != name)) other = stored properties other := by
  unfold stored
  rw [List.find?_filter]
  congr 1
  apply congrArg (fun predicate => properties.find? predicate)
  funext property
  by_cases selected : property.name=other
  · simp [selected,Ne.symm different]
  · simp [selected]

theorem own_removed_same (object : JSObject) (name : JSString) (kind : object.kind = .array) :
    ownProperty (removed object name) name = none := by
  simp only [ownProperty,removed]
  rw [show (List.find? (fun p => p.name == name) (object.properties.filter (fun p => p.name != name))).map (·.descriptor) = none
    from stored_removed_same object.properties name]
  simp [kind]

theorem own_removed_other (object : JSObject) (name other : JSString) (kind : object.kind = .array) (different : name≠other) :
    ownProperty (removed object name) other = ownProperty object other := by
  simp only [ownProperty,removed]
  rw [show (List.find? (fun p => p.name == other) (object.properties.filter (fun p => p.name != name))).map (·.descriptor) =
    (List.find? (fun p => p.name == other) object.properties).map (·.descriptor) from stored_removed_other object.properties name other different]

def removedHeap (heap : Heap) (array : ObjectId) (object : JSObject) (index : Nat) : Heap :=
  {heap with objects := heap.objects.set! array (removed object (MixkeyIndex.key index))}

theorem removed_present (heap : Heap) (array : ObjectId) (object : JSObject) (index : Nat) (bound : array < heap.objects.size) :
    checkedObject (removedHeap heap array object index) array = .ok (removed object (MixkeyIndex.key index)) := by
  simp [checkedObject,Heap.object?,removedHeap,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,bound]

theorem removed_other (heap : Heap) (array : ObjectId) (object : JSObject) (index other : Nat) (different : array≠other) :
    checkedObject (removedHeap heap array object index) other = checkedObject heap other := by
  simp [checkedObject,Heap.object?,removedHeap,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different]

theorem native_delete (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (index : Nat) (small : index < 256) (inside : index < frame.length) :
    deleteReference base ⟨.property (.object array) (MixkeyIndex.key index),true⟩ =
      result {base with heap := removedHeap base.heap array frame.object index} (.boolean true) := by
  simp [deleteReference,checked,frame.present,frame.shape.kind,frame.shape.unresolved,frame.shape.complete,
    frame.shape.slots index small,inside,DenseArray.descriptor,replaceObject,Heap.writeObject,frame.bound,
    removedHeap,removed]

theorem last_bound (object : JSObject) (length : Nat) (bound : ArrayIndexBound.Holds object length)
    (positive : 0 < length) : ArrayIndexBound.Holds (removed object (MixkeyIndex.key (length-1))) (length-1) := by
  intro property member index parsed
  have membership := List.mem_filter.mp member
  have old := bound property membership.1 index parsed
  have unequal : property.name≠MixkeyIndex.key (length-1) := by simpa using membership.2
  have canonical := ArrayIndexBound.canonical parsed
  have different : index≠length-1 := by intro same; apply unequal; simpa [same] using canonical
  omega

theorem no_shrink_indices (object : JSObject) (length : Nat) (bound : ArrayIndexBound.Holds object length) :
    (object.properties.filterMap fun property => (arrayIndex property.name).filter (fun index => index≥length)) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro property member
  cases parsed : arrayIndex property.name with
  | none => rfl
  | some index =>
    have inside := bound property member index parsed
    simp [Option.filter,show ¬index≥length by omega]

def finalObject (object : JSObject) (length : Nat) :=
  setArrayLength (removed object (MixkeyIndex.key (length-1))) (length-1) true

def finalHeap (heap : Heap) (array : ObjectId) (object : JSObject) (length : Nat) : Heap :=
  {heap with objects := heap.objects.set! array (finalObject object length)}

theorem native_shrink_data (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (bound : ArrayIndexBound.Holds frame.object frame.length) (positive : 0 < frame.length) :
    writeDataProperty (removedHeap base.heap array frame.object (frame.length-1)) array
      (removed frame.object (MixkeyIndex.key (frame.length-1))) (JSString.ofString "length")
      (.number (Number.ofNat (frame.length-1))) (.data (.number (Number.ofNat (frame.length-1))) true false false) =
      .ok (finalHeap base.heap array frame.object frame.length,true) := by
  have small : frame.length-1 < 256 := by have := frame.shape.bound; omega
  have different := DenseArray.length_not_key (frame.length-1) small
  have oldSize : ownProperty (removed frame.object (MixkeyIndex.key (frame.length-1))) (JSString.ofString "length") =
      some (.data (.number (Number.ofNat frame.length)) true false false) := by
    rw [own_removed_other _ _ _ frame.shape.kind (Ne.symm different),frame.shape.size]
  have conversionOld := (MixkeyArray.native_length_table ⟨frame.length,by have := frame.shape.bound; omega⟩).1
  have equalOld := (MixkeyArray.native_length_table ⟨frame.length,by have := frame.shape.bound; omega⟩).2
  have wordOld : (UInt32.ofNat frame.length).toNat = frame.length := by
    simp [UInt32.toNat_ofNat,Nat.mod_eq_of_lt (show frame.length<4294967296 by have := frame.shape.bound; omega)]
  have conversionNew := (MixkeyArray.native_length_table ⟨frame.length-1,by omega⟩).1
  have equalNew := (MixkeyArray.native_length_table ⟨frame.length-1,by omega⟩).2
  have wordNew : (UInt32.ofNat (frame.length-1)).toNat = frame.length-1 := by
    simp [UInt32.toNat_ofNat,Nat.mod_eq_of_lt (show frame.length-1<4294967296 by omega)]
  have oldLength : arrayLength (removed frame.object (MixkeyIndex.key (frame.length-1))) = .ok (frame.length,true) := by
    simp [arrayLength,oldSize,conversionOld,equalOld,wordOld]
  have indices := no_shrink_indices _ _ (last_bound frame.object frame.length bound positive)
  have kind : (removed frame.object (MixkeyIndex.key (frame.length-1))).kind = .array := frame.shape.kind
  simp only [writeDataProperty,kind,oldLength,toNumber,conversionNew,wordNew,equalNew,
    beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,Except.bind,bind,Except.pure,pure]
  simp only [show ¬frame.length-1≥frame.length by omega,↓reduceIte,indices,List.mergeSort_nil,shrinkArray]
  simp [setArrayLength,MixkeyArray.changed_kind,removed,frame.shape.kind,replaceObject,Heap.writeObject,removedHeap,finalHeap,
    finalObject,frame.bound,Array.setIfInBounds,Array.set!_eq_setIfInBounds,Array.set_set,Except.bind,bind,Except.pure,pure]


theorem native_shrink (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (bound : ArrayIndexBound.Holds frame.object frame.length) (positive : 0 < frame.length) :
    writeProperty {base with heap := removedHeap base.heap array frame.object (frame.length-1)} (.object array)
      (JSString.ofString "length") (.number (Number.ofNat (frame.length-1))) true =
      result {base with heap := finalHeap base.heap array frame.object frame.length} (.number (Number.ofNat (frame.length-1))) := by
  have small : frame.length-1<256 := by have := frame.shape.bound; omega
  have oldSize : ownProperty (removed frame.object (MixkeyIndex.key (frame.length-1))) (JSString.ofString "length") =
      some (.data (.number (Number.ofNat frame.length)) true false false) := by
    rw [own_removed_other _ _ _ frame.shape.kind (Ne.symm (DenseArray.length_not_key (frame.length-1) small)),frame.shape.size]
  have present := removed_present base.heap array frame.object (frame.length-1) frame.bound
  have inspected : (removed frame.object (MixkeyIndex.key (frame.length-1))).unresolvedOwnNames=[] := frame.shape.unresolved
  have kind : (removed frame.object (MixkeyIndex.key (frame.length-1))).kind=.array := frame.shape.kind
  have lookup : lookupProperty (removedHeap base.heap array frame.object (frame.length-1)) array (JSString.ofString "length") =
      .ok (some (.data (.number (Number.ofNat frame.length)) true false false)) := by
    simp [lookupProperty,findProperty,present,inspected,oldSize,Except.bind,bind,Except.pure,pure]
  have write := native_shrink_data base array frame bound positive
  simp [writeProperty,checked,present,kind,lookup,requireDescriptor,oldSize,write]

theorem final_shape (object : JSObject) (length : Nat) (values : Nat → Value)
    (shape : DenseArray.Shape object length values) (positive : 0<length) :
    DenseArray.Shape (finalObject object length) (length-1) values := by
  have small : length-1<256 := by have := shape.bound; omega
  constructor
  · simp [finalObject,setArrayLength,MixkeyArray.changed_kind,removed,shape.kind]
  · simp [finalObject,setArrayLength,MixkeyArray.changed_complete,removed,shape.complete]
  · simp [finalObject,setArrayLength,MixkeyArray.changed_unresolved,removed,shape.unresolved]
  · simp [finalObject,setArrayLength,MixkeyArray.changed_extensible,removed,shape.extensible]
  · have := shape.bound; omega
  · exact MixkeyArray.own_changed_same _ _ _
  · intro index indexSmall
    rw [finalObject,setArrayLength,MixkeyArray.own_changed_other _ _ _ _ (DenseArray.length_not_key index indexSmall)]
    by_cases last : index=length-1
    · subst index
      rw [own_removed_same _ _ shape.kind]
      simp
    · have different : MixkeyIndex.key (length-1) ≠ MixkeyIndex.key index := by
        intro same
        exact last (MixkeyIndex.key_injective indexSmall small same.symm)
      rw [own_removed_other _ _ _ shape.kind different,shape.slots index indexSmall]
      have test : (index<length) ↔ index<length-1 := by omega
      simp [test]

theorem final_bound (object : JSObject) (length : Nat) (bound : ArrayIndexBound.Holds object length)
    (positive : 0<length) : ArrayIndexBound.Holds (finalObject object length) (length-1) :=
  ArrayIndexBound.length_changed (last_bound object length bound positive) _ _

theorem final_present (heap : Heap) (array : ObjectId) (object : JSObject) (length : Nat) (bound : array<heap.objects.size) :
    checkedObject (finalHeap heap array object length) array = .ok (finalObject object length) := by
  simp [checkedObject,Heap.object?,finalHeap,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,bound]

theorem final_other (heap : Heap) (array : ObjectId) (object : JSObject) (length other : Nat) (different : array≠other) :
    checkedObject (finalHeap heap array object length) other = checkedObject heap other := by
  simp [checkedObject,Heap.object?,finalHeap,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different]

def finalFrame {heap : Heap} {array : ObjectId} (frame : DenseArrayState.Frame heap array) (positive : 0<frame.length) :
    DenseArrayState.Frame (finalHeap heap array frame.object frame.length) array := {
  object := finalObject frame.object frame.length, length := frame.length-1, values := frame.values
  shape := final_shape _ _ _ frame.shape positive
  present := final_present _ _ _ _ frame.bound
  prototype := frame.prototype.transport (by simp [finalObject,setArrayLength,MixkeyArray.changed_prototype,removed])
    (by rw [final_other _ _ _ _ _ frame.arrayDifferent]; exact frame.prototype.arrayRead)
    (by rw [final_other _ _ _ _ _ frame.rootDifferent]; exact frame.prototype.rootRead)
  room := by simpa [finalHeap] using frame.room
  bound := by simpa [finalHeap] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

end CookieClicker.JavaScript.ArrayPopData

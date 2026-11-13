import CookieClicker.JavaScriptMixkeyArray

/-! Native dense array data properties for the bounded notification queues.
The values may be arbitrary JavaScript values; all descriptor operations remain explicit. -/
namespace CookieClicker.JavaScript.DenseArray
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open MixkeyArray (stored changed updated updated_name stored_updated_same stored_updated_other
  stored_changed_same stored_changed_other changed_properties changed_kind changed_complete
  changed_unresolved changed_extensible changed_prototype own_changed_same own_changed_other
  native_length_table PrototypeFrame)

def descriptor (value : Value) : PropertyDescriptor := .data value true true true

def nextLength (length index : Nat) := if index ≥ length then index + 1 else length
def nextValues (values : Nat → Value) (index : Nat) (value : Value) : Nat → Value :=
  fun slot => if slot = index then value else values slot

def written (object : JSObject) (length index : Nat) (value : Value) : JSObject :=
  let changed := setOwnProperty object (MixkeyIndex.key index) (descriptor value)
  if index ≥ length then setArrayLength changed (index + 1) true else changed

structure Shape (object : JSObject) (length : Nat) (values : Nat → Value) : Prop where
  kind : object.kind = .array
  complete : object.propertiesComplete = true
  unresolved : object.unresolvedOwnNames = []
  extensible : object.extensible = true
  bound : length ≤ 256
  size : ownProperty object (JSString.ofString "length") =
    some (.data (.number (Number.ofNat length)) true false false)
  slots : ∀ index, index < 256 → ownProperty object (MixkeyIndex.key index) =
    if index < length then some (descriptor (values index)) else none

theorem length_not_key (index : Nat) (small : index < 256) :
    JSString.ofString "length" ≠ MixkeyIndex.key index := by
  intro same
  have check := MixkeyIndex.index_key index small
  rw [←same] at check
  contradiction


theorem native_length (object : JSObject) (length : Nat) (values : Nat → Value)
    (shape : Shape object length values) : arrayLength object = .ok (length,true) := by
  have bound : length < 257 := by have := shape.bound; omega
  have conversion := (native_length_table ⟨length,bound⟩).1
  have equal := (native_length_table ⟨length,bound⟩).2
  have word : (UInt32.ofNat length).toNat = length := by
    simp [UInt32.toNat_ofNat,Nat.mod_eq_of_lt (show length < 4294967296 by omega)]
  simp [arrayLength,shape.size,conversion,word,equal]

theorem written_shape (object : JSObject) (length : Nat) (values : Nat → Value)
    (shape : Shape object length values) (index : Nat) (small : index < 256)
    (adjacent : index ≤ length) (value : Value) :
    Shape (written object length index value) (nextLength length index) (nextValues values index value) := by
  have lengthBound := shape.bound
  have different := length_not_key index small
  have unchangedLength := own_changed_other object (MixkeyIndex.key index) (JSString.ofString "length")
    (descriptor value) (Ne.symm different)
  constructor
  · simp only [written,setArrayLength,changed_kind]; split <;> simp [changed_kind,shape.kind]
  · simp only [written,setArrayLength]; split <;> simp [changed_complete,shape.complete]
  · simp only [written,setArrayLength]; split <;> simp [changed_unresolved,shape.unresolved]
  · simp only [written,setArrayLength]; split <;> simp [changed_extensible,shape.extensible]
  · simp only [nextLength]; split <;> omega
  · simp only [written,nextLength,setArrayLength]
    split
    · exact own_changed_same _ _ _
    · rw [unchangedLength,shape.size]
  · intro slot smallSlot
    by_cases same : slot = index
    · subst slot
      have inside : index < nextLength length index := by unfold nextLength; split <;> omega
      simp only [inside,↓reduceIte,nextValues]
      simp only [written,setArrayLength]
      split
      · rw [own_changed_other _ _ _ _ different,own_changed_same]
      · exact own_changed_same _ _ _
    · have keysDifferent : MixkeyIndex.key index ≠ MixkeyIndex.key slot := by
        intro keys
        exact same ((MixkeyIndex.key_injective small smallSlot keys).symm)
      have oldSlot := own_changed_other object (MixkeyIndex.key index) (MixkeyIndex.key slot)
        (descriptor value) keysDifferent
      have test : (slot < nextLength length index) ↔ slot < length := by
        unfold nextLength; split <;> omega
      simp only [nextValues,same,↓reduceIte,test]
      simp only [written,setArrayLength]
      split
      · rw [own_changed_other _ _ _ _ (length_not_key slot smallSlot),oldSlot,shape.slots slot smallSlot]
      · rw [oldSlot,shape.slots slot smallSlot]

def writtenHeap (heap : Heap) (id : ObjectId) (object : JSObject)
    (length index : Nat) (value : Value) : Heap :=
  {heap with objects := heap.objects.set! id (written object length index value)}

theorem native_write_data (heap : Heap) (id : ObjectId) (object : JSObject)
    (length : Nat) (values : Nat → Value) (shape : Shape object length values)
    (index : Nat) (small : index < 256) (value : Value) (bound : id < heap.objects.size) :
    writeDataProperty heap id object (MixkeyIndex.key index) (value) (descriptor value) =
      .ok (writtenHeap heap id object length index value,true) := by
  have nameDifferent : (MixkeyIndex.key index == JSString.ofString "length") = false := by
    simp [Ne.symm (length_not_key index small)]
  simp only [writeDataProperty,shape.kind,native_length object length values shape,
    nameDifferent,Bool.false_eq_true,↓reduceIte,MixkeyIndex.index_key index small,
    Bool.not_true,Bool.and_false,Except.bind,bind,Except.pure,pure]
  have kind : (written object length index value).kind = .array := by
    simp only [written,setArrayLength]; split <;> simp [changed_kind,shape.kind]
  change (do
    let next ← replaceObject heap id (written object length index value)
    let next ← match (written object length index value).kind with
      | .arguments mappings => match mappings.find? (fun (entry : JSString × EnvId × String) => entry.1 == MixkeyIndex.key index) with
        | some (_,environment,binding) => setBinding next environment binding (value) false
        | none => pure next
      | _ => pure next
    pure (next,true)) = _
  simp [kind,replaceObject,Heap.writeObject,bound,writtenHeap,Except.bind,bind,Except.pure,pure]

theorem written_heap_checked (heap : Heap) (id : ObjectId) (object : JSObject)
    (length index : Nat) (value : Value) (bound : id < heap.objects.size) :
    checkedObject (writtenHeap heap id object length index value) id =
      .ok (written object length index value) := by
  simp [checkedObject,Heap.object?,writtenHeap,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,bound]

theorem written_heap_other (heap : Heap) (id other : ObjectId) (object : JSObject)
    (length index : Nat) (value : Value) (different : id ≠ other) :
    checkedObject (writtenHeap heap id object length index value) other = checkedObject heap other := by
  simp [checkedObject,Heap.object?,writtenHeap,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,different]

theorem written_prototype (object : JSObject) (length index : Nat) (value : Value) :
    (written object length index value).prototype = object.prototype := by
  simp only [written,setArrayLength]; split <;> simp [changed_prototype]


theorem find_slot (heap : Heap) (id : ObjectId) (object : JSObject)
    (length : Nat) (values : Nat → Value) (shape : Shape object length values)
    (present : checkedObject heap id = .ok object) (prototype : PrototypeFrame heap object)
    (index : Nat) (small : index < 256) (fuel : Nat) :
    findProperty heap (fuel+3) id (MixkeyIndex.key index) =
      .ok (if index < length then some (descriptor (values index)) else none) := by
  by_cases occupied : index < length
  · simp [show fuel+3=(fuel+2)+1 by omega,findProperty,present,shape.unresolved,
      shape.slots index small,occupied,Except.bind,bind,Except.pure,pure]
  · simp [show fuel+3=(fuel+2)+1 by omega,findProperty,present,shape.unresolved,
      shape.slots index small,occupied,shape.complete,prototype.parent,
      prototype.arrayRead,prototype.arrayUnresolved,prototype.arraySlots index small,
      prototype.arrayComplete,prototype.arrayParent,prototype.rootRead,prototype.rootUnresolved,
      prototype.rootSlots index small,prototype.rootComplete,prototype.rootParent,
      prototype.rootKind,prototype.arrayKind,shape.kind,Except.bind,bind,Except.pure,pure]

theorem lookup_slot (heap : Heap) (id : ObjectId) (object : JSObject)
    (length : Nat) (values : Nat → Value) (shape : Shape object length values)
    (present : checkedObject heap id = .ok object) (prototype : PrototypeFrame heap object)
    (index : Nat) (small : index < 256) (room : 2 ≤ heap.objects.size) :
    lookupProperty heap id (MixkeyIndex.key index) =
      .ok (if index < length then some (descriptor (values index)) else none) := by
  unfold lookupProperty
  rw [show heap.objects.size+1=(heap.objects.size-2)+3 by omega]
  exact find_slot heap id object length values shape present prototype index small _

def readValue (length : Nat) (values : Nat → Value) (index : Nat) : Value :=
  if index < length then (values index) else .undefined

theorem native_read (machine : Machine) (id : ObjectId) (object : JSObject)
    (length : Nat) (values : Nat → Value) (shape : Shape object length values)
    (present : checkedObject machine.heap id = .ok object) (prototype : PrototypeFrame machine.heap object)
    (index : Nat) (small : index < 256) (room : 2 ≤ machine.heap.objects.size) :
    readProperty machine (.object id) (MixkeyIndex.key index) =
      result machine (readValue length values index) := by
  by_cases occupied : index < length <;>
    simp [readProperty,toObject,checked,readObjectProperty,present,shape.kind,
      lookup_slot machine.heap id object length values shape present prototype index small room,
      occupied,readValue,descriptor,Except.bind,bind,Except.pure,pure]

theorem native_write (machine : Machine) (id : ObjectId) (object : JSObject)
    (length : Nat) (values : Nat → Value) (shape : Shape object length values)
    (present : checkedObject machine.heap id = .ok object) (prototype : PrototypeFrame machine.heap object)
    (index : Nat) (small : index < 256) (value : Value) (room : 2 ≤ machine.heap.objects.size)
    (bound : id < machine.heap.objects.size) (strict : Bool) :
    writeProperty machine (.object id) (MixkeyIndex.key index) (value) strict =
      result {machine with heap := writtenHeap machine.heap id object length index value} (value) := by
  have write := native_write_data machine.heap id object length values shape index small value bound
  dsimp [descriptor] at write
  by_cases occupied : index < length <;>
    simp [writeProperty,checked,present,shape.kind,
      lookup_slot machine.heap id object length values shape present prototype index small room,
      requireDescriptor,shape.slots index small,occupied,descriptor,shape.extensible,
      write]


def prototypeAfterWrite {heap : Heap} {object : JSObject}
    (frame : PrototypeFrame heap object) (id length index : Nat) (value : Value)
    (arrayDifferent : id ≠ frame.arrayId) (rootDifferent : id ≠ frame.rootId) :
    PrototypeFrame (writtenHeap heap id object length index value) (written object length index value) :=
  frame.transport (written_prototype object length index value)
    (by rw [written_heap_other _ _ _ _ _ _ _ arrayDifferent]; exact frame.arrayRead)
    (by rw [written_heap_other _ _ _ _ _ _ _ rootDifferent]; exact frame.rootRead)

end CookieClicker.JavaScript.DenseArray

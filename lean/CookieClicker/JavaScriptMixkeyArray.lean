import CookieClicker.JavaScriptMixkeyIndex

/-! Native descriptor-preserving writes to the seed helper's256-slot array.
The retained object may have unrelated own properties and prototype links. -/
namespace CookieClicker.JavaScript.MixkeyArray
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def stored (properties : List OwnProperty) (name : JSString) :=
  (properties.find? (fun p => p.name == name)).map (·.descriptor)
def changed (properties : List OwnProperty) (name : JSString) (descriptor : PropertyDescriptor) :=
  if properties.any (fun p => p.name == name) then
    properties.map fun p => if p.name == name then {p with descriptor} else p
  else properties ++ [⟨name,descriptor⟩]

def updated (name : JSString) (descriptor : PropertyDescriptor) (p : OwnProperty) : OwnProperty :=
  if p.name == name then {p with descriptor} else p

theorem updated_name (name : JSString) (descriptor : PropertyDescriptor) (p : OwnProperty) :
    (updated name descriptor p).name = p.name := by
  simp only [updated]; split <;> rfl

theorem stored_updated_same (properties : List OwnProperty) (name : JSString) (descriptor : PropertyDescriptor) :
    stored (properties.map (updated name descriptor)) name =
      (stored properties name).map (fun _ => descriptor) := by
  simp only [stored,List.find?_map,Function.comp_def,updated_name]
  cases found : properties.find? (fun p => p.name == name) with
  | none => rfl
  | some p =>
    have same := List.find?_some found
    simp [updated,same]

theorem stored_updated_other (properties : List OwnProperty) (name other : JSString)
    (descriptor : PropertyDescriptor) (different : name ≠ other) :
    stored (properties.map (updated name descriptor)) other = stored properties other := by
  simp only [stored,List.find?_map,Function.comp_def,updated_name]
  cases found : properties.find? (fun p => p.name == other) with
  | none => rfl
  | some p =>
    have same : p.name = other := by simpa using List.find?_some found
    simp [updated,same,Ne.symm different]

theorem stored_changed_same (properties : List OwnProperty) (name : JSString) (descriptor : PropertyDescriptor) :
    stored (changed properties name descriptor) name = some descriptor := by
  unfold changed
  split
  next present =>
    change stored (properties.map (updated name descriptor)) name = _
    rw [stored_updated_same]
    cases found : properties.find? (fun p => p.name == name) with
    | none =>
      have absent := List.find?_eq_none.mp found
      simp only [List.any_eq_true] at present
      obtain ⟨p,member,yes⟩ := present
      exact False.elim (absent p member yes)
    | some p => simp [stored,found]
  next absent =>
    have found : properties.find? (fun p => p.name == name) = none := by
      apply List.find?_eq_none.mpr
      intro p member yes
      exact absent (List.any_eq_true.mpr ⟨p,member,yes⟩)
    simp [stored,List.find?_append,found]

theorem stored_changed_other (properties : List OwnProperty) (name other : JSString)
    (descriptor : PropertyDescriptor) (different : name ≠ other) :
    stored (changed properties name descriptor) other = stored properties other := by
  unfold changed
  split
  · exact stored_updated_other properties name other descriptor different
  · simp only [stored,List.find?_append,List.find?_singleton,beq_iff_eq,different,↓reduceIte,Option.or_none]

theorem changed_properties (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object name descriptor).properties = changed object.properties name descriptor := by
  simp only [setOwnProperty,changed]; split <;> rfl

theorem changed_kind (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object name descriptor).kind = object.kind := by
  simp only [setOwnProperty]; split <;> rfl

theorem changed_complete (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object name descriptor).propertiesComplete = object.propertiesComplete := by
  simp only [setOwnProperty]; split <;> rfl

theorem changed_unresolved (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object name descriptor).unresolvedOwnNames = object.unresolvedOwnNames := by
  simp only [setOwnProperty]; split <;> rfl

theorem changed_extensible (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object name descriptor).extensible = object.extensible := by
  simp only [setOwnProperty]; split <;> rfl

theorem changed_prototype (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object name descriptor).prototype = object.prototype := by
  simp only [setOwnProperty]; split <;> rfl

theorem own_changed_same (object : JSObject) (name : JSString) (descriptor : PropertyDescriptor) :
    ownProperty (setOwnProperty object name descriptor) name = some descriptor := by
  unfold ownProperty
  rw [changed_properties,show (List.find? (fun p => p.name == name) (changed object.properties name descriptor)).map (·.descriptor) =
    some descriptor from stored_changed_same object.properties name descriptor]

theorem own_changed_other (object : JSObject) (name other : JSString)
    (descriptor : PropertyDescriptor) (different : name ≠ other) :
    ownProperty (setOwnProperty object name descriptor) other = ownProperty object other := by
  unfold ownProperty
  rw [changed_properties,changed_kind,show (List.find? (fun p => p.name == other) (changed object.properties name descriptor)).map (·.descriptor) =
    (List.find? (fun p => p.name == other) object.properties).map (·.descriptor) from
      stored_changed_other object.properties name other descriptor different]

def byteValue (byte : UInt8) : Value := .number (Number.ofNat byte.toNat)
def byteDescriptor (byte : UInt8) : PropertyDescriptor := .data (byteValue byte) true true true

def nextLength (length index : Nat) := if index ≥ length then index + 1 else length
def nextBytes (bytes : Nat → UInt8) (index : Nat) (byte : UInt8) : Nat → UInt8 :=
  fun slot => if slot = index then byte else bytes slot

def written (object : JSObject) (length index : Nat) (byte : UInt8) : JSObject :=
  let changed := setOwnProperty object (MixkeyIndex.key index) (byteDescriptor byte)
  if index ≥ length then setArrayLength changed (index + 1) true else changed

structure Shape (object : JSObject) (length : Nat) (bytes : Nat → UInt8) : Prop where
  kind : object.kind = .array
  complete : object.propertiesComplete = true
  unresolved : object.unresolvedOwnNames = []
  extensible : object.extensible = true
  bound : length ≤ 256
  size : ownProperty object (JSString.ofString "length") =
    some (.data (.number (Number.ofNat length)) true false false)
  slots : ∀ index, index < 256 → ownProperty object (MixkeyIndex.key index) =
    if index < length then some (byteDescriptor (bytes index)) else none

theorem length_not_key (index : Nat) (small : index < 256) :
    JSString.ofString "length" ≠ MixkeyIndex.key index := by
  intro same
  have check := MixkeyIndex.index_key index small
  rw [←same] at check
  contradiction

theorem native_length_table : ∀ length : Fin 257,
    Number.toUInt32 (Number.ofNat length.val) = UInt32.ofNat length.val ∧
    Number.equal (Number.ofNat length.val) (Number.ofNat length.val) = true := by
  decide +kernel

theorem native_length (object : JSObject) (length : Nat) (bytes : Nat → UInt8)
    (shape : Shape object length bytes) : arrayLength object = .ok (length,true) := by
  have bound : length < 257 := by have := shape.bound; omega
  have conversion := (native_length_table ⟨length,bound⟩).1
  have equal := (native_length_table ⟨length,bound⟩).2
  have word : (UInt32.ofNat length).toNat = length := by
    simp [UInt32.toNat_ofNat,Nat.mod_eq_of_lt (show length < 4294967296 by omega)]
  simp [arrayLength,shape.size,conversion,word,equal]

theorem written_shape (object : JSObject) (length : Nat) (bytes : Nat → UInt8)
    (shape : Shape object length bytes) (index : Nat) (small : index < 256)
    (adjacent : index ≤ length) (byte : UInt8) :
    Shape (written object length index byte) (nextLength length index) (nextBytes bytes index byte) := by
  have lengthBound := shape.bound
  have different := length_not_key index small
  have unchangedLength := own_changed_other object (MixkeyIndex.key index) (JSString.ofString "length")
    (byteDescriptor byte) (Ne.symm different)
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
      simp only [inside,↓reduceIte,nextBytes]
      simp only [written,setArrayLength]
      split
      · rw [own_changed_other _ _ _ _ different,own_changed_same]
      · exact own_changed_same _ _ _
    · have keysDifferent : MixkeyIndex.key index ≠ MixkeyIndex.key slot := by
        intro keys
        exact same ((MixkeyIndex.key_injective small smallSlot keys).symm)
      have oldSlot := own_changed_other object (MixkeyIndex.key index) (MixkeyIndex.key slot)
        (byteDescriptor byte) keysDifferent
      have test : (slot < nextLength length index) ↔ slot < length := by
        unfold nextLength; split <;> omega
      simp only [nextBytes,same,↓reduceIte,test]
      simp only [written,setArrayLength]
      split
      · rw [own_changed_other _ _ _ _ (length_not_key slot smallSlot),oldSlot,shape.slots slot smallSlot]
      · rw [oldSlot,shape.slots slot smallSlot]

def writtenHeap (heap : Heap) (id : ObjectId) (object : JSObject)
    (length index : Nat) (byte : UInt8) : Heap :=
  {heap with objects := heap.objects.set! id (written object length index byte)}

theorem native_write_data (heap : Heap) (id : ObjectId) (object : JSObject)
    (length : Nat) (bytes : Nat → UInt8) (shape : Shape object length bytes)
    (index : Nat) (small : index < 256) (byte : UInt8) (bound : id < heap.objects.size) :
    writeDataProperty heap id object (MixkeyIndex.key index) (byteValue byte) (byteDescriptor byte) =
      .ok (writtenHeap heap id object length index byte,true) := by
  have nameDifferent : (MixkeyIndex.key index == JSString.ofString "length") = false := by
    simp [Ne.symm (length_not_key index small)]
  simp only [writeDataProperty,shape.kind,native_length object length bytes shape,
    nameDifferent,Bool.false_eq_true,↓reduceIte,MixkeyIndex.index_key index small,
    Bool.not_true,Bool.and_false,Except.bind,bind,Except.pure,pure]
  have kind : (written object length index byte).kind = .array := by
    simp only [written,setArrayLength]; split <;> simp [changed_kind,shape.kind]
  change (do
    let next ← replaceObject heap id (written object length index byte)
    let next ← match (written object length index byte).kind with
      | .arguments mappings => match mappings.find? (fun (entry : JSString × EnvId × String) => entry.1 == MixkeyIndex.key index) with
        | some (_,environment,binding) => setBinding next environment binding (byteValue byte) false
        | none => pure next
      | _ => pure next
    pure (next,true)) = _
  simp [kind,replaceObject,Heap.writeObject,bound,writtenHeap,Except.bind,bind,Except.pure,pure]

theorem written_heap_checked (heap : Heap) (id : ObjectId) (object : JSObject)
    (length index : Nat) (byte : UInt8) (bound : id < heap.objects.size) :
    checkedObject (writtenHeap heap id object length index byte) id =
      .ok (written object length index byte) := by
  simp [checkedObject,Heap.object?,writtenHeap,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,bound]

theorem written_heap_other (heap : Heap) (id other : ObjectId) (object : JSObject)
    (length index : Nat) (byte : UInt8) (different : id ≠ other) :
    checkedObject (writtenHeap heap id object length index byte) other = checkedObject heap other := by
  simp [checkedObject,Heap.object?,writtenHeap,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,different]

theorem written_prototype (object : JSObject) (length index : Nat) (byte : UInt8) :
    (written object length index byte).prototype = object.prototype := by
  simp only [written,setArrayLength]; split <;> simp [changed_prototype]

structure PrototypeFrame (heap : Heap) (object : JSObject) where
  arrayId : ObjectId
  rootId : ObjectId
  arrayObject : JSObject
  rootObject : JSObject
  parent : object.prototype = some arrayId
  arrayRead : checkedObject heap arrayId = .ok arrayObject
  rootRead : checkedObject heap rootId = .ok rootObject
  arrayKind : arrayObject.kind = .array
  rootKind : rootObject.kind = .ordinary
  arrayParent : arrayObject.prototype = some rootId
  rootParent : rootObject.prototype = none
  arrayComplete : arrayObject.propertiesComplete = true
  rootComplete : rootObject.propertiesComplete = true
  arrayUnresolved : arrayObject.unresolvedOwnNames = []
  rootUnresolved : rootObject.unresolvedOwnNames = []
  arraySlots : ∀ index, index < 256 → ownProperty arrayObject (MixkeyIndex.key index) = none
  rootSlots : ∀ index, index < 256 → ownProperty rootObject (MixkeyIndex.key index) = none

theorem find_slot (heap : Heap) (id : ObjectId) (object : JSObject)
    (length : Nat) (bytes : Nat → UInt8) (shape : Shape object length bytes)
    (present : checkedObject heap id = .ok object) (prototype : PrototypeFrame heap object)
    (index : Nat) (small : index < 256) (fuel : Nat) :
    findProperty heap (fuel+3) id (MixkeyIndex.key index) =
      .ok (if index < length then some (byteDescriptor (bytes index)) else none) := by
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
    (length : Nat) (bytes : Nat → UInt8) (shape : Shape object length bytes)
    (present : checkedObject heap id = .ok object) (prototype : PrototypeFrame heap object)
    (index : Nat) (small : index < 256) (room : 2 ≤ heap.objects.size) :
    lookupProperty heap id (MixkeyIndex.key index) =
      .ok (if index < length then some (byteDescriptor (bytes index)) else none) := by
  unfold lookupProperty
  rw [show heap.objects.size+1=(heap.objects.size-2)+3 by omega]
  exact find_slot heap id object length bytes shape present prototype index small _

def readByte (length : Nat) (bytes : Nat → UInt8) (index : Nat) : Value :=
  if index < length then byteValue (bytes index) else .undefined

theorem native_read (machine : Machine) (id : ObjectId) (object : JSObject)
    (length : Nat) (bytes : Nat → UInt8) (shape : Shape object length bytes)
    (present : checkedObject machine.heap id = .ok object) (prototype : PrototypeFrame machine.heap object)
    (index : Nat) (small : index < 256) (room : 2 ≤ machine.heap.objects.size) :
    readProperty machine (.object id) (MixkeyIndex.key index) =
      result machine (readByte length bytes index) := by
  by_cases occupied : index < length <;>
    simp [readProperty,toObject,checked,readObjectProperty,present,shape.kind,
      lookup_slot machine.heap id object length bytes shape present prototype index small room,
      occupied,readByte,byteDescriptor,Except.bind,bind,Except.pure,pure]

theorem native_write (machine : Machine) (id : ObjectId) (object : JSObject)
    (length : Nat) (bytes : Nat → UInt8) (shape : Shape object length bytes)
    (present : checkedObject machine.heap id = .ok object) (prototype : PrototypeFrame machine.heap object)
    (index : Nat) (small : index < 256) (byte : UInt8) (room : 2 ≤ machine.heap.objects.size)
    (bound : id < machine.heap.objects.size) (strict : Bool) :
    writeProperty machine (.object id) (MixkeyIndex.key index) (byteValue byte) strict =
      result {machine with heap := writtenHeap machine.heap id object length index byte} (byteValue byte) := by
  have write := native_write_data machine.heap id object length bytes shape index small byte bound
  dsimp [byteDescriptor] at write
  by_cases occupied : index < length <;>
    simp [writeProperty,checked,present,shape.kind,
      lookup_slot machine.heap id object length bytes shape present prototype index small room,
      requireDescriptor,shape.slots index small,occupied,byteDescriptor,shape.extensible,
      write]

def PrototypeFrame.transport {heap later : Heap} {object after : JSObject}
    (frame : PrototypeFrame heap object) (parent : after.prototype = object.prototype)
    (arrayRead : checkedObject later frame.arrayId = .ok frame.arrayObject)
    (rootRead : checkedObject later frame.rootId = .ok frame.rootObject) :
    PrototypeFrame later after := {
  arrayId := frame.arrayId, rootId := frame.rootId
  arrayObject := frame.arrayObject, rootObject := frame.rootObject
  parent := parent.trans frame.parent
  arrayRead := arrayRead, rootRead := rootRead
  arrayKind := frame.arrayKind, rootKind := frame.rootKind
  arrayParent := frame.arrayParent, rootParent := frame.rootParent
  arrayComplete := frame.arrayComplete, rootComplete := frame.rootComplete
  arrayUnresolved := frame.arrayUnresolved, rootUnresolved := frame.rootUnresolved
  arraySlots := frame.arraySlots, rootSlots := frame.rootSlots }

def PrototypeFrame.afterWrite {heap : Heap} {object : JSObject}
    (frame : PrototypeFrame heap object) (id length index : Nat) (byte : UInt8)
    (arrayDifferent : id ≠ frame.arrayId) (rootDifferent : id ≠ frame.rootId) :
    PrototypeFrame (writtenHeap heap id object length index byte) (written object length index byte) :=
  frame.transport (written_prototype object length index byte)
    (by rw [written_heap_other _ _ _ _ _ _ _ arrayDifferent]; exact frame.arrayRead)
    (by rw [written_heap_other _ _ _ _ _ _ _ rootDifferent]; exact frame.rootRead)

def maskedByte (bits : UInt64) : UInt8 := UInt8.ofNat ((Number.toUInt32 bits).toNat%256)

theorem masked_value (bits : UInt64) :
    .number (Number.bitAnd (Number.ofNat 255) bits) = byteValue (maskedByte bits) := by
  rw [IndexBits.mask_byte]
  simp [byteValue,maskedByte,UInt8.toNat_ofNat,Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0<256))]

end CookieClicker.JavaScript.MixkeyArray

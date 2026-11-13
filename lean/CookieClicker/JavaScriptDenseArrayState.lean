import CookieClicker.JavaScriptDenseArray
import CookieClicker.JavaScriptMixkeyApply

/-! Native dense queue frames retain their descriptors through each write. -/
namespace CookieClicker.JavaScript.DenseArrayState
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Frame (heap : Heap) (array : ObjectId) where
  object : JSObject
  length : Nat
  values : Nat → Value
  shape : DenseArray.Shape object length values
  present : checkedObject heap array = .ok object
  prototype : MixkeyArray.PrototypeFrame heap object
  room : 2 ≤ heap.objects.size
  bound : array < heap.objects.size
  arrayDifferent : array ≠ prototype.arrayId
  rootDifferent : array ≠ prototype.rootId

def writtenHeap {heap : Heap} {array : ObjectId} (frame : Frame heap array) (index : Nat) (value : Value) :=
  DenseArray.writtenHeap heap array frame.object frame.length index value

def write {heap : Heap} {array : ObjectId} (frame : Frame heap array) (index : Nat) (value : Value)
    (small : index < 256) (adjacent : index ≤ frame.length) : Frame (writtenHeap frame index value) array := {
  object := DenseArray.written frame.object frame.length index value
  length := DenseArray.nextLength frame.length index
  values := DenseArray.nextValues frame.values index value
  shape := DenseArray.written_shape frame.object frame.length frame.values frame.shape index small adjacent value
  present := DenseArray.written_heap_checked _ _ _ _ _ _ frame.bound
  prototype := DenseArray.prototypeAfterWrite frame.prototype array frame.length index value frame.arrayDifferent frame.rootDifferent
  room := by simpa [writtenHeap,DenseArray.writtenHeap] using frame.room
  bound := by simpa [writtenHeap,DenseArray.writtenHeap] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

theorem native_read_length (machine : Machine) (array : ObjectId) (frame : Frame machine.heap array) :
    readProperty machine (.object array) (JSString.ofString "length") = result machine (.number (Number.ofNat frame.length)) := by
  have lookup : lookupProperty machine.heap array (JSString.ofString "length") =
      .ok (some (.data (.number (Number.ofNat frame.length)) true false false)) := by
    simp [lookupProperty,findProperty,frame.present,frame.shape.unresolved,frame.shape.size,Except.bind,bind,Except.pure,pure]
  simp [readProperty,toObject,checked,readObjectProperty,frame.present,frame.shape.kind,lookup]

def lengthObject {heap : Heap} {array : ObjectId} (frame : Frame heap array) := setArrayLength frame.object frame.length true

def lengthHeap {heap : Heap} {array : ObjectId} (frame : Frame heap array) : Heap :=
  {heap with objects := heap.objects.set! array (lengthObject frame)}

theorem lengthShape {heap : Heap} {array : ObjectId} (frame : Frame heap array) :
    DenseArray.Shape (lengthObject frame) frame.length frame.values := by
  constructor
  · simp [lengthObject,setArrayLength,MixkeyArray.changed_kind,frame.shape.kind]
  · simp [lengthObject,setArrayLength,MixkeyArray.changed_complete,frame.shape.complete]
  · simp [lengthObject,setArrayLength,MixkeyArray.changed_unresolved,frame.shape.unresolved]
  · simp [lengthObject,setArrayLength,MixkeyArray.changed_extensible,frame.shape.extensible]
  · exact frame.shape.bound
  · exact MixkeyArray.own_changed_same _ _ _
  · intro index small
    rw [lengthObject,setArrayLength,MixkeyArray.own_changed_other _ _ _ _ (DenseArray.length_not_key index small)]
    exact frame.shape.slots index small

theorem native_length_write_data (machine : Machine) (array : ObjectId) (frame : Frame machine.heap array) :
    writeDataProperty machine.heap array frame.object (JSString.ofString "length") (.number (Number.ofNat frame.length))
      (.data (.number (Number.ofNat frame.length)) true false false) = .ok (lengthHeap frame,true) := by
  have bound : frame.length < 257 := by have := frame.shape.bound; omega
  have conversion := (MixkeyArray.native_length_table ⟨frame.length,bound⟩).1
  have equal := (MixkeyArray.native_length_table ⟨frame.length,bound⟩).2
  have word : (UInt32.ofNat frame.length).toNat = frame.length := by
    simp [UInt32.toNat_ofNat,Nat.mod_eq_of_lt (show frame.length < 4294967296 by omega)]
  simp [writeDataProperty,frame.shape.kind,DenseArray.native_length _ _ _ frame.shape,
    toNumber,conversion,word,equal,Except.bind,bind,Except.pure,pure,
    MixkeyArray.changed_kind,replaceObject,Heap.writeObject,frame.bound,lengthHeap,lengthObject,setArrayLength]

theorem native_length_write (machine : Machine) (array : ObjectId) (frame : Frame machine.heap array) :
    writeProperty machine (.object array) (JSString.ofString "length") (.number (Number.ofNat frame.length)) true =
      result {machine with heap := lengthHeap frame} (.number (Number.ofNat frame.length)) := by
  have lookup : lookupProperty machine.heap array (JSString.ofString "length") =
      .ok (some (.data (.number (Number.ofNat frame.length)) true false false)) := by
    simp [lookupProperty,findProperty,frame.present,frame.shape.unresolved,frame.shape.size,Except.bind,bind,Except.pure,pure]
  simp [writeProperty,checked,frame.present,frame.shape.kind,lookup,requireDescriptor,frame.shape.size,
    native_length_write_data machine array frame]


theorem length_checked {heap : Heap} {array : ObjectId} (frame : Frame heap array) :
    checkedObject (lengthHeap frame) array = .ok (lengthObject frame) := by
  simp [checkedObject,Heap.object?,lengthHeap,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,frame.bound]

theorem length_other {heap : Heap} {array : ObjectId} (frame : Frame heap array) (other : ObjectId)
    (different : array ≠ other) : checkedObject (lengthHeap frame) other = checkedObject heap other := by
  simp [checkedObject,Heap.object?,lengthHeap,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,different]

def finish {heap : Heap} {array : ObjectId} (frame : Frame heap array) : Frame (lengthHeap frame) array := {
  object := lengthObject frame, length := frame.length, values := frame.values, shape := lengthShape frame
  present := length_checked frame
  prototype := frame.prototype.transport (by simp [lengthObject,setArrayLength,MixkeyArray.changed_prototype])
    (by rw [length_other frame _ frame.arrayDifferent]; exact frame.prototype.arrayRead)
    (by rw [length_other frame _ frame.rootDifferent]; exact frame.prototype.rootRead)
  room := by simpa [lengthHeap] using frame.room
  bound := by simpa [lengthHeap] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

end CookieClicker.JavaScript.DenseArrayState

import CookieClicker.JavaScriptTimestampMixkeyIteration

/-! Preservation of the native key array and captured String intrinsics
through allocations and byte writes in the complete mixing loop. -/
namespace CookieClicker.JavaScript.TimestampMixkeyFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey TimestampMixkeyLoop TimestampMixkeyCode TimestampMixkeyFinish

def referenceHeap (i : Inputs) (objects : Array JSObject) := heap i objects .undefined 0
def referenceMachine (i : Inputs) (objects : Array JSObject) : Machine :=
  {base i with heap := referenceHeap i objects}

structure Frame (i : Inputs) (objects : Array JSObject) where
  object : JSObject
  length : Nat
  bytes : Nat → UInt8
  shape : MixkeyArray.Shape object length bytes
  present : checkedObject (referenceHeap i objects) (key i) = .ok object
  prototype : MixkeyArray.PrototypeFrame (referenceHeap i objects) object
  stringFrame : MixkeyString.PrototypeFrame (referenceMachine i objects)
  methodObject : JSObject
  methodPresent : checkedObject (referenceHeap i objects) stringFrame.method = .ok methodObject
  methodKind : methodObject.kind = .builtin MixkeyString.methodId
  arrayDifferent : key i ≠ prototype.arrayId
  rootDifferent : key i ≠ prototype.rootId
  stringDifferent : key i ≠ stringFrame.prototype
  methodDifferent : key i ≠ stringFrame.method
  room : 2 ≤ objects.size
  keyBound : key i < objects.size

theorem checked_source (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) (id : ObjectId) :
    checkedObject (heap i objects d index) id = checkedObject (referenceHeap i objects) id := rfl

def sourcePrototype (i : Inputs) (objects : Array JSObject) (frame : Frame i objects) (d : Value) (index : Nat) :
    MixkeyArray.PrototypeFrame (heap i objects d index) frame.object :=
  frame.prototype.transport rfl
    (by rw [checked_source]; exact frame.prototype.arrayRead)
    (by rw [checked_source]; exact frame.prototype.rootRead)

def sourceString (i : Inputs) (objects : Array JSObject) (frame : Frame i objects)
    (d : UInt64) (index : Nat) (previous : Option Value) :
    MixkeyString.PrototypeFrame (atMethod i objects d index previous) := {
  prototype := frame.stringFrame.prototype
  method := frame.stringFrame.method
  object := frame.stringFrame.object
  linked := frame.stringFrame.linked
  present := by change checkedObject (heap i objects (.number d) index) _ = _
                rw [checked_source]; exact frame.stringFrame.present
  inspected := frame.stringFrame.inspected
  member := frame.stringFrame.member }

def iteration (i : Inputs) (objects : Array JSObject) (frame : Frame i objects)
    (smear : Option UInt64) (index : Nat) (previous : Option Value) (bound : index < (seed i).size) :
    TimestampMixkeyIteration.Inputs := {
  source := i, objects := objects, smear := smear, index := index, previous := previous, bound := bound
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := by rw [checked_source]; exact frame.present
  prototype := sourcePrototype i objects frame (smearValue smear) index
  room := frame.room, keyBound := frame.keyBound
  stringFrame := sourceString i objects frame (nextSmear smear frame.length frame.bytes index) index previous
  methodObject := frame.methodObject
  methodPresent := by rw [checked_source]; exact frame.methodPresent
  methodKind := frame.methodKind }

theorem append_extends (i : Inputs) (objects : Array JSObject) (added : JSObject) :
    HeapExtension.Extends (referenceHeap i objects) (referenceHeap i (objects.push added)) :=
  HeapExtension.trans (HeapExtension.append_object _ added)
    (HeapExtension.same_objects (before := ((referenceHeap i objects).allocateObject added).2)
      (after := referenceHeap i (objects.push added)) rfl)

def append (i : Inputs) (objects : Array JSObject) (frame : Frame i objects) (added : JSObject) :
    Frame i (objects.push added) := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := HeapExtension.checked_object (append_extends i objects added) _ _ frame.present
  prototype := frame.prototype.transport rfl
    (HeapExtension.checked_object (append_extends i objects added) _ _ frame.prototype.arrayRead)
    (HeapExtension.checked_object (append_extends i objects added) _ _ frame.prototype.rootRead)
  stringFrame := {
    prototype := frame.stringFrame.prototype, method := frame.stringFrame.method, object := frame.stringFrame.object
    linked := frame.stringFrame.linked
    present := HeapExtension.checked_object (append_extends i objects added) _ _ frame.stringFrame.present
    inspected := frame.stringFrame.inspected, member := frame.stringFrame.member }
  methodObject := frame.methodObject
  methodPresent := HeapExtension.checked_object (append_extends i objects added) _ _ frame.methodPresent
  methodKind := frame.methodKind
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent
  stringDifferent := frame.stringDifferent, methodDifferent := frame.methodDifferent
  room := by simpa only [Array.size_push] using Nat.le_trans frame.room (Nat.le_succ _)
  keyBound := by simpa only [Array.size_push] using Nat.lt_succ_of_lt frame.keyBound }

def writeObjects (i : Inputs) (objects : Array JSObject) (frame : Frame i objects) (slot : Nat) (value : UInt8) :=
  objects.set! (key i) (MixkeyArray.written frame.object frame.length slot value)

theorem written_reference (i : Inputs) (objects : Array JSObject) (frame : Frame i objects) (slot : Nat) (value : UInt8) :
    referenceHeap i (writeObjects i objects frame slot value) =
      MixkeyArray.writtenHeap (referenceHeap i objects) (key i) frame.object frame.length slot value := rfl

def write (i : Inputs) (objects : Array JSObject) (frame : Frame i objects) (slot : Nat) (value : UInt8)
    (small : slot < 256) (adjacent : slot ≤ frame.length) :
    Frame i (writeObjects i objects frame slot value) := {
  object := MixkeyArray.written frame.object frame.length slot value
  length := MixkeyArray.nextLength frame.length slot
  bytes := MixkeyArray.nextBytes frame.bytes slot value
  shape := MixkeyArray.written_shape frame.object frame.length frame.bytes frame.shape slot small adjacent value
  present := by rw [written_reference]
                exact MixkeyArray.written_heap_checked _ _ _ _ _ _ frame.keyBound
  prototype := (frame.prototype.afterWrite (key i) frame.length slot value frame.arrayDifferent frame.rootDifferent).transport rfl
    (by rw [written_reference]; exact MixkeyArray.written_heap_other _ _ _ _ _ _ _ frame.arrayDifferent |>.trans frame.prototype.arrayRead)
    (by rw [written_reference]; exact MixkeyArray.written_heap_other _ _ _ _ _ _ _ frame.rootDifferent |>.trans frame.prototype.rootRead)
  stringFrame := {
    prototype := frame.stringFrame.prototype, method := frame.stringFrame.method, object := frame.stringFrame.object
    linked := frame.stringFrame.linked
    present := by change checkedObject (referenceHeap i (writeObjects i objects frame slot value)) _ = _
                  rw [written_reference,MixkeyArray.written_heap_other _ _ _ _ _ _ _ frame.stringDifferent]
                  exact frame.stringFrame.present
    inspected := frame.stringFrame.inspected, member := frame.stringFrame.member }
  methodObject := frame.methodObject
  methodPresent := by
    change checkedObject (referenceHeap i (writeObjects i objects frame slot value)) frame.stringFrame.method = .ok frame.methodObject
    rw [written_reference,MixkeyArray.written_heap_other _ _ _ _ _ _ _ frame.methodDifferent]
    exact frame.methodPresent
  methodKind := frame.methodKind
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent
  stringDifferent := frame.stringDifferent, methodDifferent := frame.methodDifferent
  room := by simpa [writeObjects] using frame.room
  keyBound := by simpa [writeObjects] using frame.keyBound }

end CookieClicker.JavaScript.TimestampMixkeyFrame

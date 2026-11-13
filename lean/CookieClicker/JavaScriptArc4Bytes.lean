import CookieClicker.JavaScriptArc4IdentityComplete

/-! The native byte-array frames shared by ARC4 scheduling and generation. -/
namespace CookieClicker.JavaScript.Arc4Bytes
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Frame (heap : Heap) (array : ObjectId) where
  object : JSObject
  length : Nat
  bytes : Nat → UInt8
  shape : MixkeyArray.Shape object length bytes
  present : checkedObject heap array = .ok object
  prototype : MixkeyArray.PrototypeFrame heap object
  room : 2 ≤ heap.objects.size
  bound : array < heap.objects.size
  arrayDifferent : array ≠ prototype.arrayId
  rootDifferent : array ≠ prototype.rootId

def transport {before after : Heap} {array : ObjectId} (frame : Frame before array)
    (same : after.objects = before.objects) : Frame after array := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := by simpa only [checkedObject,Heap.object?,same] using frame.present
  prototype := frame.prototype.transport rfl
    (by simpa only [checkedObject,Heap.object?,same] using frame.prototype.arrayRead)
    (by simpa only [checkedObject,Heap.object?,same] using frame.prototype.rootRead)
  room := by simpa only [same] using frame.room
  bound := by simpa only [same] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

def writtenHeap {heap : Heap} {array : ObjectId} (frame : Frame heap array) (index : Nat) (byte : UInt8) :=
  MixkeyArray.writtenHeap heap array frame.object frame.length index byte

def write {heap : Heap} {array : ObjectId} (frame : Frame heap array) (index : Nat) (byte : UInt8)
    (small : index<256) (adjacent : index≤frame.length) : Frame (writtenHeap frame index byte) array := {
  object := MixkeyArray.written frame.object frame.length index byte
  length := MixkeyArray.nextLength frame.length index
  bytes := MixkeyArray.nextBytes frame.bytes index byte
  shape := MixkeyArray.written_shape frame.object frame.length frame.bytes frame.shape index small adjacent byte
  present := MixkeyArray.written_heap_checked _ _ _ _ _ _ frame.bound
  prototype := frame.prototype.transport (MixkeyArray.written_prototype _ _ _ _)
    (by rw [writtenHeap,MixkeyArray.written_heap_other _ _ _ _ _ _ _ frame.arrayDifferent]; exact frame.prototype.arrayRead)
    (by rw [writtenHeap,MixkeyArray.written_heap_other _ _ _ _ _ _ _ frame.rootDifferent]; exact frame.prototype.rootRead)
  room := by simpa [writtenHeap,MixkeyArray.writtenHeap] using frame.room
  bound := by simpa [writtenHeap,MixkeyArray.writtenHeap] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

def retain {heap : Heap} {array target : ObjectId} (frame : Frame heap array)
    (targetFrame : Frame heap target) (index : Nat) (byte : UInt8)
    (different : target≠array) (arrayDifferent : target≠frame.prototype.arrayId)
    (rootDifferent : target≠frame.prototype.rootId) : Frame (writtenHeap targetFrame index byte) array := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := by rw [writtenHeap,MixkeyArray.written_heap_other _ _ _ _ _ _ _ different]; exact frame.present
  prototype := frame.prototype.transport rfl
    (by rw [writtenHeap,MixkeyArray.written_heap_other _ _ _ _ _ _ _ arrayDifferent]; exact frame.prototype.arrayRead)
    (by rw [writtenHeap,MixkeyArray.written_heap_other _ _ _ _ _ _ _ rootDifferent]; exact frame.prototype.rootRead)
  room := by simpa [writtenHeap,MixkeyArray.writtenHeap] using frame.room
  bound := by simpa [writtenHeap,MixkeyArray.writtenHeap] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

def fromIdentity {i : Arc4Locals.Inputs} {argument array : Nat} {v : Arc4Locals.Values}
    (stage : Arc4IdentityComplete.Stage i argument array v) :
    Frame (Arc4Locals.heap i (Arc4IdentityComplete.finished stage).cursor.objects argument
      (Arc4Identity.values v array (Arc4IdentityComplete.finished stage).cursor.index)) array := by
  let frame := (Arc4IdentityComplete.finished stage).cursor.frame
  refine ⟨frame.object,256,(fun slot => UInt8.ofNat slot),?_,frame.present,frame.prototype,
    frame.room,frame.bound,frame.arrayDifferent,frame.rootDifferent⟩
  refine ⟨frame.shape.kind,frame.shape.complete,frame.shape.unresolved,frame.shape.extensible,by decide,?_,?_⟩
  · simpa only [frame,Arc4IdentityComplete.complete_length] using frame.shape.size
  · intro slot small
    change ownProperty frame.object (MixkeyIndex.key slot) =
      if slot<256 then some (MixkeyArray.byteDescriptor (UInt8.ofNat slot)) else none
    simpa [small,MixkeyArray.byteDescriptor,MixkeyArray.byteValue,UInt8.toNat_ofNat,Nat.mod_eq_of_lt small,frame]
      using Arc4IdentityComplete.complete_own_property stage slot small

end CookieClicker.JavaScript.Arc4Bytes

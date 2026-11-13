import CookieClicker.JavaScriptArc4Bytes
import CookieClicker.JavaScriptNaturalRemainder

/-! The source ARC4 key schedule retains binary64 byte arithmetic, native
property reads and writes, and every local assignment in their original order. -/
namespace CookieClicker.JavaScript.Arc4Schedule
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals

def objectHeap (source : Arc4Locals.Inputs) (objects : Array JSObject) : Heap :=
  {(base source).heap with objects}

structure Inputs where
  source : Arc4Locals.Inputs
  objects : Array JSObject
  argument : ObjectId
  key : ObjectId
  array : ObjectId
  index : Nat
  small : index<256
  keyFrame : Arc4Bytes.Frame (objectHeap source objects) key
  nonempty : 0<keyFrame.length
  arrayFrame : Arc4Bytes.Frame (objectHeap source objects) array
  full : arrayFrame.length=256
  oldG : UInt8
  oldB : Value
  receiver : Value
  different : array≠key
  keyArrayDifferent : array≠keyFrame.prototype.arrayId
  keyRootDifferent : array≠keyFrame.prototype.rootId

def source (i : Inputs) := i.source
def objects (i : Inputs) := i.objects
def argument (i : Inputs) := i.argument
def key (i : Inputs) := i.key
def array (i : Inputs) := i.array
def index (i : Inputs) := i.index
def length (i : Inputs) := i.keyFrame.length
def oldG (i : Inputs) := i.oldG.toNat
def oldB (i : Inputs) := i.oldB
def receiver (i : Inputs) := i.receiver
def slot (i : Inputs) := i.index%i.keyFrame.length
def keyByte (i : Inputs) := i.keyFrame.bytes (slot i)
def keyNat (i : Inputs) := (keyByte i).toNat
def oldByte (i : Inputs) := i.arrayFrame.bytes i.index
def oldNat (i : Inputs) := (oldByte i).toNat
def total (i : Inputs) := Number.add (Number.add (Number.ofNat (oldG i)) (Number.ofNat (keyNat i))) (Number.ofNat (oldNat i))
def nextG (i : Inputs) := MixkeyArray.maskedByte (total i)
def nextIndex (i : Inputs) := (nextG i).toNat
def movedByte (i : Inputs) := i.arrayFrame.bytes (nextIndex i)
def movedNat (i : Inputs) := (movedByte i).toNat

def values (i : Inputs) (b g : Value) : Arc4Locals.Values := {
  a := .object (key i), b := b, c := .number (Number.ofNat (length i)), e := receiver i
  f := .number (Number.ofNat (index i)), g := g, h := .object (array i) }
def initialValues (i : Inputs) := values i (oldB i) (.number (Number.ofNat (oldG i)))
def localHeap (i : Inputs) (v : Arc4Locals.Values) := heap (source i) (objects i) (argument i) v

def localKeyFrame (i : Inputs) (v : Arc4Locals.Values) : Arc4Bytes.Frame (localHeap i v) (key i) :=
  Arc4Bytes.transport i.keyFrame rfl

def localArrayFrame (i : Inputs) (v : Arc4Locals.Values) : Arc4Bytes.Frame (localHeap i v) (array i) :=
  Arc4Bytes.transport i.arrayFrame rfl

theorem slot_small (i : Inputs) : slot i<256 := by
  have below := Nat.mod_lt i.index i.nonempty
  have := i.keyFrame.shape.bound
  unfold slot
  omega

theorem next_small (i : Inputs) : nextIndex i<256 := (nextG i).toNat_lt

theorem native_remainder (i : Inputs) :
    binary .remainder (.number (Number.ofNat (index i))) (.number (Number.ofNat (length i))) =
      .ok (.number (Number.ofNat (slot i))) := by
  change (Except.ok (.number (Number.remainder (Number.ofNat i.index) (Number.ofNat i.keyFrame.length))) : Checked Value) = _
  rw [NaturalRemainder.byte_remainder i.index i.keyFrame.length i.small i.nonempty i.keyFrame.shape.bound]
  rfl

theorem index_key (i : Inputs) : toJSString (.number (Number.ofNat (index i))) = .ok (MixkeyIndex.key (index i)) :=
  Arc4Identity.native_key i.index i.small

theorem slot_key (i : Inputs) : toJSString (.number (Number.ofNat (slot i))) = .ok (MixkeyIndex.key (slot i)) :=
  Arc4Identity.native_key (slot i) (slot_small i)

theorem next_key (i : Inputs) : toJSString (.number (Number.ofNat (nextIndex i))) = .ok (MixkeyIndex.key (nextIndex i)) :=
  Arc4Identity.native_key (nextIndex i) (next_small i)

theorem checked_key (i : Inputs) (v : Arc4Locals.Values) :
    checkedObject (localHeap i v) (key i) = .ok i.keyFrame.object := (localKeyFrame i v).present

theorem checked_array (i : Inputs) (v : Arc4Locals.Values) :
    checkedObject (localHeap i v) (array i) = .ok i.arrayFrame.object := (localArrayFrame i v).present

theorem key_kind (i : Inputs) : i.keyFrame.object.kind = .array := i.keyFrame.shape.kind

theorem array_kind (i : Inputs) : i.arrayFrame.object.kind = .array := i.arrayFrame.shape.kind

theorem lookup_key (i : Inputs) (v : Arc4Locals.Values) :
    lookupProperty (localHeap i v) (key i) (MixkeyIndex.key (slot i)) =
      .ok (some (.data (.number (Number.ofNat (keyNat i))) true true true)) := by
  have native := MixkeyArray.lookup_slot (localHeap i v) (key i) i.keyFrame.object i.keyFrame.length i.keyFrame.bytes
    i.keyFrame.shape (checked_key i v) (localKeyFrame i v).prototype (slot i) (slot_small i) (localKeyFrame i v).room
  simpa [slot,keyNat,keyByte,MixkeyArray.byteDescriptor,MixkeyArray.byteValue,Nat.mod_lt _ i.nonempty] using native

theorem lookup_old (i : Inputs) (v : Arc4Locals.Values) :
    lookupProperty (localHeap i v) (array i) (MixkeyIndex.key (index i)) =
      .ok (some (.data (.number (Number.ofNat (oldNat i))) true true true)) := by
  have native := MixkeyArray.lookup_slot (localHeap i v) (array i) i.arrayFrame.object i.arrayFrame.length i.arrayFrame.bytes
    i.arrayFrame.shape (checked_array i v) (localArrayFrame i v).prototype (index i) i.small (localArrayFrame i v).room
  simpa [index,oldNat,oldByte,i.full,MixkeyArray.byteDescriptor,MixkeyArray.byteValue,i.small] using native

theorem lookup_moved (i : Inputs) (v : Arc4Locals.Values) :
    lookupProperty (localHeap i v) (array i) (MixkeyIndex.key (nextIndex i)) =
      .ok (some (.data (.number (Number.ofNat (movedNat i))) true true true)) := by
  have native := MixkeyArray.lookup_slot (localHeap i v) (array i) i.arrayFrame.object i.arrayFrame.length i.arrayFrame.bytes
    i.arrayFrame.shape (checked_array i v) (localArrayFrame i v).prototype (nextIndex i) (next_small i) (localArrayFrame i v).room
  simpa [movedNat,movedByte,i.full,MixkeyArray.byteDescriptor,MixkeyArray.byteValue,next_small i] using native

theorem native_add (a b : UInt64) :
    binary .add (.number a) (.number b) = .ok (.number (Number.add a b)) := rfl

theorem native_mask (i : Inputs) :
    binary .bitAnd (.number (Number.ofNat 255))
      (.number (Number.add (Number.add (Number.ofNat (oldG i)) (Number.ofNat (keyNat i))) (Number.ofNat (oldNat i)))) =
      .ok (.number (Number.ofNat (nextIndex i))) := by
  change (Except.ok (.number (Number.bitAnd (Number.ofNat 255) (total i))) : Checked Value) = _
  rw [MixkeyArray.masked_value]
  rfl

end CookieClicker.JavaScript.Arc4Schedule

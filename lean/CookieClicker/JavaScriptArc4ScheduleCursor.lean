import CookieClicker.JavaScriptArc4ScheduleIteration

/-! The ARC4 schedule state is advanced from the actual two native writes.
The input key and all prototype objects are retained through both swaps. -/
namespace CookieClicker.JavaScript.Arc4ScheduleCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Schedule Arc4ScheduleWrites

structure Cursor where
  source : Arc4Locals.Inputs
  objects : Array JSObject
  argument : ObjectId
  key : ObjectId
  array : ObjectId
  index : Nat
  small : index≤256
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

def inputs (cursor : Cursor) (small : cursor.index<256) : Inputs := {
  source := cursor.source, objects := cursor.objects, argument := cursor.argument
  key := cursor.key, array := cursor.array, index := cursor.index, small := small
  keyFrame := cursor.keyFrame, nonempty := cursor.nonempty
  arrayFrame := cursor.arrayFrame, full := cursor.full
  oldG := cursor.oldG, oldB := cursor.oldB, receiver := cursor.receiver
  different := cursor.different, keyArrayDifferent := cursor.keyArrayDifferent, keyRootDifferent := cursor.keyRootDifferent }

def firstKey (i : Inputs) :
    Arc4Bytes.Frame (Arc4Locals.heap (source i) (firstObjects i) (argument i) (finalValues i)) (key i) :=
  Arc4Bytes.retain (localKeyFrame i (finalValues i)) (localArrayFrame i (finalValues i))
    (index i) (movedByte i) i.different i.keyArrayDifferent i.keyRootDifferent

def secondKey (i : Inputs) :
    Arc4Bytes.Frame (Arc4Locals.heap (source i) (secondObjects i) (argument i) (finalValues i)) (key i) :=
  Arc4Bytes.retain (firstKey i) (firstFrame i) (nextIndex i) (oldByte i)
    i.different i.keyArrayDifferent i.keyRootDifferent

def next (cursor : Cursor) (small : cursor.index<256) : Cursor :=
  let i := inputs cursor small
  { source := cursor.source
    objects := secondObjects i
    argument := cursor.argument, key := cursor.key, array := cursor.array
    index := cursor.index+1, small := by omega
    keyFrame := Arc4Bytes.transport (secondKey i) rfl
    nonempty := cursor.nonempty
    arrayFrame := Arc4Bytes.transport (secondFrame i) rfl
    full := second_length i
    oldG := nextG i
    oldB := .number (Number.ofNat (oldNat i))
    receiver := cursor.receiver
    different := cursor.different
    keyArrayDifferent := cursor.keyArrayDifferent
    keyRootDifferent := cursor.keyRootDifferent }

def values (cursor : Cursor) : Arc4Locals.Values := {
  a := .object cursor.key, b := cursor.oldB, c := .number (Number.ofNat cursor.keyFrame.length), e := cursor.receiver
  f := .number (Number.ofNat cursor.index), g := .number (Number.ofNat cursor.oldG.toNat), h := .object cursor.array }

def start (cursor : Cursor) (previous : Option Value) (tail : List Frame) : Machine :=
  Arc4Locals.machine cursor.source cursor.objects cursor.argument (values cursor) (.expression Arc4ScheduleBody.test)
    (.forTest (some Arc4ScheduleBody.test) Arc4ScheduleBody.update Arc4ScheduleBody.body [] previous :: tail)

def previous (cursor : Cursor) (small : cursor.index<256) : Option Value :=
  some (.number (Number.ofNat (oldNat (inputs cursor small))))

theorem actual_iteration (cursor : Cursor) (old : Option Value) (tail : List Frame)
    (small : cursor.index<256) (fuel : Nat) :
    Builtins.run (114+fuel) (start cursor old tail) =
      Builtins.run fuel (start (next cursor small) (previous cursor small) tail) := by
  exact Arc4ScheduleIteration.actual_iteration (inputs cursor small) old tail fuel

theorem retained_key_object (cursor : Cursor) (small : cursor.index<256) :
    (next cursor small).keyFrame.object = cursor.keyFrame.object := rfl

theorem retained_key_bytes (cursor : Cursor) (small : cursor.index<256) :
    (next cursor small).keyFrame.bytes = cursor.keyFrame.bytes := rfl

theorem successor_index (cursor : Cursor) (small : cursor.index<256) :
    (next cursor small).index = cursor.index+1 := rfl

theorem successor_array (cursor : Cursor) (small : cursor.index<256) :
    (next cursor small).arrayFrame.bytes =
      MixkeyArray.nextBytes
        (MixkeyArray.nextBytes cursor.arrayFrame.bytes cursor.index (movedByte (inputs cursor small)))
        (nextIndex (inputs cursor small)) (oldByte (inputs cursor small)) := rfl

theorem successor_g (cursor : Cursor) (small : cursor.index<256) :
    (next cursor small).oldG = nextG (inputs cursor small) := rfl

end CookieClicker.JavaScript.Arc4ScheduleCursor

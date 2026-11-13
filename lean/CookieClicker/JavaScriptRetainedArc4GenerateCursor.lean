import CookieClicker.JavaScriptRetainedArc4GenerateGuard

/-! Each source generator iteration derives the next native state from the
post-swap output read. Its loop counter decreases without a supplied result. -/
namespace CookieClicker.JavaScript.RetainedArc4GenerateCursor
open RetainedArc4Generate RetainedArc4GenerateWrites RetainedArc4GenerateOutput
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Cursor where
  source : RetainedArc4GeneratorLocals.Inputs
  objects : Array JSObject
  argument : ObjectId
  array : ObjectId
  arrayFrame : Arc4Bytes.Frame (objectHeap source objects) array
  full : arrayFrame.length=256
  remaining : Nat
  small : remaining≤256
  oldB : Value
  accumulator : UInt64
  oldF : UInt8
  oldG : UInt8

def inputs (cursor : Cursor) : Inputs := {
  source := cursor.source, objects := cursor.objects, argument := cursor.argument, array := cursor.array
  arrayFrame := cursor.arrayFrame, full := cursor.full
  count := .number (Number.ofNat (cursor.remaining-1))
  oldB := cursor.oldB, accumulator := cursor.accumulator, oldF := cursor.oldF, oldG := cursor.oldG }

def next (cursor : Cursor) : Cursor :=
  let i := inputs cursor
  {source := cursor.source, objects := secondObjects i, argument := cursor.argument, array := cursor.array
   arrayFrame := Arc4Bytes.transport (secondFrame i) rfl
   full := second_length i
   remaining := cursor.remaining-1, small := Nat.le_trans (Nat.sub_le _ _) cursor.small
   oldB := .number (Number.ofNat (picked i)), accumulator := accumulated i
   oldF := nextF i, oldG := nextG i }

def values (cursor : Cursor) : RetainedArc4GeneratorLocals.Values := {
  a := .number (Number.ofNat cursor.remaining), b := cursor.oldB, c := .number cursor.accumulator
  f := .number (Number.ofNat cursor.oldF.toNat), g := .number (Number.ofNat cursor.oldG.toNat), h := .object cursor.array }

def start (cursor : Cursor) (previous : Option Value) (tail : List Frame) :=
  RetainedArc4GeneratorLocals.machine cursor.source cursor.objects cursor.argument (values cursor)
    (.expression RetainedArc4GenerateBody.test)
    (.forTest (some RetainedArc4GenerateBody.test) none RetainedArc4GenerateBody.body [] previous :: tail)

def previous (cursor : Cursor) : Option Value := some (.number (accumulated (inputs cursor)))

theorem actual_enter_body (cursor : Cursor) (old : Option Value) (tail : List Frame)
    (nonempty : 0<cursor.remaining) (fuel : Nat) :
    Builtins.run (8+fuel) (start cursor old tail)=
      Builtins.run fuel (RetainedArc4GenerateBody.start (inputs cursor) old tail) := by
  have native := RetainedArc4GenerateGuard.actual_guard cursor.source cursor.objects cursor.argument cursor.remaining
    (values cursor) old tail cursor.small fuel
  have different : cursor.remaining≠0 := Nat.ne_of_gt nonempty
  simp only [different,↓reduceIte] at native
  simpa only [RetainedArc4GenerateGuard.start,RetainedArc4GenerateGuard.atBody,RetainedArc4GenerateGuard.values,
    RetainedArc4GenerateGuard.afterValues,RetainedArc4GenerateGuard.decremented,different,↓reduceIte,
    RetainedArc4GenerateBody.start,inputs,initialValues,RetainedArc4Generate.values,count,oldB,accumulator,oldF,oldG,array,
    source,objects,argument,start,values] using native

theorem same_next (cursor : Cursor) (tail : List Frame) :
    RetainedArc4GenerateOutput.finish (inputs cursor) tail=start (next cursor) (previous cursor) tail := rfl

theorem actual_iteration (cursor : Cursor) (old : Option Value) (tail : List Frame)
    (nonempty : 0<cursor.remaining) (fuel : Nat) :
    Builtins.run (136+fuel) (start cursor old tail)=
      Builtins.run fuel (start (next cursor) (previous cursor) tail) := by
  rw [show 136+fuel=8+(128+fuel) by omega,actual_enter_body cursor old tail nonempty,
    actual_body,same_next]

theorem next_remaining (cursor : Cursor) : (next cursor).remaining=cursor.remaining-1 := rfl

theorem next_accumulator (cursor : Cursor) : (next cursor).accumulator=
    Number.add (Number.mul cursor.accumulator (Number.ofNat 256))
      (Number.ofNat (outputByte (inputs cursor)).toNat) := rfl

theorem next_permutation (cursor : Cursor) : (next cursor).arrayFrame.bytes=
    MixkeyArray.nextBytes
      (MixkeyArray.nextBytes cursor.arrayFrame.bytes (fIndex (inputs cursor)) (movedByte (inputs cursor)))
      (gIndex (inputs cursor)) (pickedByte (inputs cursor)) := rfl

end CookieClicker.JavaScript.RetainedArc4GenerateCursor

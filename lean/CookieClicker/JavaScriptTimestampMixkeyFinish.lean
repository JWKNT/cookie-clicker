import CookieClicker.JavaScriptTimestampMixkeyCode

/-! The retained native mask, array assignment and next-loop transition. -/
namespace CookieClicker.JavaScript.TimestampMixkeyFinish
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey TimestampMixkeyLoop TimestampMixkeyCode

def total (d : UInt64) (unit : UInt16) := Number.add d (Number.ofNat unit.toNat)
def byte (d : UInt64) (unit : UInt16) := MixkeyArray.maskedByte (total d unit)

def atWrite (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size) : Machine := {
  atInvoke i objects d index previous method with
  control := .putValue ⟨.property (.object (key i)) (MixkeyIndex.key (Nat.mod index 256)),false⟩
    (MixkeyArray.byteValue (byte d (seed i)[index]))
  continuation := .expressionStatement :: (start i objects (.number d) (index+1) previous).continuation }

theorem native_add (a b : UInt64) : binary .add (.number a) (.number b) = .ok (.number (Number.add a b)) := rfl

theorem native_mask (bits : UInt64) : binary .bitAnd (.number (Number.ofNat 255)) (.number bits) =
    .ok (MixkeyArray.byteValue (MixkeyArray.maskedByte bits)) := by
  change (Except.ok (.number (Number.bitAnd (Number.ofNat 255) bits)) : Checked Value) = _
  rw [MixkeyArray.masked_value]

attribute [local cbv_opaque] base scope seed key heap localIndex bodyHeap MixkeyIndex.key Nat.mod Number.ofNat
  Number.add binary MixkeyArray.byteValue MixkeyArray.maskedByte
attribute [local cbv_eval] native_add native_mask

theorem actual_mask (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size) (fuel : Nat) :
    Builtins.run (3+fuel) (afterCode i objects d index previous method bound) =
      Builtins.run fuel (atWrite i objects d index previous method bound) := by
  rw [Nat.add_comm 3 fuel]
  cbv

def nextObjects (i : Inputs) (objects : Array JSObject) (object : JSObject) (length : Nat)
    (index : Nat) (d : UInt64) (bound : index < (seed i).size) :=
  objects.set! (key i) (MixkeyArray.written object length (Nat.mod index 256) (byte d (seed i)[index]))

def afterWrite (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size)
    (object : JSObject) (length : Nat) : Machine :=
  result {atWrite i objects d index previous method bound with
    heap := heap i (nextObjects i objects object length index d bound) (.number d) (index+1)}
    (MixkeyArray.byteValue (byte d (seed i)[index]))

theorem written_heap (i : Inputs) (objects : Array JSObject) (object : JSObject)
    (length slot : Nat) (value : UInt8) (d : Value) (index : Nat) :
    MixkeyArray.writtenHeap (heap i objects d index) (key i) object length slot value =
      heap i (objects.set! (key i) (MixkeyArray.written object length slot value)) d index := rfl

theorem actual_write (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size)
    (object : JSObject) (length : Nat) (bytes : Nat → UInt8)
    (shape : MixkeyArray.Shape object length bytes)
    (present : checkedObject (heap i objects (.number d) (index+1)) (key i) = .ok object)
    (prototype : MixkeyArray.PrototypeFrame (heap i objects (.number d) (index+1)) object)
    (room : 2 ≤ objects.size) (keyBound : key i < objects.size) :
    Builtins.builtinStep (atWrite i objects d index previous method bound) =
      afterWrite i objects d index previous method bound object length := by
  change {writeProperty (atWrite i objects d index previous method bound) (.object (key i))
    (MixkeyIndex.key (Nat.mod index 256)) (MixkeyArray.byteValue (byte d (seed i)[index])) false
    with elapsed := (base i).elapsed} = _
  rw [MixkeyArray.native_write (atWrite i objects d index previous method bound) (key i) object length bytes
    shape present prototype (Nat.mod index 256) (show Nat.mod index 256<256 from Nat.mod_lt _ (by decide))
    (byte d (seed i)[index]) room keyBound false]
  change result {atWrite i objects d index previous method bound with
    heap := MixkeyArray.writtenHeap (heap i objects (.number d) (index+1)) (key i) object length
      (Nat.mod index 256) (byte d (seed i)[index])} (MixkeyArray.byteValue (byte d (seed i)[index])) = _
  rw [written_heap]
  unfold afterWrite nextObjects
  rfl



def nextGuard (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (bound : index < (seed i).size) (object : JSObject) (length : Nat) : Machine :=
  atGuard (base i) (scope i) (seed i) (key i) (nextObjects i objects object length index d bound) (.number d)
    (index+1) (some (MixkeyArray.byteValue (byte d (seed i)[index])))

attribute [local cbv_opaque] nextObjects byte total

theorem actual_continue (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size)
    (object : JSObject) (length fuel : Nat) :
    Builtins.run (2+fuel) (afterWrite i objects d index previous method bound object length) =
      Builtins.run fuel (nextGuard i objects d index bound object length) := by
  rw [Nat.add_comm 2 fuel]
  cbv

end CookieClicker.JavaScript.TimestampMixkeyFinish

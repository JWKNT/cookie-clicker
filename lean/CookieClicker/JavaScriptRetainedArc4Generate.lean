import CookieClicker.JavaScriptRetainedArc4GeneratorEntry

/-! Exact native state for one source generator iteration. The accumulator
is retained as binary64 bits, including overflow during the discarded block. -/
namespace CookieClicker.JavaScript.RetainedArc4Generate
open RetainedArc4GeneratorLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def objectHeap (source : RetainedArc4GeneratorLocals.Inputs) (objects : Array JSObject) : Heap :=
  {(base source).heap with objects}
structure Inputs where
  source : RetainedArc4GeneratorLocals.Inputs
  objects : Array JSObject
  argument : ObjectId
  array : ObjectId
  arrayFrame : Arc4Bytes.Frame (objectHeap source objects) array
  full : arrayFrame.length=256
  count : Value
  oldB : Value
  accumulator : UInt64
  oldF : UInt8
  oldG : UInt8

def source (i : Inputs) := i.source
def objects (i : Inputs) := i.objects
def argument (i : Inputs) := i.argument
def array (i : Inputs) := i.array
def count (i : Inputs) := i.count
def oldB (i : Inputs) := i.oldB
def accumulator (i : Inputs) := i.accumulator
def oldF (i : Inputs) := i.oldF.toNat
def oldG (i : Inputs) := i.oldG.toNat
def fBits (i : Inputs) := Number.add (Number.ofNat (oldF i)) Number.one
def nextF (i : Inputs) := MixkeyArray.maskedByte (fBits i)
def fIndex (i : Inputs) := (nextF i).toNat
def pickedByte (i : Inputs) := i.arrayFrame.bytes (fIndex i)
def picked (i : Inputs) := (pickedByte i).toNat
def gBits (i : Inputs) := Number.add (Number.ofNat (oldG i)) (Number.ofNat (picked i))
def nextG (i : Inputs) := MixkeyArray.maskedByte (gBits i)
def gIndex (i : Inputs) := (nextG i).toNat
def movedByte (i : Inputs) := i.arrayFrame.bytes (gIndex i)
def moved (i : Inputs) := (movedByte i).toNat
def product (i : Inputs) := Number.mul (accumulator i) (Number.ofNat 256)

def values (i : Inputs) (b : Value) (acc : UInt64) (f g : Nat) : RetainedArc4GeneratorLocals.Values := {
  a := count i, b := b, c := .number acc
  f := .number (Number.ofNat f), g := .number (Number.ofNat g), h := .object (array i) }
def initialValues (i : Inputs) := values i (oldB i) (accumulator i) (oldF i) (oldG i)
def updatedValues (i : Inputs) := values i (.number (Number.ofNat (picked i))) (accumulator i) (fIndex i) (gIndex i)
def localFrame (i : Inputs) (v : RetainedArc4GeneratorLocals.Values) :
    Arc4Bytes.Frame (heap (source i) (objects i) (argument i) v) (array i) :=
  Arc4Bytes.transport i.arrayFrame rfl

theorem f_small (i : Inputs) : fIndex i<256 := (nextF i).toNat_lt
theorem g_small (i : Inputs) : gIndex i<256 := (nextG i).toNat_lt

theorem f_key (i : Inputs) : toJSString (.number (Number.ofNat (fIndex i)))=.ok (MixkeyIndex.key (fIndex i)) :=
  Arc4Identity.native_key _ (f_small i)
theorem g_key (i : Inputs) : toJSString (.number (Number.ofNat (gIndex i)))=.ok (MixkeyIndex.key (gIndex i)) :=
  Arc4Identity.native_key _ (g_small i)

theorem native_mul (a b : UInt64) : binary .multiply (.number a) (.number b)=.ok (.number (Number.mul a b)) := rfl

theorem native_f_mask (i : Inputs) :
    binary .bitAnd (.number (Number.ofNat 255)) (.number (Number.add (Number.ofNat (oldF i)) Number.one))=
      .ok (.number (Number.ofNat (fIndex i))) := by
  change (Except.ok (.number (Number.bitAnd (Number.ofNat 255) (fBits i))) : Checked Value) = _
  rw [MixkeyArray.masked_value]
  rfl

theorem native_g_mask (i : Inputs) :
    binary .bitAnd (.number (Number.ofNat 255)) (.number (Number.add (Number.ofNat (oldG i)) (Number.ofNat (picked i))))=
      .ok (.number (Number.ofNat (gIndex i))) := by
  change (Except.ok (.number (Number.bitAnd (Number.ofNat 255) (gBits i))) : Checked Value) = _
  rw [MixkeyArray.masked_value]
  rfl

theorem native_f_mask_literal (i : Inputs) :
    binary .bitAnd (.number (Number.ofNat 255))
      (.number (Number.add (Number.ofNat (oldF i)) 4607182418800017408))=
      .ok (.number (Number.ofNat (fIndex i))) := native_f_mask i

end CookieClicker.JavaScript.RetainedArc4Generate

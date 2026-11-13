import CookieClicker.JavaScriptArrayUnshift

/-! Final native item insertion and length write for one-element unshift. -/
namespace CookieClicker.JavaScript.ArrayUnshiftFinish
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
open ArrayUnshift (continuation next)

def inserted (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) (value : Value) : Machine :=
  {base with heap := DenseArrayState.writtenHeap frame 0 value}
def insertedFrame (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) (value : Value) :=
  DenseArrayState.write frame 0 value (by decide) (Nat.zero_le _)

def afterItem (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :=
  result {inserted base array frame value with
    continuation := .builtin (continuation array original 1 value "unshiftItems") :: base.continuation} value

def itemResponse (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) : Machine := {
  inserted base array frame value with control := .resumeBuiltin (continuation array original 1 value "unshiftItems") value }

def finalHeap (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) (value : Value) :=
  DenseArrayState.lengthHeap (insertedFrame base array frame value)

def afterLength (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :=
  result {base with
    heap := finalHeap base array frame value
    continuation := .builtin (continuation array original 1 value "unshiftLength") :: base.continuation}
    (.number (Number.ofNat (original+1)))

def lengthResponse (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) : Machine := {
  base with
  heap := finalHeap base array frame value
  control := .resumeBuiltin (continuation array original 1 value "unshiftLength") (.number (Number.ofNat (original+1))) }

def returned (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :=
  result {base with heap := finalHeap base array frame value} (.number (Number.ofNat (original+1)))

theorem insert_item (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :
    Builtins.builtinStep (next base array original 0 value) = afterItem base array frame original value := by
  have phase : "unshiftItems".startsWith "has:" = false := by decide +kernel
  simp only [next,Builtins.arrayUnshiftNext,continuation,List.isEmpty_cons,Bool.or_self,Bool.true_or,beq_self_eq_true,↓reduceIte,
    Builtins.builtinStep,Builtins.resume,ArrayUnshift.id,String.reduceBEq,Bool.false_or,Bool.false_and,Bool.false_eq_true,phase]
  change Builtins.suspendPut (next base array original 0 value)
    (continuation array original 1 value "unshiftItems") (.object array) (MixkeyIndex.key 0) value = _
  have write := DenseArray.native_write
    {next base array original 0 value with
      continuation := .builtin (continuation array original 1 value "unshiftItems") :: base.continuation}
    array frame.object frame.length frame.values frame.shape frame.present frame.prototype 0 (by decide)
    value frame.room frame.bound true
  exact write

theorem consume_item (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :
    Builtins.builtinStep (afterItem base array frame original value) = itemResponse base array frame original value := rfl

theorem write_length (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) (length : DenseArray.nextLength frame.length 0 = original+1) :
    Builtins.builtinStep (itemResponse base array frame original value) = afterLength base array frame original value := by
  have phase : "unshiftItems".startsWith "has:" = false := by decide +kernel
  simp only [Builtins.builtinStep,itemResponse,Builtins.resume,continuation,ArrayUnshift.id,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  change Builtins.suspendPut (itemResponse base array frame original value)
    (continuation array original 1 value "unshiftLength") (.object array) (JSString.ofString "length")
      (.number (Number.ofNat (original+1))) = _
  have write := DenseArrayState.native_length_write
    {itemResponse base array frame original value with
      continuation := .builtin (continuation array original 1 value "unshiftLength") :: base.continuation}
    array (insertedFrame base array frame value)
  change writeProperty _ _ _ (.number (Number.ofNat (DenseArray.nextLength frame.length 0))) true =
    result _ (.number (Number.ofNat (DenseArray.nextLength frame.length 0))) at write
  rw [length] at write
  exact write

theorem consume_length (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :
    Builtins.builtinStep (afterLength base array frame original value) = lengthResponse base array frame original value := rfl

theorem return_length (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) :
    Builtins.builtinStep (lengthResponse base array frame original value) = returned base array frame original value := by
  have phase : "unshiftLength".startsWith "has:" = false := by decide +kernel
  simp only [Builtins.builtinStep,lengthResponse,Builtins.resume,continuation,ArrayUnshift.id,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  rfl

theorem actual_finish (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original : Nat) (value : Value) (length : DenseArray.nextLength frame.length 0 = original+1) (fuel : Nat) :
    Builtins.run (5+fuel) (next base array original 0 value) = Builtins.run fuel (returned base array frame original value) := by
  rw [show 5+fuel=((((fuel+1)+1)+1)+1)+1 by omega]
  change Builtins.run ((((fuel+1)+1)+1)+1) (Builtins.builtinStep (next base array original 0 value)) = _
  rw [insert_item base array frame original value]
  change Builtins.run (((fuel+1)+1)+1) (Builtins.builtinStep (afterItem base array frame original value)) = _
  rw [consume_item]
  change Builtins.run ((fuel+1)+1) (Builtins.builtinStep (itemResponse base array frame original value)) = _
  rw [write_length base array frame original value length]
  change Builtins.run (fuel+1) (Builtins.builtinStep (afterLength base array frame original value)) = _
  rw [consume_length]
  change Builtins.run fuel (Builtins.builtinStep (lengthResponse base array frame original value)) = _
  rw [return_length]

end CookieClicker.JavaScript.ArrayUnshiftFinish

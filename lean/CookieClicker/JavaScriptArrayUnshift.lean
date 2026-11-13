import CookieClicker.JavaScriptDenseArrayState

/-! The native Array.unshift continuation over a dense notification array.
Each copied slot is read and written by the shared evaluator. -/
namespace CookieClicker.JavaScript.ArrayUnshift
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

def id : BuiltinId := ⟨"Array.prototype","unshift"⟩
def continuation (array original index : Nat) (value : Value) (phase : String) : BuiltinContinuation := {
  id := id, phase := phase, thisValue := .object array, arguments := [value], indices := [original,index] }

def next (base : Machine) (array original index : Nat) (value : Value) :=
  Builtins.arrayUnshiftNext base (continuation array original index value "unshiftWrite")

def has (base : Machine) (array original index : Nat) (value : Value) : Machine := {
  base with control := .resumeBuiltin (continuation array original index value "has:arrayUnshiftNext") (.boolean true) }

def afterRead (base : Machine) (array original index : Nat) (value copied : Value) :=
  result {base with continuation := .builtin (continuation array original index value "unshiftRead") :: base.continuation} copied

def readResponse (base : Machine) (array original index : Nat) (value copied : Value) : Machine := {
  base with control := .resumeBuiltin (continuation array original index value "unshiftRead") copied }

def changed (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) (index : Nat) :=
  {base with heap := DenseArrayState.writtenHeap frame index (frame.values (index-1))}

def afterWrite (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) :=
  result {changed base array frame index with
    continuation := .builtin (continuation array original (index-1) value "unshiftWrite") :: base.continuation}
    (frame.values (index-1))

def writeResponse (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) : Machine := {
  changed base array frame index with
  control := .resumeBuiltin (continuation array original (index-1) value "unshiftWrite") (frame.values (index-1)) }

attribute [local cbv_opaque] Builtins.arrayUnshiftNext Builtins.suspendGet Builtins.suspendPut
  MixkeyIndex.key DenseArrayState.writtenHeap

theorem next_positive (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) (positive : 0 < index) (small : index < 256) (within : index ≤ frame.length) :
    next base array original index value = has base array original index value := by
  have slotSmall : index-1 < 256 := by omega
  have occupied : index-1 < frame.length := by omega
  have found := DenseArray.lookup_slot base.heap array frame.object frame.length frame.values frame.shape
    frame.present frame.prototype (index-1) slotSmall frame.room
  simp only [occupied,↓reduceIte] at found
  unfold next
  simp only [Builtins.arrayUnshiftNext,continuation,show (index == 0) = false by simp [show index≠0 by omega],
    List.isEmpty_cons,Bool.or_self,Bool.false_eq_true,↓reduceIte]
  change Builtins.suspendHas base (continuation array original index value "has:arrayUnshiftNext")
    array (MixkeyIndex.key (index-1)) = _
  simp only [Builtins.suspendHas,found,Option.isSome_some]
  rfl

theorem resume_has (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) (positive : 0 < index) (small : index < 256) (within : index ≤ frame.length) :
    Builtins.builtinStep (has base array original index value) =
      afterRead base array original index value (frame.values (index-1)) := by
  have phase : "has:arrayUnshiftNext".startsWith "has:" = true := by decide +kernel
  simp only [Builtins.builtinStep,has,Builtins.resume,continuation,id,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  change Builtins.arrayUnshiftNext (has base array original index value)
    (continuation array original index value "has:arrayUnshiftNext") (some true) = _
  simp only [Builtins.arrayUnshiftNext,continuation,show (index == 0) = false by simp [show index≠0 by omega],
    List.isEmpty_cons,Bool.or_self,Bool.false_eq_true,↓reduceIte]
  change Builtins.suspendGet (has base array original index value)
    (continuation array original index value "unshiftRead") (.object array) (MixkeyIndex.key (index-1)) = _
  have read := DenseArray.native_read
    {has base array original index value with continuation := .builtin (continuation array original index value "unshiftRead") :: base.continuation}
    array frame.object frame.length frame.values frame.shape frame.present frame.prototype (index-1) (by omega) frame.room
  simp only [DenseArray.readValue,show index-1<frame.length by omega,↓reduceIte] at read
  exact read

theorem consume_read (base : Machine) (array original index : Nat) (value copied : Value) :
    Builtins.builtinStep (afterRead base array original index value copied) = readResponse base array original index value copied := rfl

theorem resume_read (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) (small : index < 256) :
    Builtins.builtinStep (readResponse base array original index value (frame.values (index-1))) =
      afterWrite base array frame original index value := by
  have phase : "unshiftRead".startsWith "has:" = false := by decide +kernel
  simp only [Builtins.builtinStep,readResponse,Builtins.resume,continuation,id,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  change Builtins.suspendPut (readResponse base array original index value (frame.values (index-1)))
    (continuation array original (index-1) value "unshiftWrite") (.object array) (Builtins.indexKey (index+1-1))
      (frame.values (index-1)) = _
  simp only [Nat.add_sub_cancel]
  have write := DenseArray.native_write
    {readResponse base array original index value (frame.values (index-1)) with
      continuation := .builtin (continuation array original (index-1) value "unshiftWrite") :: base.continuation}
    array frame.object frame.length frame.values frame.shape frame.present frame.prototype index small
    (frame.values (index-1)) frame.room frame.bound true
  exact write

theorem consume_write (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) :
    Builtins.builtinStep (afterWrite base array frame original index value) = writeResponse base array frame original index value := rfl

theorem resume_write (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) :
    Builtins.builtinStep (writeResponse base array frame original index value) =
      next (changed base array frame index) array original (index-1) value := by
  have phase : "unshiftWrite".startsWith "has:" = false := by decide +kernel
  simp only [Builtins.builtinStep,writeResponse,Builtins.resume,continuation,id,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  change Builtins.arrayUnshiftNext (writeResponse base array frame original index value)
    (continuation array original (index-1) value "unshiftWrite") = _
  rfl

theorem actual_copy (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (original index : Nat) (value : Value) (positive : 0 < index) (small : index < 256) (within : index ≤ frame.length)
    (fuel : Nat) :
    Builtins.run (5+fuel) (next base array original index value) =
      Builtins.run fuel (next (changed base array frame index) array original (index-1) value) := by
  rw [next_positive base array frame original index value positive small within]
  rw [show 5+fuel=((((fuel+1)+1)+1)+1)+1 by omega]
  change Builtins.run ((((fuel+1)+1)+1)+1) (Builtins.builtinStep (has base array original index value)) = _
  rw [resume_has base array frame original index value positive small within]
  change Builtins.run (((fuel+1)+1)+1) (Builtins.builtinStep (afterRead base array original index value (frame.values (index-1)))) = _
  rw [consume_read]
  change Builtins.run ((fuel+1)+1) (Builtins.builtinStep (readResponse base array original index value (frame.values (index-1)))) = _
  rw [resume_read base array frame original index value small]
  change Builtins.run (fuel+1) (Builtins.builtinStep (afterWrite base array frame original index value)) = _
  rw [consume_write]
  change Builtins.run fuel (Builtins.builtinStep (writeResponse base array frame original index value)) = _
  rw [resume_write]

end CookieClicker.JavaScript.ArrayUnshift

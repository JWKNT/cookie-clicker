import CookieClicker.JavaScriptArrayUnshiftLoop

/-! Actual builtin entry and full one-element unshift for bounded native queues. -/
namespace CookieClicker.JavaScript.ArrayUnshiftCall
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ArrayUnshift (continuation next)

def lengthContinuation (array : ObjectId) (value : Value) : BuiltinContinuation := {
  id := ArrayUnshift.id, phase := "length", thisValue := .object array, arguments := [value] }

def request (base : Machine) (array : ObjectId) (value : Value) : Machine := {
  base with control := .unresolved (.builtin ArrayUnshift.id (.object array) [value] false) }

def atLength (base : Machine) (array original : Nat) (value : Value) :=
  result {base with continuation := .builtin (lengthContinuation array value) :: base.continuation}
    (.number (Number.ofNat original))

def lengthResponse (base : Machine) (array original : Nat) (value : Value) : Machine := {
  base with control := .resumeBuiltin (lengthContinuation array value) (.number (Number.ofNat original)) }

theorem actual_dispatch (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) (value : Value) :
    Builtins.builtinStep (request base array value) = atLength base array frame.length value := by
  have read := DenseArrayState.native_read_length
    {request base array value with continuation := .builtin (lengthContinuation array value) :: base.continuation} array frame
  change Builtins.dispatch (request base array value) ArrayUnshift.id (.object array) [value] false = _
  simpa [Builtins.dispatch,Builtins.arrayCall,ArrayUnshift.id,toObject,checked,Builtins.suspendGet,
    lengthContinuation,atLength,request,result] using read

theorem consume_length (base : Machine) (array original : Nat) (value : Value) :
    Builtins.builtinStep (atLength base array original value) = lengthResponse base array original value := rfl

theorem next_phase (base : Machine) (array original index : Nat) (value : Value) (phase : String) :
    Builtins.arrayUnshiftNext base (continuation array original index value phase) = next base array original index value := rfl

theorem resume_length (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) :
    Builtins.builtinStep (lengthResponse base array frame.length value) = next base array frame.length frame.length value := by
  have phase : "length".startsWith "has:" = false := by decide +kernel
  have conversion := MixkeyApply.length_conversion ⟨frame.length,by omega⟩
  have capacity : ¬frame.length+1>2^53-1 := by omega
  simp only [Builtins.builtinStep,lengthResponse,Builtins.resume,lengthContinuation,ArrayUnshift.id,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase,isObject,conversion,checked]
  simp only [Builtins.arrayLengthReady,String.reduceBEq,List.length_cons,List.length_nil,Nat.zero_add,
    capacity,↓reduceIte]
  change Builtins.arrayUnshiftNext (lengthResponse base array frame.length value)
    (continuation array frame.length frame.length value "length") = _
  rw [next_phase]
  rfl

theorem actual_entry (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) (fuel : Nat) :
    Builtins.run (3+fuel) (request base array value) = Builtins.run fuel (next base array frame.length frame.length value) := by
  rw [show 3+fuel=((fuel+1)+1)+1 by omega]
  simp only [Builtins.run,status,request]
  change (match status (Builtins.builtinStep (request base array value)) with
    | .unresolved _ | .fault _ => Builtins.builtinStep (request base array value)
    | _ => Builtins.run ((fuel+1)+1) (Builtins.builtinStep (request base array value))) = _
  rw [actual_dispatch base array frame value]
  change Builtins.run (fuel+1) (Builtins.builtinStep (atLength base array frame.length value)) = _
  rw [consume_length]
  change Builtins.run fuel (Builtins.builtinStep (lengthResponse base array frame.length value)) = _
  rw [resume_length base array frame value small]

theorem complete_call (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) (fuel : Nat) :
    Builtins.run (8+5*frame.length+fuel) (request base array value) =
      Builtins.run fuel (ArrayUnshiftLoop.returned base array frame value small) := by
  rw [show 8+5*frame.length+fuel=3+(5*frame.length+5+fuel) by omega,actual_entry base array frame value small,
    ArrayUnshiftLoop.complete_loop]

end CookieClicker.JavaScript.ArrayUnshiftCall

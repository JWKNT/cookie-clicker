import CookieClicker.JavaScriptArrayPop

/-! Empty native pop performs its length write and returns undefined. -/
namespace CookieClicker.JavaScript.ArrayPopEmpty
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Inputs where
  base : Machine
  array : ObjectId
  frame : DenseArrayState.Frame base.heap array
  empty : frame.length=0

def request (i : Inputs) : Machine := {i.base with control := .unresolved (.builtin ArrayPop.method (.object i.array) [] false)}
def atLength (i : Inputs) :=
  result {i.base with continuation := .builtin (ArrayPop.initialContinuation i.array) :: i.base.continuation}
    (.number (Number.ofNat 0))
def lengthResponse (i : Inputs) : Machine := {
  i.base with control := .resumeBuiltin (ArrayPop.initialContinuation i.array) (.number (Number.ofNat 0)) }
def returnContinuation (array : ObjectId) : BuiltinContinuation := {
  ArrayPop.initialContinuation array with phase := "popLength",locals := [.undefined] }
def afterWrite (i : Inputs) :=
  result {i.base with
    heap := DenseArrayState.lengthHeap i.frame
    continuation := .builtin (returnContinuation i.array) :: i.base.continuation}
    (.number (Number.ofNat 0))
def writeResponse (i : Inputs) : Machine := {
  i.base with
  heap := DenseArrayState.lengthHeap i.frame
  control := .resumeBuiltin (returnContinuation i.array) (.number (Number.ofNat 0)) }
def returned (i : Inputs) := result {i.base with heap := DenseArrayState.lengthHeap i.frame} .undefined

theorem dispatch (i : Inputs) : Builtins.builtinStep (request i)=atLength i := by
  have read := DenseArrayState.native_read_length
    {request i with continuation := .builtin (ArrayPop.initialContinuation i.array) :: i.base.continuation} i.array i.frame
  rw [i.empty] at read
  change Builtins.dispatch (request i) ArrayPop.method (.object i.array) [] false = _
  simpa [Builtins.dispatch,Builtins.arrayCall,ArrayPop.method,toObject,checked,Builtins.suspendGet,
    ArrayPop.initialContinuation,atLength,request,result] using read

theorem consume_length (i : Inputs) : Builtins.builtinStep (atLength i)=lengthResponse i := rfl

theorem write_length (i : Inputs) : Builtins.builtinStep (lengthResponse i)=afterWrite i := by
  have phase : "length".startsWith "has:"=false := by decide +kernel
  have conversion := MixkeyApply.length_conversion ⟨0,by decide⟩
  simp only [Builtins.builtinStep,lengthResponse,Builtins.resume,ArrayPop.initialContinuation,ArrayPop.method,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase,isObject,conversion,checked]
  simp only [Builtins.arrayLengthReady,String.reduceBEq,beq_self_eq_true,↓reduceIte]
  change Builtins.suspendPut (lengthResponse i) (returnContinuation i.array)
    (.object i.array) (JSString.ofString "length") (.number (Number.ofNat 0)) = _
  have write := DenseArrayState.native_length_write
    {lengthResponse i with continuation := .builtin (returnContinuation i.array) :: i.base.continuation} i.array i.frame
  rw [i.empty] at write
  exact write

theorem consume_write (i : Inputs) : Builtins.builtinStep (afterWrite i)=writeResponse i := rfl

theorem return_undefined (i : Inputs) : Builtins.builtinStep (writeResponse i)=returned i := by
  have phase : "popLength".startsWith "has:"=false := by decide +kernel
  simp only [Builtins.builtinStep,writeResponse,Builtins.resume,returnContinuation,ArrayPop.initialContinuation,
    ArrayPop.method,String.reduceBEq,Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  rfl

theorem complete_call (i : Inputs) (fuel : Nat) :
    Builtins.run (5+fuel) (request i)=Builtins.run fuel (returned i) := by
  rw [show 5+fuel=((((fuel+1)+1)+1)+1)+1 by omega]
  simp only [Builtins.run,status,request]
  change (match status (Builtins.builtinStep (request i)) with
    | .unresolved _ | .fault _ => Builtins.builtinStep (request i)
    | _ => Builtins.run (fuel+4) (Builtins.builtinStep (request i))) = _
  rw [dispatch]
  change Builtins.run (((fuel+1)+1)+1) (Builtins.builtinStep (atLength i)) = _
  rw [consume_length]
  change Builtins.run ((fuel+1)+1) (Builtins.builtinStep (lengthResponse i)) = _
  rw [write_length]
  change Builtins.run (fuel+1) (Builtins.builtinStep (afterWrite i)) = _
  rw [consume_write]
  change Builtins.run fuel (Builtins.builtinStep (writeResponse i)) = _
  rw [return_undefined]

def finalFrame (i : Inputs) : DenseArrayState.Frame (returned i).heap i.array := DenseArrayState.finish i.frame

theorem final_length (i : Inputs) : (finalFrame i).length=0 := i.empty

theorem final_index_bound (i : Inputs) (bound : ArrayIndexBound.Holds i.frame.object i.frame.length) :
    ArrayIndexBound.Holds (finalFrame i).object (finalFrame i).length :=
  ArrayIndexBound.length_changed bound _ true

theorem elapsed (i : Inputs) : (returned i).elapsed=i.base.elapsed := rfl

theorem free_draws (i : Inputs) : (returned i).freeDrawCount=i.base.freeDrawCount := rfl

end CookieClicker.JavaScript.ArrayPopEmpty

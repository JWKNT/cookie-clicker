import CookieClicker.JavaScriptArrayPopData

/-! Complete native pop entry, last-value read, deletion and length update. -/
namespace CookieClicker.JavaScript.ArrayPop
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def method : BuiltinId := ⟨"Array.prototype","pop"⟩
def initialContinuation (array : ObjectId) : BuiltinContinuation := {
  id := method,phase := "length",thisValue := .object array }
def continuation (array length : Nat) (phase : String) (locals : List Value) : BuiltinContinuation := {
  id := method,phase := phase,thisValue := .object array,indices := [length],locals := locals }

structure Inputs where
  base : Machine
  array : ObjectId
  frame : DenseArrayState.Frame base.heap array
  bounded : ArrayIndexBound.Holds frame.object frame.length
  positive : 0<frame.length

def selected (i : Inputs) := i.frame.values (i.frame.length-1)
def request (i : Inputs) : Machine := {i.base with control := .unresolved (.builtin method (.object i.array) [] false)}
def atLength (i : Inputs) :=
  result {i.base with continuation := .builtin (initialContinuation i.array) :: i.base.continuation}
    (.number (Number.ofNat i.frame.length))
def lengthResponse (i : Inputs) : Machine := {
  i.base with control := .resumeBuiltin (initialContinuation i.array) (.number (Number.ofNat i.frame.length)) }
def atLast (i : Inputs) :=
  result {i.base with continuation := .builtin (continuation i.array i.frame.length "popValue" []) :: i.base.continuation} (selected i)
def lastResponse (i : Inputs) : Machine := {
  i.base with control := .resumeBuiltin (continuation i.array i.frame.length "popValue" []) (selected i) }
def removedHeap (i : Inputs) := ArrayPopData.removedHeap i.base.heap i.array i.frame.object (i.frame.length-1)
def afterDelete (i : Inputs) :=
  result {i.base with
    heap := removedHeap i
    continuation := .builtin (continuation i.array i.frame.length "popDelete" [selected i]) :: i.base.continuation} (.boolean true)
def deleteResponse (i : Inputs) : Machine := {
  i.base with
  heap := removedHeap i
  control := .resumeBuiltin (continuation i.array i.frame.length "popDelete" [selected i]) (.boolean true) }
def finalHeap (i : Inputs) := ArrayPopData.finalHeap i.base.heap i.array i.frame.object i.frame.length
def afterWrite (i : Inputs) :=
  result {i.base with
    heap := finalHeap i
    continuation := .builtin (continuation i.array i.frame.length "popLength" [selected i]) :: i.base.continuation}
    (.number (Number.ofNat (i.frame.length-1)))
def writeResponse (i : Inputs) : Machine := {
  i.base with
  heap := finalHeap i
  control := .resumeBuiltin (continuation i.array i.frame.length "popLength" [selected i]) (.number (Number.ofNat (i.frame.length-1))) }
def returned (i : Inputs) := result {i.base with heap := finalHeap i} (selected i)

theorem dispatch (i : Inputs) : Builtins.builtinStep (request i) = atLength i := by
  have read := DenseArrayState.native_read_length
    {request i with continuation := .builtin (initialContinuation i.array) :: i.base.continuation} i.array i.frame
  change Builtins.dispatch (request i) method (.object i.array) [] false = _
  simpa [Builtins.dispatch,Builtins.arrayCall,method,toObject,checked,Builtins.suspendGet,
    initialContinuation,atLength,request,result] using read

theorem consume_length (i : Inputs) : Builtins.builtinStep (atLength i) = lengthResponse i := rfl

theorem read_last (i : Inputs) : Builtins.builtinStep (lengthResponse i) = atLast i := by
  have phase : "length".startsWith "has:"=false := by decide +kernel
  have conversion := MixkeyApply.length_conversion ⟨i.frame.length,by have := i.frame.shape.bound; omega⟩
  have positive : i.frame.length ≠ 0 := Nat.ne_of_gt i.positive
  simp only [Builtins.builtinStep,lengthResponse,Builtins.resume,initialContinuation,method,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase,isObject,conversion,checked]
  simp only [Builtins.arrayLengthReady,String.reduceBEq,show (i.frame.length==0)=false by simp [positive],Bool.false_eq_true,↓reduceIte]
  change Builtins.suspendGet (lengthResponse i) (continuation i.array i.frame.length "popValue" [])
    (.object i.array) (MixkeyIndex.key (i.frame.length-1)) = _
  have read := DenseArray.native_read
    {lengthResponse i with continuation := .builtin (continuation i.array i.frame.length "popValue" []) :: i.base.continuation}
    i.array i.frame.object i.frame.length i.frame.values i.frame.shape i.frame.present i.frame.prototype
    (i.frame.length-1) (by have := i.frame.shape.bound; omega) i.frame.room
  simp only [DenseArray.readValue,show i.frame.length-1<i.frame.length by have := i.positive; omega,↓reduceIte] at read
  exact read

theorem consume_last (i : Inputs) : Builtins.builtinStep (atLast i) = lastResponse i := rfl

theorem delete_last (i : Inputs) : Builtins.builtinStep (lastResponse i) = afterDelete i := by
  have phase : "popValue".startsWith "has:"=false := by decide +kernel
  simp only [Builtins.builtinStep,lastResponse,Builtins.resume,continuation,method,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  change Builtins.suspendDelete (lastResponse i) (continuation i.array i.frame.length "popDelete" [selected i])
    (.object i.array) (MixkeyIndex.key (i.frame.length-1)) = _
  exact ArrayPopData.native_delete
    {lastResponse i with continuation := .builtin (continuation i.array i.frame.length "popDelete" [selected i]) :: i.base.continuation}
    i.array i.frame (i.frame.length-1) (by have := i.frame.shape.bound; omega) (by have := i.positive; omega)

theorem consume_delete (i : Inputs) : Builtins.builtinStep (afterDelete i) = deleteResponse i := rfl

theorem write_length (i : Inputs) : Builtins.builtinStep (deleteResponse i) = afterWrite i := by
  have phase : "popDelete".startsWith "has:"=false := by decide +kernel
  simp only [Builtins.builtinStep,deleteResponse,Builtins.resume,continuation,method,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  change Builtins.suspendPut (deleteResponse i) (continuation i.array i.frame.length "popLength" [selected i])
    (.object i.array) (JSString.ofString "length") (.number (Number.ofNat (i.frame.length-1))) = _
  have write := ArrayPopData.native_shrink
    {i.base with
      control := (deleteResponse i).control
      continuation := .builtin (continuation i.array i.frame.length "popLength" [selected i]) :: i.base.continuation}
    i.array i.frame i.bounded i.positive
  exact write

theorem consume_write (i : Inputs) : Builtins.builtinStep (afterWrite i) = writeResponse i := rfl

theorem return_last (i : Inputs) : Builtins.builtinStep (writeResponse i) = returned i := by
  have phase : "popLength".startsWith "has:"=false := by decide +kernel
  simp only [Builtins.builtinStep,writeResponse,Builtins.resume,continuation,method,String.reduceBEq,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,↓reduceIte,phase]
  rfl

theorem complete_call (i : Inputs) (fuel : Nat) :
    Builtins.run (9+fuel) (request i) = Builtins.run fuel (returned i) := by
  rw [show 9+fuel=((((((((fuel+1)+1)+1)+1)+1)+1)+1)+1)+1 by omega]
  simp only [Builtins.run,status,request]
  change (match status (Builtins.builtinStep (request i)) with
    | .unresolved _ | .fault _ => Builtins.builtinStep (request i)
    | _ => Builtins.run (fuel+8) (Builtins.builtinStep (request i))) = _
  rw [dispatch]
  change Builtins.run (((((((fuel+1)+1)+1)+1)+1)+1)+1) (Builtins.builtinStep (atLength i)) = _
  rw [consume_length]
  change Builtins.run ((((((fuel+1)+1)+1)+1)+1)+1) (Builtins.builtinStep (lengthResponse i)) = _
  rw [read_last]
  change Builtins.run (((((fuel+1)+1)+1)+1)+1) (Builtins.builtinStep (atLast i)) = _
  rw [consume_last]
  change Builtins.run ((((fuel+1)+1)+1)+1) (Builtins.builtinStep (lastResponse i)) = _
  rw [delete_last]
  change Builtins.run (((fuel+1)+1)+1) (Builtins.builtinStep (afterDelete i)) = _
  rw [consume_delete]
  change Builtins.run ((fuel+1)+1) (Builtins.builtinStep (deleteResponse i)) = _
  rw [write_length]
  change Builtins.run (fuel+1) (Builtins.builtinStep (afterWrite i)) = _
  rw [consume_write]
  change Builtins.run fuel (Builtins.builtinStep (writeResponse i)) = _
  rw [return_last]

def finalFrame (i : Inputs) : DenseArrayState.Frame (returned i).heap i.array :=
  ArrayPopData.finalFrame i.frame i.positive

theorem final_index_bound (i : Inputs) : ArrayIndexBound.Holds (finalFrame i).object (finalFrame i).length :=
  ArrayPopData.final_bound i.frame.object i.frame.length i.bounded i.positive

theorem elapsed (i : Inputs) : (returned i).elapsed=i.base.elapsed := rfl

theorem free_draws (i : Inputs) : (returned i).freeDrawCount=i.base.freeDrawCount := rfl

end CookieClicker.JavaScript.ArrayPop

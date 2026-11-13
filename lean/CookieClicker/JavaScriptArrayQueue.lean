import CookieClicker.JavaScriptArrayUnshiftBound
import CookieClicker.JavaScriptArrayPopEmpty

/-! Native queue operations retain their caller and all unrelated heap objects.
The notification source chooses when to call the proved pop operation. -/
namespace CookieClicker.JavaScript.ArrayQueue
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem shifted_other {array : ObjectId} (index : Nat) (state : ArrayUnshiftLoop.State array)
    (small : index<256) (within : index≤state.frame.length) (other : ObjectId) (different : array≠other) :
    checkedObject (ArrayUnshiftLoop.shift index state small within).heap other=checkedObject state.heap other := by
  induction index generalizing state with
  | zero => rfl
  | succ index ih =>
    rw [ArrayUnshiftLoop.shift,ih]
    exact DenseArray.written_heap_other _ _ _ _ _ _ _ different

theorem unshift_other (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) (other : ObjectId) (different : array≠other) :
    checkedObject (ArrayUnshiftLoop.returned base array frame value small).heap other=checkedObject base.heap other := by
  change checkedObject (DenseArrayState.lengthHeap (ArrayUnshiftFinish.insertedFrame _ _ _ _)) other = _
  rw [DenseArrayState.length_other _ other different]
  change checkedObject (DenseArray.writtenHeap _ array _ _ 0 value) other = _
  rw [DenseArray.written_heap_other _ _ _ _ _ _ _ different]
  exact shifted_other frame.length (ArrayUnshiftLoop.initial base array frame) small (Nat.le_refl _) other different

theorem shifted_environments {array : ObjectId} (index : Nat) (state : ArrayUnshiftLoop.State array)
    (small : index<256) (within : index≤state.frame.length) :
    (ArrayUnshiftLoop.shift index state small within).heap.environments=state.heap.environments := by
  induction index generalizing state with
  | zero => rfl
  | succ index ih => rw [ArrayUnshiftLoop.shift,ih]; rfl

theorem unshift_environments (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) :
    (ArrayUnshiftLoop.returned base array frame value small).heap.environments=base.heap.environments :=
  shifted_environments frame.length (ArrayUnshiftLoop.initial base array frame) small (Nat.le_refl _)

theorem unshift_context (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) :
    (ArrayUnshiftLoop.returned base array frame value small).context=base.context := rfl

theorem unshift_continuation (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) :
    (ArrayUnshiftLoop.returned base array frame value small).continuation=base.continuation := rfl

theorem unshift_elapsed (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) :
    (ArrayUnshiftLoop.returned base array frame value small).elapsed=base.elapsed := rfl

theorem unshift_free_draws (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) :
    (ArrayUnshiftLoop.returned base array frame value small).freeDrawCount=base.freeDrawCount := rfl

def popInputs (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) (bounded : ArrayIndexBound.Holds frame.object frame.length) : ArrayPop.Inputs := {
  base := ArrayUnshiftLoop.returned base array frame value small
  array := array
  frame := ArrayUnshiftLoop.finalFrame base array frame value small
  bounded := ArrayUnshiftBound.final base array frame value small bounded
  positive := by rw [ArrayUnshiftLoop.final_length]; omega }

theorem pop_after_unshift (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) (bounded : ArrayIndexBound.Holds frame.object frame.length) (fuel : Nat) :
    Builtins.run (9+fuel) (ArrayPop.request (popInputs base array frame value small bounded)) =
      Builtins.run fuel (ArrayPop.returned (popInputs base array frame value small bounded)) :=
  ArrayPop.complete_call _ fuel

theorem popped_length (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) (bounded : ArrayIndexBound.Holds frame.object frame.length) :
    (ArrayPop.finalFrame (popInputs base array frame value small bounded)).length=frame.length := by
  change (ArrayUnshiftLoop.finalFrame base array frame value small).length-1=frame.length
  rw [ArrayUnshiftLoop.final_length]
  omega

theorem popped_first (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) (bounded : ArrayIndexBound.Holds frame.object frame.length) :
    (ArrayPop.finalFrame (popInputs base array frame value small bounded)).values 0=value :=
  ArrayUnshiftLoop.final_first base array frame value small

theorem popped_following (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) (bounded : ArrayIndexBound.Holds frame.object frame.length)
    (slot : Nat) (positive : 0<slot) (included : slot≤frame.length) :
    (ArrayPop.finalFrame (popInputs base array frame value small bounded)).values slot=frame.values (slot-1) :=
  ArrayUnshiftLoop.final_following base array frame value small slot positive included

theorem pop_other (i : ArrayPop.Inputs) (other : ObjectId) (different : i.array≠other) :
    checkedObject (ArrayPop.returned i).heap other=checkedObject i.base.heap other :=
  ArrayPopData.final_other _ _ _ _ other different

theorem pop_environments (i : ArrayPop.Inputs) : (ArrayPop.returned i).heap.environments=i.base.heap.environments := rfl

theorem pop_context (i : ArrayPop.Inputs) : (ArrayPop.returned i).context=i.base.context := rfl

theorem pop_continuation (i : ArrayPop.Inputs) : (ArrayPop.returned i).continuation=i.base.continuation := rfl

end CookieClicker.JavaScript.ArrayQueue

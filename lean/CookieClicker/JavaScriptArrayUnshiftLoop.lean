import CookieClicker.JavaScriptArrayUnshiftFinish

/-! The native backward copy loop terminates and preserves each queue value. -/
namespace CookieClicker.JavaScript.ArrayUnshiftLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure State (array : ObjectId) where
  heap : Heap
  frame : DenseArrayState.Frame heap array

def machine {array : ObjectId} (base : Machine) (state : State array) : Machine := {base with heap := state.heap}

def copy {array : ObjectId} (state : State array) (index : Nat) (small : index < 256) (within : index ≤ state.frame.length) : State array := {
  heap := DenseArrayState.writtenHeap state.frame index (state.frame.values (index-1))
  frame := DenseArrayState.write state.frame index (state.frame.values (index-1)) small within }

def shift {array : ObjectId} : (index : Nat) → (state : State array) → index < 256 → index ≤ state.frame.length → State array
  | 0,state,_,_ => state
  | index+1,state,small,within =>
    shift index (copy state (index+1) small within) (by omega)
      (by change index ≤ DenseArray.nextLength state.frame.length (index+1); unfold DenseArray.nextLength; split <;> omega)

theorem actual_shift {array : ObjectId} (base : Machine) (original : Nat) (value : Value) (index : Nat)
    (state : State array) (small : index < 256) (within : index ≤ state.frame.length) (fuel : Nat) :
    Builtins.run (5*index+fuel) (ArrayUnshift.next (machine base state) array original index value) =
      Builtins.run fuel (ArrayUnshift.next (machine base (shift index state small within)) array original 0 value) := by
  induction index generalizing state with
  | zero => simp [shift]
  | succ index ih =>
    rw [show 5*(index+1)+fuel=5+(5*index+fuel) by omega,
      ArrayUnshift.actual_copy (machine base state) array state.frame original (index+1) value (by omega) small within]
    change Builtins.run (5*index+fuel)
      (ArrayUnshift.next (machine base (copy state (index+1) small within)) array original index value) = _
    exact ih _ _ _

theorem shifted_length_inside {array : ObjectId} (index : Nat) (state : State array)
    (small : index < 256) (within : index ≤ state.frame.length) (inside : index < state.frame.length) :
    (shift index state small within).frame.length = state.frame.length := by
  induction index generalizing state with
  | zero => rfl
  | succ index ih =>
    rw [shift,ih]
    · simp [copy,DenseArrayState.write,DenseArray.nextLength,show ¬ index+1≥state.frame.length by omega]
    · change index < DenseArray.nextLength state.frame.length (index+1)
      unfold DenseArray.nextLength
      split <;> omega

theorem shifted_full_length {array : ObjectId} (index : Nat) (state : State array) (small : index < 256)
    (length : state.frame.length = index) :
    DenseArray.nextLength (shift index state small (by omega)).frame.length 0 = index+1 := by
  cases index with
  | zero => simp [length,shift,DenseArray.nextLength]
  | succ index =>
    rw [shift,shifted_length_inside]
    · simp [copy,DenseArrayState.write,DenseArray.nextLength,length]
    · change index < DenseArray.nextLength state.frame.length (index+1)
      simp only [DenseArray.nextLength,length,Nat.le_refl,↓reduceIte]
      omega

theorem unchanged_above {array : ObjectId} (index : Nat) (state : State array)
    (small : index < 256) (within : index ≤ state.frame.length) (slot : Nat) (above : index < slot) :
    (shift index state small within).frame.values slot = state.frame.values slot := by
  induction index generalizing state with
  | zero => rfl
  | succ index ih =>
    rw [shift,ih _ _ _ (by omega)]
    simp [copy,DenseArrayState.write,DenseArray.nextValues,show slot≠index+1 by omega]

theorem shifted_value {array : ObjectId} (index : Nat) (state : State array)
    (small : index < 256) (within : index ≤ state.frame.length) (slot : Nat) (positive : 0 < slot) (included : slot ≤ index) :
    (shift index state small within).frame.values slot = state.frame.values (slot-1) := by
  induction index generalizing state with
  | zero => omega
  | succ index ih =>
    rw [shift]
    by_cases last : slot=index+1
    · rw [unchanged_above _ _ _ _ slot (by omega)]
      simp [copy,DenseArrayState.write,DenseArray.nextValues,last]
    · rw [ih _ _ _ (by omega)]
      simp [copy,DenseArrayState.write,DenseArray.nextValues,show slot-1≠index+1 by omega]

def initial (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) : State array := ⟨base.heap,frame⟩
def shifted (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array) (small : frame.length < 256) :=
  shift frame.length (initial base array frame) small (Nat.le_refl _)

def returned (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) :=
  ArrayUnshiftFinish.returned (machine base (shifted base array frame small)) array
    (shifted base array frame small).frame frame.length value

theorem complete_loop (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) (fuel : Nat) :
    Builtins.run (5*frame.length+5+fuel) (ArrayUnshift.next base array frame.length frame.length value) =
      Builtins.run fuel (returned base array frame value small) := by
  rw [Nat.add_assoc]
  change Builtins.run (5*frame.length+(5+fuel))
    (ArrayUnshift.next (machine base (initial base array frame)) array frame.length frame.length value) = _
  rw [actual_shift]
  exact ArrayUnshiftFinish.actual_finish _ _ _ _ _ (shifted_full_length frame.length (initial base array frame) small rfl) fuel

def finalFrame (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) : DenseArrayState.Frame (returned base array frame value small).heap array :=
  DenseArrayState.finish (ArrayUnshiftFinish.insertedFrame (machine base (shifted base array frame small)) array
    (shifted base array frame small).frame value)

theorem final_length (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) : (finalFrame base array frame value small).length = frame.length+1 :=
  shifted_full_length frame.length (initial base array frame) small rfl

theorem final_first (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) : (finalFrame base array frame value small).values 0 = value := by
  simp [finalFrame,DenseArrayState.finish,ArrayUnshiftFinish.insertedFrame,DenseArrayState.write,DenseArray.nextValues]

theorem final_following (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256) (slot : Nat) (positive : 0 < slot) (included : slot ≤ frame.length) :
    (finalFrame base array frame value small).values slot = frame.values (slot-1) := by
  simp only [finalFrame,DenseArrayState.finish,ArrayUnshiftFinish.insertedFrame,DenseArrayState.write,
    DenseArray.nextValues,show slot≠0 by omega,↓reduceIte]
  exact shifted_value frame.length (initial base array frame) small (Nat.le_refl _) slot positive included

end CookieClicker.JavaScript.ArrayUnshiftLoop

import CookieClicker.JavaScriptNativeMixkeyFrame

/-! Native traversal of the 256 entropy UTF16 units by the retained source.
The cost here counts evaluator steps only; it is not game time. -/
namespace CookieClicker.JavaScript.NativeMixkeyTraversal
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open NativeMixkey NativeMixkeyLoop NativeMixkeyCode NativeMixkeyFinish NativeMixkeyFrame

structure State (i : Inputs) where
  objects : Array JSObject
  frame : NativeMixkeyFrame.Frame i objects
  smear : Option UInt64
  index : Nat
  previous : Option Value
  originalLength : Nat
  originalBound : originalLength≤256
  within : index≤256
  length_eq : frame.length = max originalLength index

def machine (i : Inputs) (state : State i) :=
  atGuard (base i) (scope i) (seed i) (key i) state.objects (smearValue state.smear) state.index state.previous

theorem slot_adjacent (original index : Nat) (small : index<256) :
    Nat.mod index 256 ≤ max original index := by
  change index % 256 ≤ max original index
  rw [Nat.mod_eq_of_lt small]
  exact Nat.le_max_right _ _

theorem length_next (original index : Nat) (small : index<256) :
    MixkeyArray.nextLength (max original index) (Nat.mod index 256) = max original (index+1) := by
  have mod : Nat.mod index 256=index := Nat.mod_eq_of_lt small
  rw [mod]
  simp only [MixkeyArray.nextLength]
  split <;> omega

def guardFrame (i : Inputs) (state : State i) :=
  NativeMixkeyFrame.append i state.objects state.frame (stringWrapper (base i) (seed i))

def methodFrame (i : Inputs) (state : State i) :=
  NativeMixkeyFrame.append i (state.objects.push (stringWrapper (base i) (seed i))) (guardFrame i state)
    (stringWrapper (base i) (seed i))

def iteration (i : Inputs) (state : State i) (bound : state.index < (seed i).size) :=
  NativeMixkeyFrame.iteration i (state.objects.push (stringWrapper (base i) (seed i))) (guardFrame i state)
    state.smear state.index state.previous bound

def newSmear (i : Inputs) (state : State i) := nextSmear state.smear state.frame.length state.frame.bytes state.index

def newByte (i : Inputs) (state : State i) (bound : state.index < (seed i).size) :=
  byte (newSmear i state) (seed i)[state.index]

def advancedFrame (i : Inputs) (state : State i) (bound : state.index < (seed i).size) :=
  NativeMixkeyFrame.write i
    ((state.objects.push (stringWrapper (base i) (seed i))).push (stringWrapper (base i) (seed i)))
    (methodFrame i state) (Nat.mod state.index 256) (newByte i state bound)
    (show Nat.mod state.index 256 < 256 from Nat.mod_lt _ (by decide))
    (by change Nat.mod state.index 256 ≤ state.frame.length
        rw [state.length_eq]; exact slot_adjacent _ _ (by have h:=i.seedSize; change (seed i).size=256 at h; omega))

def advance (i : Inputs) (state : State i) (bound : state.index < (seed i).size) : State i := {
  objects := writeObjects i
    ((state.objects.push (stringWrapper (base i) (seed i))).push (stringWrapper (base i) (seed i)))
    (methodFrame i state) (Nat.mod state.index 256) (newByte i state bound)
  frame := advancedFrame i state bound
  smear := some (newSmear i state)
  index := state.index+1
  previous := some (MixkeyArray.byteValue (newByte i state bound))
  originalLength := state.originalLength
  originalBound := state.originalBound
  within := by have h:=i.seedSize; change (seed i).size=256 at h; omega
  length_eq := by change MixkeyArray.nextLength state.frame.length (Nat.mod state.index 256) = max state.originalLength (state.index+1)
                  rw [state.length_eq,length_next _ _ (by have h:=i.seedSize; change (seed i).size=256 at h; omega)] }

theorem actual_advance (i : Inputs) (state : State i) (bound : state.index < (seed i).size) (fuel : Nat) :
    Builtins.run (93+fuel) (machine i state) = Builtins.run fuel (machine i (advance i state bound)) := by
  unfold machine
  rw [show 93+fuel=14+(79+fuel) by omega,actual_guard _ _ _ _ _ _ _ _ (show (seed i).size=256 from i.seedSize) state.within]
  simp only [bound,↓reduceIte]
  change Builtins.run (79+fuel) (NativeMixkeyIteration.start (iteration i state bound)) = _
  rw [NativeMixkeyIteration.actual_iteration]
  rfl

def traverse (i : Inputs) : (count : Nat) → (state : State i) →
    state.index + count ≤ (seed i).size → State i
  | 0,state,_ => state
  | count+1,state,fits =>
    traverse i count (advance i state (by omega)) (by change state.index+1+count ≤ (seed i).size; omega)

theorem traverse_index (i : Inputs) (count : Nat) (state : State i) (fits : state.index+count ≤ (seed i).size) :
    (traverse i count state fits).index = state.index+count := by
  induction count generalizing state with
  | zero => simp [traverse]
  | succ count ih =>
    simp only [traverse,ih,advance]
    omega

theorem actual_traverse (i : Inputs) (count : Nat) (state : State i) (fits : state.index+count ≤ (seed i).size) (fuel : Nat) :
    Builtins.run (93*count+fuel) (machine i state) = Builtins.run fuel (machine i (traverse i count state fits)) := by
  induction count generalizing state with
  | zero => simp [traverse]
  | succ count ih =>
    rw [show 93*(count+1)+fuel=93+(93*count+fuel) by omega]
    rw [actual_advance i state (by omega)]
    exact ih _ _

def exited (i : Inputs) (state : State i) :=
  atExit (base i) (scope i) (seed i) (key i) (state.objects.push (stringWrapper (base i) (seed i)))
    (smearValue state.smear) state.index state.previous

theorem actual_exit (i : Inputs) (state : State i) (atEnd : state.index = (seed i).size) (fuel : Nat) :
    Builtins.run (14+fuel) (machine i state) = Builtins.run fuel (exited i state) := by
  unfold machine
  rw [actual_guard _ _ _ _ _ _ _ _ (show (seed i).size=256 from i.seedSize) state.within]
  simp [exited,atEnd]

theorem complete_source_loop (i : Inputs) (state : State i) (within : state.index ≤ (seed i).size) (fuel : Nat) :
    Builtins.run (93*((seed i).size-state.index)+14+fuel) (machine i state) =
      Builtins.run fuel (exited i (traverse i ((seed i).size-state.index) state (by omega))) := by
  rw [Nat.add_assoc,actual_traverse i ((seed i).size-state.index) state (by omega)]
  apply actual_exit
  rw [traverse_index]
  omega

def initial (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) : State i := {
  objects := objectsWithArgument (base i) (seed i) (key i) callee
  frame := NativeMixkeyFrame.append i (base i).heap.objects frame
    (argumentObject (base i) (seed i) (key i) callee)
  smear := none, index := 0, previous := none
  originalLength := frame.length
  originalBound := frame.shape.bound
  within := by omega
  length_eq := by change frame.length=max frame.length 0; omega }

def traversed (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) :=
  traverse i (seed i).size (initial i frame callee) (by change 0+(seed i).size≤(seed i).size; omega)

theorem actual_source_loop (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) (fuel : Nat) :
    Builtins.run (26+93*(seed i).size+14+fuel)
      (prepared (base i) (scope i) (seed i) (key i) callee) =
      Builtins.run fuel (exited i (traversed i frame callee)) := by
  rw [show 26+93*(seed i).size+14+fuel = 8+(18+(93*(seed i).size+14+fuel)) by omega,
    actual_hoist,actual_initializers]
  change Builtins.run (93*(seed i).size+14+fuel) (machine i (initial i frame callee)) = _
  have loop := complete_source_loop i (initial i frame callee) (by change 0≤(seed i).size; omega) fuel
  simpa only [initial,traversed,Nat.sub_zero] using loop

theorem traversed_index (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) :
    (traversed i frame callee).index = (seed i).size := by
  rw [traversed,traverse_index]
  simp [initial]

theorem traversed_length (i : Inputs) (frame : NativeMixkeyFrame.Frame i (base i).heap.objects)
    (callee : ObjectId) :
    (traversed i frame callee).frame.length = 256 := by
  rw [(traversed i frame callee).length_eq,traversed_index,show (seed i).size=256 from i.seedSize]
  exact Nat.max_eq_right (traversed i frame callee).originalBound

end CookieClicker.JavaScript.NativeMixkeyTraversal

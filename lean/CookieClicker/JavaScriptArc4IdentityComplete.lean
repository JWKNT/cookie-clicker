import CookieClicker.JavaScriptArc4IdentityLoop

/-! The entire retained first ARC4 loop, including its final failed guard. -/
namespace CookieClicker.JavaScript.Arc4IdentityComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals Arc4Identity Arc4IdentityLoop

structure Stage (i : Inputs) (argument array : Nat) (v : Values) where
  cursor : Cursor i argument array v
  previous : Option Value

def advance {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v)
    (small : stage.cursor.index<256) : Stage i argument array v :=
  ⟨next stage.cursor small,some (.number (Number.ofNat stage.cursor.index))⟩

def traverse {i : Inputs} {argument array : Nat} {v : Values} :
    (count : Nat) → (stage : Stage i argument array v) → stage.cursor.index+count≤256 → Stage i argument array v
  | 0,stage,_ => stage
  | count+1,stage,bound => traverse count (advance stage (by omega)) (by simp [advance,next]; omega)

theorem final_index {i : Inputs} {argument array : Nat} {v : Values}
    (count : Nat) (stage : Stage i argument array v) (bound : stage.cursor.index+count≤256) :
    (traverse count stage bound).cursor.index = stage.cursor.index+count := by
  induction count generalizing stage with
  | zero => simp [traverse]
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    simp [advance,next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem actual_iterations {i : Inputs} {argument array : Nat} {v : Values}
    (count : Nat) (stage : Stage i argument array v) (bound : stage.cursor.index+count≤256)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (33*count+fuel) (start stage.cursor stage.previous tail) =
      Builtins.run fuel (start (traverse count stage bound).cursor (traverse count stage bound).previous tail) := by
  induction count generalizing stage with
  | zero => simp [traverse]
  | succ count induction =>
    have small : stage.cursor.index<256 := by omega
    rw [show 33*(count+1)+fuel=33+(33*count+fuel) by omega,
      actual_iteration stage.cursor stage.previous tail small]
    change Builtins.run (33*count+fuel)
      (start (advance stage small).cursor (advance stage small).previous tail) = _
    rw [induction (advance stage small)]
    rfl

def finished {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v) :=
  traverse (256-stage.cursor.index) stage (by have := stage.cursor.small; omega)

def result {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v)
    (tail : List Frame) : Machine :=
  let final := finished stage
  atExit i final.cursor.objects argument array final.cursor.index v final.previous tail

theorem finished_index {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v) :
    (finished stage).cursor.index = 256 := by
  rw [finished,final_index]
  have := stage.cursor.small
  omega

theorem actual_complete_loop {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (33*(256-stage.cursor.index)+10+fuel) (start stage.cursor stage.previous tail) =
      Builtins.run fuel (result stage tail) := by
  rw [show 33*(256-stage.cursor.index)+10+fuel=33*(256-stage.cursor.index)+(10+fuel) by omega,
    actual_iterations (256-stage.cursor.index) stage (by have := stage.cursor.small; omega)]
  change Builtins.run (10+fuel) (start (finished stage).cursor (finished stage).previous tail) = _
  unfold start
  rw [actual_guard _ _ _ _ _ _ _ _ (finished stage).cursor.small]
  simp only [result,finished_index,Nat.lt_irrefl,↓reduceIte]

theorem complete_length {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v) :
    (finished stage).cursor.frame.length = 256 := by
  rw [(finished stage).cursor.length,finished_index]

theorem complete_permutation {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v)
    (slot : Nat) (small : slot<256) :
    (finished stage).cursor.frame.values slot = .number (Number.ofNat slot) :=
  (finished stage).cursor.initialized slot (by simpa only [finished_index] using small)

theorem complete_own_property {i : Inputs} {argument array : Nat} {v : Values} (stage : Stage i argument array v)
    (slot : Nat) (small : slot<256) :
    ownProperty (finished stage).cursor.frame.object (MixkeyIndex.key slot) =
      some (.data (.number (Number.ofNat slot)) true true true) := by
  rw [(finished stage).cursor.frame.shape.slots slot small,complete_length]
  simp only [small,↓reduceIte,DenseArray.descriptor,complete_permutation stage slot small]

end CookieClicker.JavaScript.Arc4IdentityComplete

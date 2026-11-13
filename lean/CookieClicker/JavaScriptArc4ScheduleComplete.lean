import CookieClicker.JavaScriptArc4ScheduleCursor

/-! All256 source key-scheduling iterations, retaining the exact byte swap
recurrence and the actual final failed native loop guard. -/
namespace CookieClicker.JavaScript.Arc4ScheduleComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4ScheduleCursor Arc4Locals

structure Stage where
  cursor : Cursor
  previous : Option Value

def advance (stage : Stage) (small : stage.cursor.index<256) : Stage :=
  ⟨next stage.cursor small,Arc4ScheduleCursor.previous stage.cursor small⟩

def traverse : (count : Nat) → (stage : Stage) → stage.cursor.index+count≤256 → Stage
  | 0,stage,_ => stage
  | count+1,stage,bound => traverse count (advance stage (by omega)) (by simp [advance,next]; omega)

theorem final_index (count : Nat) (stage : Stage) (bound : stage.cursor.index+count≤256) :
    (traverse count stage bound).cursor.index = stage.cursor.index+count := by
  induction count generalizing stage with
  | zero => simp [traverse]
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    simp [advance,next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem actual_iterations (count : Nat) (stage : Stage) (bound : stage.cursor.index+count≤256)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (114*count+fuel) (start stage.cursor stage.previous tail) =
      Builtins.run fuel (start (traverse count stage bound).cursor (traverse count stage bound).previous tail) := by
  induction count generalizing stage with
  | zero => simp [traverse]
  | succ count induction =>
    have small : stage.cursor.index<256 := by omega
    rw [show 114*(count+1)+fuel=114+(114*count+fuel) by omega,
      Arc4ScheduleCursor.actual_iteration stage.cursor stage.previous tail small]
    change Builtins.run (114*count+fuel)
      (start (advance stage small).cursor (advance stage small).previous tail) = _
    rw [induction (advance stage small)]
    rfl

def finished (stage : Stage) := traverse (256-stage.cursor.index) stage (by have := stage.cursor.small; omega)
def exit (cursor : Cursor) (previous : Option Value) (tail : List Frame) : Machine :=
  machine cursor.source cursor.objects cursor.argument (Arc4ScheduleCursor.values cursor) (.completion (.normal previous)) tail

theorem finished_index (stage : Stage) : (finished stage).cursor.index=256 := by
  rw [finished,final_index]
  have := stage.cursor.small
  omega

theorem closed_guard : binary .greater (.number (Number.ofNat 256)) (.number (Number.ofNat 256)) = .ok (.boolean false) := rfl

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h closed_guard

theorem actual_exit (cursor : Cursor) (previous : Option Value) (tail : List Frame)
    (done : cursor.index=256) (fuel : Nat) :
    Builtins.run (10+fuel) (start cursor previous tail) = Builtins.run fuel (exit cursor previous tail) := by
  rw [Nat.add_comm 10 fuel]
  simp only [start,exit,Arc4ScheduleCursor.values,done]
  cbv

theorem actual_complete_loop (stage : Stage) (tail : List Frame) (fuel : Nat) :
    Builtins.run (114*(256-stage.cursor.index)+10+fuel) (start stage.cursor stage.previous tail) =
      Builtins.run fuel (exit (finished stage).cursor (finished stage).previous tail) := by
  rw [show 114*(256-stage.cursor.index)+10+fuel=114*(256-stage.cursor.index)+(10+fuel) by omega,
    actual_iterations (256-stage.cursor.index) stage (by have := stage.cursor.small; omega)]
  exact actual_exit (finished stage).cursor (finished stage).previous tail (finished_index stage) fuel

theorem retained_key_object (count : Nat) (stage : Stage) (bound : stage.cursor.index+count≤256) :
    (traverse count stage bound).cursor.keyFrame.object=stage.cursor.keyFrame.object := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    rfl

theorem retained_key_bytes (count : Nat) (stage : Stage) (bound : stage.cursor.index+count≤256) :
    (traverse count stage bound).cursor.keyFrame.bytes=stage.cursor.keyFrame.bytes := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    rfl

end CookieClicker.JavaScript.Arc4ScheduleComplete

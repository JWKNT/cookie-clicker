import CookieClicker.JavaScriptRetainedArc4GenerateCursor

/-! The complete bounded native generator loop. Every output byte follows
the actual swap order, and the final failed guard stores minus one. -/
namespace CookieClicker.JavaScript.RetainedArc4GenerateComplete
open RetainedArc4GenerateCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Stage where
  cursor : Cursor
  previous : Option Value

def advance (stage : Stage) : Stage := ⟨next stage.cursor,RetainedArc4GenerateCursor.previous stage.cursor⟩
def traverse : (count : Nat) → (stage : Stage) → count≤stage.cursor.remaining → Stage
  | 0,stage,_ => stage
  | count+1,stage,bound => traverse count (advance stage) (by simp [advance,next]; omega)

theorem remaining_after (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining) :
    (traverse count stage bound).cursor.remaining=stage.cursor.remaining-count := by
  induction count generalizing stage with
  | zero => simp [traverse]
  | succ count induction =>
    simp only [traverse]
    rw [induction]
    simp only [advance,next]
    omega

theorem actual_iterations (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*count+fuel) (start stage.cursor stage.previous tail)=
      Builtins.run fuel (start (traverse count stage bound).cursor (traverse count stage bound).previous tail) := by
  induction count generalizing stage with
  | zero => simp [traverse]
  | succ count induction =>
    have nonempty : 0<stage.cursor.remaining := by omega
    rw [show 136*(count+1)+fuel=136+(136*count+fuel) by omega,
      actual_iteration stage.cursor stage.previous tail nonempty]
    change Builtins.run (136*count+fuel) (start (advance stage).cursor (advance stage).previous tail)=_
    rw [induction (advance stage)]
    rfl

def finished (stage : Stage) := traverse stage.cursor.remaining stage (Nat.le_refl _)
def exit (cursor : Cursor) (previous : Option Value) (tail : List Frame) :=
  RetainedArc4GeneratorLocals.machine cursor.source cursor.objects cursor.argument
    {values cursor with a := .number 13830554455654793216} (.completion (.normal previous)) tail

theorem finished_remaining (stage : Stage) : (finished stage).cursor.remaining=0 := by
  rw [finished,remaining_after,Nat.sub_self]

theorem actual_exit (cursor : Cursor) (previous : Option Value) (tail : List Frame)
    (done : cursor.remaining=0) (fuel : Nat) :
    Builtins.run (8+fuel) (start cursor previous tail)=Builtins.run fuel (exit cursor previous tail) := by
  have native := RetainedArc4GenerateGuard.actual_guard cursor.source cursor.objects cursor.argument cursor.remaining
    (values cursor) previous tail cursor.small fuel
  simpa only [RetainedArc4GenerateGuard.start,RetainedArc4GenerateGuard.values,RetainedArc4GenerateGuard.atExit,
    RetainedArc4GenerateGuard.afterValues,RetainedArc4GenerateGuard.decremented,done,↓reduceIte,start,values,exit] using native

theorem actual_complete_loop (stage : Stage) (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*stage.cursor.remaining+8+fuel) (start stage.cursor stage.previous tail)=
      Builtins.run fuel (exit (finished stage).cursor (finished stage).previous tail) := by
  rw [show 136*stage.cursor.remaining+8+fuel=136*stage.cursor.remaining+(8+fuel) by omega,
    actual_iterations stage.cursor.remaining stage (Nat.le_refl _)]
  exact actual_exit (finished stage).cursor (finished stage).previous tail (finished_remaining stage) fuel

theorem actual_discard_loop (stage : Stage) (count : stage.cursor.remaining=256) (tail : List Frame) (fuel : Nat) :
    Builtins.run (34824+fuel) (start stage.cursor stage.previous tail)=
      Builtins.run fuel (exit (finished stage).cursor (finished stage).previous tail) := by
  have native := actual_complete_loop stage tail fuel
  simpa only [count] using native

end CookieClicker.JavaScript.RetainedArc4GenerateComplete

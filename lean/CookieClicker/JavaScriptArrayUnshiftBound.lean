import CookieClicker.JavaScriptArrayUnshiftCall
import CookieClicker.JavaScriptArrayIndexBound

/-! Every actual unshift write preserves the native indexed-property bound. -/
namespace CookieClicker.JavaScript.ArrayUnshiftBound
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem shifted {array : ObjectId} (index : Nat) (state : ArrayUnshiftLoop.State array)
    (small : index < 256) (within : index ≤ state.frame.length)
    (bounded : ArrayIndexBound.Holds state.frame.object state.frame.length) :
    ArrayIndexBound.Holds (ArrayUnshiftLoop.shift index state small within).frame.object
      (ArrayUnshiftLoop.shift index state small within).frame.length := by
  induction index generalizing state with
  | zero => exact bounded
  | succ index ih =>
    rw [ArrayUnshiftLoop.shift]
    apply ih
    exact ArrayIndexBound.written bounded (index+1) _ small

theorem final (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length < 256)
    (bounded : ArrayIndexBound.Holds frame.object frame.length) :
    ArrayIndexBound.Holds (ArrayUnshiftLoop.finalFrame base array frame value small).object
      (ArrayUnshiftLoop.finalFrame base array frame value small).length := by
  have preserved := shifted frame.length (ArrayUnshiftLoop.initial base array frame) small (Nat.le_refl _) bounded
  have inserted := ArrayIndexBound.written preserved 0 value (by decide)
  exact ArrayIndexBound.length_changed inserted _ true

end CookieClicker.JavaScript.ArrayUnshiftBound

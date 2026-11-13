import CookieClicker.JavaScriptTimestampMixkeyFinish
import CookieClicker.JavaScriptBrowserCoreStep

/-! Retained source prefixes under the composed browser handlers. -/
namespace CookieClicker.JavaScript.TimestampMixkeyFinishRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkeyFinish
open TimestampMixkey TimestampMixkeyLoop TimestampMixkeyCode

attribute [local cbv_opaque] base scope seed key heap localIndex bodyHeap MixkeyIndex.key Nat.mod Number.ofNat
  Number.add binary MixkeyArray.byteValue MixkeyArray.maskedByte

attribute [local cbv_eval] native_add native_mask

theorem actual_mask (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size) (fuel : Nat) :
    BrowserRuntime.run (3+fuel) {state with machine := (afterCode i objects d index previous method bound)} =
      BrowserRuntime.run fuel {state with machine := (atWrite i objects d index previous method bound)} := by
  rw [Nat.add_comm 3 fuel]
  cbv


attribute [local cbv_opaque] nextObjects byte total

theorem actual_continue (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size)
    (object : JSObject) (length fuel : Nat) :
    BrowserRuntime.run (2+fuel) {state with machine := (afterWrite i objects d index previous method bound object length)} =
      BrowserRuntime.run fuel {state with machine := (nextGuard i objects d index bound object length)} := by
  rw [Nat.add_comm 2 fuel]
  cbv



theorem actual_write (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size)
    (object : JSObject) (length : Nat) (bytes : Nat → UInt8)
    (shape : MixkeyArray.Shape object length bytes)
    (present : checkedObject (heap i objects (.number d) (index+1)) (key i) = .ok object)
    (prototype : MixkeyArray.PrototypeFrame (heap i objects (.number d) (index+1)) object)
    (room : 2 ≤ objects.size) (keyBound : key i < objects.size) :
    BrowserRuntime.step {state with machine := atWrite i objects d index previous method bound} =
      {state with machine := afterWrite i objects d index previous method bound object length} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,
    TimestampMixkeyFinish.actual_write i objects d index previous method bound object length bytes shape present prototype room keyBound]
  rfl

end CookieClicker.JavaScript.TimestampMixkeyFinishRuntime

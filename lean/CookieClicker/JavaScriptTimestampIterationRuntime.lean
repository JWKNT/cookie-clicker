import CookieClicker.JavaScriptTimestampMixkeyIteration
import CookieClicker.JavaScriptTimestampMixkeyLoopRuntime
import CookieClicker.JavaScriptTimestampMixkeyCodeRuntime
import CookieClicker.JavaScriptTimestampMixkeyFinishRuntime

/-! One complete retained timestamp-mixing iteration through browser dispatch. -/
namespace CookieClicker.JavaScript.TimestampIterationRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey TimestampMixkeyLoop TimestampMixkeyCode TimestampMixkeyFinish
open TimestampMixkeyIteration

theorem actual_iteration (state : Browser.State) (i : TimestampMixkeyIteration.Inputs) (fuel : Nat) :
    BrowserRuntime.run (79+fuel) {state with machine := TimestampMixkeyIteration.start i} =
      BrowserRuntime.run fuel {state with machine := finish i} := by
  unfold TimestampMixkeyIteration.start
  rw [show 79+fuel=48+((4+(8+((9+(2+(3+((2+fuel)+1)))))+1))+1) by omega]
  rw [TimestampMixkeyLoopRuntime.actual_before_old_byte]
  change BrowserRuntime.run (4+(8+((9+(2+(3+((2+fuel)+1))))+1)))
    (BrowserRuntime.step {state with machine := atOldByte i.source i.objects (smearValue i.smear) i.index i.previous}) = _
  rw [TimestampMixkeyLoopRuntime.actual_read_old_byte state i.source i.objects (smearValue i.smear) i.index i.previous i.object i.length i.bytes
    i.shape i.present i.prototype i.room]
  rw [TimestampMixkeyLoopRuntime.actual_smear]
  change BrowserRuntime.run (8+((9+(2+(3+((2+fuel)+1))))+1))
    {state with machine := startCode i.source i.objects (smear i) i.index i.previous} = _
  rw [TimestampMixkeyCodeRuntime.actual_method_prefix]
  change BrowserRuntime.run (9+(2+(3+((2+fuel)+1))))
    (BrowserRuntime.step {state with machine := atMethod i.source i.objects (smear i) i.index i.previous}) = _
  rw [TimestampMixkeyCodeRuntime.actual_method_lookup state i.source i.objects (smear i) i.index i.previous i.stringFrame]
  change BrowserRuntime.run (9+(2+(3+((2+fuel)+1))))
    {state with machine := {atMethod i.source (pushed i) (smear i) i.index i.previous with control := .expressionResult (.value (.object i.stringFrame.method))}} = _
  rw [TimestampMixkeyCodeRuntime.actual_postincrement]
  rw [TimestampMixkeyCodeRuntime.actual_builtin_call state i.source (pushed i) (smear i) i.index i.previous i.stringFrame.method i.methodObject
    (methodPresent i) i.methodKind i.bound]
  rw [TimestampMixkeyFinishRuntime.actual_mask]
  change BrowserRuntime.run (2+fuel)
    (BrowserRuntime.step {state with machine := atWrite i.source (pushed i) (smear i) i.index i.previous i.stringFrame.method i.bound}) = _
  rw [TimestampMixkeyFinishRuntime.actual_write state i.source (pushed i) (smear i) i.index i.previous i.stringFrame.method i.bound i.object i.length i.bytes
    i.shape (writePresent i) (writePrototype i)
    (by have := i.room; simp only [pushed,Array.size_push]; omega)
    (by simpa only [pushed,Array.size_push] using Nat.lt_succ_of_lt i.keyBound)]
  rw [TimestampMixkeyFinishRuntime.actual_continue]
  rfl

end CookieClicker.JavaScript.TimestampIterationRuntime

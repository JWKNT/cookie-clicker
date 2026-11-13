import CookieClicker.JavaScriptTimestampMixkeyComplete
import CookieClicker.JavaScriptTimestampTraversalRuntime
import CookieClicker.JavaScriptTimestampMixkeyReturnRuntime
import CookieClicker.JavaScriptMixkeyToStringRuntime

/-! Complete tagged mixkey execution, native apply, source helper and return
under the composed browser runtime, with all represented browser state retained. -/
namespace CookieClicker.JavaScript.TimestampMixkeyRuntimeComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkeyComplete
attribute [local cbv_opaque] global loop state completedHeap text

theorem actual_outer_return (browser : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (3+fuel) {browser with machine := afterInnerReturn i}=
      BrowserRuntime.run fuel {browser with machine := returned i} := by
  change BrowserRuntime.run (3+fuel) {browser with machine := {
    (global i).base with
    heap := completedHeap i
    context := ⟨TimestampMixkey.localIndex (global i).base,TimestampMixkey.localIndex (global i).base,
      .object (global i).base.globalObject,false⟩
    control := .expressionResult (.value (.string (text i)))
    continuation := .returnValue :: .statementList [] (state i).previous ::
      .callBoundary (global i).base.context none :: (global i).base.continuation }} = _
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_complete_helper (browser : Browser.State) (i : Inputs)
    (notSeed : browser.nativeSeedrandom≠some (global i).codes) (fuel : Nat) :
    BrowserRuntime.run (88+93*i.library.seed.size+2*(arrayData i).length+fuel)
      {browser with machine := TimestampMixkey.prepared (global i).base (global i).scope i.library.seed (global i).array i.callee}=
      BrowserRuntime.run fuel {browser with machine := returned i} := by
  rw [show 88+93*i.library.seed.size+2*(arrayData i).length+fuel=
    (26+93*i.library.seed.size+14)+(12+(33+2*(arrayData i).length+(3+fuel))) by omega]
  change BrowserRuntime.run (26+93*(TimestampMixkeyLoop.seed (loop i)).size+14+
    (12+(33+2*(arrayData i).length+(3+fuel))))
    {browser with machine := TimestampMixkey.prepared (TimestampMixkeyLoop.base (loop i)) (TimestampMixkeyLoop.scope (loop i)) (TimestampMixkeyLoop.seed (loop i)) (TimestampMixkeyLoop.key (loop i)) i.callee} = _
  rw [TimestampTraversalRuntime.actual_source_loop browser (loop i) i.frame i.empty i.callee]
  change BrowserRuntime.run (12+(33+2*(arrayData i).length+(3+fuel)))
    {browser with machine := TimestampMixkeyReturn.start (returnInput i)} = _
  rw [TimestampMixkeyReturnRuntime.actual_return_call]
  change BrowserRuntime.run (33+2*(arrayData i).length+(3+fuel))
    {browser with machine := MixkeyToString.start (toStringInput i)} = _
  rw [MixkeyToStringRuntime.actual_source_helper browser (toStringInput i) (arrayData i) notSeed]
  exact actual_outer_return browser i fuel

end CookieClicker.JavaScript.TimestampMixkeyRuntimeComplete

import CookieClicker.JavaScriptTimestampFlattenRuntime

/-! The actual browser capture follows the retained seed argument and flatten path. -/
namespace CookieClicker.JavaScript.SeedRuntimeCapture
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampSeedSetup

theorem invocation_step (state : Browser.State) (base : Machine) (function receiver : Value)
    (arguments : List Value) (construct : Bool) :
    BrowserRuntime.step {state with machine := {base with control := .invoke function receiver arguments construct}} =
      Browser.step {state with machine := {base with control := .invoke function receiver arguments construct}} := rfl

theorem actual_flatten_step (state : Browser.State) (i : Inputs)
    (notMixkey : state.nativeTimestampMixkey ≠ some (flatten i)) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i)=.ok object)
    (kind : object.kind=.function (TimestampSeedFlatten.closure (scope i))) :
    BrowserRuntime.step {state with machine := atFlatten i} =
      {state with machine := TimestampSeedFlatten.prepared (atFlatten i) (scope i) (base i).globalObject (seed i) (flatten i)} := by
  change Browser.step {state with machine := atFlatten i} = _
  have notCaptured : (state.nativeTimestampMixkey == some (flatten i))=false := by simpa using notMixkey
  have internal : Browser.internalStep {state with machine := atFlatten i} =
      {state with machine := Builtins.builtinStep (atFlatten i)} := by
    unfold Browser.internalStep
    change (if state.nativeTimestampMixkey == some (flatten i) then _ else _) = _
    rw [notCaptured]
    rfl
  simp only [Browser.step,internal]
  rw [TimestampSeedSetup.actual_flatten_step i object present kind]
  rfl

theorem actual_flatten_return (state : Browser.State) (i : Inputs)
    (notMixkey : state.nativeTimestampMixkey ≠ some (flatten i)) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i)=.ok object)
    (kind : object.kind=.function (TimestampSeedFlatten.closure (scope i))) (fuel : Nat) :
    BrowserRuntime.run (78+fuel) {state with machine := atFlatten i} =
      BrowserRuntime.run fuel {state with machine := afterFlatten i} := by
  rw [show 78+fuel=(77+fuel)+1 by omega]
  change BrowserRuntime.run (77+fuel) (BrowserRuntime.step {state with machine := atFlatten i}) = _
  rw [actual_flatten_step state i notMixkey object present kind,TimestampFlattenRuntime.actual_prepared_return]
  rfl

attribute [local cbv_opaque] base scope receiver callee seed mixkey flatten libraryBindings libraryOuter
attribute [local cbv_opaque] retainedHeap sourceHeap checkedEnvironment readBinding
  SeedrandomInvocation.localIndex SeedrandomInvocation.argumentIndex Array.push Array.size initialObjects
attribute [local cbv_eval] Array.size_push
attribute [local cbv_eval] retained_checked_local retained_read_j

theorem actual_mixkey_arguments (state : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (5+fuel) {state with machine := afterFlatten i} =
      BrowserRuntime.run fuel {state with machine := atMixkey i} := by
  rw [afterFlatten_view,Nat.add_comm 5 fuel]
  cbv

theorem actual_seedrandom_to_mixkey (state : Browser.State) (i : Inputs)
    (notMixkey : state.nativeTimestampMixkey ≠ some (flatten i)) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i)=.ok object)
    (kind : object.kind=.function (TimestampSeedFlatten.closure (scope i))) (fuel : Nat) :
    BrowserRuntime.run (128+fuel)
      {state with machine := SeedrandomInvocation.preparedText (base i) (scope i) (receiver i) (seed i) (callee i)} =
      BrowserRuntime.run fuel {state with machine := atMixkey i} := by
  rw [show 128+fuel=7+(38+(78+(5+fuel))) by omega,TimestampSeedRuntime.actual_hoist]
  change BrowserRuntime.run (38+(78+(5+fuel))) {state with machine := sourceStart i} = _
  rw [TimestampSeedRuntime.actual_flatten_prefix,actual_flatten_return state i notMixkey object present kind,
    actual_mixkey_arguments]

end CookieClicker.JavaScript.SeedRuntimeCapture

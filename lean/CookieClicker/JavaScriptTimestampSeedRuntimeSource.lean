import CookieClicker.JavaScriptTimestampSeedRuntimeComplete

/-! The source computeLumpType seed expression enters the proved browser
mixing path with its actual Math receiver and captured closure. -/
namespace CookieClicker.JavaScript.TimestampSeedRuntimeSource
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open SeedrandomEntry
attribute [local cbv_opaque] heap localScope globalScope window math seedrandom random windowObject mathObject

attribute [local cbv_opaque] game gameObject seed birth birthText

attribute [local cbv_opaque] checkedEnvironment checkedObject lookupProperty Environment.identifier JSString.ofString binary

attribute [local cbv_opaque] Browser.restoreFreeRandom

attribute [local cbv_eval] checked_global checked_window checked_math window_kind math_kind windowMath_read seedrandom_read identifier_math_explicit

attribute [local cbv_eval] checked_game game_kind windowGame_read seed_read birth_read identifier_game_explicit string_append timestamp_append

theorem actual_seed_argument (browser : Browser.State) (entry : Inputs) (fuel : Nat) :
    BrowserRuntime.run (32+fuel) (start browser entry)=BrowserRuntime.run fuel (atInvoke browser entry) := by
  rw [Nat.add_comm 32 fuel]
  cbv

theorem actual_invocation (browser : Browser.State) (entry : Inputs) (scope : EnvId)
    (object : JSObject) (present : checkedObject entry.host.heap entry.host.seedrandom=.ok object)
    (kind : object.kind=.function (SeedrandomInvocation.closure scope))
    (separate : browser.nativeTimestampMixkey≠some entry.host.seedrandom) (fuel : Nat) :
    BrowserRuntime.run (33+fuel) (start browser entry)=
      BrowserRuntime.run fuel (SeedrandomInvocation.atPrepared browser entry scope) := by
  rw [show 33+fuel=32+(fuel+1) by omega,actual_seed_argument]
  change BrowserRuntime.run fuel (BrowserRuntime.step (atInvoke browser entry)) = _
  rw [SeedrandomInvocation.runtime_invoke browser entry scope object present kind separate]


structure Alignment (browser : Browser.State) (entry : Inputs) (i : TimestampSeedMixing.Inputs) where
  base : i.globals.base=SeedrandomInvocation.callBase browser entry
  seed : i.seed=argument entry
  receiver : i.receiver=entry.host.math
  callee : i.seedrandom=entry.host.seedrandom

theorem mixkey_different (browser : Browser.State) (i : TimestampSeedMixing.Inputs)
    (capture : TimestampSeedRuntimeComplete.Capture i browser) : i.mixkey≠i.seedrandom := by
  intro same
  have objects : (Except.ok i.mixkeyObject : Checked JSObject)=Except.ok capture.seedObject := by
    rw [←i.mixkeyPresent,←capture.present,same]
  have kinds := congrArg JSObject.kind (Except.ok.inj objects)
  rw [i.mixkeyKind,capture.kind] at kinds
  have names := congrArg (fun kind => match kind with
    | .function closure => closure.name
    | _ => none) kinds
  have impossible : some "m"= (none : Option String) := names
  cases impossible

theorem actual_source_path (browser : Browser.State) (entry : Inputs) (i : TimestampSeedMixing.Inputs)
    (aligned : Alignment browser entry i)
    (capture : TimestampSeedRuntimeComplete.Capture i (browserAmbient browser entry)) (fuel : Nat) :
    BrowserRuntime.run (250+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing i)).length+fuel)
      (start browser entry)=
      BrowserRuntime.run fuel (TimestampSeedRuntimeComplete.resultState (browserAmbient browser entry) i) := by
  have present : checkedObject entry.host.heap entry.host.seedrandom=.ok capture.seedObject := by
    simpa only [aligned.base,aligned.callee,SeedrandomInvocation.callBase,ambient,heap] using capture.present
  have notMixkey : browser.nativeTimestampMixkey≠some entry.host.seedrandom := by
    have captured : browser.nativeTimestampMixkey=some i.mixkey := capture.mixCaptured
    rw [captured,←aligned.callee]
    exact fun same => mixkey_different _ i capture (Option.some.inj same)
  have prepared : SeedrandomInvocation.atPrepared browser entry i.globals.scope =
      {browserAmbient browser entry with machine := SeedrandomInvocation.preparedText i.globals.base i.globals.scope i.receiver i.seed i.seedrandom} := by
    simp only [SeedrandomInvocation.atPrepared,aligned.base,aligned.receiver,aligned.seed,aligned.callee]
  rw [show 250+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing i)).length+fuel=
    33+(217+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing i)).length+fuel) by omega,
    actual_invocation browser entry i.globals.scope capture.seedObject present capture.kind notMixkey,prepared]
  exact TimestampSeedRuntimeComplete.actual_complete_path (browserAmbient browser entry) i capture fuel


theorem retained_math_object (browser : Browser.State) (entry : Inputs) (i : TimestampSeedMixing.Inputs)
    (aligned : Alignment browser entry i) :
    checkedObject (TimestampSeedRuntimeComplete.resultState (browserAmbient browser entry) i).machine.heap entry.host.math=
      .ok entry.host.mathObject := by
  apply TimestampSeedRuntimeComplete.retained_object
  simpa only [aligned.base,SeedrandomInvocation.callBase,ambient,heap] using entry.host.mathRead

end CookieClicker.JavaScript.TimestampSeedRuntimeSource

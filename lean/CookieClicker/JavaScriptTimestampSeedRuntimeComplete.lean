import CookieClicker.JavaScriptTimestampSeedRuntimeEntry
import CookieClicker.JavaScriptTimestampMixkeyRuntimeComplete

/-! The retained seedrandom argument selection, flatten, captured timestamp
mixing, native character construction and helper returns form one runtime path.
ARC4 construction and random-function installation follow this endpoint. -/
namespace CookieClicker.JavaScript.TimestampSeedRuntimeComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampSeedMixing

structure Capture (i : Inputs) (browser : Browser.State) where
  seedObject : JSObject
  present : checkedObject i.globals.base.heap i.seedrandom=.ok seedObject
  kind : seedObject.kind=.function (SeedrandomInvocation.closure i.globals.scope)
  seedCaptured : browser.nativeSeedrandom=some i.seedrandom
  mixCaptured : browser.nativeTimestampMixkey=some i.mixkey

theorem codes_different (i : Inputs) (browser : Browser.State) (capture : Capture i browser) :
    i.seedrandom≠i.globals.codes := by
  intro same
  have objects : (Except.ok capture.seedObject : Checked JSObject)=Except.ok i.globals.codesObject := by
    rw [←capture.present,←i.globals.codesRead,same]
  have kinds := congrArg JSObject.kind (Except.ok.inj objects)
  rw [capture.kind,i.globals.codesKind] at kinds
  cases kinds

def resultState (browser : Browser.State) (i : Inputs) : Browser.State := {
  browser with
  machine := returned i
  timestampMixkeyActivations := browser.timestampMixkeyActivations+1 }

theorem actual_complete_path (browser : Browser.State) (i : Inputs) (capture : Capture i browser) (fuel : Nat) :
    BrowserRuntime.run (217+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (mixing i)).length+fuel)
      {browser with machine := SeedrandomInvocation.preparedText i.globals.base i.globals.scope i.receiver i.seed i.seedrandom}=
      BrowserRuntime.run fuel (resultState browser i) := by
  rw [show 217+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (mixing i)).length+fuel=
    129+(88+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (mixing i)).length+fuel) by omega,
    TimestampSeedRuntimeEntry.actual_setup_and_capture browser i capture.mixCaptured]
  exact TimestampMixkeyRuntimeComplete.actual_complete_helper
    {browser with
      machine := TimestampSeedMixingCapture.prepared i
      timestampMixkeyActivations := browser.timestampMixkeyActivations+1}
    (mixing i) (by
      change browser.nativeSeedrandom≠some i.globals.codes
      rw [capture.seedCaptured]
      exact fun same => codes_different i browser capture (Option.some.inj same)) fuel

theorem resulting_machine (browser : Browser.State) (i : Inputs) : (resultState browser i).machine=returned i := rfl

theorem one_capture (browser : Browser.State) (i : Inputs) :
    (resultState browser i).timestampMixkeyActivations=browser.timestampMixkeyActivations+1 := rfl

theorem elapsed (browser : Browser.State) (i : Inputs) :
    (resultState browser i).machine.elapsed=i.globals.base.elapsed := rfl

theorem free_draws (browser : Browser.State) (i : Inputs) :
    (resultState browser i).machine.freeDrawCount=i.globals.base.freeDrawCount := rfl

theorem random_tape (browser : Browser.State) (i : Inputs) : (resultState browser i).randomInputs=browser.randomInputs := rfl


theorem retained_object (browser : Browser.State) (i : Inputs) (id : ObjectId) (object : JSObject)
    (present : checkedObject i.globals.base.heap id=.ok object) :
    checkedObject (resultState browser i).machine.heap id=.ok object :=
  (TimestampMixkeyComplete.retained_objects (mixing i)).read id object
    (TimestampSeedMixingFrame.key_different (setup i) id object present)
    (HeapExtension.checked_object (extension i) id object present)

theorem free_random_identity (browser : Browser.State) (i : Inputs) :
    (resultState browser i).freeRandom=browser.freeRandom := rfl

end CookieClicker.JavaScript.TimestampSeedRuntimeComplete

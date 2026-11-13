import CookieClicker.JavaScriptTimestampSeedMixing
import CookieClicker.JavaScriptBrowser

/-! The selected timestamp-text activation is the actual Browser capture
transition. The surrounding source prefixes use the shared JavaScript core. -/
namespace CookieClicker.JavaScript.TimestampSeedMixingCapture
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampSeedMixing

def prepared (i : Inputs) := TimestampMixkey.prepared (beforeMixing i) i.globals.scope i.seed.toArray (key i) i.mixkey

theorem source_capture (i : Inputs) :
    TimestampText.invoke (beforeMixing i) i.mixkey .undefined [.timestampText i.seed.toArray,.object (key i)] =
      .ok (prepared i) :=
  TimestampMixkey.actual_captured_invocation _ _ _ _ _ _
    (HeapExtension.checked_object (extension i) _ _ i.mixkeyPresent) i.mixkeyKind

theorem actual_browser_capture (i : Inputs) (state : Browser.State)
    (machine : state.machine = beforeMixing i)
    (captured : state.nativeTimestampMixkey = some i.mixkey) :
    Browser.internalStep state =
      {state with machine := prepared i, timestampMixkeyActivations := state.timestampMixkeyActivations+1} := by
  have control : state.machine.control = .invoke (.object i.mixkey) .undefined [.timestampText i.seed.toArray,.object (key i)] false := by
    rw [machine]; rfl
  rw [Browser.internalStep,control]
  simp only [captured,beq_self_eq_true,↓reduceIte]
  rw [machine,source_capture]
  rfl

theorem actual_browser_step (i : Inputs) (state : Browser.State)
    (machine : state.machine = beforeMixing i)
    (captured : state.nativeTimestampMixkey = some i.mixkey) :
    Browser.step state =
      {state with machine := prepared i, timestampMixkeyActivations := state.timestampMixkeyActivations+1} := by
  unfold Browser.step
  rw [actual_browser_capture i state machine captured]
  have elapsed : (prepared i).elapsed = state.machine.elapsed := by rw [machine]; rfl
  simp only [←elapsed]

theorem actual_body (i : Inputs) (fuel : Nat) :
    Builtins.run (88+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (mixing i)).length+fuel) (prepared i) =
      Builtins.run fuel (returned i) :=
  TimestampMixkeyComplete.actual_complete_helper (mixing i) fuel

theorem source_chain (i : Inputs) :
    Builtins.run 128 (SeedrandomInvocation.preparedText i.globals.base i.globals.scope i.receiver i.seed i.seedrandom) =
      beforeMixing i ∧
    TimestampText.invoke (beforeMixing i) i.mixkey .undefined [.timestampText i.seed.toArray,.object (key i)] = .ok (prepared i) ∧
    Builtins.run (88+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (mixing i)).length) (prepared i) = returned i := by
  constructor
  · exact actual_setup_prefix i 0
  · exact ⟨source_capture i,actual_body i 0⟩

end CookieClicker.JavaScript.TimestampSeedMixingCapture

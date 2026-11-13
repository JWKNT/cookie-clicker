import CookieClicker.JavaScriptBrowserCoreStep
namespace CookieClicker.JavaScript.EscapeSpan
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def pureControl : Control → Bool
  | .resumeBuiltin .. | .unresolved .. | .fault .. | .idle => false
  | _ => true

def machineStep (machine : Machine) : Machine :=
  {Builtins.builtinStep machine with elapsed := machine.elapsed}

theorem pure_step (state : Browser.State)
    (noSeed : state.nativeSeedrandom=none) (noMix : state.nativeTimestampMixkey=none)
    (source : pureControl state.machine.control=true) (running : status state.machine=.running) :
    BrowserRuntime.step state = {state with machine := machineStep state.machine} := by
  cases control : state.machine.control <;> simp only [pureControl,control] at source
  case invoke function receiver arguments construct =>
    simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,running,
      Bool.false_and,Bool.false_eq_true,↓reduceIte,
      BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
      BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,BrowserLayout.handle,
      BrowserGeometry.handle,BrowserCookies.handle,BrowserEvents.handle,BrowserNodeList.handle,
      BrowserCanvasImage.handle,BrowserCanvas.handle,BrowserConsole.handle,BrowserDocument.handle,
      BrowserEnvironment.handle,BrowserStorage.handle,BrowserTokenList.handle,BrowserStyle.handle,
      BrowserResources.handle,control,Browser.step,Browser.internalStep,noSeed,noMix]
    cases function <;> cases arguments <;> cases construct <;> try rfl
    all_goals rename_i first rest
    all_goals cases first <;> rfl
  all_goals first
    | contradiction
    | exact BrowserCoreStep.plain_step state (by simp [BrowserCoreStep.plain,control]) running

def run : Nat → Machine → Machine
  | 0,machine => machine
  | count+1,machine => run count (machineStep machine)

def certificate : Nat → Machine → Bool
  | 0,_ => true
  | count+1,machine => pureControl machine.control &&
    (match status machine with | .running => true | _ => false) &&
    certificate count (machineStep machine)

theorem native_run (count : Nat) (state : Browser.State)
    (noSeed : state.nativeSeedrandom=none) (noMix : state.nativeTimestampMixkey=none)
    (closed : certificate count state.machine=true) :
    BrowserRuntime.run count state = {state with machine := run count state.machine} := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    simp only [certificate,Bool.and_eq_true] at closed
    rcases closed with ⟨⟨source,running⟩,tail⟩
    have statusEq : status state.machine=.running := by
      cases h : status state.machine <;> simp [h] at running ⊢
    simp only [BrowserRuntime.run,statusEq]
    rw [pure_step state noSeed noMix source statusEq]
    rw [ih {state with machine := machineStep state.machine} noSeed noMix tail]
    rfl

theorem native_prefix (count : Nat) (state : Browser.State) (fuel : Nat)
    (noSeed : state.nativeSeedrandom=none) (noMix : state.nativeTimestampMixkey=none)
    (closed : certificate count state.machine=true) :
    BrowserRuntime.run (count+fuel) state =
      BrowserRuntime.run fuel {state with machine := run count state.machine} := by
  induction count generalizing state with
  | zero => simp [run]
  | succ count ih =>
    simp only [certificate,Bool.and_eq_true] at closed
    rcases closed with ⟨⟨source,running⟩,tail⟩
    have statusEq : status state.machine=.running := by
      cases h : status state.machine <;> simp [h] at running ⊢
    rw [Nat.succ_add]
    simp only [BrowserRuntime.run,statusEq]
    rw [pure_step state noSeed noMix source statusEq]
    exact ih {state with machine := machineStep state.machine} noSeed noMix tail

end CookieClicker.JavaScript.EscapeSpan

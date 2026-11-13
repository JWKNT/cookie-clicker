import CookieClicker.JavaScriptEscapeReduction
namespace CookieClicker.JavaScript.EscapeHostStep
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def restore (state next : Browser.State) : Browser.State :=
  {next with machine := {next.machine with elapsed := state.machine.elapsed}}

def fastStep (state : Browser.State) : Browser.State :=
  match state.machine.control with
  | .resumeBuiltin continuation value =>
    if continuation.id.namespaceName == "Browser.Events" then
      restore state ((BrowserEvents.handle state).getD state)
    else EscapeReduction.reducedStep state
  | .unresolved (.builtin id receiver arguments construct) =>
    if id.namespaceName == "Browser.KeyboardEvent" then
      restore state (BrowserInput.dispatch state id receiver arguments construct)
    else EscapeReduction.reducedStep state
  | .unresolved (.nativeCallbackResult continuation _) =>
    if continuation.id.namespaceName == "Browser.Events" then
      restore state ((BrowserEvents.handle state).getD state)
    else EscapeReduction.reducedStep state
  | _ => EscapeReduction.reducedStep state

theorem step_fast (state : Browser.State) : BrowserRuntime.step state=fastStep state := by
  cases control : state.machine.control <;>
    simp only [fastStep,control]
  all_goals try {exact EscapeReduction.step_reduction state}
  case resumeBuiltin continuation value =>
    split
    · rename_i nsMatch
      have ns : continuation.id.namespaceName="Browser.Events" := by simpa using nsMatch
      simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,status,control,
        BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
        BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,BrowserLayout.handle,
        BrowserGeometry.handle,BrowserCookies.handle,BrowserEvents.handle,ns,restore,
        String.reduceBEq,Bool.false_and,Bool.false_eq_true,↓reduceIte,Option.getD_some] <;> simp [bne]
    · exact EscapeReduction.step_reduction state
  case unresolved request =>
    cases request <;> simp only [fastStep,control]
    all_goals try {exact EscapeReduction.step_reduction state}
    case builtin id receiver arguments construct =>
      split
      · rename_i nsMatch
        have ns : id.namespaceName="Browser.KeyboardEvent" := by simpa using nsMatch
        simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,status,control,
          BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
          BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,ns,restore,
          String.reduceBEq,List.contains_cons,List.contains_nil,Bool.false_or,Bool.true_or,
          Bool.false_and,Bool.false_eq_true,↓reduceIte,Option.getD_some] <;> simp [bne]
      · exact EscapeReduction.step_reduction state
    case nativeCallbackResult continuation completion =>
      split
      · rename_i nsMatch
        have ns : continuation.id.namespaceName="Browser.Events" := by simpa using nsMatch
        simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,status,control,
          BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
          BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,BrowserLayout.handle,
          BrowserGeometry.handle,BrowserCookies.handle,BrowserEvents.handle,ns,restore,
          String.reduceBEq,Bool.false_and,Bool.false_eq_true,↓reduceIte,Option.getD_some] <;> simp [bne]
      · exact EscapeReduction.step_reduction state
end CookieClicker.JavaScript.EscapeHostStep

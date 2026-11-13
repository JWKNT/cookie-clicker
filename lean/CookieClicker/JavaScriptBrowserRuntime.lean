import CookieClicker.JavaScriptBrowserStyle
import CookieClicker.JavaScriptBrowserResources
import CookieClicker.JavaScriptBrowserEnvironment
import CookieClicker.JavaScriptBrowserStorage
import CookieClicker.JavaScriptBrowserTokenList
import CookieClicker.JavaScriptBrowserDocument
import CookieClicker.JavaScriptBrowserConsole
import CookieClicker.JavaScriptBrowserCanvas
import CookieClicker.JavaScriptBrowserCanvasImage
import CookieClicker.JavaScriptBrowserNodeList
import CookieClicker.JavaScriptBrowserEvents
import CookieClicker.JavaScriptBrowserCookies
import CookieClicker.JavaScriptBrowserGeometry
import CookieClicker.JavaScriptBrowserInput
import CookieClicker.JavaScriptBrowserLayout
import CookieClicker.JavaScriptBrowserFocus
import CookieClicker.JavaScriptBrowserWindowName
import CookieClicker.JavaScriptBrowserMetrics
import CookieClicker.JavaScriptBrowserTextArea
import CookieClicker.JavaScriptBrowserAnimation
import CookieClicker.JavaScriptBrowserTextSelection

/-! Concrete composition of the source interpreter and implemented browser
families. All remaining host requirements remain unresolved. Diagnostic fuel
and task budgets are not restrictions on an admissible game strategy. -/
namespace CookieClicker.JavaScript.BrowserRuntime

open Browser

def internalStep (state : State) : State :=
  if Browser.taskFinished state.machine && state.activeResource.isSome then BrowserResources.finish state
  else if Browser.taskFinished state.machine && state.activeTimer.isSome then Browser.finishTimer state
  else if Browser.taskFinished state.machine && state.animation.active.isSome then BrowserAnimation.advance state
  else match BrowserTextSelection.handle state with
    | some next => next
    | none => match BrowserAnimation.handle state with
    | some next => next
    | none => match BrowserTextArea.handle state with
    | some next => next
    | none => match BrowserMetrics.handle state with
    | some next => next
    | none => match BrowserWindowName.handle state with
    | some next => next
    | none => match BrowserFocus.handle state with
    | some next => next
    | none => match BrowserInput.handle state with
    | some next => next
    | none => match BrowserLayout.handle state with
    | some next => next
    | none => match BrowserGeometry.handle state with
    | some next => next
    | none => match BrowserCookies.handle state with
    | some next => next
    | none => match BrowserEvents.handle state with
    | some next => next
    | none => match BrowserNodeList.handle state with
      | some next => next
      | none => match BrowserCanvasImage.handle state with
        | some next => next
        | none => match BrowserCanvas.handle state with
          | some next => next
          | none => match BrowserConsole.handle state with
            | some next => next
            | none => match BrowserDocument.handle state with
              | some next => next
              | none => match BrowserEnvironment.handle state with
                | some next => next
                | none => match BrowserStorage.handle state with
                  | some next => next
                  | none => match BrowserTokenList.handle state with
                    | some next => next
                    | none => match BrowserStyle.handle state with
                      | some next => next
                      | none => match BrowserResources.handle state with
                        | some next => next
                        | none => Browser.step state

def step (state : State) : State :=
  let elapsed := state.machine.elapsed
  let next := internalStep state
  { next with machine := { next.machine with elapsed } }

/-- Scalar extraction preserves the exact transition while allowing compiled
execution to release the old heap before a mutation. -/
theorem step_eq_elapsed_restore (state : State) :
    step state =
      let next := internalStep state
      { next with machine := { next.machine with elapsed := state.machine.elapsed } } := rfl

theorem step_preserves_elapsed (state : State) :
    (step state).machine.elapsed = state.machine.elapsed := rfl

def run : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
    match status state.machine with
    | .running => run fuel (step state)
    | .unresolved request =>
      let next := step state
      match status next.machine with
      | .unresolved nextRequest => if nextRequest == request then next else run fuel next
      | .fault _ => next
      | _ => run fuel next
    | _ =>
      if state.activeResource.isSome || state.animation.active.isSome then
        let next := step state
        match status next.machine with
        | .unresolved _ | .fault _ => next
        | _ => run fuel next
      else if state.activeTimer.isSome then step state else state

/-- Resolve the selected zero-latency resource model before selecting the next
event. Ordering is explicit by deadline and initialization order. Unresolved
resource work cannot be skipped in favor of a later timer. -/
def fireNextTask (state : State) : State :=
  if !Browser.taskFinished state.machine then state else
  if !state.animation.pending.isEmpty || state.animation.active.isSome ||
      !state.textSelection.pending.isEmpty || state.textSelection.active.isSome then
    Browser.fail state (.unresolved (.unsupportedSyntax
      "Rendering-event or MiscPlatformAPI event opportunity and native task ordering are not configured")) else
  let state := BrowserResources.finish (Browser.finishTimer state)
  if !Browser.taskFinished state.machine then state else
  Browser.checked state (BrowserResources.prepare state) fun state =>
    match BrowserResources.nextTask state, Browser.nextTimer state with
    | none, none => state
    | some _, none => BrowserResources.fireNextTask state
    | none, some _ => Browser.fireNextTimer state
    | some resource, some timer =>
      if resource.due < timer.due || (resource.due == timer.due && resource.request.order < timer.order) then
        BrowserResources.fireNextTask state
      else Browser.fireNextTimer state

def hasPendingTask (state : State) : Bool :=
  !state.timers.isEmpty || !state.resourceRequests.isEmpty || !state.resourceTasks.isEmpty ||
    state.activeTimer.isSome || state.activeResource.isSome || !state.animation.pending.isEmpty || state.animation.active.isSome || !state.textSelection.pending.isEmpty || state.textSelection.active.isSome

def runTasks : Nat → Nat → State → State
  | 0, _, state => state
  | tasks + 1, fuel, state =>
    let state := run fuel state
    if !Browser.taskFinished state.machine || !hasPendingTask state then state else
    let next := run fuel (fireNextTask state)
    if !Browser.taskFinished next.machine then next else runTasks tasks fuel next

end CookieClicker.JavaScript.BrowserRuntime

import CookieClicker.JavaScriptBrowserEvents

/-! Source-visible dispatch of the queued animation-frame events. A caller
must supply an actual rendering-event stage; this module does not invent its
time, skip earlier rendering phases, or equate it with setTimeout. -/
namespace CookieClicker.JavaScript.BrowserAnimation

open Browser

/-- Allocate at scheduling time, as Event::CreateBubble does. The event target
is retained even when later DOM actions detach it from the document. -/
def enqueueSelect (state : State) (target : Nat) : Checked State := do
  let node ← checkedNode state target
  let (event,state) ← BrowserEventData.allocateEvent state (JSString.ofString "select") (.object node.object)
  let id ← BrowserEventData.eventId state event
  let some data := state.domEvents[id]? |
    .error (.fault (.invalidContinuation "Missing newly allocated select event"))
  pure {state with
    domEvents := state.domEvents.set! id {data with bubbles := true,phase := 0,currentTarget := .null}
    animation := BrowserAnimationState.enqueue state.animation id}

def advance (state : State) : State :=
  match state.animation.active with
  | none => Browser.fail state (.fault (.invalidContinuation "No active animation-event dispatch"))
  | some [] => Browser.result {state with animation := {state.animation with active := none}} .undefined
  | some (id :: rest) =>
    match state.domEvents[id]? with
    | none => Browser.fail state (.fault (.invalidContinuation "Missing queued animation event"))
    | some event =>
      let continuation : BuiltinContinuation := {
        id := ⟨"Browser.Animation","advance"⟩,phase := "advance",thisValue := .undefined }
      BrowserEvents.dispatchEvent {state with
        animation := {state.animation with active := some rest}
        machine := {state.machine with continuation := .builtin continuation :: state.machine.continuation}}
        event.target [.object event.object] true

/-- The event-dispatch phase of one externally supplied rendering opportunity.
Earlier autofocus/media-query phases and later frame callbacks are separate
requirements. Native select events use this ordinary FIFO, not the unique-event
map. A callback cannot recursively service another rendering stage. -/
def beginDispatch (state : State) : State :=
  if !Browser.taskFinished state.machine || state.activeTimer.isSome || state.activeResource.isSome ||
      state.animation.active.isSome || state.textSelection.active.isSome then
    Browser.fail state (.fault (.invalidContinuation "Animation event stage during an active source task"))
  else advance {state with
    animation := BrowserAnimationState.beginDispatch state.animation
    currentTimerNesting := none
    machine := {state.machine with continuation := []}}

def handle (state : State) : Option State :=
  match state.machine.control with
  | .resumeBuiltin continuation _ | .unresolved (.builtinContinuation continuation _) =>
    if continuation.id.namespaceName == "Browser.Animation" && continuation.phase == "advance" then
      some (advance state)
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserAnimation

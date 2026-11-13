import CookieClicker.JavaScriptBrowserAnimation

/-! Native textarea cache/FrameSelection synchronization on a represented
internal editor. Document selectionchange uses the native MiscPlatformAPI task
source; select uses the separate animation-event queue. Neither queue supplies
a scheduling cadence or skips source callbacks. -/
namespace CookieClicker.JavaScript.BrowserTextSelection

open Browser
private def key := JSString.ofString
private def missing (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Textarea FrameSelection: " ++ message)))

def range (state : State) (id : Nat) : Checked (Nat × Nat × TextControl.Direction) := do
  let node ← checkedNode state id
  if state.focus.element != some id then pure (node.textarea.start,node.textarea.finish,node.textarea.direction)
  else match state.textSelection.current with
  | some current =>
    if current.owner != id then pure (0,0,BrowserTextSelectionState.direction current)
    else if current.revision != node.textarea.revision then
      missing "focused editor range is not represented"
    else pure (current.start,current.finish,BrowserTextSelectionState.direction current)
  | none => pure (0,0,.none)

private def enqueueSelectionchange (state : State) : Checked State := do
  let document ← checkedNode state state.document
  let (value,state) ← BrowserEventData.allocateEvent state (key "selectionchange") (.object document.object)
  let event ← BrowserEventData.eventId state value
  let some data := state.domEvents[event]? |
    .error (.fault (.invalidContinuation "Missing selectionchange event"))
  pure {state with
    domEvents := state.domEvents.set! event {data with phase := 0,currentTarget := .null}
    textSelection := {state.textSelection with pending := state.textSelection.pending ++ [event]}}

/-- FrameSelection's equality test includes directionality. A changed frame
selection notifies the text control before it enqueues selectionchange. -/
def applyCache (state : State) (id : Nat) : Checked State := do
  if state.focus.element != some id then pure state else
  let node ← checkedNode state id
  if !(← connectedToDocument state (state.nodes.size+1) id) then pure state else
  let next := BrowserTextSelectionState.fromCache id node.textarea
  if state.textSelection.current == some next then pure state else
  let node := {node with textarea := {node.textarea with direction := BrowserTextSelectionState.direction next}}
  let state ← replaceNode state id node
  enqueueSelectionchange {state with textSelection := {state.textSelection with current := some next}}

def setRange (state : State) (id : Nat) (start finish : Nat)
    (direction : TextControl.Direction) : Checked State := do
  let node ← checkedNode state id
  let textarea := TextControl.setRange node.textarea start finish direction
  let changed := node.textarea.start != textarea.start || node.textarea.finish != textarea.finish ||
    node.textarea.direction != textarea.direction
  let state ← replaceNode state id {node with textarea}
  let state ← applyCache state id
  if changed then BrowserAnimation.enqueueSelect state id else pure state

def restore (state : State) (id : Nat) : Checked State := do
  let node ← checkedNode state id
  setRange state id node.textarea.start node.textarea.finish node.textarea.direction

/-- One explicit MiscPlatformAPI event task. It retains the event's original
target and timestamp; the dispatcher obtains current listeners and ancestors. -/
def fireNextTask (state : State) : State :=
  if !Browser.taskFinished state.machine || state.activeTimer.isSome || state.activeResource.isSome ||
      state.animation.active.isSome || state.textSelection.active.isSome then
    Browser.fail state (.fault (.invalidContinuation "Selection task during another active procedure"))
  else match state.textSelection.pending with
  | [] => state
  | id :: rest => match state.domEvents[id]? with
    | none => Browser.fail state (.fault (.invalidContinuation "Missing selectionchange task event"))
    | some event =>
      let continuation : BuiltinContinuation := {
        id := ⟨"Browser.TextSelection","finish"⟩,phase := "finish",thisValue := .undefined }
      BrowserEvents.dispatchEvent {state with
        currentTimerNesting := none
        textSelection := {state.textSelection with pending := rest,active := some id}
        machine := {state.machine with continuation := [.builtin continuation]}}
        event.target [.object event.object] true

def handle (state : State) : Option State :=
  match state.machine.control with
  | .resumeBuiltin continuation _ | .unresolved (.builtinContinuation continuation _) =>
    if continuation.id.namespaceName == "Browser.TextSelection" && continuation.phase == "finish" then
      some (Browser.result {state with textSelection := {state.textSelection with active := none}} .undefined)
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserTextSelection

import CookieClicker.JavaScriptBrowser

/-! Base Event identity and field operations shared by source dispatch and
resource tasks. Unsupported event subclasses and native reflection remain
explicit model requirements. -/
namespace CookieClicker.JavaScript.BrowserEventData

open Browser
private def key := JSString.ofString
private def unresolved (state : State) (message : String) : State :=
  Browser.fail state (.unresolved (.unsupportedSyntax message))

private def intrinsicPrototype (state : State) (name : String) : Checked ObjectId := do
  let some (_,prototype) := state.prototypes.specific.find? (fun entry => entry.1 == "#" ++ name) |
    .error (.fault (.invalidContinuation ("Missing captured native prototype " ++ name)))
  pure prototype

def allocateEvent (state : State) (eventType : JSString) (target : Value) : Checked (Value × State) := do
  let prototype ← intrinsicPrototype state "Event"
  let id := state.domEvents.size
  let (object,heap) := state.machine.heap.allocateObject {
    kind := .host "DOM.Event" id, prototype := some prototype }
  let (getter,heap) := heap.allocateObject {
    kind := .builtin ⟨"Browser.Event","get isTrusted"⟩, prototype := state.machine.functionPrototype,
    propertiesComplete := false }
  let objectData ← checkedObject heap object
  let heap ← replaceObject heap object (setOwnProperty objectData (key "isTrusted")
    (.accessor (some getter) none true false))
  let event : DomEvent := { object, eventType, target, currentTarget := target, time := state.machine.elapsed, phase := 2 }
  pure (.object object,{ state with
    machine := { state.machine with heap }
    domEvents := state.domEvents.push event })

def eventId (state : State) (receiver : Value) : Checked Nat := do
  match receiver with
  | .object object => match (← checkedObject state.machine.heap object).kind with
    | .host "DOM.Event" id => pure id
    | _ => .error (.exception "TypeError" "Event receiver required")
  | _ => .error (.exception "TypeError" "Event receiver required")

def eventCall (state : State) (name : String) (receiver : Value) (arguments : List Value := []) : State :=
  Browser.checked state (eventId state receiver) fun id =>
  match state.domEvents[id]? with
  | none => Browser.fail state (.fault (.invalidContinuation "Missing DOM event"))
  | some event =>
    if name == "get target" || name == "get srcElement" then Browser.result state event.target
    else if name == "get currentTarget" then Browser.result state event.currentTarget
    else if name == "get type" then Browser.result state (.string event.eventType)
    else if name == "get bubbles" then Browser.result state (.boolean event.bubbles)
    else if name == "get cancelable" then Browser.result state (.boolean event.cancelable)
    else if name == "get defaultPrevented" then Browser.result state (.boolean event.defaultPrevented)
    else if name == "get returnValue" then Browser.result state (.boolean (!event.defaultPrevented))
    else if name == "get cancelBubble" then Browser.result state (.boolean event.propagationStopped)
    else if name == "get isTrusted" then Browser.result state (.boolean event.isTrusted)
    else if name == "get eventPhase" then Browser.result state (.number (Number.ofNat event.phase))
    else if name == "get composed" then Browser.result state (.boolean event.composed)
    else if name == "get timeStamp" then
      if event.time < 0 || event.time.den != 1 || event.time.num.natAbs > 2^53 then
        unresolved state "Exact unbounded/fractional DOM event timestamp conversion"
      else Browser.result state (.number (Number.ofInt event.time.num))
    else if name == "set cancelBubble" then
      let event := { event with propagationStopped := event.propagationStopped || truthy (Builtins.argument arguments 0) }
      Browser.result { state with domEvents := state.domEvents.set! id event } .undefined
    else if name == "set returnValue" then
      let event := { event with defaultPrevented := event.defaultPrevented ||
        (!truthy (Builtins.argument arguments 0) && event.cancelable && !event.handlingPassive) }
      Browser.result { state with domEvents := state.domEvents.set! id event } .undefined
    else if name == "preventDefault" then
      let event := { event with defaultPrevented := event.defaultPrevented || (event.cancelable && !event.handlingPassive) }
      Browser.result { state with domEvents := state.domEvents.set! id event } .undefined
    else if name == "stopPropagation" || name == "stopImmediatePropagation" then
      let event := { event with
        propagationStopped := true
        immediateStopped := event.immediateStopped || name == "stopImmediatePropagation" }
      Browser.result { state with domEvents := state.domEvents.set! id event } .undefined
    else Browser.fail state (.unresolved (.builtin ⟨"Browser.Event",name⟩ receiver arguments false))

end CookieClicker.JavaScript.BrowserEventData

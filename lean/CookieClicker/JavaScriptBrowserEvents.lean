import CookieClicker.JavaScriptBrowserEventData
import CookieClicker.JavaScriptBrowserInline

/-! Ordered dispatch of base Event objects through the explicit DOM tree.
Callbacks run in the source interpreter and their completions return through
nativeCallback frames. This is not a model of mouse activation, shadow trees,
special inline-handler scopes or trusted user input yet.
The traversal and at-target registration order follow Chromium 87's
core/dom/events/event_dispatcher.cc, rather than a newer browser algorithm. -/
namespace CookieClicker.JavaScript.BrowserEvents

open Browser BrowserEventState

private def key := JSString.ofString
private def argument := Builtins.argument
private def unresolved (state : State) (message : String) : State :=
  Browser.fail state (.unresolved (.unsupportedSyntax ("Event dispatch: " ++ message)))

private def event (state : State) (id : Nat) : Checked DomEvent :=
  match state.domEvents[id]? with
  | some event => pure event
  | none => .error (.fault (.invalidContinuation "Missing event identity"))

private def targetValue (state : State) : Target → Checked Value
  | .window => pure (.object state.machine.globalObject)
  | .node id => nodeValue state (some id)

private def receiverTarget (state : State) (receiver : Value) : Checked Target := do
  if receiver == .object state.machine.globalObject then pure .window
  else pure (.node (← receiverNode state receiver).1)

private def registrations (state : State) (target : Target) : Checked (List Listener × List Handler) := do
  match target with
  | .window => pure (state.windowListeners,state.windowHandlers)
  | .node id =>
    let node ← checkedNode state id
    pure (node.listeners,node.handlers)

private def parentPath (state : State) : Nat → Nat → Checked (List Target)
  | 0, _ => .error (.fault (.invalidContinuation "Cyclic event ancestor path"))
  | fuel + 1, id => do
    let node ← checkedNode state id
    if id == state.document then pure [.node id,.window]
    else match node.parent with
    | none => pure [.node id]
    | some parent => pure (.node id :: (← parentPath state fuel parent))

private def snapshot (state : State) (eventType : JSString) (visit : Visit) : Checked (List Invocation) := do
  let (listeners,handlers) ← registrations state visit.target
  let listeners := listeners.filterMap fun listener =>
    if listener.eventType == eventType && (visit.phase == 2 || listener.capture == visit.capture) then
      some { serial := listener.serial, callback := listener.callback, propertyHandler := false : Invocation }
    else none
  let handlers ← if visit.phase != 2 && visit.capture then pure [] else
    handlers.foldlM (fun output handler => do
      if handler.eventType != eventType then pure output else
      match handler.body,handler.serial with
      | none,_ => pure output
      | some (.callback callback),some serial =>
        pure (output ++ [{ serial, callback, propertyHandler := true }])
      | some (.inlineText _),some serial =>
        pure (output ++ [{ serial, callback := .undefined, propertyHandler := true }])
      | _,_ => .error (.fault (.invalidContinuation "Active event handler without registration identity"))) []
  pure ((listeners ++ handlers).mergeSort (fun left right => left.serial ≤ right.serial))

private def activeCallback (state : State) (eventType : JSString) (visit : Visit)
    (invocation : Invocation) : Checked (Option (Value × Bool × Bool) × State) := do
  let (listeners,handlers) ← registrations state visit.target
  if !invocation.propertyHandler then
    pure (((listeners.find? (fun listener => listener.serial == invocation.serial)).map
      (fun listener => (listener.callback,listener.once,listener.passive))),state)
  else
    match handlers.find? (fun handler => handler.eventType == eventType && handler.serial == some invocation.serial) with
    | none => pure (none,state)
    | some handler => match handler.body with
      | none => pure (none,state)
      | some (.callback callback) => pure (some (callback,false,false),state)
      | some (.inlineText _) => match visit.target with
        | .window => .error (.unresolved (.unsupportedSyntax "Window inline handler compilation scope"))
        | .node id =>
          let (callback,state) ← BrowserInline.value state id eventType
          pure (some (callback,false,false),state)

private def callbackSupported (event : DomEvent) (visit : Visit)
    (invocation : Invocation) : Checked Unit := do
  if invocation.propertyHandler && visit.target == .window &&
      [key "error",key "beforeunload"].contains event.eventType then
    .error (.unresolved (.unsupportedSyntax "Window special event-handler arguments and return processing"))
  else pure ()

private def removeOnce (state : State) (target : Target) (serial : Nat) : Checked State := do
  match target with
  | .window => pure { state with windowListeners := state.windowListeners.filter (·.serial != serial) }
  | .node id =>
    let node ← checkedNode state id
    replaceNode state id { node with listeners := node.listeners.filter (·.serial != serial) }

private def advanceRequest (state : State) : State :=
  { state with machine := { state.machine with
    control := .resumeBuiltin {
      id := ⟨"Browser.Events","dispatch"⟩, thisValue := .undefined,
      arguments := [], phase := "advance" } .undefined } }

private def finish (state : State) (dispatch : Dispatch) (rest : List Dispatch) (event : DomEvent) : State :=
  if dispatch.requireCanceledMouseClick && !event.defaultPrevented then
    unresolved state "Uncanceled MouseEvent click requires native DOMActivate/default behavior"
  else
    let finalTarget := if dispatch.clearTarget then Value.null else event.target
    let event := { event with
      target := finalTarget,
      currentTarget := if dispatch.windowTarget then event.currentTarget else .null,
      phase := 0, dispatching := false, handlingPassive := false,
      propagationStopped := dispatch.windowTarget && event.propagationStopped,
      immediateStopped := dispatch.windowTarget && event.immediateStopped }
    Browser.result { state with
      eventDispatches := rest, domEvents := state.domEvents.set! dispatch.event event,
      inputEvents := if dispatch.clearTarget then state.inputEvents.map (fun (id,data) =>
        (id,if id == dispatch.event then match data with
          | .focus fields => .focus { fields with relatedTarget := .null }
          | other => other else data)) else state.inputEvents }
      (.boolean (!event.defaultPrevented))

def advance (state : State) : State :=
  match state.eventDispatches with
  | [] => Browser.fail state (.fault (.invalidContinuation "No active event dispatch"))
  | dispatch :: rest => Browser.checked state (event state dispatch.event) fun event =>
    match dispatch.pending,dispatch.current with
    | invocation :: pending,some visit =>
      if event.immediateStopped then advanceRequest { state with
        eventDispatches := { dispatch with pending := [] } :: rest }
      else Browser.checked state (activeCallback state event.eventType visit invocation) fun (callback,state) =>
        let state := { state with eventDispatches := { dispatch with pending } :: rest }
        match callback with
        | none => advanceRequest state
        | some (callback,once,passive) => Browser.checked state (callbackSupported event visit invocation) fun _ =>
          Browser.checked state (if once then removeOnce state visit.target invocation.serial else pure state) fun state =>
          Browser.checked state (Builtins.isCallable state.machine callback) fun callable =>
          Browser.checked state (targetValue state visit.target) fun receiver =>
            let state := { state with domEvents := state.domEvents.set! dispatch.event { event with handlingPassive := passive } }
            let continuation : BuiltinContinuation := {
              id := ⟨"Browser.Events","dispatch"⟩, thisValue := receiver, arguments := [],
              phase := "callback", indices := [dispatch.event,if invocation.propertyHandler then 1 else 0] }
            let frames := .nativeCallback continuation state.machine.context :: state.machine.continuation
            if callable then
              { state with machine := { state.machine with
                control := .invoke callback receiver [.object event.object] false
                continuation := frames } }
            else
              let objectContinuation : BuiltinContinuation := {
                id := ⟨"Browser.Events","dispatch"⟩, thisValue := callback,
                arguments := [.object event.object], phase := "objectListener" }
              { state with machine := readProperty { state.machine with
                continuation := .builtin objectContinuation :: frames } callback (key "handleEvent") }
    | _,_ =>
      if (!dispatch.windowTarget && event.propagationStopped) || dispatch.visits.isEmpty then finish state dispatch rest event
      else match dispatch.visits with
      | [] => finish state dispatch rest event
      | visit :: visits => Browser.checked state (snapshot state event.eventType visit) fun pending =>
        Browser.checked state (targetValue state visit.target) fun currentTarget =>
          advanceRequest { state with
            eventDispatches := { dispatch with visits, current := some visit, pending } :: rest
            domEvents := state.domEvents.set! dispatch.event { event with currentTarget, phase := visit.phase } }

/-- Closed script-dispatch fragment. Related-target retargeting, trusted input,
checkbox/radio preactivation, disabled controls and foreign trees stay explicit.
The accepted ordinary HTML path has no legacy pre/post activation mutation.
A click can finish only if the actual source callbacks cancel its default. -/
private def admitScriptMouse (state : State) (id : Nat) (trusted : Bool)
    (path : List Target) : Checked Bool := do
  match state.inputEvents.find? (fun entry => entry.1 == id) with
  | none => pure false
  | some (_, .focus _) => pure false
  | some (_, .mouse mouse) =>
    if trusted then .error (.unresolved (.unsupportedSyntax "Trusted pointer input requires hit-testing and native delivery state"))
    else if mouse.relatedTarget != .null then
      .error (.unresolved (.unsupportedSyntax "MouseEvent related-target path adjustment"))
    else
      for target in path do
        match target with
        | .window => pure ()
        | .node id =>
          let node ← checkedNode state id
          match node.kind with
          | .document => pure ()
          | .element tag =>
            if !["html","body","div","span","button"].contains tag then
              .error (.unresolved (.unsupportedSyntax ("MouseEvent native activation path: " ++ tag)))
            else if tag == "button" && ((getAttribute node "disabled").isSome || (getAttribute node "form").isSome) then
              .error (.unresolved (.unsupportedSyntax "MouseEvent disabled/form-associated button path"))
            else pure ()
          | _ => .error (.unresolved (.unsupportedSyntax "MouseEvent non-element target path"))
      let event ← event state id
      pure (event.eventType == key "click")
  | some (_, .keyboard keyboard) =>
    let dispatched ← event state id
    if !trusted || dispatched.eventType != key "keyup" || keyboard.key != key "Escape" ||
        keyboard.code != key "Escape" || keyboard.keyCode != 27 || keyboard.charCode != 0 ||
        keyboard.location != 0 || keyboard.repeating || keyboard.composing then
      .error (.unresolved (.unsupportedSyntax "Native keyboard dispatch outside the closed Escape key-up fragment"))
    else
      -- Chromium87 KeyboardEventManager::DefaultKeyboardEventHandler handles
      -- only Enter on key-up. The ordinary HTML path has no activation behavior
      -- for Escape. Physical targeting and device state are checked upstream.
      for target in path do
        match target with
        | .window => pure ()
        | .node id =>
          let node ← checkedNode state id
          match node.kind with
          | .document => pure ()
          | .element tag =>
            if !["html","body","div","span"].contains tag then
              .error (.unresolved (.unsupportedSyntax "Escape key-up outside the ordinary HTML default-action fragment"))
          | _ => .error (.unresolved (.unsupportedSyntax "Escape key-up non-element target path"))
      pure false
  | some _ => .error (.unresolved (.unsupportedSyntax "UI or keyboard native dispatch behavior"))

def dispatchEvent (state : State) (receiver : Value) (arguments : List Value) (trusted : Bool := false) : State :=
  Browser.checked state (receiverTarget state receiver) fun target =>
  if arguments.isEmpty then Browser.fail state (.exception "TypeError" "dispatchEvent requires an Event")
  else Browser.checked state (BrowserEventData.eventId state (argument arguments 0)) fun id =>
  Browser.checked state (event state id) fun event =>
    if event.dispatching then Browser.fail state (.exception "InvalidStateError" "Event is already being dispatched")
    else if event.eventType == key "textInput" || event.eventType == key "DOMActivate" then
      unresolved state "Native activation/default action for this event type"
    else Browser.checked state (match target with
      | .window => pure [Target.window]
      | .node node => parentPath state (state.nodes.size + 1) node) fun path =>
      Browser.checked state (admitScriptMouse state id trusted path) fun requireCanceledMouseClick =>
      let path := if target != .window && event.eventType == key "load" then path.filter (· != .window) else path
      let ancestors := path.drop 1
      let visits := ancestors.reverse.map (fun target => { target, capture := true, phase := 1 : Visit }) ++
        [{ target, capture := false, phase := 2 }] ++
        (if event.bubbles then ancestors.map (fun target => { target, capture := false, phase := 3 }) else [])
      Browser.checked state (targetValue state target) fun targetValue =>
        advanceRequest { state with
          domEvents := state.domEvents.set! id { event with
            target := targetValue, currentTarget := .null, phase := 0, dispatching := true, isTrusted := trusted }
          eventDispatches := {
            event := id, visits, clearTarget := !path.contains .window,
            windowTarget := target == .window, requireCanceledMouseClick } :: state.eventDispatches }

/-- A selected resource task constructs a trusted base Event. This does not
turn script dispatch into trusted input or supply mouse activation behavior. -/
def beginTrusted (state : State) (target : Value) (eventType : JSString) : State :=
  Browser.checked state (BrowserEventData.allocateEvent state eventType .null) fun (event,state) =>
    dispatchEvent state target [event] true

private def callbackComplete (state : State) (continuation : BuiltinContinuation) (completion : Completion) : State :=
  match state.eventDispatches,continuation.indices with
  | dispatch :: _,[id,propertyHandler] =>
    if id != dispatch.event then Browser.fail state (.fault (.invalidContinuation "Event callback identity mismatch"))
    else Browser.checked state (event state id) fun event =>
      let event := { event with handlingPassive := false }
      let state := { state with domEvents := state.domEvents.set! id event }
      match completion with
      | .normal value =>
        let canceled := propertyHandler == 1 && value == some (.boolean false) && event.cancelable
        advanceRequest { state with
          domEvents := state.domEvents.set! id { event with defaultPrevented := event.defaultPrevented || canceled } }
      | .throw value =>
        if state.windowListeners.any (fun listener => listener.eventType == key "error") ||
            state.windowHandlers.any (fun handler => handler.eventType == key "error" && handler.body.isSome) then
          unresolved state "Report source callback exception through actual Window ErrorEvent handlers"
        else advanceRequest { state with reportedExceptions := state.reportedExceptions ++ [value] }
      | _ => Browser.fail state (.fault (.invalidContinuation "Nonlocal event callback completion"))
  | _,_ => Browser.fail state (.fault (.invalidContinuation "Missing event callback state"))

private def isTopLevelTarget (state : State) (target : Target) : Checked Bool := do
  match target with
  | .window => pure true
  | .node id =>
    if id == state.document then pure true else
    let document ← checkedNode state state.document
    let root := document.children.find? fun child =>
      (state.nodes[child]?).any fun node => match node.kind with | .element _ => true | _ => false
    if root == some id then pure true else
    match root with
    | none => pure false
    | some root =>
      let node ← checkedNode state root
      if node.kind != .element "html" then pure false else
      let body := node.children.find? fun child => (state.nodes[child]?).any fun node =>
        node.kind == .element "body" || node.kind == .element "frameset"
      pure (body == some id)

private def finishRegistration (state : State) (name : String) (receiver : Value)
    (arguments flags : List Value) : State :=
  Browser.checked state (receiverTarget state receiver) fun target =>
  Browser.checked state (toJSString (argument arguments 0)) fun eventType =>
    let callback := argument arguments 1
    if callback == .undefined || callback == .null then Browser.result state .undefined else
    Browser.checked state (registrations state target) fun (listeners,_) =>
    Browser.checked state (if name == "removeEventListener" || argument flags 2 != .undefined then pure false else
      isTopLevelTarget state target) fun topLevel =>
      let capture := truthy (argument flags 0)
      let once := truthy (argument flags 1)
      let passive := if argument flags 2 != .undefined then truthy (argument flags 2) else
        topLevel && [key "touchstart",key "touchmove",key "wheel",key "mousewheel"].contains eventType
      let same := fun (listener : Listener) => listener.eventType == eventType &&
        listener.callback == callback && listener.capture == capture
      let fresh := name == "addEventListener" && !listeners.any same
      let listeners := if name == "removeEventListener" then listeners.filter (!same ·)
        else if !fresh then listeners else listeners ++ [{
          eventType,callback,capture,once,passive,serial := state.nextListenerSerial }]
      let state := { state with nextListenerSerial := state.nextListenerSerial + (if fresh then 1 else 0) }
      Browser.checked state (match target with
        | .window => pure { state with windowListeners := listeners }
        | .node id => do
          let node ← checkedNode state id
          replaceNode state id { node with listeners }) fun next => Browser.result next .undefined

private def readListenerOption (state : State) (name : String) (receiver : Value)
    (arguments flags : List Value) : State :=
  let names := if name == "removeEventListener" then ["capture"] else ["capture","once","passive"]
  match names[flags.length]? with
  | none => finishRegistration state name receiver arguments flags
  | some field =>
    let continuation : BuiltinContinuation := {
      id := ⟨"Browser.Events",name⟩, thisValue := receiver,
      arguments, phase := "listenerOption", locals := flags }
    { state with machine := readProperty { state.machine with
      continuation := .builtin continuation :: state.machine.continuation } (argument arguments 2) (key field) }

private def registrationCall (state : State) (name : String) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Event registration is not a constructor")
  else Browser.checked state (receiverTarget state receiver) fun _ =>
    if arguments.length < 2 then Browser.fail state (.exception "TypeError" "Event registration requires type and callback")
    else match Browser.convertArguments state ⟨"Browser.Events",name⟩ receiver arguments false [(0,"string")] with
    | some next => next
    | none => Browser.checked state (toJSString (argument arguments 0)) fun eventType =>
      let arguments := .string eventType :: arguments.drop 1
      let callback := argument arguments 1
      if callback != .undefined && callback != .null && !isObject callback then
        Browser.fail state (.exception "TypeError" "Event listener callback must be an object or null")
      else if isObject (argument arguments 2) then readListenerOption state name receiver arguments []
      else finishRegistration state name receiver arguments [.boolean (truthy (argument arguments 2)),.boolean false,.undefined]

private def create (state : State) (eventType : JSString) (flags : List Value) : State :=
  Browser.checked state (BrowserEventData.allocateEvent state eventType .null) fun (value,next) =>
  Browser.checked next (BrowserEventData.eventId next value) fun id =>
  Browser.checked next (event next id) fun event =>
      Browser.result { next with
        domEvents := next.domEvents.set! id { event with
          currentTarget := .null, phase := 0, isTrusted := false,
          bubbles := truthy (argument flags 0), cancelable := truthy (argument flags 1),
          composed := truthy (argument flags 2) } } value

private def readOption (state : State) (eventType : JSString) (options : Value) (flags : List Value) : State :=
  match ["bubbles","cancelable","composed"][flags.length]? with
  | none => create state eventType flags
  | some name =>
    let continuation : BuiltinContinuation := {
      id := ⟨"Browser.Events","Event"⟩, thisValue := .undefined,
      arguments := [.string eventType,options], phase := "option", locals := flags }
    { state with machine := readProperty { state.machine with
      continuation := .builtin continuation :: state.machine.continuation } options (key name) }

private def constructEvent (state : State) (arguments : List Value) (construct : Bool) : State :=
  if !construct || arguments.isEmpty then Browser.fail state (.exception "TypeError" "Event requires new and a type")
  else match Browser.convertArguments state ⟨"Browser.Events","Event"⟩ .undefined arguments true [(0,"string")] with
  | some next => next
  | none => Browser.checked state (toJSString (argument arguments 0)) fun eventType =>
    let options := argument arguments 1
    if options == .undefined || options == .null then create state eventType []
    else if !isObject options then Browser.fail state (.exception "TypeError" "Event options must be an object")
    else readOption state eventType options []

private def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "advance" then advance state
  else if continuation.phase == "convert" then
    Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      let index := continuation.indices[0]?.getD 0
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
      if continuation.id.name == "Event" then constructEvent state arguments true
      else registrationCall state continuation.id.name continuation.thisValue arguments false
  else if continuation.phase == "listenerOption" then
    let converted := if continuation.locals.length == 2 && value == .undefined then Value.undefined else .boolean (truthy value)
    readListenerOption state continuation.id.name continuation.thisValue continuation.arguments (continuation.locals ++ [converted])
  else if continuation.phase == "objectListener" then
    { state with machine := { state.machine with
      control := .invoke value continuation.thisValue continuation.arguments false } }
  else if continuation.phase == "option" then
    match continuation.arguments with
    | [.string eventType,options] => readOption state eventType options (continuation.locals ++ [.boolean (truthy value)])
    | _ => Browser.fail state (.fault (.invalidContinuation "Event option conversion state"))
  else state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin id receiver arguments construct) =>
    if id.name.startsWith "get on" &&
        (["Browser.Node","Browser.Element","Browser.HTMLElement","Browser.Document","Browser.HTMLDocument"].contains id.namespaceName ||
          id.namespaceName.startsWith "Browser.HTML") then
      some (BrowserInline.getter state id.namespaceName id.name receiver construct)
    else if id.namespaceName == "Browser.Constructor" && id.name == "Event" then some (constructEvent state arguments construct)
    else if id.namespaceName == "Browser.Node" && ["addEventListener","removeEventListener"].contains id.name then
      some (registrationCall state id.name receiver arguments construct)
    else if id.namespaceName == "Browser.Node" && id.name == "dispatchEvent" then
      some (if construct then Browser.fail state (.exception "TypeError" "dispatchEvent is not a constructor")
        else dispatchEvent state receiver arguments)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.Events" then some (resume state continuation value) else none
  | .unresolved (.nativeCallbackResult continuation completion) =>
    if continuation.id.namespaceName == "Browser.Events" then some (callbackComplete state continuation completion) else none
  | .unresolved (.hostGet "DOM.Event" _ name) =>
    if name == key "__proto__" then none else some (Browser.result state .undefined)
  | .unresolved (.hostHas "DOM.Event" _ name) =>
    if name == key "__proto__" then none else some (Browser.result state (.boolean false))
  | _ => none

end CookieClicker.JavaScript.BrowserEvents

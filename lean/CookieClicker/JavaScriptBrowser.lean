import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptTimestampText
import CookieClicker.JavaScriptDomSyntax
import CookieClicker.JavaScriptBrowserInterfaces
import CookieClicker.JavaScriptRandom
import CookieClicker.JavaScriptBrowserStorageState
import CookieClicker.JavaScriptBrowserEventState
import CookieClicker.JavaScriptBrowserAnimationState
import CookieClicker.JavaScriptBrowserTextSelectionState
import CookieClicker.JavaScriptBrowserCookieState
import CookieClicker.JavaScriptBrowserGeometryState
import CookieClicker.JavaScriptCssSyntax
import CookieClicker.JavaScriptBrowserInputState
import CookieClicker.JavaScriptBrowserFocusState
import CookieClicker.JavaScriptBrowserCanvasState
import CookieClicker.JavaScriptTextControl

/-! Explicit browser host state for source startup. This module records browser
objects and queued source callbacks. Unimplemented DOM, rendering, resource and
calendar operations remain model-incompleteness requests; they are not no-ops.
No game entry point, external resource, save file or native callback is executed
by these definitions. A complete browser/source refinement is still required.
-/
namespace CookieClicker.JavaScript.Browser

inductive NodeKind where
  | document
  | doctype
  | element (tag : String)
  | text (data : JSString)
  | comment (data : JSString)
  | fragment
  deriving Repr, DecidableEq

inductive ScriptStatus where
  | unstarted | parserPending | inert | started
  deriving Repr, DecidableEq

inductive ResourceStatus where
  | empty
  | pending (source : JSString)
  | image (source : JSString) (width height : Nat)
  | audio (source : JSString) (duration : UInt64) (readyState networkState : Nat)
  | failed (source : JSString)
  deriving Repr, DecidableEq

structure Listener where
  eventType : JSString
  callback : Value
  capture : Bool := false
  serial : Nat := 0
  once : Bool := false
  passive : Bool := false
  deriving Repr, DecidableEq

structure Node where
  object : ObjectId
  kind : NodeKind
  parent : Option Nat := none
  children : List Nat := []
  attributes : List DomSyntax.Attribute := []
  listeners : List Listener := []
  handlers : List BrowserEventState.Handler := []
  value : JSString := []
  textarea : TextControl.State := {}
  scriptStatus : Option ScriptStatus := none
  styleObject : Option ObjectId := none
  classListObject : Option ObjectId := none
  childNodesObject : Option ObjectId := none
  canvasContext : Option ObjectId := none
  canvasAlpha : Bool := true
  canvasDrawing : BrowserCanvasState.State := {}
  styleCache : Option (JSString × List (String × String × Bool)) := none
  /-- False once autoplay has been requested; removing the attribute cannot
  restore evidence that this element has never started native playback. -/
  mediaPlaybackPristine : Bool := true
  resourceStatus : ResourceStatus := .empty
  lastResourceOrder : Option Nat := none
  deriving Repr

structure Prototypes where
  node : ObjectId
  element : ObjectId
  htmlElement : ObjectId
  document : ObjectId
  canvas : ObjectId
  image : ObjectId
  canvasContext : ObjectId
  tokenList : ObjectId
  nodeList : ObjectId
  collection : ObjectId
  style : ObjectId
  specific : List (String × ObjectId) := []
  brands : List (String × List String) := []
  deriving Repr, DecidableEq

structure Timer where
  id : Nat
  due : Rat
  order : Nat
  nesting : Nat
  repeating : Bool
  delay : UInt64
  callback : Value
  arguments : List Value
  deriving Repr

inductive CollectionFilter where
  | tag (tag : JSString)
  | classes (names : List JSString)
  deriving Repr

structure Collection where
  object : ObjectId
  root : Nat
  filter : CollectionFilter
  deriving Repr

structure ResourceRequest where
  node : Nat
  kind : String
  source : JSString
  order : Nat
  deriving Repr

structure ResourceTask where
  request : ResourceRequest
  due : Rat
  deriving Repr

structure ActiveResource where
  task : ResourceTask
  phase : String
  deriving Repr

structure DomEvent where
  object : ObjectId
  eventType : JSString
  target : Value
  currentTarget : Value
  time : Rat
  bubbles : Bool := false
  cancelable : Bool := false
  defaultPrevented : Bool := false
  propagationStopped : Bool := false
  immediateStopped : Bool := false
  isTrusted : Bool := true
  composed : Bool := false
  phase : Nat := 0
  dispatching : Bool := false
  handlingPassive : Bool := false
  deriving Repr

structure ConsoleEvent where
  level : String
  arguments : List Value
  deriving Repr

structure State where
  machine : Machine
  prototypes : Prototypes
  nodes : Array Node := #[]
  document : Nat := 0
  stylesheets : List Css.Stylesheet := []
  stylesheetsConfigured : Bool := false
  timers : List Timer := []
  cancelledTimers : List Nat := []
  nextTimer : Nat := 1
  nextOrder : Nat := 0
  currentTimerNesting : Option Nat := none
  activeTimer : Option Timer := none
  reportedExceptions : List Value := []
  scripts : List (String × Program) := []
  nativeSeedrandom : Option ObjectId := none
  nativeTimestampMixkey : Option ObjectId := none
  timestampMixkeyActivations : Nat := 0
  mathObject : Option ObjectId := none
  freeRandom : Option ObjectId := none
  randomInputs : List Nat := []
  collections : Array Collection := #[]
  resourceRequests : List ResourceRequest := []
  resourceTasks : List ResourceTask := []
  activeResource : Option ActiveResource := none
  domEvents : Array DomEvent := #[]
  inputEvents : List (Nat × BrowserInputState.Data) := []
  focus : BrowserFocusState.State := {}
  resourceBaseURL : Option JSString := none
  windowHandlers : List BrowserEventState.Handler := []
  windowListeners : List Listener := []
  fixtureWindowData : List (JSString × Value) := []
  windowName : Option JSString := none
  configuredInstances : List (String × ObjectId) := []
  consoleEvents : Array ConsoleEvent := #[]
  nextListenerSerial : Nat := 0
  eventDispatches : List BrowserEventState.Dispatch := []
  animation : BrowserAnimationState.State := {}
  textSelection : BrowserTextSelectionState.State := {}
  storage : BrowserStorageState.State := {}
  cookieOrigin : BrowserCookieState.Origin := .unconfigured
  rectangles : Array BrowserGeometryState.Rect := #[]
  deriving Repr

def checkedNode (state : State) (id : Nat) : Checked Node :=
  match state.nodes[id]? with
  | some node => pure node
  | none => .error (.fault (.invalidContinuation "missing DOM node"))

def receiverNode (state : State) (value : Value) : Checked (Nat × Node) := do
  match value with
  | .object object =>
    let object ← checkedObject state.machine.heap object
    match object.kind with
    | .host "DOM.Node" id => pure (id, ← checkedNode state id)
    | _ => .error (.exception "TypeError" "DOM method called on incompatible receiver")
  | _ => .error (.exception "TypeError" "DOM method called on incompatible receiver")

private def refreshTextArea (state : State) (id : Nat) : Checked State := do
  let node ← checkedNode state id
  if node.kind != .element "textarea" || node.textarea.dirty then pure state else
  let text ← node.children.foldlM (fun text child => do
    let child ← checkedNode state child
    pure (text ++ (match child.kind with | .text value => value | _ => []))) []
  let next := {node with textarea := TextControl.childrenChanged node.textarea text}
  pure {state with nodes := state.nodes.set! id next}

def replaceNode (state : State) (id : Nat) (node : Node) : Checked State := do
  let old ← checkedNode state id
  -- Blink87 synchronously clears focus through native blur callbacks when a
  -- focused subtree is removed. Attribute/CSS changes may also invalidate its
  -- focusability. Until the mutation procedure runs that lifecycle, do not
  -- silently retain a focused pointer or skip those source callbacks.
  if state.textSelection.current.isSome &&
      (old.kind != node.kind || old.parent != node.parent || old.children != node.children) then
    .error (.unresolved (.unsupportedSyntax "FrameSelection: DOM mutation requires native range adjustment"))
  else if state.focus.element.isSome &&
      (old.kind != node.kind || old.parent != node.parent || old.children != node.children ||
        old.attributes != node.attributes) then
    .error (.unresolved (.unsupportedSyntax "Focus: DOM/CSS mutation requires focus lifecycle"))
  else
    let node := { node with mediaPlaybackPristine := old.mediaPlaybackPristine &&
      node.mediaPlaybackPristine && !(old.kind == .element "audio" &&
        old.attributes.any (fun attr => attr.name == "autoplay")) && !(node.kind == .element "audio" &&
        node.attributes.any (fun attr => attr.name == "autoplay")) }
    let state := { state with nodes := state.nodes.set! id node }
    let parents := if (match old.kind with | .text _ => true | _ => false) ||
        (match node.kind with | .text _ => true | _ => false) then
      old.parent.toList ++ node.parent.toList else []
    ((if node.kind == .element "textarea" then [id] else []) ++ parents).eraseDups.foldlM
      refreshTextArea state

def nodePrototype (prototypes : Prototypes) (kind : NodeKind) : Checked ObjectId := do
  match kind with
  | .document => pure prototypes.document
  | _ =>
    let name := match kind with
      | .element tag => tag | .text _ => "#text" | .comment _ => "#comment"
      | .fragment => "#fragment" | .document => "#document" | .doctype => "#doctype"
    match prototypes.specific.find? (fun p => p.1 == name) with
    | some (_,id) => pure id
    | none => .error (.unresolved (.unsupportedSyntax ("Uncatalogued DOM element interface: " ++ name)))

def allocateNode (state : State) (kind : NodeKind) : Checked (Nat × State) := do
  let prototype ← nodePrototype state.prototypes kind
  let id := state.nodes.size
  let (object, heap) := state.machine.heap.allocateObject {
    kind := .host "DOM.Node" id
    prototype := some prototype }
  pure (id, { state with
    machine := { state.machine with heap }
    nodes := state.nodes.push {
      object := object, kind := kind
      scriptStatus := if kind == .element "script" then some .unstarted else none } })

def getAttribute (node : Node) (name : String) : Option JSString :=
  (node.attributes.find? (fun attr => attr.name == name)).map (·.value)

private def catalogueHandlerProperty : Nat → Nat → String → Bool
  | 0,_,_ => false
  | fuel+1,id,name =>
    match BrowserCatalogue.objects.find? (fun object => object.id == id) with
    | none => false
    | some object =>
      if object.properties.any (fun property => property.key == .name name &&
          (match property.descriptor with | .accessor (some _) (some _) _ _ => true | _ => false)) then true
      else match object.prototype with
        | none => false
        | some parent => catalogueHandlerProperty fuel parent name

/-- The captured native interface determines which content attributes are event
handlers. An arbitrary attribute beginning with `on` is inert. This lookup uses
the initial interface table, not mutable JavaScript properties of the element. -/
def isHandlerAttribute (kind : NodeKind) (name : String) : Bool :=
  if !name.startsWith "on" || name.length ≤ 2 then false else
  match kind with
  | .element tag =>
    (BrowserCatalogue.elementTypes.find? (fun entry => entry.tag == tag)).any fun entry =>
      catalogueHandlerProperty (BrowserCatalogue.objects.size+1) entry.prototype name
  | _ => false

def handlerEventType (name : String) : JSString := JSString.ofString <|
  match name with
  | "onwebkitanimationend" => "webkitAnimationEnd"
  | "onwebkitanimationstart" => "webkitAnimationStart"
  | "onwebkitanimationiteration" => "webkitAnimationIteration"
  | "onwebkittransitionend" => "webkitTransitionEnd"
  | _ => (name.drop 2).toString

def changeHandler (handlers : List BrowserEventState.Handler) (serial : Nat)
    (eventType : JSString) (body : Option BrowserEventState.HandlerBody) :
    List BrowserEventState.Handler × Nat :=
  let previous := (handlers.find? (fun handler => handler.eventType == eventType)).getD { eventType }
  let fresh := body.isSome && previous.serial.isNone
  let updated := { previous with
    body := body
    serial := if body.isNone then none else previous.serial.or (some serial) }
  let handlers := if handlers.any (fun handler => handler.eventType == eventType) then
      handlers.map fun handler => if handler.eventType == eventType then updated else handler
    else handlers ++ [updated]
  (handlers, if fresh then serial + 1 else serial)

def handlerValue (handlers : List BrowserEventState.Handler) (eventType : JSString) : Checked Value :=
  match (handlers.find? (fun handler => handler.eventType == eventType)).bind (·.body) with
  | none => pure .null
  | some (.callback value) => pure value
  | some (.inlineText _) => .error (.unresolved (.unsupportedSyntax "Compile actual DOM event attribute in its element scope"))

def setNodeHandler (state : State) (id : Nat) (eventType : JSString)
    (body : Option BrowserEventState.HandlerBody) : Checked State := do
  let node ← checkedNode state id
  let (handlers,nextSerial) := changeHandler node.handlers state.nextListenerSerial eventType body
  replaceNode { state with nextListenerSerial := nextSerial } id { node with handlers }

def setAttribute (node : Node) (name : String) (value : JSString) : Node :=
  let node := if name == "style" then { node with styleCache := none } else node
  if node.attributes.any (fun attr => attr.name == name) then
    { node with attributes := node.attributes.map fun attr => if attr.name == name then { attr with value } else attr }
  else { node with attributes := node.attributes ++ [⟨name, value⟩] }

def connectedToDocument (state : State) : Nat → Nat → Checked Bool
  | 0, _ => .error (.fault (.invalidContinuation "Cyclic DOM ancestor links"))
  | fuel + 1, id =>
    if id == state.document then pure true else do
      match (← checkedNode state id).parent with
      | none => pure false
      | some parent => connectedToDocument state fuel parent

def setNodeAttribute (state : State) (id : Nat) (name : String) (value : JSString) : Checked State := do
  let node ← checkedNode state id
  if isHandlerAttribute node.kind name then
    let state ← replaceNode state id (setAttribute node name value)
    setNodeHandler state id (handlerEventType name) (some (.inlineText value))
  else if node.kind == .element "canvas" && ["width","height"].contains name && node.canvasContext.isSome then
    replaceNode state id { (setAttribute node name value) with canvasDrawing := BrowserCanvasState.reset node.canvasDrawing }
  else if ["crossorigin","preload"].contains name && (getAttribute node "src").isSome &&
      [NodeKind.element "img",.element "audio"].contains node.kind then
    .error (.unresolved (.unsupportedSyntax "Resource reselection after metadata mutation"))
  else
  let node := setAttribute node name value
  let kind := match node.kind with | .element tag => tag | _ => ""
  if name == "src" && ["img","audio","script"].contains kind &&
      node.scriptStatus != some .inert && node.scriptStatus != some .started then
    if node.scriptStatus == some .parserPending then
      .error (.unresolved (.unsupportedSyntax "Parser-owned script source mutation"))
    else if node.lastResourceOrder.isSome && (match node.resourceStatus with | .pending _ => true | _ => false) then
      .error (.unresolved (.unsupportedSyntax "Source replacement while a native resource is pending"))
    else if kind == "img" && (match node.resourceStatus with | .image _ _ _ => true | _ => false) then
      .error (.unresolved (.unsupportedSyntax "Image request replacement retains a native current/pending image pair"))
    else if kind == "script" && !(← connectedToDocument state (state.nodes.size + 1) id) then
      replaceNode state id { node with resourceStatus := .pending value, lastResourceOrder := none }
    else
    let node := { node with resourceStatus := .pending value, lastResourceOrder := some state.nextOrder }
    let state ← replaceNode state id node
    pure { state with
      resourceRequests := state.resourceRequests ++ [⟨id,kind,value,state.nextOrder⟩]
      nextOrder := state.nextOrder + 1 }
  else replaceNode state id node

def nodeType : NodeKind → Nat
  | .element _ => 1 | .text _ => 3 | .comment _ => 8 | .document => 9 | .fragment => 11
  | .doctype => 10

def nodeName : NodeKind → JSString
  | .element tag => JSString.ofString tag.toUpper
  | .text _ => JSString.ofString "#text"
  | .comment _ => JSString.ofString "#comment"
  | .document => JSString.ofString "#document"
  | .doctype => JSString.ofString "html"
  | .fragment => JSString.ofString "#document-fragment"

def fail (state : State) (failure : EvalFailure) : State :=
  { state with machine := JavaScript.fail state.machine failure }

def checked (state : State) (value : Checked α) (next : α → State) : State :=
  match value with | .ok value => next value | .error failure => fail state failure

def result (state : State) (value : Value) : State :=
  { state with machine := JavaScript.result state.machine value }

def nodeValue (state : State) (id : Option Nat) : Checked Value :=
  match id with
  | none => pure .null
  | some id => do pure (.object (← checkedNode state id).object)

def installAccessor (machine : Machine) (object : ObjectId) (namespaceName name : String)
    (writable : Bool := false) : Machine := Id.run do
  let mut next := Builtins.installGetter machine object namespaceName name
  if writable then
    let (setter, heap) := next.heap.allocateObject {
      kind := .builtin ⟨namespaceName, "set " ++ name⟩
      prototype := next.functionPrototype
      properties := [⟨JSString.ofString "length", .data (.number Number.one) false false true⟩] }
    next := { next with heap }
    match checkedObject next.heap object with
    | .error failure => return JavaScript.fail next failure
    | .ok receiver =>
      match ownProperty receiver (JSString.ofString name) with
      | some (.accessor getter _ enumerable configurable) =>
        match replaceObject next.heap object (setOwnProperty receiver (JSString.ofString name)
            (.accessor getter (some setter) enumerable configurable)) with
        | .ok heap => next := { next with heap }
        | .error failure => return JavaScript.fail next failure
      | _ => return JavaScript.fail next (.fault (.invalidContinuation "DOM accessor installation"))
  return next

def createPrototype (machine : Machine) (name : String) (parent : Option ObjectId) : ObjectId × Machine :=
  let (prototype, heap) := machine.heap.allocateObject { prototype := parent }
  let (constructor, next) := Builtins.installConstructor { machine with heap } name prototype 0
  let next := match next.heap.object? constructor with
    | none => JavaScript.fail next (.fault (.missingObject constructor))
    | some object => match next.heap.writeObject constructor { object with kind := .builtin ⟨"Browser.Constructor", name⟩ } with
      | none => JavaScript.fail next (.fault (.missingObject constructor))
      | some heap => { next with heap }
  (prototype, next)

/-- Prototype identities for the source-used browser classes. Registered host
methods still require an implementation; this does not certify a full DOM. -/
def initial : State := Id.run do
  let mut machine := Builtins.standardMachine
  let (node, next) := createPrototype machine "Node" machine.objectPrototype
  machine := next
  let (element, next) := createPrototype machine "Element" (some node)
  machine := next
  let (htmlElement, next) := createPrototype machine "HTMLElement" (some element)
  machine := next
  let (document, next) := createPrototype machine "Document" (some node)
  machine := next
  let (canvas, next) := createPrototype machine "HTMLCanvasElement" (some htmlElement)
  machine := next
  let (image, next) := createPrototype machine "HTMLImageElement" (some htmlElement)
  machine := next
  let (canvasContext, next) := createPrototype machine "CanvasRenderingContext2D" machine.objectPrototype
  machine := next
  let (tokenList, next) := createPrototype machine "DOMTokenList" machine.objectPrototype
  machine := next
  let (nodeList, next) := createPrototype machine "NodeList" machine.objectPrototype
  machine := next
  let (collection, next) := createPrototype machine "HTMLCollection" machine.objectPrototype
  machine := next
  let (style, next) := createPrototype machine "CSSStyleDeclaration" machine.objectPrototype
  machine := next
  machine := Builtins.installMethods machine node "Browser.Node"
    [("appendChild",1),("removeChild",1),("insertBefore",2),("cloneNode",1),
     ("addEventListener",2),("removeEventListener",2),("dispatchEvent",1)]
  machine := Builtins.installMethods machine element "Browser.Element"
    [("getAttribute",1),("setAttribute",2),("removeAttribute",1),("getBoundingClientRect",0),
     ("getElementsByTagName",1),("getElementsByClassName",1),("querySelector",1),("querySelectorAll",1)]
  machine := Builtins.installMethods machine document "Browser.Document"
    [("createElement",1),("createElementNS",2),("createTextNode",1),("createComment",1),("createDocumentFragment",0),
     ("getElementById",1),("getElementsByTagName",1),("getElementsByClassName",1),
     ("querySelector",1),("querySelectorAll",1),("hasFocus",0)]
  machine := Builtins.installMethods machine canvas "Browser.Canvas" [("getContext",1),("toDataURL",0)]
  machine := Builtins.installMethods machine canvasContext "Browser.CanvasContext"
    [("drawImage",3),("fillRect",4),("clearRect",4),("save",0),("restore",0),
     ("translate",2),("rotate",1),("scale",2),("measureText",1),("createPattern",2)]
  machine := installAccessor machine collection "Browser.Collection" "length"
  machine := Builtins.installMethods machine collection "Browser.Collection" [("item",1),("namedItem",1)]
  for (name, writable) in [("nodeType",false),("nodeName",false),("parentNode",false),
      ("parentElement",false),("firstChild",false),("lastChild",false),("textContent",true)] do
    machine := installAccessor machine node "Browser.Node" name writable
  for name in ["id", "className", "innerHTML"] do
    machine := installAccessor machine element "Browser.Element" name true
  machine := installAccessor machine element "Browser.Element" "tagName"
  for name in ["body", "head", "documentElement"] do
    machine := installAccessor machine document "Browser.Document" name
  machine := Builtins.installMethods machine machine.globalObject "Browser.Timer"
    [("setTimeout",1),("setInterval",1),("clearTimeout",0),("clearInterval",0)]
  for name in ["window", "self", "top", "parent", "globalThis"] do
    machine := Builtins.putData machine machine.globalObject name (.object machine.globalObject)
  let prototypes : Prototypes := {
    node := node, element, htmlElement, document, canvas, image, canvasContext
    tokenList, nodeList, collection, style }
  let (installedMachine, prototypes, configuredInstances) : Machine × Prototypes × List (String × ObjectId) := match BrowserInterfaces.install machine with
    | .error failure => (JavaScript.fail machine failure,prototypes,[])
    | .ok installed =>
      let resolve := fun (name : String) (fallback : ObjectId) => ((installed.prototypes.find? (fun p => p.1 == name)).map Prod.snd).getD fallback
      let elements : List (String × ObjectId) := BrowserCatalogue.elementTypes.toList.filterMap fun (element : BrowserCatalogue.ElementType) =>
        installed.identities[element.prototype]?.map (fun prototype => (element.tag,prototype))
      let specific : List (String × ObjectId) := elements ++ ([("audio","HTMLAudioElement"),("img","HTMLImageElement"),
          ("#text","Text"),("#comment","Comment"),("#fragment","DocumentFragment"),
          ("#doctype","DocumentType"),("#DOMRect","DOMRect"),("#DOMRectReadOnly","DOMRectReadOnly"),
          ("#Event","Event"),("#Storage","Storage"),("#UIEvent","UIEvent"),
          ("#MouseEvent","MouseEvent"),("#KeyboardEvent","KeyboardEvent"),
          ("#FocusEvent","FocusEvent")].filterMap fun (tag,interface) =>
            (installed.prototypes.find? (fun p => p.1 == interface)).map (fun p => (tag,p.2))
        )
      (installed.machine,{ prototypes with
        document := resolve "HTMLDocument" document
        specific := specific
        brands := installed.brands },installed.instances)
  let mathObject : Option ObjectId := do
    let global ← installedMachine.heap.object? installedMachine.globalObject
    match ownProperty global (JSString.ofString "Math") with
    | some (.data (.object id) _ _ _) => some id
    | _ => none
  let freeRandom : Option ObjectId := do
    let math ← mathObject >>= installedMachine.heap.object?
    match ownProperty math (JSString.ofString "random") with
    | some (.data (.object id) _ _ _) => some id
    | _ => none
  let state : State := { machine := installedMachine, prototypes, mathObject, freeRandom, configuredInstances }
  let (documentId, state) ← match allocateNode state .document with
    | .error failure => return fail state failure
    | .ok value => pure value
  match state.nodes[documentId]? with
  | none => return fail state (.fault (.invalidContinuation "initial document allocation"))
  | some node =>
    let some (_,nativeDocument) := configuredInstances.find? (fun pair => pair.1 == "document") |
      return fail state (.fault (.invalidContinuation "Native Document instance catalogue missing"))
    match (do
      let native ← checkedObject state.machine.heap nativeDocument
      let logical ← checkedObject state.machine.heap node.object
      replaceObject state.machine.heap node.object { logical with
        properties := native.properties, propertiesComplete := native.propertiesComplete }) with
    | .error failure => return fail state failure
    | .ok heap => return { state with
        machine := { state.machine with heap }
        document := documentId
        configuredInstances := configuredInstances.map (fun pair => if pair.1 == "document" then (pair.1,node.object) else pair) }

private def key := JSString.ofString
private def argument := Builtins.argument

private def asciiString (units : JSString) : Checked String :=
  if units.all (fun u => u.toNat < 128) then
    pure (String.ofList (units.map (fun u => Char.ofNat u.toNat)))
  else .error (.unresolved (.unsupportedSyntax "Non-ASCII DOM qualified name"))

private def asciiName (units : JSString) : Checked String := do
  let name ← asciiString units
  let first := name.toList.head?
  if !first.any (fun c => c.isAlpha || c == '_' || c == ':') ||
      !(name.toList.all fun c => c.isAlphanum || c == '_' || c == ':' || c == '-' || c == '.') then
    .error (.exception "InvalidCharacterError" "Invalid XML name")
  else pure name

private def splitSpaces (text : JSString) : List JSString :=
  text.splitOn 32 |>.flatMap (fun part => part.splitOn 9) |>.flatMap (fun part => part.splitOn 10) |>
    List.flatMap (fun part => part.splitOn 12) |>.flatMap (fun part => part.splitOn 13) |>.filter (!·.isEmpty)

private def escapeText (text : JSString) (isAttribute : Bool := false) : JSString :=
  text.flatMap fun unit =>
    if unit == 38 then key "&amp;" else if unit == 160 then key "&nbsp;"
    else if unit == 34 && isAttribute then key "&quot;"
    else if unit == 60 && !isAttribute then key "&lt;"
    else if unit == 62 && !isAttribute then key "&gt;" else [unit]

def serializeNodes (state : State) : Nat → List Nat → Bool → Checked JSString
  | 0, [], _ => pure []
  | 0, _, _ => .error (.fault (.invalidContinuation "cyclic DOM serialization"))
  | _ + 1, [], _ => pure []
  | fuel + 1, id :: rest, raw => do
    let node ← checkedNode state id
    let first ← match node.kind with
      | .text text => pure (if raw then text else escapeText text)
      | .comment text => pure (key "<!--" ++ text ++ key "-->")
      | .doctype => pure (key "<!DOCTYPE html>")
      | .document | .fragment => serializeNodes state fuel node.children false
      | .element tag => do
        let attrs := node.attributes.flatMap fun attr =>
          key (" " ++ attr.name ++ "=\"") ++ escapeText attr.value true ++ key "\""
        let start := key ("<" ++ tag) ++ attrs ++ key ">"
        if ["area","base","basefont","bgsound","link","meta","br","wbr","col","embed","hr","img","input","keygen","param","source","track"].contains tag then pure start
        else
          let contents ← serializeNodes state fuel node.children
            (["style","script","xmp","iframe","noembed","noframes","plaintext"].contains tag)
          pure (start ++ contents ++ key ("</" ++ tag ++ ">"))
    pure (first ++ (← serializeNodes state fuel rest raw))

def innerHTML (state : State) (id : Nat) : Checked JSString := do
  let node ← checkedNode state id
  let raw := match node.kind with
    | .element tag => ["style","script","xmp","iframe","noembed","noframes","plaintext"].contains tag
    | _ => false
  serializeNodes state (state.nodes.size + 1) node.children raw

def descendants (state : State) : Nat → List Nat → Checked (List Nat)
  | 0, [] => pure []
  | 0, _ => .error (.fault (.invalidContinuation "cyclic DOM child links"))
  | _ + 1, [] => pure []
  | fuel + 1, id :: rest => do
    let node ← checkedNode state id
    pure (id :: (← descendants state fuel (node.children ++ rest)))

def subtree (state : State) (root : Nat) : Checked (List Nat) :=
  descendants state (state.nodes.size + 1) [root]

def collectionMembers (state : State) (id : Nat) : Checked (List Nat) := do
  let some collection := state.collections[id]? |
    .error (.fault (.invalidContinuation "Missing live DOM collection"))
  let children := (← checkedNode state collection.root).children
  let ids ← descendants state (state.nodes.size + 1) children
  pure (ids.filter fun id => (state.nodes[id]?).any fun node =>
    match node.kind with
    | .element tag => match collection.filter with
      | .tag name => name == key "*" || name == key tag
      | .classes names => !names.isEmpty && names.all (fun name =>
        (splitSpaces ((getAttribute node "class").getD [])).contains name)
    | _ => false)

def allocateCollection (state : State) (root : Nat) (filter : CollectionFilter) : State :=
  let id := state.collections.size
  let (object, heap) := state.machine.heap.allocateObject {
    kind := .host "DOM.Collection" id, prototype := some state.prototypes.collection }
  result { state with
    machine := { state.machine with heap }
    collections := state.collections.push ⟨object, root, filter⟩ } (.object object)

def collectionId (state : State) (value : Value) : Checked Nat := do
  match value with
  | .object id => match (← checkedObject state.machine.heap id).kind with
    | .host "DOM.Collection" id => pure id
    | _ => .error (.exception "TypeError" "HTMLCollection receiver required")
  | _ => .error (.exception "TypeError" "HTMLCollection receiver required")

def collectionProperty (state : State) (id : Nat) (name : JSString) : Checked Value := do
  let members ← collectionMembers state id
  match arrayIndex name with
  | some index =>
    match members[index]? with
    | none => pure .undefined
    | some node => nodeValue state (some node)
  | none =>
    let found := if name.isEmpty then none else members.find? fun node =>
      (state.nodes[node]?).any fun n => getAttribute n "id" == some name || getAttribute n "name" == some name
    match found with
    | none => pure .undefined
    | some node => nodeValue state (some node)

def collectionNamedItem (state : State) (id : Nat) (name : JSString) : Checked Value := do
  let members ← collectionMembers state id
  let found := if name.isEmpty then none else members.find? fun node =>
    (state.nodes[node]?).any fun n => getAttribute n "id" == some name || getAttribute n "name" == some name
  nodeValue state found

def nodeBrand (state : State) (namespaceName : String) (receiver : Value) : Checked Unit := do
  let (_, node) ← receiverNode state receiver
  let kind := match node.kind with
    | .element tag => tag
    | .document => "#document"
    | .text _ => "#text"
    | .comment _ => "#comment"
    | .doctype => "#doctype"
    | .fragment => "#fragment"
  let name := if namespaceName == "Browser.Canvas" then "HTMLCanvasElement"
    else (namespaceName.drop 8).toString
  let some (_,brands) := state.prototypes.brands.find? (fun pair => pair.1 == kind) |
    .error (.unresolved (.unsupportedSyntax ("Uncatalogued native DOM brand: " ++ kind)))
  if brands.contains name then pure ()
  else .error (.exception "TypeError" "DOM interface receiver has incompatible internal type")

def detach (state : State) (child : Nat) : Checked State := do
  let node ← checkedNode state child
  let state ← match node.parent with
    | none => pure state
    | some parent => do
      let parentNode ← checkedNode state parent
      replaceNode state parent { parentNode with children := parentNode.children.filter (· != child) }
  replaceNode state child { node with parent := none }

/-- A detached external script starts loading only when its subtree becomes
connected. No queued task is discarded merely because its node was detached. -/
def activateConnectedScripts (state : State) (root : Nat) : Checked State := do
  if !(← connectedToDocument state (state.nodes.size + 1) root) then pure state else
    (← subtree state root).foldlM (fun state id => do
      let node ← checkedNode state id
      if node.kind == .element "script" && node.scriptStatus == some .unstarted && node.lastResourceOrder.isNone then
        match getAttribute node "src" with
        | some source => setNodeAttribute state id "src" source
        | none => if node.children.isEmpty then pure state else
            .error (.unresolved (.unsupportedSyntax "Connected inline script compilation and execution"))
      else pure state) state

def append (state : State) (parent child : Nat) (before : Option Nat := none) : Checked State := do
  let parentNode ← checkedNode state parent
  let childNode ← checkedNode state child
  if parent == child || (← subtree state child).contains parent then
    .error (.exception "HierarchyRequestError" "A node cannot contain itself")
  else if before.any (fun id => !parentNode.children.contains id) then
    .error (.exception "NotFoundError" "Reference node is not a child")
  else
    match parentNode.kind, childNode.kind with
    | .text _, _ | .comment _, _ | .doctype, _ | _, .document | _, .doctype =>
      .error (.exception "HierarchyRequestError" "Invalid node insertion")
    | .document, _ | _, .fragment =>
      .error (.unresolved (.unsupportedSyntax "Document or fragment insertion validation"))
    | _, _ =>
      let before := if before == some child then
        (parentNode.children.dropWhile (· != child)).drop 1 |>.head? else before
      let state ← detach state child
      let parentNode ← checkedNode state parent
      let children := match before with
        | none => parentNode.children ++ [child]
        | some ref => (parentNode.children.takeWhile (· != ref)) ++ [child] ++
            parentNode.children.dropWhile (· != ref)
      let state ← replaceNode state parent { parentNode with children }
      let state ← replaceNode state child { childNode with parent := some parent }
      activateConnectedScripts state child

def textContent (state : State) (root : Nat) : Checked Value := do
  let node ← checkedNode state root
  match node.kind with
  | .document | .doctype => pure .null
  | .text text | .comment text => pure (.string text)
  | _ =>
    let ids ← subtree state root
    let texts ← ids.mapM fun id => do
      match (← checkedNode state id).kind with
      | .text text => pure text
      | _ => pure []
    pure (.string texts.flatten)

def replaceChildren (state : State) (parent : Nat) (children : List Nat) : Checked State := do
  let node ← checkedNode state parent
  let state ← node.children.foldlM (fun state id => do
    let child ← checkedNode state id
    replaceNode state id { child with parent := none }) state
  let state ← replaceNode state parent { node with children }
  children.foldlM (fun state id => do
    let child ← checkedNode state id
    replaceNode state id { child with parent := some parent }) state

def allocateParsed (state : State) : Nat → List DomSyntax.Node → Checked (List Nat × State)
  | 0, [] => pure ([], state)
  | 0, _ => .error (.unresolved (.unsupportedSyntax "DOM parsed-tree allocation budget"))
  | _ + 1, [] => pure ([], state)
  | fuel + 1, first :: rest => do
    let kind := match first with
      | .text text => NodeKind.text text
      | .comment text => NodeKind.comment text
      | .element tag _ _ => NodeKind.element tag
    let (id, state) ← allocateNode state kind
    let state ← match first with
      | .element _ attributes children => do
        let node ← checkedNode state id
        let state ← replaceNode state id { node with
          attributes
          scriptStatus := if node.kind == .element "script" then some .inert else node.scriptStatus }
        let state ← attributes.foldlM (fun state attr =>
          if isHandlerAttribute node.kind attr.name then
            setNodeHandler state id (handlerEventType attr.name) (some (.inlineText attr.value))
          else pure state) state
        let state ← if node.kind == .element "img" || node.kind == .element "audio" then
          match attributes.find? (fun attr => attr.name == "src") with
          | some attr => setNodeAttribute state id "src" attr.value
          | none => pure state
          else pure state
        let (children, state) ← allocateParsed state fuel children
        replaceChildren state id children
      | _ => pure state
    let (remaining, state) ← allocateParsed state fuel rest
    pure (id :: remaining, state)

/-- The strict source-file parser creates the initial document tree. Scripts
are marked pending, not executed by parsing; the bootstrap runner must execute
their pinned source programs in native parser order before exposing user input. -/
def initializeDocument (state : State) (source : JSString) : Checked State := do
  let document ← checkedNode state state.document
  if !document.children.isEmpty then
    .error (.fault (.invalidContinuation "Document initialization after tree construction"))
  else
    let parsed ← match DomSyntax.parseDocument source with
      | .ok parsed => pure parsed
      | .error error => .error (.unresolved (.unsupportedSyntax ("HTML document: " ++ reprStr error)))
    let (children, state) ← parsed.foldlM (fun (children,state) item => do
      match item with
      | .doctype =>
        let (id,state) ← allocateNode state .doctype
        pure (children ++ [id],state)
      | .content node =>
        let (ids,state) ← allocateParsed state (source.length + 2) [node]
        pure (children ++ ids,state)) ([],state)
    let state ← replaceChildren state state.document children
    let nodes := state.nodes.map fun node =>
      if node.kind == .element "script" then { node with scriptStatus := some .parserPending } else node
    pure { state with nodes }

def setInnerHTML (state : State) (id : Nat) (html : JSString) : Checked State := do
  let node ← checkedNode state id
  match node.kind with
  | .element tag =>
    match DomSyntax.parseFragment tag html with
    | .error error => .error (.unresolved (.unsupportedSyntax ("HTML fragment: " ++ reprStr error)))
    | .ok parsed =>
      let (children, state) ← allocateParsed state (html.length + 2) parsed
      replaceChildren state id children
  | _ => .error (.exception "TypeError" "innerHTML requires an Element")

private def lowerAscii (text : JSString) : JSString :=
  text.map fun unit => if 65 ≤ unit.toNat && unit.toNat ≤ 90 then UInt16.ofNat (unit.toNat + 32) else unit

private def enumAttribute (node : Node) (name fallback : String) (valid : List String) : JSString :=
  let value := lowerAscii ((getAttribute node name).getD [])
  if valid.any (fun name => value == key name) then value else key fallback

def getter (state : State) (name : String) (thisValue : Value) (namespaceName : String := "Browser.Node") : State :=
  checked state (receiverNode state thisValue) fun (id, node) =>
    if name == "nodeType" then result state (.number (Number.ofNat (nodeType node.kind)))
    else if name == "nodeName" || name == "tagName" then result state (.string (nodeName node.kind))
    else if name == "parentNode" then checked state (nodeValue state node.parent) (result state)
    else if name == "parentElement" then checked state (do
      match node.parent with
      | none => pure .null
      | some parent => match (← checkedNode state parent).kind with
        | .element _ => nodeValue state (some parent)
        | _ => pure .null) (result state)
    else if name == "firstChild" || name == "lastChild" then
      checked state (nodeValue state (if name == "firstChild" then node.children.head? else node.children.getLast?)) (result state)
    else if name == "textContent" then checked state (textContent state id) (result state)
    else if name == "nodeValue" then
      result state (match node.kind with | .text text | .comment text => .string text | _ => .null)
    else if name == "innerHTML" then checked state (innerHTML state id) (fun value => result state (.string value))
    else if name == "id" || name == "className" then
      result state (.string ((getAttribute node (if name == "id" then "id" else "class")).getD []))
    else if node.kind == .doctype && ["name","publicId","systemId"].contains name then
      result state (.string (if name == "name" then key "html" else []))
    else if name == "type" && node.kind == .element "input" then
      result state (.string (enumAttribute node "type" "text"
        ["hidden","text","search","tel","url","email","password","date","month","week","time",
         "datetime-local","number","range","color","checkbox","radio","file","submit","image","reset","button"]))
    else if name == "type" && node.kind == .element "button" then
      result state (.string (enumAttribute node "type" "submit" ["submit","reset","button"]))
    else if name == "type" && node.kind == .element "select" then
      result state (.string (key (if (getAttribute node "multiple").isSome then "select-multiple" else "select-one")))
    else if name == "type" && node.kind == .element "textarea" then result state (.string (key "textarea"))
    else if name == "preload" then
      let value := if getAttribute node "preload" == some [] then key "auto"
        else enumAttribute node "preload" "metadata" ["none","metadata","auto"]
      result state (.string value)
    else if name == "crossOrigin" then
      match getAttribute node "crossorigin" with
      | none => result state .null
      | some _ => result state (.string (enumAttribute node "crossorigin" "anonymous" ["anonymous","use-credentials"]))
    else if ["type","media","alt","title"].contains name then
      result state (.string ((getAttribute node name).getD []))
    else if name.startsWith "on" then
      checked state (handlerValue node.handlers (handlerEventType name)) (result state)
    else if ["body", "head", "documentElement"].contains name then checked state (do
      let ids ← subtree state id
      let target := if name == "documentElement" then "html" else name
      let found := ids.find? (fun i => (state.nodes[i]?).any (fun n => n.kind == .element target))
      nodeValue state found) (result state)
    else fail state (.unresolved (.builtin ⟨namespaceName, "get " ++ name⟩ thisValue [] false))

def setter (state : State) (name : String) (thisValue value : Value) (namespaceName : String := "Browser.Node") : State :=
  checked state (receiverNode state thisValue) fun (id, node) =>
  if name.startsWith "on" then
    checked state (Builtins.isCallable state.machine value) fun callable =>
      if !callable && value != .null && value != .undefined then
        fail state (.unresolved (.unsupportedSyntax "Noncallable EventHandler property conversion"))
      else
        let eventType := handlerEventType name
        checked state (setNodeHandler state id eventType (if callable then some (.callback value) else none))
          (fun state => result state .undefined)
  else
  if name == "crossOrigin" && (value == .null || value == .undefined) then
    if (getAttribute node "src").isSome then fail state (.unresolved (.unsupportedSyntax "Resource reselection after metadata removal"))
    else checked state (replaceNode state id { node with attributes := node.attributes.filter (fun attr => attr.name != "crossorigin") })
      (fun next => result next .undefined)
  else checked state (if ((name == "textContent" || name == "nodeValue") && (value == .null || value == .undefined)) ||
      (name == "innerHTML" && value == .null) then pure [] else toJSString value) fun text =>
    if name == "id" || name == "className" then
      checked state (replaceNode state id (setAttribute node (if name == "id" then "id" else "class") text))
        (fun state => result state .undefined)
    else if name == "innerHTML" then checked state (setInnerHTML state id text) (fun state => result state .undefined)
    else if ["type","media","preload","alt","title","crossOrigin"].contains name then
      checked state (setNodeAttribute state id (if name == "crossOrigin" then "crossorigin" else name) text)
        (fun state => result state .undefined)
    else if name == "src" then
      checked state (setNodeAttribute state id "src" text) (fun next => result next .undefined)
    else if name == "nodeValue" then
      let kind := match node.kind with | .text _ => .text text | .comment _ => .comment text | other => other
      checked state (replaceNode state id { node with kind }) (fun next => result next .undefined)
    else if name == "textContent" then
      match node.kind with
      | .document | .doctype => result state .undefined
      | .text _ => checked state (replaceNode state id { node with kind := .text text }) (fun state => result state .undefined)
      | .comment _ => checked state (replaceNode state id { node with kind := .comment text }) (fun state => result state .undefined)
      | _ =>
        checked state (do
          if text.isEmpty then pure ([],state) else
            let (child, state) ← allocateNode state (.text text)
            pure ([child],state)) fun (children,state) =>
          checked state (replaceChildren state id children) (fun state => result state .undefined)
    else fail state (.unresolved (.builtin ⟨namespaceName, "set " ++ name⟩ thisValue [value] false))

/-- Primitive arguments are converted by the same source callback machinery as
ordinary JavaScript. The adapter never evaluates a user callback externally. -/
def convertArguments (state : State) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) (construct : Bool) (conversions : List (Nat × String)) : Option State :=
  match conversions.find? (fun (index, _) => isObject (argument arguments index)) with
  | none => none
  | some (index, hint) => some { state with machine := { state.machine with
      control := .toPrimitive (argument arguments index) hint
      continuation := .builtin {
        id, phase := "convert", thisValue, arguments
        locals := [.string (key hint)]
        indices := [index, if construct then 1 else 0] } :: state.machine.continuation } }

def convertedArgument (continuation : BuiltinContinuation) (value : Value) : Checked Value :=
  if continuation.locals.head? == some (.string (key "string")) then Value.string <$> toJSString value
  else if continuation.locals.head? == some (.string (key "number")) then Value.number <$> toNumber value
  else .error (.fault (.invalidContinuation "Missing host argument conversion hint"))

def timerDelay (nesting : Option Nat) (bits : UInt64) : Nat :=
  let milliseconds := (max 0 (Number.toInt32 bits)).toNat
  if nesting.getD 0 + 1 ≥ 5 then max 4 milliseconds else max 1 milliseconds

def nextTimerIdentifier (id : Nat) : Nat := if id ≥ 2147483647 then 1 else id + 1

def unusedTimerIdentifier (state : State) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, candidate =>
    if state.timers.any (fun timer => timer.id == candidate) then
      unusedTimerIdentifier state fuel (nextTimerIdentifier candidate)
    else some candidate

def timerCall (state : State) (name : String) (arguments : List Value) : State :=
  if name == "clearTimeout" || name == "clearInterval" then
    checked state (toNumber (argument arguments 0)) fun bits =>
      let id := (Number.toInt32 bits).toNat
      result { state with
        timers := state.timers.filter (fun timer => timer.id != id)
        cancelledTimers := id :: state.cancelledTimers } .undefined
  else checked state (Builtins.isCallable state.machine (argument arguments 0)) fun callback =>
    if !callback then fail state (.unresolved (.unsupportedSyntax "String-valued HTML timer compilation"))
    else checked state (toNumber (argument arguments 1)) fun delay =>
      match unusedTimerIdentifier state (state.timers.length + 1) state.nextTimer with
      | none => fail state (.unresolved (.unsupportedSyntax "Exhausted Chromium positive timer IDs"))
      | some timerId =>
      let timer : Timer := {
        id := timerId, due := state.machine.elapsed + timerDelay state.currentTimerNesting delay
        order := state.nextOrder, nesting := state.currentTimerNesting.getD 0 + 1
        repeating := name == "setInterval", delay, callback := argument arguments 0, arguments := arguments.drop 2 }
      result { state with
        timers := state.timers ++ [timer], nextTimer := nextTimerIdentifier timerId
        nextOrder := state.nextOrder + 1 } (.number (Number.ofNat timer.id))

def windowCall (state : State) (id : BuiltinId) (receiver : Value) (arguments : List Value) : State :=
  if receiver != .object state.machine.globalObject then fail state (.exception "TypeError" "Window receiver required")
  else if id.name.startsWith "get " then
    let name := (id.name.drop 4).toString
    if name.startsWith "on" then
      checked state (handlerValue state.windowHandlers (handlerEventType name)) (result state)
    else match state.configuredInstances.find? (fun p => p.1 == name) with
      | some (_,object) => result state (.object object)
      | none => match state.fixtureWindowData.find? (fun p => p.1 == key name) with
        | some (_,value) => result state value
        | none => fail state (.unresolved (.builtin id receiver arguments false))
  else if id.name.startsWith "set on" then
    let name := handlerEventType ((id.name.drop 4).toString)
    let value := argument arguments 0
    checked state (Builtins.isCallable state.machine value) fun callable =>
      if !callable && value != .null && value != .undefined then
        fail state (.unresolved (.unsupportedSyntax "Noncallable Window EventHandler conversion"))
      else
        let (handlers,nextSerial) := changeHandler state.windowHandlers state.nextListenerSerial name
          (if callable then some (.callback value) else none)
        result { state with windowHandlers := handlers, nextListenerSerial := nextSerial } .undefined
  else if id.name == "addEventListener" || id.name == "removeEventListener" then
    checked state (toJSString (argument arguments 0)) fun eventType =>
      let callback := argument arguments 1
      if callback != .undefined && callback != .null && !isObject callback then
        fail state (.exception "TypeError" "Event listener callback must be an object or null")
      else if isObject (argument arguments 2) then fail state (.unresolved (.unsupportedSyntax "Window event listener options dictionary"))
      else if callback == .undefined || callback == .null then result state .undefined
      else
        let capture := truthy (argument arguments 2)
        let sameListener := fun (listener : Listener) => listener.eventType == eventType && listener.callback == callback && listener.capture == capture
        let fresh := id.name == "addEventListener" && !state.windowListeners.any sameListener
        let listeners := if id.name == "removeEventListener" then state.windowListeners.filter (!sameListener ·)
          else if state.windowListeners.any sameListener then state.windowListeners
          else state.windowListeners ++ [{ eventType,callback,capture,serial := state.nextListenerSerial }]
        result { state with
          windowListeners := listeners
          nextListenerSerial := state.nextListenerSerial + (if fresh then 1 else 0) } .undefined
  else fail state (.unresolved (.builtin id receiver arguments false))

def dispatch (state : State) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  let windowEvent := thisValue == .object state.machine.globalObject &&
    id.namespaceName == "Browser.Node" && ["addEventListener","removeEventListener","dispatchEvent"].contains id.name
  if id.namespaceName == "Browser.Collection" then
    if let .error failure := collectionId state thisValue then return fail state failure
  else if ["Browser.Node","Browser.Element","Browser.HTMLElement","Browser.Document","Browser.HTMLDocument",
      "Browser.Text","Browser.Comment","Browser.DocumentType","Browser.Canvas"].contains id.namespaceName || id.namespaceName.startsWith "Browser.HTML" then
    if !windowEvent then
    if let .error failure := nodeBrand state id.namespaceName thisValue then return fail state failure
  if id.namespaceName == "Browser.HTMLBodyElement" &&
      (id.name.startsWith "get on" || id.name.startsWith "set on") then
    return fail state (.unresolved (.unsupportedSyntax "Body event handler forwarding to Window"))
  let required := if id.name.startsWith "set " && id.name != "set innerHTML" then 1 else
    if ["setAttribute","createElementNS","insertBefore","addEventListener","removeEventListener"].contains id.name then 2 else
    if ["createElement","createTextNode","createComment","getElementById","getAttribute","removeAttribute",
        "getElementsByTagName","getElementsByClassName","appendChild","removeChild","item","namedItem",
        "setTimeout","setInterval"].contains id.name then 1 else 0
  if arguments.length < required then return fail state (.exception "TypeError" "Insufficient arguments for native DOM operation")
  let stringArgs := if (id.name.startsWith "set " && !id.name.startsWith "set on") ||
      ["createElement", "createTextNode", "createComment", "getElementById", "getAttribute", "removeAttribute",
       "getElementsByTagName", "getElementsByClassName", "namedItem"].contains id.name
      then [(0, "string")] else if id.name == "createElementNS" || id.name == "setAttribute" then [(0,"string"),(1,"string")]
      else if ["addEventListener", "removeEventListener"].contains id.name then [(0,"string")]
      else if id.namespaceName == "Browser.Timer" then [(if id.name.startsWith "clear" then 0 else 1,"number")]
      else if id.namespaceName == "Browser.Collection" && id.name == "item" then [(0,"number")] else []
  if let some next := convertArguments state id thisValue arguments construct stringArgs then return next
  if id.namespaceName == "Browser.Timer" && !construct then return timerCall state id.name arguments
  if (id.namespaceName == "Browser.Window" || windowEvent) && !construct then return windowCall state id thisValue arguments
  if id.namespaceName == "Browser.Constructor" && (id.name == "Audio" || id.name == "Image") then
    -- The empty legacy factories create real detached HTML elements. Supplying
    -- a URL or dimensions needs the corresponding resource/IDL operation.
    if arguments.any (· != .undefined) then
      return fail state (.unresolved (.builtin id thisValue arguments construct))
    return checked state (allocateNode state (.element (if id.name == "Audio" then "audio" else "img"))) fun (created,next) =>
      checked next (do
      if id.name != "Audio" then pure next else
        let node ← checkedNode next created
        replaceNode next created (setAttribute node "preload" (key "auto"))) fun next =>
      checked next (nodeValue next (some created)) (result next)
  if construct then return fail state (.unresolved (.builtin id thisValue arguments true))
  if id.namespaceName == "Browser.Collection" then
    return checked state (collectionId state thisValue) fun collection =>
      checked state (collectionMembers state collection) fun members =>
      if id.name == "get length" then result state (.number (Number.ofNat members.length))
      else if id.name == "item" then checked state (toNumber (argument arguments 0)) fun bits =>
        checked state (nodeValue state members[(Number.toUInt32 bits).toNat]?) (result state)
      else if id.name == "namedItem" then checked state (toJSString (argument arguments 0)) fun name =>
        checked state (collectionNamedItem state collection name) (result state)
      else fail state (.unresolved (.builtin id thisValue arguments false))
  if !["Browser.Node","Browser.Element","Browser.HTMLElement","Browser.Document","Browser.HTMLDocument",
      "Browser.Text","Browser.Comment","Browser.DocumentType","Browser.Canvas"].contains id.namespaceName &&
      !id.namespaceName.startsWith "Browser.HTML" then
    return fail state (.unresolved (.builtin id thisValue arguments construct))
  if id.name.startsWith "get " then return getter state (id.name.drop 4).toString thisValue id.namespaceName
  if id.name.startsWith "set " then return setter state (id.name.drop 4).toString thisValue (argument arguments 0) id.namespaceName
  return checked state (receiverNode state thisValue) fun (receiverId, node) =>
    if ["createElement", "createElementNS", "createTextNode", "createComment", "createDocumentFragment"].contains id.name then
      checked state (do
        if node.kind != .document then .error (.exception "TypeError" "Document method receiver") else pure ()) fun _ =>
      checked state (if id.name == "createDocumentFragment" then pure [] else
        toJSString (argument arguments (if id.name == "createElementNS" then 1 else 0))) fun text =>
      checked state (if id.name == "createElementNS" then do
        let ns ← toJSString (argument arguments 0)
        if ns == key "http://www.w3.org/1999/xhtml" then pure ()
        else .error (.unresolved (.unsupportedSyntax "Non-HTML element namespace")) else pure ()) fun _ =>
      checked state (if id.name == "createElement" || id.name == "createElementNS" then do
        let name ← asciiName text
        if id.name == "createElementNS" && name.contains ':' then
          .error (.unresolved (.unsupportedSyntax "Namespace-qualified HTML element name"))
        else pure (.element (if id.name == "createElement" then name.toLower else name))
        else pure (if id.name == "createTextNode" then .text text else if id.name == "createComment" then .comment text else .fragment)) fun kind =>
      checked state (allocateNode state kind) fun (created,state) =>
        checked state (nodeValue state (some created)) (result state)
    else if id.name == "getElementById" then checked state (toJSString (argument arguments 0)) fun wanted =>
      checked state (subtree state receiverId) fun ids =>
      let found := if wanted.isEmpty then none else ids.find? (fun i =>
        (state.nodes[i]?).any (fun n => getAttribute n "id" == some wanted))
      checked state (nodeValue state found) (result state)
    else if id.name == "getElementsByTagName" || id.name == "getElementsByClassName" then
      checked state (toJSString (argument arguments 0)) fun wanted =>
      let lower := wanted.map (fun u => if 65 ≤ u.toNat && u.toNat ≤ 90 then UInt16.ofNat (u.toNat + 32) else u)
      allocateCollection state receiverId (if id.name == "getElementsByTagName" then .tag lower else .classes (splitSpaces wanted))
    else if id.name == "getAttribute" || id.name == "setAttribute" || id.name == "removeAttribute" then
      checked state (toJSString (argument arguments 0) >>= asciiString) fun name =>
      let name := name.toLower
      if id.name == "getAttribute" then result state ((getAttribute node name).map Value.string |>.getD .null)
      else if id.name == "removeAttribute" then
        checked state (do
          if node.kind == .element "canvas" && ["width","height"].contains name && node.canvasContext.isSome then
            if (getAttribute node name).isNone then pure state
            else replaceNode state receiverId { node with
              attributes := node.attributes.filter (fun attr => attr.name != name)
              canvasDrawing := BrowserCanvasState.reset node.canvasDrawing }
          else if ["crossorigin","preload"].contains name && (getAttribute node "src").isSome &&
              [NodeKind.element "img",.element "audio"].contains node.kind then
            .error (.unresolved (.unsupportedSyntax "Resource reselection after metadata removal"))
          else if name == "src" && node.kind == .element "img" &&
              (match node.resourceStatus with | .image _ _ _ => true | _ => false) then
            .error (.unresolved (.unsupportedSyntax "Removing a loaded image source needs native image-request state"))
          else if name == "src" && node.lastResourceOrder.isSome &&
              (match node.resourceStatus with | .pending _ => true | _ => false) then
            .error (.unresolved (.unsupportedSyntax "Removing a source while a native resource is pending"))
          else
            let next ← replaceNode state receiverId { node with attributes := node.attributes.filter (fun a => a.name != name) }
            if name.startsWith "on" && name.length > 2 then
              setNodeHandler next receiverId (handlerEventType name) none
            else pure next)
          (fun state => result state .undefined)
      else checked state (asciiName (key name)) fun _ =>
        checked state (toJSString (argument arguments 1)) fun value =>
        checked state (setNodeAttribute state receiverId name value) (fun state => result state .undefined)
    else if id.name == "appendChild" || id.name == "insertBefore" || id.name == "removeChild" then
      checked state (receiverNode state (argument arguments 0)) fun (childId, child) =>
      if id.name == "removeChild" then
        if child.parent != some receiverId then fail state (.exception "NotFoundError" "Node is not a child")
        else checked state (detach state childId) (fun state => result state (argument arguments 0))
      else checked state (if id.name == "appendChild" || argument arguments 1 == .null || argument arguments 1 == .undefined
          then pure none else do pure (some (← receiverNode state (argument arguments 1)).1)) fun before =>
        checked state (append state receiverId childId before) (fun state => result state (argument arguments 0))
    else if id.name == "addEventListener" || id.name == "removeEventListener" then
      checked state (toJSString (argument arguments 0)) fun eventType =>
      let callback := argument arguments 1
      if callback != .undefined && callback != .null && !isObject callback then
        fail state (.exception "TypeError" "Event listener callback must be an object or null")
      else if isObject (argument arguments 2) then fail state (.unresolved (.unsupportedSyntax "Event listener options dictionary"))
      else if callback == .undefined || callback == .null then result state .undefined
      else
        let capture := truthy (argument arguments 2)
        let existing := node.listeners.any (fun l => l.eventType == eventType && l.callback == callback && l.capture == capture)
        let fresh := id.name == "addEventListener" && !existing
        let listeners := if id.name == "removeEventListener" then node.listeners.filter
          (fun l => !(l.eventType == eventType && l.callback == callback && l.capture == capture))
          else if existing then node.listeners else node.listeners ++ [{ eventType,callback,capture,serial := state.nextListenerSerial }]
        checked state (replaceNode { state with
          nextListenerSerial := state.nextListenerSerial + (if fresh then 1 else 0) } receiverId { node with listeners })
          (fun state => result state .undefined)
    else fail state (.unresolved (.builtin id thisValue arguments false))

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "convert" then
    checked state (convertedArgument continuation value) fun value =>
    let index := continuation.indices[0]?.getD 0
    let arguments := continuation.arguments.zipIdx.map (fun (old, i) => if i == index then value else old)
    dispatch state continuation.id continuation.thisValue arguments (continuation.indices[1]? == some 1)
  else fail state (.unresolved (.builtinContinuation continuation value))

/-- One supplied draw is consumed only at the actual Math.random request. This
deterministic tape driver is diagnostic; the stochastic kernel must quantify
over fresh IID53 draws instead of revealing this tape to a policy. -/
def supplyRandom (state : State) : State :=
  match state.randomInputs with
  | [] => state
  | draw :: remaining =>
    if bound : draw < 2^53 then result { state with
      randomInputs := remaining
      machine := { state.machine with freeDrawCount := state.machine.freeDrawCount + 1 } }
      (.number (Random.encode ⟨draw,bound⟩))
    else fail state (.fault (.invalidContinuation "IID53 draw outside support"))

/-- Call this only at the pinned source-bootstrap boundary, before any policy
input. The actual source closure identity is retained; names alone never trigger
the no-argument mathematical random-law extension. -/
def captureSeedrandom (state : State) : Checked State := do
  let some math := state.mathObject | .error (.fault (.invalidContinuation "Missing initial Math identity"))
  let object ← checkedObject state.machine.heap math
  match ownProperty object (key "seedrandom") with
  | some (.data (.object id) _ _ _) =>
    match (← checkedObject state.machine.heap id).kind with
    | .function closure =>
      let reference ← resolveName state.machine.heap closure.strict
        (state.machine.heap.environments.size + 1) closure.scope "m"
      let .environment scope name := reference.base |
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey is not a lexical source binding"))
      let .object mixkey ← readBinding state.machine.heap scope name |
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey binding is not a source function"))
      let .function helper := (← checkedObject state.machine.heap mixkey).kind |
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey binding is not a source closure"))
      if !TimestampText.nativeClosure helper then
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey source body does not match"))
      else pure { state with nativeSeedrandom := some id, nativeTimestampMixkey := some mixkey }
    | _ => .error (.fault (.invalidContinuation "Pinned seeded generator is not a source closure"))
  | _ => .error (.fault (.invalidContinuation "Source bootstrap did not install Math.seedrandom"))

def restoreFreeRandom (state : State) : State :=
  match state.mathObject, state.freeRandom, state.machine.continuation.head? with
  | some math, some random, some (.expressionStatement) =>
    let next := Builtins.putData state.machine math "random" (.object random)
    result { state with machine := next } .undefined
  | _, _, _ => fail state (.unresolved (.unsupportedSyntax
      "No-argument seeded-generator extension requires an unused expression-statement return value"))

def internalStep (state : State) : State :=
  match state.machine.control with
  | .invoke (.object function) _ [] false =>
    if state.nativeSeedrandom == some function then restoreFreeRandom state
    else { state with machine := Builtins.builtinStep state.machine }
  | .invoke (.object function) receiver arguments@(.timestampText _ :: _) false =>
    if state.nativeTimestampMixkey == some function then
      checked state (TimestampText.invoke state.machine function receiver arguments) fun machine =>
        { state with machine, timestampMixkeyActivations := state.timestampMixkeyActivations + 1 }
    else { state with machine := Builtins.builtinStep state.machine }
  | .unresolved (.builtin id receiver arguments construct) =>
    if id.namespaceName.startsWith "Browser." then dispatch state id receiver arguments construct
    else { state with machine := Builtins.builtinStep state.machine }
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName.startsWith "Browser." then resume state continuation value
    else { state with machine := Builtins.builtinStep state.machine }
  | .unresolved .freeRandom => supplyRandom state
  | .unresolved (.hostGet "DOM.Collection" id name) =>
    checked state (collectionProperty state id name) (result state)
  | .unresolved (.hostHas "DOM.Collection" id name) =>
    checked state (collectionProperty state id name) (fun value => result state (.boolean (value != .undefined)))
  | .unresolved (.hostGet "DOM.Node" id name) =>
    checked state (checkedNode state id) fun node =>
      if name == key "__proto__" then state else
      match node.kind with
      | .document | .element "select" | .element "form" | .element "object" | .element "embed" => state
      | _ => result state .undefined
  | .unresolved (.hostHas "DOM.Node" id name) =>
    checked state (checkedNode state id) fun node =>
      if name == key "__proto__" then state else
      match node.kind with
      | .document =>
        checked state (subtree state id) fun nodes =>
          if nodes.any (fun id => (state.nodes[id]?).any (fun candidate =>
              getAttribute candidate "id" == some name || getAttribute candidate "name" == some name)) then state
          else result state (.boolean false)
      | .element "select" | .element "form" | .element "object" | .element "embed" => state
      | _ => result state (.boolean false)
  | .unresolved (.hostPut "DOM.Node" id name value) =>
    checked state (checkedNode state id) fun node =>
      if name == key "__proto__" then state else
      match node.kind with
      | .document | .element "select" | .element "form" | .element "object" | .element "embed" => state
      | _ => checked state (do
          let object ← checkedObject state.machine.heap node.object
          if !object.extensible then .error (.unresolved (.unsupportedSyntax "Host expando nonextensible strict assignment"))
          else replaceObject state.machine.heap node.object (setOwnProperty object name (.data value true true true))) fun heap =>
            result { state with machine := { state.machine with heap } } value
  | _ => { state with machine := Builtins.builtinStep state.machine }

/-- One source or host operation takes zero modeled time. Event boundaries
advance elapsed time explicitly; source assignment cannot change the clock. -/
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
    | _ => state

def startProgram (state : State) (program : Program) : State :=
  { state with machine := JavaScript.startProgram state.machine program }

def taskFinished (machine : Machine) : Bool :=
  match status machine with
  | .completion _ | .value _ | .idle => true
  | _ => false

/-- A callback completes even when it throws. Chromium schedules the next
interval before this callback starts; a clear operation can remove it during
the callback. Model faults and unresolved operations cannot finish a task. -/
def finishTimer (state : State) : State :=
  if !taskFinished state.machine then state else
  match state.activeTimer with
  | none => state
  | some _ =>
    let reportedExceptions := match status state.machine with
      | .completion (.throw exception) => state.reportedExceptions ++ [exception]
      | _ => state.reportedExceptions
    { state with
      activeTimer := none
      currentTimerNesting := none
      reportedExceptions }

def nextTimer (state : State) : Option Timer :=
  state.timers.foldl (fun current timer => match current with
    | none => some timer
    | some earlier => if timer.due < earlier.due ||
        (timer.due == earlier.due && timer.order < earlier.order) then some timer else some earlier) none

/-- This explicit boundary starts the uniquely next scheduled timer. It does
not skip an unfinished source task or supply a host result for missing code. -/
def fireNextTimer (state : State) : State :=
  if !taskFinished state.machine then state else
  if !state.resourceRequests.isEmpty then
    fail state (.unresolved (.unsupportedSyntax "Pending native resource tasks require explicit resolution and ordering")) else
  let state := finishTimer state
  match nextTimer state with
  | none => state
  | some timer =>
    let elapsed := max state.machine.elapsed timer.due
    let remaining := state.timers.filter (fun candidate => candidate.id != timer.id)
    let following : Timer := { timer with
      due := elapsed + timerDelay (some timer.nesting) timer.delay
      order := state.nextOrder
      nesting := timer.nesting + 1 }
    { state with
      timers := if timer.repeating then remaining ++ [following] else remaining
      nextOrder := if timer.repeating then state.nextOrder + 1 else state.nextOrder
      activeTimer := some timer
      currentTimerNesting := some timer.nesting
      machine := { state.machine with
        elapsed
        control := .invoke timer.callback (.object state.machine.globalObject) timer.arguments false
        continuation := [] } }

theorem timerDelay_positive (nesting : Option Nat) (bits : UInt64) :
    1 ≤ timerDelay nesting bits := by
  unfold timerDelay
  split
  · exact Nat.le_trans (by decide) (Nat.le_max_left _ _)
  · exact Nat.le_max_left _ _

theorem timerDelay_nested_minimum (nesting : Nat) (bits : UInt64) (h : nesting ≥ 4) :
    4 ≤ timerDelay (some nesting) bits := by
  have h' : nesting + 1 ≥ 5 := by omega
  simp only [timerDelay, Option.getD_some, h', ite_true]
  exact Nat.le_max_left _ _

end CookieClicker.JavaScript.Browser

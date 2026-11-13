import CookieClicker.JavaScriptBrowserEventData
import CookieClicker.JavaScriptBrowserInputState

/-! Native UI/Mouse/Keyboard event construction and observable fields.
Dictionary getters and coercions run in source order. Input targeting, focus,
activation, related-target retargeting and coordinate layout remain separate
requirements; event construction is not a trusted-input transition.
-/
namespace CookieClicker.JavaScript.BrowserInput

open Browser BrowserInputState
private def key := JSString.ofString
private def argument := Builtins.argument
private def missing (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Input event: " ++ message)))

inductive FieldType where
  | boolean | long | short | unsignedShort | unsignedLong | double | string | nullableString
  | window | capabilities | target
  deriving Repr, DecidableEq

def uiFields : List (String × FieldType) := [
  ("bubbles",.boolean),("cancelable",.boolean),("composed",.boolean),
  ("detail",.long),("sourceCapabilities",.capabilities),("view",.window)]
def modifierFields : List (String × FieldType) :=
  ["altKey","ctrlKey","metaKey","modifierAltGraph","modifierCapsLock","modifierFn",
   "modifierNumLock","modifierScrollLock","modifierSymbol","shiftKey"].map (·,.boolean)
def mouseFields : List (String × FieldType) := [
  ("button",.short),("buttons",.unsignedShort),("clientX",.double),("clientY",.double),
  ("movementX",.long),("movementY",.long),("region",.nullableString),
  ("relatedTarget",.target),("screenX",.double),("screenY",.double)]
def keyboardFields : List (String × FieldType) := [
  ("charCode",.unsignedLong),("code",.string),("isComposing",.boolean),("key",.string),
  ("keyCode",.unsignedLong),("location",.unsignedLong),("repeat",.boolean)]

def fields (name : String) := uiFields ++
  (if name == "UIEvent" then [] else if name == "FocusEvent" then [("relatedTarget",.target)] else modifierFields ++
    if name == "MouseEvent" then mouseFields else keyboardFields)

private def defaultValue : FieldType → Value
  | .boolean => .boolean false
  | .string => .string []
  | .nullableString | .window | .capabilities | .target => .null
  | _ => .number Number.positiveZero

private def numeric : FieldType → Bool
  | .long | .short | .unsignedShort | .unsignedLong | .double => true
  | _ => false

private def convert (state : State) (kind : FieldType) (value : Value) : Checked Value := do
  if value == .undefined then pure (defaultValue kind) else
  match kind with
  | .boolean => pure (.boolean (truthy value))
  | .string => pure (.string (← toJSString value))
  | .nullableString => if value == .null then pure .null else pure (.string (← toJSString value))
  | .window =>
    if value == .null || value == .object state.machine.globalObject then pure value
    else .error (.exception "TypeError" "Event view must be Window or null")
  | .capabilities =>
    if value == .null then pure .null
    else if let .object id := value then
      match (← checkedObject state.machine.heap id).kind with
      | .host _ _ => missing "InputDeviceCapabilities brand and fields"
      | _ => .error (.exception "TypeError" "InputDeviceCapabilities required")
    else .error (.exception "TypeError" "InputDeviceCapabilities required")
  | .target =>
    if value == .null || value == .object state.machine.globalObject then pure value
    else if let .object id := value then
      match (← checkedObject state.machine.heap id).kind with
      | .host "DOM.Node" _ => pure value
      | .host _ _ => missing "additional EventTarget brands"
      | _ => .error (.exception "TypeError" "Related target must be EventTarget or null")
    else .error (.exception "TypeError" "Related target must be EventTarget or null")
  | _ =>
    let bits ← toNumber value
    if kind == .double then
      if Number.isFinite bits then pure (.number bits)
      else .error (.exception "TypeError" "Mouse coordinate must be finite")
    else if kind == .long then pure (.number (Number.ofInt (Number.toInt32 bits)))
    else if kind == .unsignedLong then pure (.number (Number.ofNat (Number.toUInt32 bits).toNat))
    else
      let value := (Number.toUInt32 bits).toNat % 65536
      pure (.number (if kind == .unsignedShort then Number.ofNat value else
        Number.ofInt (if value ≥ 32768 then (value : Int)-65536 else value)))

private def fieldValue (pairs : List (String × Value)) (name : String) : Value :=
  ((pairs.find? (fun entry => entry.1 == name)).map Prod.snd).getD .undefined
private def fieldBits (pairs : List (String × Value)) (name : String) : UInt64 :=
  match fieldValue pairs name with | .number bits => bits | _ => Number.positiveZero
private def fieldBool (pairs : List (String × Value)) (name : String) : Bool :=
  truthy (fieldValue pairs name)
private def fieldText (pairs : List (String × Value)) (name : String) : JSString :=
  match fieldValue pairs name with | .string text => text | _ => []

private def ui (pairs : List (String × Value)) : UI := {
  view := fieldValue pairs "view"
  detail := Number.toInt32 (fieldBits pairs "detail")
  sourceCapabilities := fieldValue pairs "sourceCapabilities" }
private def modifiers (pairs : List (String × Value)) : Modifiers := {
  altKey := fieldBool pairs "altKey", controlKey := fieldBool pairs "ctrlKey",
  metaKey := fieldBool pairs "metaKey", shiftKey := fieldBool pairs "shiftKey",
  altGraph := fieldBool pairs "modifierAltGraph", capsLock := fieldBool pairs "modifierCapsLock",
  functionKey := fieldBool pairs "modifierFn", numLock := fieldBool pairs "modifierNumLock",
  scrollLock := fieldBool pairs "modifierScrollLock", symbolKey := fieldBool pairs "modifierSymbol" }

private def record (name : String) (pairs : List (String × Value)) : Data :=
  if name == "UIEvent" then .ui (ui pairs)
  else if name == "FocusEvent" then .focus { ui := ui pairs, relatedTarget := fieldValue pairs "relatedTarget" }
  else if name == "MouseEvent" then .mouse {
    ui := ui pairs, modifiers := modifiers pairs,
    screenX := fieldBits pairs "screenX",screenY := fieldBits pairs "screenY",
    clientX := fieldBits pairs "clientX",clientY := fieldBits pairs "clientY",
    button := Number.toInt32 (fieldBits pairs "button"),
    buttons := (Number.toUInt32 (fieldBits pairs "buttons")).toNat,
    movementX := Number.toInt32 (fieldBits pairs "movementX"),
    movementY := Number.toInt32 (fieldBits pairs "movementY"),
    relatedTarget := fieldValue pairs "relatedTarget",
    region := match fieldValue pairs "region" with | .string text => some text | _ => none,
    page := if fieldValue pairs "view" == .null then some
      (Number.add (fieldBits pairs "clientX") Number.positiveZero,
       Number.add (fieldBits pairs "clientY") Number.positiveZero) else none }
  else .keyboard {
    ui := ui pairs, modifiers := modifiers pairs,
    key := fieldText pairs "key",code := fieldText pairs "code",
    location := (Number.toUInt32 (fieldBits pairs "location")).toNat,
    repeating := fieldBool pairs "repeat",composing := fieldBool pairs "isComposing",
    charCode := (Number.toUInt32 (fieldBits pairs "charCode")).toNat,
    keyCode := (Number.toUInt32 (fieldBits pairs "keyCode")).toNat }

def allocate (state : State) (name : String) (eventType : JSString) (data : Data)
    (bubbles cancelable composed trusted : Bool) : Checked (Value × State) := do
  let (value,next) ← BrowserEventData.allocateEvent state eventType .null
  let id ← BrowserEventData.eventId next value
  let some event := next.domEvents[id]? | .error (.fault (.invalidContinuation "Missing input event"))
  let some (_,prototype) := next.prototypes.specific.find? (fun entry => entry.1 == "#" ++ name) |
    missing ("captured native prototype " ++ name)
  let object ← checkedObject next.machine.heap event.object
  let heap ← replaceObject next.machine.heap event.object { object with prototype := some prototype }
  pure (value,{ next with
    machine := { next.machine with heap }, inputEvents := (id,data) :: next.inputEvents,
    domEvents := next.domEvents.set! id { event with
      isTrusted := trusted,currentTarget := .null,phase := 0,bubbles,cancelable,composed } })

private def create (state : State) (name : String) (eventType : JSString) (values : List Value) : State :=
  if values.length != (fields name).length then Browser.fail state (.fault (.invalidContinuation "Input event dictionary fields"))
  else
  let pairs := (fields name).map Prod.fst |>.zip values
  Browser.checked state (allocate state name eventType (record name pairs)
    (fieldBool pairs "bubbles") (fieldBool pairs "cancelable") (fieldBool pairs "composed") false)
    fun (value,next) => Browser.result next value

private def readField (state : State) (continuation : BuiltinContinuation) : State :=
  match (fields continuation.id.name)[continuation.locals.length]? with
  | none => Browser.checked state (toJSString (argument continuation.arguments 0)) fun eventType =>
    create state continuation.id.name eventType continuation.locals
  | some (name,_) =>
    let next := { continuation with phase := "field" }
    if argument continuation.arguments 1 == .null || argument continuation.arguments 1 == .undefined then
      { state with machine := { state.machine with control := .resumeBuiltin next .undefined } }
    else { state with
      machine := readProperty { state.machine with
        continuation := .builtin next :: state.machine.continuation }
        (argument continuation.arguments 1) (key name) }

private def convertedField (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  match (fields continuation.id.name)[continuation.locals.length]? with
  | none => Browser.fail state (.fault (.invalidContinuation "Input event conversion index"))
  | some (_,kind) =>
    if isObject value && (numeric kind || kind == .string || kind == .nullableString) then
      { state with
        machine := primitiveThen state.machine value (if numeric kind then "number" else "string")
          (.builtin { continuation with phase := "convertedField" }) }
    else Browser.checked state (convert state kind value) fun converted =>
      readField state { continuation with locals := continuation.locals ++ [converted] }

def constructEvent (state : State) (name : String) (arguments : List Value) (construct : Bool) : State :=
  if !construct || arguments.isEmpty then Browser.fail state (.exception "TypeError" "UI event requires new and a type")
  else match Browser.convertArguments state ⟨"Browser.Input",name⟩ .undefined arguments true [(0,"string")] with
  | some next => next
  | none => Browser.checked state (toJSString (argument arguments 0)) fun eventType =>
    let options := argument arguments 1
    if options != .null && options != .undefined && !isObject options then
      Browser.fail state (.exception "TypeError" "UI event options must be an object")
    else readField state {
      id := ⟨"Browser.Input",name⟩,phase := "field",thisValue := .undefined,
      arguments := [.string eventType,options] }

private def inputRecord (state : State) (receiver : Value) : Checked (Nat × DomEvent × Data) := do
  let id ← BrowserEventData.eventId state receiver
  let some event := state.domEvents[id]? | .error (.fault (.invalidContinuation "Input event identity"))
  let some (_,data) := state.inputEvents.find? (fun entry => entry.1 == id) |
    .error (.exception "TypeError" "UI event receiver required")
  pure (id,event,data)

private def coordinate (bits : UInt64) : Checked Value :=
  let integer := Number.truncateInt bits
  if integer < -2147483648 || integer > 2147483647 then missing "out-of-range native C++ coordinate integer cast"
  else pure (.number (Number.ofInt integer))

private def nodeOrNull (state : State) (value : Value) : Value :=
  match value with
  | .object id => match (state.machine.heap.object? id).map (fun object : JSObject => object.kind) with
    | some (.host "DOM.Node" _) => value
    | _ => .null
  | _ => .null

private def mouseProperty (state : State) (event : DomEvent) (mouse : Mouse) (name : String) : Checked Value := do
  if name == "clientX" || name == "x" then coordinate mouse.clientX
  else if name == "clientY" || name == "y" then coordinate mouse.clientY
  else if name == "screenX" then coordinate mouse.screenX
  else if name == "screenY" then coordinate mouse.screenY
  else if name == "movementX" then pure (.number (Number.ofInt mouse.movementX))
  else if name == "movementY" then pure (.number (Number.ofInt mouse.movementY))
  else if name == "button" then pure (.number (Number.ofInt
    (if mouse.button == -1 || ["mousemove","mouseleave","mouseenter","mouseover","mouseout"].any
      (fun name => event.eventType == key name) then 0 else mouse.button)))
  else if name == "buttons" then pure (.number (Number.ofNat mouse.buttons))
  else if name == "relatedTarget" then pure mouse.relatedTarget
  else if name == "fromElement" || name == "toElement" then
    let exits := event.eventType == key "mouseout" || event.eventType == key "mouseleave"
    pure (nodeOrNull state (if (name == "toElement") == exits then mouse.relatedTarget else event.target))
  else if ["pageX","pageY","layerX","layerY","offsetX","offsetY"].contains name then
    let some (x,y) := mouse.page | missing "view scroll snapshot for page coordinates"
    let bits := if name.endsWith "X" then x else y
    if name.startsWith "page" then coordinate bits
    else if event.target != .null then missing "target layout and relative-coordinate cache"
    else if name.startsWith "layer" then coordinate bits
    else pure (.number (if Number.signBit bits then Number.neg (Number.round (Number.abs bits)) else Number.round bits))
  else missing ("MouseEvent property " ++ name)

private def modifier (data : Modifiers) (name : JSString) : Bool :=
  if name == key "Alt" then data.altKey
  else if name == key "Control" then data.controlKey
  else if name == key "Meta" || name == key "Accel" then data.metaKey
  else if name == key "Shift" then data.shiftKey
  else if name == key "AltGraph" then data.altGraph
  else if name == key "CapsLock" then data.capsLock
  else if name == key "Fn" then data.functionKey
  else if name == key "NumLock" then data.numLock
  else if name == key "ScrollLock" then data.scrollLock
  else if name == key "Symbol" then data.symbolKey
  else false

private def property (state : State) (event : DomEvent) (data : Data) (name : String) : Checked Value := do
  if name == "view" then pure data.uiFields.view
  else if name == "detail" then pure (.number (Number.ofInt data.uiFields.detail))
  else if name == "sourceCapabilities" then pure data.uiFields.sourceCapabilities
  else if name == "which" then pure (.number (Number.ofNat (match data with
    | .ui _ | .focus _ => 0
    | .mouse fields => ((fields.button+1) % 4294967296).toNat
    | .keyboard fields => fields.keyCode)))
  else if ["altKey","ctrlKey","metaKey","shiftKey"].contains name then
    let some flags := data.modifiers | .error (.exception "TypeError" "Modifier event receiver required")
    pure (.boolean (if name == "altKey" then flags.altKey else if name == "ctrlKey" then flags.controlKey
      else if name == "metaKey" then flags.metaKey else flags.shiftKey))
  else match data with
  | .ui _ => missing ("UIEvent property " ++ name)
  | .focus fields =>
    if name == "relatedTarget" then pure fields.relatedTarget
    else missing ("FocusEvent property " ++ name)
  | .mouse fields => mouseProperty state event fields name
  | .keyboard fields =>
    if name == "key" then pure (.string fields.key)
    else if name == "code" then pure (.string fields.code)
    else if name == "location" then pure (.number (Number.ofNat fields.location))
    else if name == "repeat" then pure (.boolean fields.repeating)
    else if name == "isComposing" then pure (.boolean fields.composing)
    else if name == "charCode" || name == "keyCode" then
      let number := if name == "charCode" then fields.charCode else fields.keyCode
      pure (.number (Number.ofInt (if number ≥ 2147483648 then (number : Int)-4294967296 else number)))
    else missing ("KeyboardEvent property " ++ name)

def dispatch (state : State) (id : BuiltinId) (receiver : Value) (arguments : List Value)
    (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Input-event member is not a constructor")
  else Browser.checked state (inputRecord state receiver) fun (_,event,data) =>
    let correct := id.namespaceName == "Browser.UIEvent" ||
      (id.namespaceName == "Browser.MouseEvent" && (match data with | .mouse _ => true | _ => false)) ||
      (id.namespaceName == "Browser.KeyboardEvent" && (match data with | .keyboard _ => true | _ => false)) ||
      (id.namespaceName == "Browser.FocusEvent" && (match data with | .focus _ => true | _ => false))
    if !correct then Browser.fail state (.exception "TypeError" "Input-event receiver brand mismatch")
    else if id.name.startsWith "get " then Browser.checked state
      (property state event data ((id.name.drop 4).toString)) (Browser.result state)
    else if id.name == "getModifierState" then
      if arguments.isEmpty then Browser.fail state (.exception "TypeError" "getModifierState requires a key")
      else match Browser.convertArguments state ⟨"Browser.Input",id.namespaceName ++ ".modifier"⟩ receiver arguments false [(0,"string")] with
      | some next => next
      | none => Browser.checked state (toJSString (argument arguments 0)) fun name =>
        match data.modifiers with
        | some flags => Browser.result state (.boolean (modifier flags name))
        | none => Browser.fail state (.exception "TypeError" "Modifier event receiver required")
    else Browser.fail state (.unresolved (.builtin id receiver arguments construct))

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "field" || continuation.phase == "convertedField" then
    convertedField state continuation value
  else if continuation.phase == "convert" then
    Browser.checked state (Browser.convertedArgument continuation value) fun value =>
      let index := continuation.indices[0]?.getD 0
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then value else old
      if continuation.id.name.endsWith ".modifier" then
        dispatch state ⟨(continuation.id.name.dropEnd 9).toString,"getModifierState"⟩ continuation.thisValue arguments false
      else constructEvent state continuation.id.name arguments true
  else state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin id receiver arguments construct) =>
    if id.namespaceName == "Browser.Constructor" && ["UIEvent","MouseEvent","KeyboardEvent","FocusEvent"].contains id.name then
      some (constructEvent state id.name arguments construct)
    else if ["Browser.UIEvent","Browser.MouseEvent","Browser.KeyboardEvent","Browser.FocusEvent"].contains id.namespaceName then
      some (dispatch state id receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.Input" then some (resume state continuation value) else none
  | _ => none

end CookieClicker.JavaScript.BrowserInput

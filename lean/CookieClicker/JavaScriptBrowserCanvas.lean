import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptCssColor

/-! Canvas dimension reflection and 2D context creation in Chromium 87 on macOS.
The context stores its creation identity, alpha setting and drawing-state stack.
Raster drawing, layout, serialization, paths and nonzero native rotations remain explicit.

Source: html_canvas_element.cc Reset/setWidth/setHeight, element.cc
SetUnsignedIntegralAttribute, and html_parser_idioms.cc at Chromium 87.0.4280.141.
The pinned source files are retained under model/browser-source/chromium-87.
-/
namespace CookieClicker.JavaScript.BrowserCanvas

open Browser

private def key := JSString.ofString
private def whitespace (unit : UInt16) : Bool := [9,10,12,13,32].contains unit.toNat
private def digit (unit : UInt16) : Bool := 48 ≤ unit.toNat && unit.toNat ≤ 57

/-- Blink accepts leading HTML whitespace, a leading plus, negative zero and
trailing garbage. Canvas Reset additionally restricts the result to INT_MAX. -/
def parseDimension (text : JSString) : Option Nat := do
  let text := text.dropWhile whitespace
  let (negative,text) := match text with
    | 45 :: rest => (true,rest)
    | 43 :: rest => (false,rest)
    | _ => (false,text)
  if !text.head?.any digit then none else
  let value := (text.takeWhile digit).foldl (fun n unit => n * 10 + (unit.toNat - 48)) 0
  if value > 2147483647 || (negative && value != 0) then none else some value

def dimension (node : Node) (name : String) : Nat :=
  ((getAttribute node name).bind parseDimension).getD (if name == "width" then 300 else 150)

private def receiverCanvas (state : State) (receiver : Value) : Checked (Nat × Node) := do
  let (id,node) ← receiverNode state receiver
  if node.kind != .element "canvas" then .error (.exception "TypeError" "HTMLCanvasElement receiver required")
  else pure (id,node)

private def contextOptions : List (String × Value) :=
  [("alpha",.boolean true),("antialias",.boolean true),("depth",.boolean true),
   ("failIfMajorPerformanceCaveat",.boolean false),("powerPreference",.string (key "default")),
   ("premultipliedAlpha",.boolean true),("preserveDrawingBuffer",.boolean false),
   ("stencil",.boolean false),("desynchronized",.boolean false),("xrCompatible",.boolean false)]

private def createContext (state : State) (receiver : Value) (contextType : JSString)
    (settings : List Value) : State :=
  Browser.checked state (receiverCanvas state receiver) fun (id,node) =>
  if contextType != key "2d" then
    if node.canvasContext.isNone && ["experimental-webgl","webgl","webgl2","webgl2-compute","bitmaprenderer","gpupresent"].any (fun name => contextType == key name) then
      Browser.fail state (.unresolved (.unsupportedSyntax "Native non-2D canvas rendering context creation"))
    else Browser.result state .null
  else match node.canvasContext with
  | some object => Browser.result state (.object object)
  | none =>
    let (object,heap) := state.machine.heap.allocateObject {
      kind := .host "DOM.CanvasContext2D" id, prototype := some state.prototypes.canvasContext }
    let next := { state with machine := { state.machine with heap } }
    Browser.checked next (replaceNode next id { node with
      canvasContext := some object
      canvasAlpha := truthy (Builtins.argument settings 0) }) fun next =>
      Browser.result next (.object object)

private def readContextOption (state : State) (receiver : Value) (contextType : JSString)
    (options : Value) (settings : List Value) : State :=
  match contextOptions[settings.length]? with
  | none => createContext state receiver contextType settings
  | some (name,_) =>
    let continuation : BuiltinContinuation := {
      id := ⟨"Browser.Canvas","getContext"⟩, thisValue := receiver,
      arguments := [.string contextType,options], phase := "option", locals := settings }
    { state with machine := readProperty { state.machine with
      continuation := .builtin continuation :: state.machine.continuation } options (key name) }

private def acceptPowerPreference (state : State) (continuation : BuiltinContinuation)
    (value : Value) : State :=
  Browser.checked state (toJSString value) fun text =>
    if !["default","low-power","high-performance"].any (fun name => text == key name) then
      Browser.fail state (.exception "TypeError" "Invalid CanvasPowerPreference")
    else match continuation.arguments with
      | [.string contextType,options] => readContextOption state continuation.thisValue contextType options
          (continuation.locals ++ [.string text])
      | _ => Browser.fail state (.fault (.invalidContinuation "Canvas context option state"))

def contextReceiver (state : State) (receiver : Value) : Checked (Nat × Node) := do
  let .object object := receiver | .error (.exception "TypeError" "CanvasRenderingContext2D receiver required")
  let .host "DOM.CanvasContext2D" id := (← checkedObject state.machine.heap object).kind |
    .error (.exception "TypeError" "CanvasRenderingContext2D receiver required")
  let node ← checkedNode state id
  if node.canvasContext != some object then .error (.fault (.invalidContinuation "Canvas context identity mismatch"))
  else pure (id,node)

/-- The native methods first ask for a paint canvas. Empty canvases have none.
The current host fragment covers ordinary bounded allocations without context
loss. Larger allocations require the native resource-provider model. -/
def paintAvailable (node : Node) : Checked Bool :=
  let width := dimension node "width"
  let height := dimension node "height"
  if width == 0 || height == 0 then .ok false
  else if width ≤ 4096 && height ≤ 4096 then .ok true
  else .error (.unresolved (.unsupportedSyntax "Canvas allocation and context-loss lifecycle"))

private def transformed (drawing : BrowserCanvasState.State) (name : String)
    (numbers : List UInt64) : Checked BrowserCanvasState.State := do
  let operation ← match name,numbers with
    | "resetTransform",[] | "setTransform",[] => .ok CanvasDeferred.Operation.resetTransform
    | "translate",[x,y] => .ok (.translate x y)
    | "scale",[x,y] => .ok (.scale x y)
    | "transform",[a,b,c,d,e,f] => .ok (.transform ⟨a,b,c,d,e,f⟩)
    | "setTransform",[a,b,c,d,e,f] => .ok (.setTransform ⟨a,b,c,d,e,f⟩)
    | "rotate",[angle] => .ok (.rotate angle)
    | _,_ => .error (.fault (.invalidContinuation "Canvas transform converted argument count"))
  return {drawing with transform := CanvasDeferred.apply drawing.transform operation}

private def contextCall (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  if construct then return Browser.fail state (.exception "TypeError" "Canvas context method is not a constructor")
  let .ok (id,node) := contextReceiver state receiver |
    return Browser.checked state (contextReceiver state receiver) fun _ => state
  if builtin.name == "get canvas" then return Browser.result state (.object node.object)
    else if builtin.name == "getContextAttributes" then
      let (object,heap) := state.machine.heap.allocateObject {
        prototype := state.machine.objectPrototype,
        properties := [⟨key "alpha",.data (.boolean node.canvasAlpha) true true true⟩,
          ⟨key "desynchronized",.data (.boolean false) true true true⟩] }
      return Browser.result { state with machine := { state.machine with heap } } (.object object)
  else if builtin.name == "save" || builtin.name == "restore" then
    let drawing := if builtin.name == "save" then BrowserCanvasState.save node.canvasDrawing
      else BrowserCanvasState.restore node.canvasDrawing
    return Browser.checked state (replaceNode state id { node with canvasDrawing := drawing }) fun next =>
      Browser.result next .undefined
  else if ["translate","scale","rotate","transform","setTransform","resetTransform"].contains builtin.name then
    if builtin.name == "setTransform" && arguments.length > 0 && arguments.length < 6 then
      return Browser.fail state (.unresolved (.unsupportedSyntax "Canvas DOMMatrix2DInit overload conversion"))
    let count := if builtin.name == "resetTransform" || (builtin.name == "setTransform" && arguments.isEmpty) then 0
      else if builtin.name == "rotate" then 1
      else if builtin.name == "translate" || builtin.name == "scale" then 2 else 6
    if arguments.length < count then
      return Browser.fail state (.exception "TypeError" "Canvas transform missing required arguments")
    if let some next := Browser.convertArguments state builtin receiver arguments false
        ((List.range count).map (fun index => (index,"number"))) then return next
    return Browser.checked state (arguments.take count |>.mapM toNumber) fun numbers =>
      if builtin.name == "setTransform" && numbers.length == 6 && !numbers.all Number.isFinite then
        Browser.result state .undefined
      else Browser.checked state (paintAvailable node) fun available =>
        if !available then Browser.result state .undefined
        else Browser.checked state (transformed node.canvasDrawing builtin.name numbers) fun drawing =>
          Browser.checked state (replaceNode state id {node with canvasDrawing := drawing}) fun next =>
            Browser.result next .undefined
  else if builtin.name == "fillRect" then
    if arguments.length < 4 then
      return Browser.fail state (.exception "TypeError" "fillRect requires four arguments")
    if let some next := Browser.convertArguments state builtin receiver arguments false
        [(0,"number"),(1,"number"),(2,"number"),(3,"number")] then return next
    return Browser.checked state (arguments.take 4 |>.mapM toNumber) fun numbers =>
      match numbers with
      | [x,y,width,height] =>
        if !BrowserCanvasState.validRectangle x y width height then Browser.result state .undefined
        else Browser.checked state (paintAvailable node) fun available =>
          if !available then Browser.result state .undefined
          else Browser.checked state (replaceNode state id {node with
            canvasDrawing := BrowserCanvasState.fillRect node.canvasDrawing
              (dimension node "width") (dimension node "height") node.canvasAlpha x y width height}) fun next =>
                Browser.result next .undefined
      | _ => Browser.fail state (.fault (.invalidContinuation "Canvas fillRect converted argument count"))
  else if builtin.name == "clearRect" then
    if arguments.length < 4 then
      return Browser.fail state (.exception "TypeError" "clearRect requires four arguments")
    if let some next := Browser.convertArguments state builtin receiver arguments false
        [(0,"number"),(1,"number"),(2,"number"),(3,"number")] then return next
    return Browser.checked state (arguments.take 4 |>.mapM toNumber) fun numbers =>
      match numbers with
      | [x,y,width,height] =>
        Browser.checked state (replaceNode state id {node with
          canvasDrawing := BrowserCanvasState.clearRect node.canvasDrawing x y width height}) fun next =>
          Browser.result next .undefined
      | _ => Browser.fail state (.fault (.invalidContinuation "Canvas clearRect converted argument count"))
  else if builtin.name.startsWith "get " then
    if let some value := BrowserCanvasState.read node.canvasDrawing (builtin.name.drop 4).toString then
      return Browser.result state value
  else if builtin.name.startsWith "set " then
    let name := (builtin.name.drop 4).toString
    if BrowserCanvasState.numericNames.contains name then
      if let some next := Browser.convertArguments state builtin receiver arguments false [(0,"number")] then return next
      return Browser.checked state (toNumber (Builtins.argument arguments 0)) fun bits =>
        Browser.checked state (replaceNode state id { node with
          canvasDrawing := BrowserCanvasState.setNumber node.canvasDrawing name bits }) fun next =>
          Browser.result next .undefined
    else if !(BrowserCanvasState.keywords name).isEmpty then
      if let some next := Browser.convertArguments state builtin receiver arguments false [(0,"string")] then return next
      return Browser.checked state (toJSString (Builtins.argument arguments 0)) fun value =>
        Browser.checked state (replaceNode state id { node with
          canvasDrawing := BrowserCanvasState.setKeyword node.canvasDrawing name value }) fun next =>
          Browser.result next .undefined
    else if name == "font" then
      if let some next := Browser.convertArguments state builtin receiver arguments false [(0,"string")] then return next
      return Browser.checked state (toJSString (Builtins.argument arguments 0)) fun value =>
        if value.any (fun unit => unit.toNat ≥ 128) then
          Browser.fail state (.unresolved (.unsupportedSyntax "Canvas non-ASCII font grammar"))
        else match CssFont.parse (String.ofList (value.map (Char.ofNat ∘ UInt16.toNat))) with
        | .error reason => Browser.fail state (.unresolved (.unsupportedSyntax reason))
        | .ok none => Browser.result state .undefined
        | .ok (some parsed) =>
          Browser.checked state (replaceNode state id {node with
            canvasDrawing := BrowserCanvasState.writeFont node.canvasDrawing parsed}) fun next =>
              Browser.result next .undefined
    else if ["fillStyle","strokeStyle","shadowColor"].contains name then
      if let some next := Browser.convertArguments state builtin receiver arguments false [(0,"string")] then return next
      return Browser.checked state (toJSString (Builtins.argument arguments 0)) fun value =>
        if value.any (fun unit => unit.toNat ≥ 128) then
          Browser.fail state (.unresolved (.unsupportedSyntax "Canvas non-ASCII color grammar"))
        else match CssColor.parse (String.ofList (value.map (Char.ofNat ∘ UInt16.toNat))) with
        | .error reason => Browser.fail state (.unresolved (.unsupportedSyntax reason))
        | .ok none => Browser.result state .undefined
        | .ok (some parsed) =>
          match BrowserCanvasState.writeColor node.canvasDrawing name parsed.rgba with
          | none => Browser.fail state (.unresolved (.unsupportedSyntax "Canvas color decimal formatting"))
          | some drawing =>
            Browser.checked state (replaceNode state id {node with
              canvasDrawing := drawing}) fun next =>
                Browser.result next .undefined
    else if name == "imageSmoothingEnabled" then
      return Browser.checked state (replaceNode state id { node with
        canvasDrawing := BrowserCanvasState.write node.canvasDrawing name
          (.boolean (truthy (Builtins.argument arguments 0))) }) fun next =>
          Browser.result next .undefined
  return Browser.fail state (.unresolved (.unsupportedSyntax ("Canvas 2D state/raster operation: " ++ builtin.name)))

def dispatch (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  if !["get width","get height","set width","set height","getContext"].contains builtin.name then return state
  if construct then return Browser.fail state (.exception "TypeError" "Canvas accessor is not a constructor")
  let .ok (id,node) := receiverCanvas state receiver |
    return Browser.checked state (receiverCanvas state receiver) fun _ => state
  if builtin.name == "getContext" then
    if arguments.isEmpty then return Browser.fail state (.exception "TypeError" "getContext requires a context ID")
    if let some next := Browser.convertArguments state builtin receiver arguments false [(0,"string")] then return next
    return Browser.checked state (toJSString (Builtins.argument arguments 0)) fun contextType =>
      let options := Builtins.argument arguments 1
      if isObject options then readContextOption state receiver contextType options []
      else createContext state receiver contextType (contextOptions.map Prod.snd)
  let name := (builtin.name.drop 4).toString
  if builtin.name.startsWith "get " then return Browser.result state (.number (Number.ofNat (dimension node name)))
  if let some next := Browser.convertArguments state builtin receiver arguments false [(0,"number")] then return next
  return Browser.checked state (toNumber (Builtins.argument arguments 0)) fun bits =>
    let value := (Number.toUInt32 bits).toNat
    let value := if value > 2147483647 then (if name == "width" then 300 else 150) else value
    Browser.checked state (setNodeAttribute state id name (key value.repr)) fun next =>
      Browser.result next .undefined

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "convert" then
    let index := continuation.indices[0]?.getD 0
    Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
      if continuation.id.namespaceName == "Browser.CanvasContext" then
        contextCall state continuation.id continuation.thisValue arguments false
      else dispatch state continuation.id continuation.thisValue arguments false
  else if continuation.phase == "powerPreference" then acceptPowerPreference state continuation value
  else if continuation.phase == "option" then
    match contextOptions[continuation.locals.length]?,continuation.arguments with
    | some (name,defaultValue),[.string contextType,options] =>
      let value := if value == .undefined then defaultValue else value
      if name == "powerPreference" then
        if isObject value then { state with machine := { state.machine with
          control := .toPrimitive value "string",
          continuation := .builtin { continuation with phase := "powerPreference" } :: state.machine.continuation } }
        else acceptPowerPreference state continuation value
      else readContextOption state continuation.thisValue contextType options
        (continuation.locals ++ [.boolean (truthy value)])
    | _,_ => Browser.fail state (.fault (.invalidContinuation "Canvas option conversion state"))
  else Browser.fail state (.unresolved (.builtinContinuation continuation value))

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.namespaceName == "Browser.Canvas" then some (dispatch state builtin receiver arguments construct)
    else if builtin.namespaceName == "Browser.CanvasContext" then some (contextCall state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if ["Browser.Canvas","Browser.CanvasContext"].contains continuation.id.namespaceName then
      some (resume state continuation value) else none
  | .unresolved (.hostGet "DOM.CanvasContext2D" _ _) => some (Browser.result state .undefined)
  | .unresolved (.hostHas "DOM.CanvasContext2D" _ _) => some (Browser.result state (.boolean false))
  | _ => none

end CookieClicker.JavaScript.BrowserCanvas

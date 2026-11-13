import CookieClicker.JavaScriptBrowser

/-! DOMRect and DOMRectReadOnly values from Chromium 87 geometry sources.
Rectangle construction does not compute renderer layout. Source conversions and
dictionary getters run through the interpreter's actual continuation frames. -/
namespace CookieClicker.JavaScript.BrowserGeometry

open Browser BrowserGeometryState

private def key := JSString.ofString
private def argument := Builtins.argument

/-- Chromium uses std::min/max after a NaN guard; ties retain the first operand,
including its zero sign. This differs from JavaScript Math.min/max on zeros. -/
def nativeMin (a b : UInt64) : UInt64 :=
  if Number.isNaN a || Number.isNaN b then Number.nan
  else if Number.lessThan b a then b else a

def nativeMax (a b : UInt64) : UInt64 :=
  if Number.isNaN a || Number.isNaN b then Number.nan
  else if Number.lessThan a b then b else a

def fields (rect : Rect) : List (String × UInt64) :=
  [("x",rect.x),("y",rect.y),("width",rect.width),("height",rect.height),
   ("top",nativeMin rect.y (Number.add rect.y rect.height)),
   ("right",nativeMax rect.x (Number.add rect.x rect.width)),
   ("bottom",nativeMax rect.y (Number.add rect.y rect.height)),
   ("left",nativeMin rect.x (Number.add rect.x rect.width))]

def allocate (state : State) (writable : Bool) (x y width height : UInt64) : Checked (Value × State) := do
  let name := if writable then "#DOMRect" else "#DOMRectReadOnly"
  let some (_,prototype) := state.prototypes.specific.find? (fun pair => pair.1 == name) |
    .error (.fault (.invalidContinuation "Missing immutable native rectangle prototype"))
  let id := state.rectangles.size
  let (object,heap) := state.machine.heap.allocateObject {
    kind := .host "DOM.Rect" id, prototype := some prototype }
  pure (.object object,{ state with
    machine := { state.machine with heap }
    rectangles := state.rectangles.push { object,x,y,width,height,writable } })

private def receiverRect (state : State) (receiver : Value) (requireWritable : Bool) : Checked (Nat × Rect) := do
  let .object object := receiver | .error (.exception "TypeError" "Native rectangle receiver required")
  let .host "DOM.Rect" id := (← checkedObject state.machine.heap object).kind |
    .error (.exception "TypeError" "Native rectangle receiver required")
  let some rect := state.rectangles[id]? | .error (.fault (.invalidContinuation "Missing native rectangle"))
  if rect.object != object then .error (.fault (.invalidContinuation "Native rectangle identity mismatch"))
  else if requireWritable && !rect.writable then .error (.exception "TypeError" "DOMRect receiver required")
  else pure (id,rect)

private def create (state : State) (writable : Bool) (values : List Value) : State :=
  Browser.checked state (do
    let x ← toNumber (argument values 0)
    let y ← toNumber (argument values 1)
    let width ← toNumber (argument values 2)
    let height ← toNumber (argument values 3)
    allocate state writable x y width height) fun (value,next) => Browser.result next value

private def dictionaryNames := ["height","width","x","y"]

private def readDictionary (state : State) (writable : Bool) (options : Value)
    (values : List Value) : State :=
  match dictionaryNames[values.length]? with
  | none => create state writable [argument values 2,argument values 3,argument values 1,argument values 0]
  | some name =>
    let continuation : BuiltinContinuation := {
      id := ⟨"Browser.Geometry","fromRect"⟩, thisValue := .undefined,
      arguments := [options], locals := values, indices := [if writable then 1 else 0], phase := "dictionary" }
    { state with machine := readProperty { state.machine with
      continuation := .builtin continuation :: state.machine.continuation } options (key name) }

private def fromRect (state : State) (writable : Bool) (arguments : List Value) : State :=
  let options := argument arguments 0
  if options == .undefined || options == .null then create state writable (List.replicate 4 (.number Number.positiveZero))
  else if !isObject options then Browser.fail state (.exception "TypeError" "DOMRectInit must be an object")
  else readDictionary state writable options []

def dispatch (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  let name := builtin.name
  if name == "DOMRect" || name == "DOMRectReadOnly" then
    if !construct then return Browser.fail state (.exception "TypeError" "Rectangle constructor requires new")
    let arguments := (List.range 4).map fun index =>
      let value := argument arguments index
      if value == .undefined then Value.number Number.positiveZero else value
    if let some next := Browser.convertArguments state ⟨"Browser.Geometry",name⟩ receiver arguments true
        [(0,"number"),(1,"number"),(2,"number"),(3,"number")] then return next
    return create state (name == "DOMRect") arguments
  if construct then return Browser.fail state (.exception "TypeError" "Rectangle method is not a constructor")
  if name == "fromRect" then return fromRect state (builtin.namespaceName == "Browser.DOMRect") arguments
  let requireWritable := builtin.namespaceName == "Browser.DOMRect" || name.startsWith "set "
  let .ok (id,rect) := receiverRect state receiver requireWritable |
    return Browser.checked state (receiverRect state receiver requireWritable) fun _ => state
  if name == "toJSON" then
    let (object,heap) := state.machine.heap.allocateObject {
      prototype := state.machine.objectPrototype
      properties := (fields rect).map fun (name,bits) => ⟨key name,.data (.number bits) true true true⟩ }
    return Browser.result { state with machine := { state.machine with heap } } (.object object)
  if name.startsWith "get " then
    let property := (name.drop 4).toString
    return match (fields rect).find? (fun pair => pair.1 == property) with
      | some (_,bits) => Browser.result state (.number bits)
      | none => Browser.fail state (.unresolved (.unsupportedSyntax "Unknown native rectangle getter"))
  if name.startsWith "set " then
    if let some next := Browser.convertArguments state ⟨"Browser.Geometry",name⟩ receiver arguments false [(0,"number")] then return next
    return Browser.checked state (toNumber (argument arguments 0)) fun bits =>
      let property := (name.drop 4).toString
      let updated := if property == "x" then some { rect with x := bits }
        else if property == "y" then some { rect with y := bits }
        else if property == "width" then some { rect with width := bits }
        else if property == "height" then some { rect with height := bits } else none
      match updated with
      | none => Browser.fail state (.unresolved (.unsupportedSyntax "Unknown native rectangle setter"))
      | some rect => Browser.result { state with rectangles := state.rectangles.set! id rect } .undefined
  return Browser.fail state (.unresolved (.unsupportedSyntax ("Unknown native rectangle method " ++ name)))

private def acceptDictionaryNumber (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  Browser.checked state (toNumber value) fun bits =>
    readDictionary state (continuation.indices[0]?.getD 0 == 1)
      (argument continuation.arguments 0) (continuation.locals ++ [.number bits])

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "convert" then
    Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      let index := continuation.indices[0]?.getD 0
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
      dispatch state continuation.id continuation.thisValue arguments (continuation.indices[1]?.getD 0 == 1)
  else if continuation.phase == "dictionaryNumber" then acceptDictionaryNumber state continuation value
  else if continuation.phase == "dictionary" then
    let value := if value == .undefined then Value.number Number.positiveZero else value
    if isObject value then { state with machine := { state.machine with
      control := .toPrimitive value "number"
      continuation := .builtin { continuation with phase := "dictionaryNumber" } :: state.machine.continuation } }
    else acceptDictionaryNumber state continuation value
  else Browser.fail state (.unresolved (.builtinContinuation continuation value))

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if ["Browser.DOMRect","Browser.DOMRectReadOnly"].contains builtin.namespaceName ||
        (builtin.namespaceName == "Browser.Constructor" && ["DOMRect","DOMRectReadOnly"].contains builtin.name) then
      some (dispatch state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.Geometry" then some (resume state continuation value) else none
  | .unresolved (.hostGet "DOM.Rect" _ _) => some (Browser.result state .undefined)
  | .unresolved (.hostHas "DOM.Rect" _ _) => some (Browser.result state (.boolean false))
  | _ => none

end CookieClicker.JavaScript.BrowserGeometry

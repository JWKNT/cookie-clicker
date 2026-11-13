import CookieClicker.JavaScriptBrowser

/-! Live classList operations over the actual element class attribute. Source
callbacks run through interpreter frames. Iterator and exotic reflection
operations outside this implementation remain explicit host requests. -/
namespace CookieClicker.JavaScript.BrowserTokenList

open Browser

private def key := JSString.ofString
private def argument := Builtins.argument

private def whitespace (unit : UInt16) : Bool := [9,10,12,13,32].contains unit.toNat

def tokens (text : JSString) : List JSString := Id.run do
  let mut output : List JSString := []
  let mut token : JSString := []
  for unit in text ++ [32] do
    if whitespace unit then
      if !token.isEmpty && !output.contains token then output := output ++ [token]
      token := []
    else token := token ++ [unit]
  return output

private def validate (token : JSString) : Checked Unit :=
  if token.isEmpty then .error (.exception "SyntaxError" "Token must not be empty")
  else if token.any whitespace then .error (.exception "InvalidCharacterError" "Token contains HTML whitespace")
  else pure ()

private def receiverId (state : State) (receiver : Value) : Checked Nat := do
  let .object object := receiver | .error (.exception "TypeError" "DOMTokenList receiver required")
  let .host "DOM.TokenList" id := (← checkedObject state.machine.heap object).kind |
    .error (.exception "TypeError" "DOMTokenList receiver required")
  let _ ← checkedNode state id
  pure id

private def contents (state : State) (id : Nat) : Checked JSString := do
  pure ((getAttribute (← checkedNode state id) "class").getD [])

private def update (state : State) (id : Nat) (values : List JSString) : Checked State := do
  let node ← checkedNode state id
  let joined := values.foldl (fun text token => if text.isEmpty then token else text ++ [32] ++ token) []
  replaceNode state id (setAttribute node "class" joined)

private def getList (state : State) (receiver : Value) : State :=
  Browser.checked state (receiverNode state receiver) fun (id,node) =>
    match node.kind with
    | .element _ =>
      match node.classListObject with
      | some object => Browser.result state (.object object)
      | none =>
        let (object,heap) := state.machine.heap.allocateObject {
          kind := .host "DOM.TokenList" id, prototype := some state.prototypes.tokenList }
        let next := { state with machine := { state.machine with heap } }
        Browser.checked next (replaceNode next id { node with classListObject := some object }) fun next =>
          Browser.result next (.object object)
    | _ => Browser.fail state (.exception "TypeError" "classList getter requires an Element")

def dispatch (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  if construct then return Browser.fail state (.exception "TypeError" "DOMTokenList method is not a constructor")
  let .ok id := receiverId state receiver | return Browser.checked state (receiverId state receiver) fun _ => state
  let name := builtin.name
  let required := if name == "replace" then 2 else
    if ["contains","toggle","supports","item"].contains name then 1 else 0
  if arguments.length < required then return Browser.fail state (.exception "TypeError" "Insufficient DOMTokenList arguments")
  let conversions := if name == "add" || name == "remove" then arguments.zipIdx.map (fun (_,index) => (index,"string"))
    else if name == "replace" then [(0,"string"),(1,"string")]
    else if ["contains","toggle","supports","set value"].contains name then [(0,"string")]
    else if name == "item" then [(0,"number")] else []
  if let some next := Browser.convertArguments state ⟨"Browser.TokenList",name⟩ receiver arguments false conversions then return next
  if name == "set value" then
    return Browser.checked state (toJSString (argument arguments 0)) fun text =>
      Browser.checked state (checkedNode state id >>= fun node => replaceNode state id (setAttribute node "class" text)) fun next =>
        Browser.result next .undefined
  return Browser.checked state (contents state id) fun text =>
  let values := tokens text
  if name == "get length" then Browser.result state (.number (Number.ofNat values.length))
  else if name == "get value" || name == "toString" then Browser.result state (.string text)
  else if name == "item" then Browser.checked state (toNumber (argument arguments 0)) fun bits =>
    Browser.result state ((values[(Number.toUInt32 bits).toNat]?).map Value.string |>.getD .null)
  else if name == "supports" then Browser.fail state (.exception "TypeError" "classList has no supported-token vocabulary")
  else if name == "contains" then Browser.checked state (toJSString (argument arguments 0)) fun token =>
    Browser.result state (.boolean (values.contains token))
  else if name == "add" || name == "remove" then
    Browser.checked state (arguments.mapM toJSString) fun supplied =>
    Browser.checked state (supplied.mapM validate) fun _ =>
      let changed := if name == "add" then supplied.foldl
          (fun values token => if values.contains token then values else values ++ [token]) values
        else values.filter fun token => !supplied.contains token
      Browser.checked state (checkedNode state id) fun node =>
      if name == "remove" && (getAttribute node "class").isNone then Browser.result state .undefined
      else Browser.checked state (update state id changed) fun next => Browser.result next .undefined
  else if name == "toggle" then Browser.checked state (toJSString (argument arguments 0)) fun token =>
    Browser.checked state (validate token) fun _ =>
      let present := values.contains token
      let desired := if arguments.length < 2 || argument arguments 1 == .undefined then !present else truthy (argument arguments 1)
      if present == desired then Browser.result state (.boolean desired)
      else Browser.checked state (update state id (if desired then values ++ [token] else values.filter (· != token))) fun next =>
        Browser.result next (.boolean desired)
  else if name == "replace" then Browser.checked state (toJSString (argument arguments 0)) fun old =>
    Browser.checked state (toJSString (argument arguments 1)) fun newer =>
    Browser.checked state (validate old >>= fun _ => validate newer) fun _ =>
      if !values.contains old then Browser.result state (.boolean false)
      else
        let changed := (values.map fun token => if token == old then newer else token).foldl
          (fun values token => if values.contains token then values else values ++ [token]) []
        Browser.checked state (update state id changed) fun next => Browser.result next (.boolean true)
  else Browser.fail state (.unresolved (.builtin builtin receiver arguments construct))

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "convert" then
    let index := continuation.indices[0]?.getD 0
    Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
      dispatch state continuation.id continuation.thisValue arguments false
  else Browser.fail state (.unresolved (.builtinContinuation continuation value))

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.name == "get classList" && builtin.namespaceName.startsWith "Browser." then
      some (if construct then Browser.fail state (.exception "TypeError" "classList getter is not a constructor") else getList state receiver)
    else if builtin.namespaceName == "Browser.DOMTokenList" || builtin.namespaceName == "Browser.TokenList" then
      some (dispatch state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.TokenList" then some (resume state continuation value) else none
  | .unresolved (.hostGet "DOM.TokenList" id name) =>
    let spelling := String.ofList (name.map fun unit => Char.ofNat unit.toNat)
    match spelling.toNat? with
    | some index =>
      if name != key index.repr then some (Browser.result state .undefined) else
      some (Browser.checked state (contents state id) fun text =>
        Browser.result state (((tokens text)[index]?).map Value.string |>.getD .undefined))
    | none => some (Browser.result state .undefined)
  | .unresolved (.hostHas "DOM.TokenList" id name) =>
    let spelling := String.ofList (name.map fun unit => Char.ofNat unit.toNat)
    match spelling.toNat? with
    | some index =>
      if name != key index.repr then some (Browser.result state (.boolean false)) else
      some (Browser.checked state (contents state id) fun text =>
        Browser.result state (.boolean (index < (tokens text).length)))
    | none => some (Browser.result state (.boolean false))
  | _ => none

end CookieClicker.JavaScript.BrowserTokenList

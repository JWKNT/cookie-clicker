import CookieClicker.JavaScriptBrowser

/-! Live child-node lists. The list stores its parent identity, not a copied
array, and reads all child node kinds from the current DOM tree. The captured
native NodeList prototype supplies the exact Array.prototype.forEach alias.
Exotic reflection and indexed writes remain explicit unsupported requests. -/
namespace CookieClicker.JavaScript.BrowserNodeList

open Browser

private def receiverList (state : State) (receiver : Value) : Checked (Nat × Node) := do
  match receiver with
  | .object object => match (← checkedObject state.machine.heap object).kind with
    | .host "DOM.NodeList" parent => pure (parent, ← checkedNode state parent)
    | _ => .error (.exception "TypeError" "NodeList receiver required")
  | _ => .error (.exception "TypeError" "NodeList receiver required")

def childNodes (state : State) (receiver : Value) : State :=
  Browser.checked state (receiverNode state receiver) fun (parent,node) =>
    match node.childNodesObject with
    | some object => Browser.result state (.object object)
    | none =>
      let (object,heap) := state.machine.heap.allocateObject {
        kind := .host "DOM.NodeList" parent, prototype := some state.prototypes.nodeList }
      let state := { state with machine := { state.machine with heap } }
      Browser.checked state (replaceNode state parent { node with childNodesObject := some object }) fun next =>
        Browser.result next (.object object)

def indexedProperty (state : State) (parent : Nat) (name : JSString) : Checked Value := do
  let node ← checkedNode state parent
  match arrayIndex name with
  | none => pure .undefined
  | some index => match node.children[index]? with
    | none => pure .undefined
    | some child => nodeValue state (some child)

def dispatch (state : State) (id : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  if construct then return Browser.fail state (.exception "TypeError" "NodeList method is not a constructor")
  if id.namespaceName == "Browser.Node" && id.name == "get childNodes" then return childNodes state receiver
  let .ok (_,node) := receiverList state receiver |
    return Browser.checked state (receiverList state receiver) fun _ => state
  if id.name == "get length" then return Browser.result state (.number (Number.ofNat node.children.length))
  if id.name != "item" then return state
  if arguments.isEmpty then return Browser.fail state (.exception "TypeError" "NodeList.item requires an index")
  if let some next := Browser.convertArguments state id receiver arguments false [(0,"number")] then return next
  return Browser.checked state (toNumber (Builtins.argument arguments 0)) fun bits =>
    Browser.checked state (nodeValue state node.children[(Number.toUInt32 bits).toNat]?) (Browser.result state)

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "convert" then
    Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      let index := continuation.indices[0]?.getD 0
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
      dispatch state continuation.id continuation.thisValue arguments false
  else state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin id receiver arguments construct) =>
    if id.namespaceName == "Browser.NodeList" ||
        (id.namespaceName == "Browser.Node" && id.name == "get childNodes") then
      some (dispatch state id receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.NodeList" then some (resume state continuation value) else none
  | .unresolved (.hostGet "DOM.NodeList" parent name) =>
    if name == JSString.ofString "__proto__" then none else
      some (Browser.checked state (indexedProperty state parent name) (Browser.result state))
  | .unresolved (.hostHas "DOM.NodeList" parent name) =>
    if name == JSString.ofString "__proto__" then none else
      some (Browser.checked state (indexedProperty state parent name) fun value =>
        Browser.result state (.boolean (value != .undefined)))
  | _ => none

end CookieClicker.JavaScript.BrowserNodeList

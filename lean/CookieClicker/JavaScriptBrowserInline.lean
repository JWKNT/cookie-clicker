import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptParser

/-! Compilation of supported native content-event handlers from their actual
UTF16 attribute text. The function body is parsed by the logical parser and
executed as a source closure. Element and document object scopes remain live.
Form-owner scopes, special Window handlers, native syntax-error reporting and
Symbol mutation remain explicit requirements. No handler-result oracle is used.
-/
namespace CookieClicker.JavaScript.BrowserInline

open Browser BrowserEventState
private def key := JSString.ofString

/-- Initial Chromium 87 @@unscopables; Symbol lookup/mutation is not supported
by the value language. Native comparison records these initial names separately
from the handler-body parser and dynamic object lookup. -/
def elementExclusions : List JSString :=
  ["slot","prepend","append","replaceChildren","before","after","replaceWith","remove"].map key
def documentExclusions : List JSString :=
  ["fullscreen","prepend","append","replaceChildren"].map key

private def unsupported (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Inline event handler: " ++ message)))

private def checkFormScope (state : State) (node : Node) : Checked Unit := do
  if (getAttribute node "form").isSome then unsupported "explicit form-owner scope" else
  if [NodeKind.element "button",.element "fieldset",.element "input",.element "object",.element "output",
      .element "select",.element "textarea",.element "img"].contains node.kind then
    let mut parent := node.parent
    for _ in [:state.nodes.size+1] do
      match parent with
      | none => return ()
      | some id =>
        let ancestor ← checkedNode state id
        if ancestor.kind == .element "form" then return ← unsupported "form-owner scope"
        parent := ancestor.parent
    .error (.fault (.invalidContinuation "Cyclic inline-handler form ancestry"))
  else pure ()

private def allocate (state : State) (node : Node) (eventType text : JSString)
    (program : Program) : Checked (Value × State) := do
  checkFormScope state node
  let document ← checkedNode state state.document
  let (global,heap) := state.machine.heap.allocateEnvironment ⟨.object state.machine.globalObject false,none⟩
  let (documentScope,heap) := heap.allocateEnvironment ⟨.object document.object true,some global⟩
  let (elementScope,heap) := heap.allocateEnvironment ⟨.object node.object true,some documentScope⟩
  let machine := { state.machine with
    heap
    objectEnvironmentExclusions := (elementScope,elementExclusions) ::
      (documentScope,documentExclusions) :: state.machine.objectEnvironmentExclusions }
  if eventType.any (fun unit => unit.toNat > 127) then unsupported "non-ASCII native handler name" else
  let name := "on" ++ (String.ofList (eventType.map (fun unit => Char.ofNat unit.toNat))).toLower
  let source := key ("function " ++ name ++ "(event) {\n") ++ text ++ key "\n}"
  let (value,machine) ← allocateFunction machine
    ⟨some name,["event"],program.body,elementScope,program.strict,some source⟩
  let .object objectId := value | .error (.fault (.invalidContinuation "Inline function allocation"))
  let object ← checkedObject machine.heap objectId
  let object := setOwnProperty (setOwnProperty object (key "name")
      (.data (.string (key name)) false false true)) (key "length")
      (.data (.number Number.one) false false true)
  -- Active caller/arguments retain the allocator's explicit descriptor boundary.
  let heap ← replaceObject machine.heap objectId object
  pure (value,{ state with machine := { machine with heap } })

def value (state : State) (id : Nat) (eventType : JSString) : Checked (Value × State) := do
  let node ← checkedNode state id
  match (node.handlers.find? (fun handler => handler.eventType == eventType)).bind (·.body) with
  | none => pure (.null,state)
  | some (.callback value) => pure (value,state)
  | some (.inlineText text) =>
    if node.kind == .element "body" || node.kind == .element "frameset" then
      unsupported "body/frameset Window forwarding"
    else
      match Parser.parseFunctionBody text with
      | .error error =>
        unsupported (match error.kind with
          | .syntax => "native SyntaxError report during compilation: " ++ error.message
          | .unsupported => "source grammar: " ++ error.message
          | .exhausted => "parser diagnostic fuel exhausted")
      | .ok program =>
        let (callback,state) ← allocate state node eventType text program
        let state ← setNodeHandler state id eventType (some (.callback callback))
        pure (callback,state)

def getter (state : State) (namespaceName name : String) (receiver : Value)
    (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Event handler getter is not a constructor")
  else Browser.checked state (nodeBrand state namespaceName receiver) fun _ =>
    Browser.checked state (receiverNode state receiver) fun (id,_) =>
      Browser.checked state (value state id (handlerEventType ((name.drop 4).toString))) fun (callback,next) =>
        Browser.result next callback

end CookieClicker.JavaScript.BrowserInline

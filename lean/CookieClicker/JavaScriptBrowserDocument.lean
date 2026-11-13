import CookieClicker.JavaScriptBrowser

/-! HTML document metadata backed by the actual modeled DOM tree. The title
algorithms follow the HTML document/title rules; SVG and foreign namespaces
are outside the currently represented tree. No independent title string can
silently diverge from the source-visible title element.
https://html.spec.whatwg.org/multipage/dom.html#document.title -/
namespace CookieClicker.JavaScript.BrowserDocument

open Browser

private def key := JSString.ofString

private def documentId (state : State) (receiver : Value) : Checked Nat := do
  let (id,node) ← receiverNode state receiver
  if node.kind == .document then pure id
  else .error (.exception "TypeError" "Document receiver required")

private def firstChildElement (state : State) (parent : Nat) (accept : String → Bool) : Checked (Option Nat) := do
  let node ← checkedNode state parent
  pure (node.children.find? fun id => (state.nodes[id]?).any fun node =>
    match node.kind with | .element tag => accept tag | _ => false)

def documentElement (state : State) (document : Nat) : Checked (Option Nat) :=
  firstChildElement state document (fun _ => true)

def htmlChild (state : State) (document : Nat) (accept : String → Bool) : Checked (Option Nat) := do
  match ← documentElement state document with
  | none => pure none
  | some root =>
    if (← checkedNode state root).kind == .element "html" then firstChildElement state root accept
    else pure none

def titleElement (state : State) (document : Nat) : Checked (Option Nat) := do
  pure ((← subtree state document).find? fun id => (state.nodes[id]?).any (fun node => node.kind == .element "title"))

def childText (state : State) (id : Nat) : Checked JSString := do
  let node ← checkedNode state id
  node.children.foldlM (fun output child => do
    match (← checkedNode state child).kind with
    | .text text => pure (output ++ text)
    | _ => pure output) []

def collapseWhitespace (text : JSString) : JSString := Id.run do
  let mut output : JSString := []
  let mut pending := false
  for unit in text do
    if [9,10,12,13,32].contains unit.toNat then pending := !output.isEmpty
    else
      output := output ++ (if pending then [32] else []) ++ [unit]
      pending := false
  return output

private def replaceText (state : State) (id : Nat) (text : JSString) : Checked State := do
  if text.isEmpty then replaceChildren state id [] else
    let (child,state) ← allocateNode state (.text text)
    replaceChildren state id [child]

def setTitle (state : State) (document : Nat) (text : JSString) : Checked State := do
  match ← documentElement state document with
  | none => pure state
  | some root =>
    if (← checkedNode state root).kind != .element "html" then
      .error (.unresolved (.unsupportedSyntax "Non-HTML document title setter"))
    else match ← titleElement state document with
      | some title => replaceText state title text
      | none => match ← htmlChild state document (· == "head") with
        | none => pure state
        | some head =>
          let (title,state) ← allocateNode state (.element "title")
          let state ← append state head title
          replaceText state title text

private def dispatch (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "DOM accessor is not a constructor") else
  let isTitle := builtin.namespaceName == "Browser.HTMLTitleElement"
  Browser.checked state (if isTitle then do
    let (id,node) ← receiverNode state receiver
    if node.kind == .element "title" then pure id
    else .error (.exception "TypeError" "HTMLTitleElement receiver required")
    else documentId state receiver) fun id =>
  if builtin.name == "get title" then Browser.checked state (do
    match ← titleElement state id with
    | none => pure []
    | some title => pure (collapseWhitespace (← childText state title))) fun text =>
      Browser.result state (.string text)
  else if builtin.name == "get text" && isTitle then
    Browser.checked state (childText state id) fun text => Browser.result state (.string text)
  else if ["get documentElement","get head","get body"].contains builtin.name then
    Browser.checked state (do
      let found ← if builtin.name == "get documentElement" then documentElement state id
        else htmlChild state id (fun tag => if builtin.name == "get head" then tag == "head" else tag == "body" || tag == "frameset")
      nodeValue state found) (Browser.result state)
  else if builtin.name == "set title" || (builtin.name == "set text" && isTitle) then
    let value := arguments.head?.getD .undefined
    if isObject value then
      { state with machine := primitiveThen state.machine value "string" (.builtin {
          id := ⟨"Browser.DocumentMetadata",builtin.namespaceName ++ ":" ++ builtin.name⟩
          phase := "string", thisValue := receiver }) }
    else Browser.checked state (toJSString value) fun text =>
      Browser.checked state (if isTitle then replaceText state id text else setTitle state id text) fun next =>
        Browser.result next .undefined
  else state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if (["Browser.Document","Browser.HTMLDocument"].contains builtin.namespaceName &&
        ["get title","set title","get head","get body","get documentElement"].contains builtin.name) ||
        (builtin.namespaceName == "Browser.HTMLTitleElement" && ["get text","set text"].contains builtin.name) then
      some (dispatch state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.DocumentMetadata" && continuation.phase == "string" then
      match continuation.id.name.splitOn ":" with
      | [namespaceName,name] => some (dispatch state ⟨namespaceName,name⟩ continuation.thisValue [value] false)
      | _ => some (Browser.fail state (.fault (.invalidContinuation "Document metadata conversion")))
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserDocument

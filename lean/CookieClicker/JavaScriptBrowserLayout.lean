import CookieClicker.JavaScriptBrowserStyle
import CookieClicker.JavaScriptBrowserGeometry
import CookieClicker.JavaScriptCssHeight
import CookieClicker.JavaScriptCssParser

/-! Source stylesheet and live DOM adapter for the closed positioned-box
fragment. Stylesheet availability and viewport are explicit host configuration.
No measured rectangle, renderer callback, or target-hit oracle is used. -/
namespace CookieClicker.JavaScript.BrowserLayout

open Browser

private def key := JSString.ofString
private def unsupported (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("CSS layout: " ++ message)))
private def checked (value : Except String α) : Checked α :=
  match value with | .ok result => pure result | .error message => unsupported message

private def isElement (state : State) (id : Nat) : Bool :=
  (state.nodes[id]?).any fun node => match node.kind with | .element _ => true | _ => false

def tree (state : State) : Css.Tree := state.nodes.mapIdx fun id node =>
  match node.kind with
  | .element tag =>
    let parent := node.parent.filter (isElement state)
    let siblings := match node.parent with
      | none => []
      | some parent => ((state.nodes[parent]?).map (fun (node : Node) => node.children)).getD []
    some {
      tag := key tag,attributes := node.attributes.map (fun item => (key item.name,item.value)),
      parent := parent,
      previous := ((siblings.takeWhile (· != id)).filter (isElement state)).getLast?,
      children := node.children.filter (isElement state),
      hasText := node.children.any (fun child => (state.nodes[child]?).any fun child =>
        match child.kind with | .text value => !value.isEmpty | _ => false),
      documentRoot := node.parent == some state.document }
  | _ => none

private def ancestors : Nat → State → Nat → Checked (List Nat)
  | 0,_,_ => unsupported "DOM ancestry fuel exhausted"
  | fuel+1,state,id => do
    let node ← checkedNode state id
    if id == state.document then return []
    let some parent := node.parent | unsupported "Detached node has no renderer box in this fragment"
    return id :: (← ancestors fuel state parent)

private def preorder : Nat → State → Nat → Checked (List Nat)
  | 0,_,_ => unsupported "DOM stylesheet traversal fuel exhausted"
  | fuel+1,state,id => do
    let node ← checkedNode state id
    let descendants ← node.children.mapM (preorder fuel state)
    return id :: descendants.flatten

private def ascii (value : JSString) : Checked String :=
  if value.all (·.toNat < 128) then pure (String.ofList (value.map (Char.ofNat ∘ UInt16.toNat)))
  else unsupported "Non-ASCII stylesheet URL or inline value"

private def lower (value : String) : String := String.ofList (value.toList.map fun char =>
  if 'A' ≤ char && char ≤ 'Z' then Char.ofNat (char.toNat+32) else char)

private def words (value : String) : List String :=
  ((value.toList.splitOnP fun c => [9,10,12,13,32].contains c.toNat).filter (!·.isEmpty)).map String.ofList

/-- A registry supplies loaded source, while actual connected link order
determines the active author sheets. Unknown/alternate/media/dynamic sheets
cannot be silently omitted. -/
def activeStylesheets (state : State) : Checked (List Css.Stylesheet) := do
  if !state.stylesheetsConfigured then unsupported "Stylesheet source/loading configuration is absent"
  let mut output := []
  for id in ← preorder (state.nodes.size+1) state state.document do
    let node ← checkedNode state id
    if node.kind == .element "style" then
      let media ← ascii ((getAttribute node "media").getD [])
      let mime ← ascii ((getAttribute node "type").getD [])
      if media != "" && lower media != "all" then unsupported "Runtime stylesheet media query evaluation"
      if mime != "" && lower mime != "text/css" then unsupported "Runtime stylesheet MIME selection"
      let .string value ← Browser.textContent state id | unsupported "Runtime stylesheet text must be a string"
      if !value.isEmpty then
        let parsed ← checked (Css.Parser.parse ("runtime-style-" ++ toString id) value)
        output := output ++ [parsed]
    if node.kind == .element "link" then
      let rel ← ascii ((getAttribute node "rel").getD [])
      let rel := words (lower rel)
      if rel.contains "stylesheet" then
        if rel.contains "alternate" || (getAttribute node "disabled").isSome then
          unsupported "Disabled or alternate stylesheet selection"
        let media ← ascii ((getAttribute node "media").getD [])
        if media != "" && lower media != "all" then unsupported "Stylesheet media query evaluation"
        let mime ← ascii ((getAttribute node "type").getD [])
        if mime != "" && lower mime != "text/css" then unsupported "Stylesheet MIME selection"
        let source ← ascii ((getAttribute node "href").getD [])
        let path := (source.splitOn "?").head!
        let some sheet := state.stylesheets.find? (·.name == path) |
          unsupported ("Unconfigured stylesheet source: " ++ source)
        output := output ++ [sheet]
  return output

private def inlineToken (text : String) : Checked Css.Token := do
  if text.endsWith "%" then return .percentage (text.dropEnd 1).toString
  if text.endsWith "px" then return .dimension (text.dropEnd 2).toString (key "px")
  if text.toInt?.isSome then return .number text
  if text != "" && text.toList.all (fun c => c.isAlpha || c == '-') then return .ident (key text)
  unsupported ("Inline geometry value requires additional CSS tokens: " ++ text)

private def inlineDeclarations (state : State) (needed : List Nat)
    (requested : Option (List String) := none) : Checked (Array (List Css.Declaration)) := do
  let mut output := Array.replicate state.nodes.size []
  for id in needed do
    if isElement state id then
      let entries ← BrowserStyle.readDeclaration state id
      let mut declarations := []
      for entry in entries do
        if requested.map (·.contains entry.name) |>.getD (Css.isLayoutProperty entry.name) then
          let groups ← (words entry.value).mapM inlineToken
          let value := groups.foldl (fun list token => if list.isEmpty then [token] else list ++ [.space,token]) []
          declarations := declarations ++ [.valid entry.name value entry.important]
      output := output.set! id declarations
  return output

/-- Try ancestors before parsing descendant inline geometry. A proved
`display:none` removes every descendant layout box, independent of that
unneeded geometry. Failure to prove it falls through to the strict layout path. -/
private def provenHidden (state : State) (id : Nat) : Checked Bool := do
  let chain ← ancestors (state.nodes.size+1) state id
  let sheets ← activeStylesheets state
  let tree := tree state
  for ancestor in chain.reverse do
    if let .ok inline ← pure (inlineDeclarations state [ancestor]) then
      let context : Css.LayoutContext := {
        tree,stylesheets := sheets,inlineDeclarations := inline,
        viewportWidth := 0,viewportHeight := 0 }
      if Css.provenDisplayNone context ancestor then return true
  return false

private def viewportDimension (state : State) (name : String) : Checked Int := do
  let some (_,value) := state.fixtureWindowData.find? (·.1 == key name) |
    unsupported ("Viewport configuration is absent: " ++ name)
  let .number bits := value | unsupported "Viewport dimension is not numeric"
  if !Number.isInteger bits then unsupported "Fractional viewport requires renderer configuration"
  let value := Number.truncateInt bits
  if value < 0 || value > 1000000 then unsupported "Viewport dimension is outside the closed range"
  return value

private def layoutContext (state : State) (id : Nat) (horizontal : Bool := false) : Checked Css.LayoutContext := do
  let chain ← ancestors (state.nodes.size+1) state id
  let sheets ← activeStylesheets state
  let precedingRootSiblings := chain.flatMap fun id =>
    match state.nodes[id]? with
    | some node => if node.kind == .element "body" then
        match node.parent.bind (state.nodes[·]?) with
        | some parent => parent.children.takeWhile (· != id)
        | none => []
      else []
    | none => []
  let widthDependencies := if horizontal then
    chain.flatMap (fun id => match state.nodes[id]? with
      | some node => match node.parent.bind (state.nodes[·]?) with
        | some parent => parent.children.takeWhile (· != id)
        | none => []
      | none => []) ++
    state.nodes.toList.zipIdx.filterMap (fun (node,id) =>
      if node.kind == .element "body" && (node.parent.bind (state.nodes[·]?)).any
          (fun parent => parent.kind == .element "html" && parent.parent == some state.document) then some id else none)
    else []
  let inline ← inlineDeclarations state (chain ++ precedingRootSiblings ++ widthDependencies)
  let width ← viewportDimension state "innerWidth"
  let height ← viewportDimension state "innerHeight"
  return {
    tree := tree state,stylesheets := sheets,inlineDeclarations := inline,
    viewportWidth := width,viewportHeight := height }

private def targetDiagnostic (state : State) (id : Nat) (operation : String)
    (result : Checked α) : Checked α :=
  match result with
  | .error (.unresolved (.unsupportedSyntax reason)) =>
    let description := match state.nodes[id]? with
      | some node =>
        let tag := match node.kind with | .element tag => tag | _ => "#node"
        let nativeId := String.ofList (((getAttribute node "id").getD []).map (Char.ofNat ∘ UInt16.toNat))
        tag ++ "#" ++ nativeId
      | none => "absent"
    .error (.unresolved (.unsupportedSyntax (reason ++ " [" ++ operation ++ " node=" ++
      toString id ++ " " ++ description ++ "]")))
  | other => other

def readOnlyEditing (state : State) (id : Nat) : Checked Bool := targetDiagnostic state id "editing" do
  let chain ← ancestors (state.nodes.size+1) state id
  let sheets ← activeStylesheets state
  let inline ← inlineDeclarations state chain (some ["all","-webkit-user-modify"])
  checked (Css.readOnlyEditing {
    tree := tree state,stylesheets := sheets,inlineDeclarations := inline,
    viewportWidth := 0,viewportHeight := 0 } id)

def rectangle (state : State) (id : Nat) : Checked Css.Box := targetDiagnostic state id "rectangle" do
  if ← provenHidden state id then return ⟨0,0,0,0⟩
  checked (Css.rectangle (state.nodes.size*4+1024) (← layoutContext state id) id)

def usedWidth (state : State) (id : Nat) : Checked Css.UsedWidth := do
  if ← provenHidden state id then return ⟨0,0,0⟩
  checked (Css.Horizontal.usedWidth (state.nodes.size*4+1024) (← layoutContext state id true) id)

def usedHeight (state : State) (id : Nat) : Checked Css.UsedHeight := do
  if ← provenHidden state id then return ⟨0,0,0⟩
  checked (Css.Vertical.usedHeight (state.nodes.size*4+1024) (← layoutContext state id true) id)

def focusStyle (state : State) (id : Nat) : Checked Bool := targetDiagnostic state id "focus" do
  if ← provenHidden state id then return false
  checked (Css.focusStyle (← layoutContext state id) id)

def textareaFocusStyle (state : State) (id : Nat) : Checked Bool := targetDiagnostic state id "textarea focus" do
  let chain ← ancestors (state.nodes.size+1) state id
  let sheets ← activeStylesheets state
  let inline ← inlineDeclarations state chain (some Css.textareaFocusPropertyNames)
  checked (Css.textareaFocusStyle {
    tree := tree state,stylesheets := sheets,inlineDeclarations := inline,
    viewportWidth := 0,viewportHeight := 0 } id)

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver _ construct) =>
    if builtin.namespaceName == "Browser.Element" && builtin.name == "getBoundingClientRect" then some (
      if construct then Browser.fail state (.exception "TypeError" "Native geometry method is not a constructor")
      else Browser.checked state (receiverNode state receiver) fun (id,node) =>
        match node.kind with
        | .element _ => Browser.checked state (rectangle state id) fun box =>
          Browser.checked state (BrowserGeometry.allocate state true
            (Number.ofInt box.x) (Number.ofInt box.y) (Number.ofInt box.width) (Number.ofInt box.height)) fun (value,next) =>
            Browser.result next value
        | _ => Browser.fail state (.exception "TypeError" "Element geometry receiver required"))
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserLayout

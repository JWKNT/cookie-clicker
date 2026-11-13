import CookieClicker.JavaScriptBrowserLayout
import CookieClicker.JavaScriptBrowserDocument

/-! Native size getters on the implemented integral CSS box fragment.
The values are calculated from the live source stylesheet and DOM, not native
rectangle snapshots. General inline/replaced layout, scrollbars, zoom, quirks
mode and offset-parent coordinates remain explicit missing requirements. -/
namespace CookieClicker.JavaScript.BrowserMetrics

open Browser

private def missing (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Element metrics: " ++ message)))

private def standardsDocument (state : State) : Checked Unit := do
  let document ← checkedNode state state.document
  -- The initial strict HTML-file parser represents only the HTML doctype with
  -- empty public/system IDs. Without it, the model must not assume CSS1Compat.
  if document.children.any (fun id => (state.nodes[id]?).any (·.kind == .doctype)) then pure ()
  else missing "Quirks/limited-quirks document mode"

def size (state : State) (id : Nat) (name : String) : Checked Int := do
  if !(← connectedToDocument state (state.nodes.size+1) id) then return 0
  standardsDocument state
  let horizontal := name == "offsetWidth" || name == "clientWidth"
  let client := name == "clientWidth" || name == "clientHeight"
  let root ← BrowserDocument.documentElement state state.document
  if client && root == some id then
    -- Standards-mode documentElement client dimensions use the layout view,
    -- not its CSS box. innerWidth may include non-overlay scrollbars, so that
    -- viewport result is unavailable until root/body overflow propagation and
    -- the scrollbar environment are represented.
    missing "Root client viewport requires overflow propagation and scrollbar state"
  else if horizontal then do
    let width ← BrowserLayout.usedWidth state id
    pure (if client then width.padding else width.border)
  else do
    let height ← BrowserLayout.usedHeight state id
    pure (if client then height.padding else height.border)

private def identifiedSize (state : State) (id : Nat) (node : Node) (name : String) : Checked Int :=
  match size state id name with
  | .error (.unresolved (.unsupportedSyntax detail)) =>
    let tag := match node.kind with | .element tag => tag | _ => "non-element"
    let identifier := (getAttribute node "id").getD []
    let label := if identifier.all (·.toNat < 128) then
      String.ofList (identifier.map (Char.ofNat ∘ UInt16.toNat)) else reprStr identifier
    missing (name ++ " on node " ++ toString id ++ " <" ++ tag ++ " id=" ++ label ++ ">: " ++ detail)
  | result => result

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver _ construct) =>
    if (builtin.namespaceName == "Browser.HTMLElement" &&
        ["get offsetWidth","get offsetHeight"].contains builtin.name) ||
      (builtin.namespaceName == "Browser.Element" &&
        ["get clientWidth","get clientHeight"].contains builtin.name) then
      some (if construct then Browser.fail state (.exception "TypeError" "Native metric getter is not a constructor")
        else Browser.checked state (nodeBrand state builtin.namespaceName receiver) fun _ =>
        Browser.checked state (receiverNode state receiver) fun (id,node) =>
        Browser.checked state (identifiedSize state id node (builtin.name.drop 4).toString) fun value =>
          Browser.result state (.number (Number.ofInt value)))
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserMetrics

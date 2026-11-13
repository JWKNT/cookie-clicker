import CookieClicker.JavaScriptBrowser

/-! Native instance identities with explicitly supplied environment values.
Navigator, Screen and Location retain their captured descriptors and prototypes;
the fixture maps only supply selected getter results. An uncaptured getter is
an unresolved host operation, never an invented absent property. -/
namespace CookieClicker.JavaScript.BrowserEnvironment

open Browser

private def key := JSString.ofString

private def configuredInstance (state : State) (name : String) : Option ObjectId :=
  (state.configuredInstances.find? (fun pair => pair.1 == name)).map Prod.snd

private def field (state : State) (group name : String) : Option Value := do
  let (_, value) ← state.fixtureWindowData.find? (fun pair => pair.1 == key group)
  let .object object := value | none
  let object ← state.machine.heap.object? object
  let descriptor ← ownProperty object (key name)
  let .data value _ _ _ := descriptor | none
  pure value

private def configuredCall (state : State) (group : String) (builtin : BuiltinId)
    (receiver : Value) (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Native getter is not a constructor")
  else if !(configuredInstance state group).any (fun id => receiver == .object id) then
    Browser.fail state (.exception "TypeError" "Native environment getter receiver required")
  else
    let name := if builtin.name.startsWith "get " then some ((builtin.name.drop 4).toString)
      else if group == "location" && builtin.name == "toString" then some "href" else none
    match name >>= field state group with
    | some value => Browser.result state value
    | none => state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver _ construct) =>
    if builtin.namespaceName == "Browser.Navigator" then
      some (configuredCall state "navigator" builtin receiver construct)
    else if builtin.namespaceName == "Browser.Screen" then
      some (configuredCall state "screen" builtin receiver construct)
    else if builtin.namespaceName == "Browser.Location" then
      some (configuredCall state "location" builtin receiver construct)
    else if ["Browser.Document","Browser.HTMLDocument"].contains builtin.namespaceName &&
        ["get URL","get documentURI","get compatMode","get characterSet","get charset","get inputEncoding","get location"].contains builtin.name then
      if !(configuredInstance state "document").any (fun id => receiver == .object id) then
        some (Browser.fail state (.exception "TypeError" "Document receiver required"))
      else if builtin.name == "get location" then
        some (match configuredInstance state "location" with
          | some id => Browser.result state (.object id)
          | none => state)
      else
        let name := if builtin.name == "get documentURI" then "URL"
          else if ["get charset","get inputEncoding"].contains builtin.name then "characterSet"
          else (builtin.name.drop 4).toString
        some (match field state "document" name with
          | some value => Browser.result state value
          | none => state)
    else none
  | .unresolved (.hostGet "DOM.Configured" id _) =>
    if state.configuredInstances.any (fun pair => pair.2 == id) then
      some (Browser.result state .undefined) else some state
  | .unresolved (.hostHas "DOM.Configured" id _) =>
    if state.configuredInstances.any (fun pair => pair.2 == id) then
      some (Browser.result state (.boolean false)) else some state
  | _ => none

end CookieClicker.JavaScript.BrowserEnvironment

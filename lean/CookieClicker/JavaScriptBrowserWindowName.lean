import CookieClicker.JavaScriptBrowser

/-! Native browsing-context name, separate from the source heap's mutable
property descriptors. Initial state is an explicit fixture input. Source
ToString callbacks run before the setter changes the stored name. -/
namespace CookieClicker.JavaScript.BrowserWindowName

open Browser

private def receiverValid (state : State) (receiver : Value) : Bool :=
  receiver == .undefined || receiver == .null || receiver == .object state.machine.globalObject

def dispatch (state : State) (receiver : Value) (arguments : List Value) (construct : Bool)
    (setter : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Window name accessor is not a constructor")
  else if !receiverValid state receiver then Browser.fail state (.exception "TypeError" "Window name receiver required")
  else if !setter then match state.windowName with
    | some name => Browser.result state (.string name)
    | none => Browser.fail state (.unresolved (.unsupportedSyntax "Initial browsing-context name is not configured"))
  else
    match Browser.convertArguments state ⟨"Browser.WindowName","set name"⟩ receiver arguments false [(0,"string")] with
    | some next => next
    | none => Browser.checked state (toJSString (Builtins.argument arguments 0)) fun name =>
      Browser.result { state with windowName := some name } .undefined

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase != "convert" then Browser.fail state (.unresolved (.builtinContinuation continuation value))
  else Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
    let arguments := continuation.arguments.zipIdx.map fun (old,index) =>
      if index == continuation.indices[0]?.getD 0 then converted else old
    dispatch state continuation.thisValue arguments false true

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.namespaceName == "Browser.Window" && ["get name","set name"].contains builtin.name then
      some (dispatch state receiver arguments construct (builtin.name == "set name"))
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.WindowName" then some (resume state continuation value) else none
  | _ => none

end CookieClicker.JavaScript.BrowserWindowName

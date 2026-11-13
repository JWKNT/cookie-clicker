import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptBrowserCookieState

/-! Source-backed Document.cookie behavior for a configured file or opaque
origin. File URLs are excluded by the pinned native cookieable-scheme defaults;
string conversion still runs before native access. No user cookie jar is read.
-/
namespace CookieClicker.JavaScript.BrowserCookies

open Browser

def dispatch (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Document cookie accessor is not a constructor")
  else Browser.checked state (receiverNode state receiver) fun (id,node) =>
    if node.kind != .document then Browser.fail state (.exception "TypeError" "Document receiver required")
    else if id != state.document then
      Browser.fail state (.unresolved (.unsupportedSyntax "Cookie access for another Document origin"))
    else
      let conversion := if builtin.name == "set cookie" then
        Browser.convertArguments state ⟨"Browser.Cookies",builtin.name⟩ receiver arguments false [(0,"string")]
        else none
      match conversion with
      | some next => next
      | none =>
        let validated := if builtin.name == "set cookie" then
          (toJSString (Builtins.argument arguments 0)).map (fun _ => ()) else pure ()
        Browser.checked state validated fun _ =>
          match state.cookieOrigin with
          | .unconfigured => Browser.fail state (.unresolved (.unsupportedSyntax "Unconfigured Document cookie origin and scheme policy"))
          | .opaqueOrigin => Browser.fail state (.exception "SecurityError" "Cookie access is denied for an opaque origin")
          | .file => Browser.result state (if builtin.name == "get cookie" then .string [] else .undefined)

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.namespaceName == "Browser.Document" && ["get cookie","set cookie"].contains builtin.name then
      some (dispatch state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName != "Browser.Cookies" then none
    else if continuation.phase != "convert" then some (Browser.fail state (.unresolved (.builtinContinuation continuation value)))
    else some (Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      dispatch state continuation.id continuation.thisValue [converted] false)
  | _ => none

end CookieClicker.JavaScript.BrowserCookies

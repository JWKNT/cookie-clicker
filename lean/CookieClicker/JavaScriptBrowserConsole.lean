import CookieClicker.JavaScriptBrowser

/-! The source-used native console logger. Calls retain raw primitive arguments
as explicit console events, matching the pinned inspector event boundary.
Console display formatting and object previews are not a source-value oracle;
calls with object arguments and other console methods remain unresolved. -/
namespace CookieClicker.JavaScript.BrowserConsole

open Browser

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin _ arguments construct) =>
    if builtin.namespaceName != "Browser.Console" then none
    else if construct then
      some (Browser.fail state (.exception "TypeError" "Console method is not a constructor"))
    else if builtin.name != "log" || arguments.any isObject then some state
    else if arguments.isEmpty then some (Browser.result state .undefined)
    else some (Browser.result { state with
      consoleEvents := state.consoleEvents.push ⟨"log",arguments⟩ } .undefined)
  | _ => none

end CookieClicker.JavaScript.BrowserConsole

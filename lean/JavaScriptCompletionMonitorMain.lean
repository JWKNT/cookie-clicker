import CookieClicker.JavaScriptDecode
import CookieClicker.JavaScriptCompletionMonitor

open Lean CookieClicker.JavaScript

private def program (json : Json) : Except String Program := do
  let artifact ← decodeArtifact json
  if artifact.units.size != 1 then throw "Expected one source unit"
  let some unit := artifact.units[0]? | throw "Missing source unit"
  pure unit.program

private def evaluate (json : Json) : Except String Json := do
  let setup ← program (← json.getObjVal? "setup")
  let body ← program (← json.getObjVal? "body")
  let initialized := Browser.initial
  let base := Builtins.run 2000000 (startProgram initialized.machine setup)
  if status base != .completion (.normal (some (.object base.globalObject))) then
    match status base with
    | .completion (.normal _) | .value _ => pure ()
    | other => throw ("Fixture setup failed: " ++ reprStr other)
  let browser : Browser.State := {initialized with machine := startProgram base body}
  let state : CompletionMonitor.State Unit Unit := CompletionMonitor.initial browser ()
  let policy : PrivateController.Controller Unit Unit := fun _ _ _ => .compute ()
  let .pure result := CompletionMonitor.runPrefix (fun _ => ()) policy .tasksFirst 512 state
    | throw "A deterministic fixture unexpectedly requested a random draw"
  let source := result.controlled.source
  let (label,error) := match source.phase with
    | .complete _ => ("complete","")
    | .missing failure => ("missing",reprStr failure)
    | .invalid reason => ("invalid",reason)
    | _ => ("pending","")
  pure (Json.mkObj [
    ("status",toJson label),("error",toJson error),
    ("boundary",toJson (Execution.atBoundary source.browser)),
    ("elapsed",toJson (toString source.browser.machine.elapsed)),
    ("actions",toJson result.controlled.history.length),
    ("accessed",toJson (CookieClicker.FullGame.Pinned.requirements.accessUpgrades.filter (CompletionMonitor.history result.log)))])

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let output := do
    let json ← Json.parse input
    Json.arr <$> (← json.getArr?).mapM evaluate
  match output with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok output => (← IO.getStdout).putStrLn output.compress; return 0

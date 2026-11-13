import CookieClicker.JavaScriptDecode
import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptCompletion

open Lean CookieClicker.JavaScript CookieClicker.FullGame

private def program (json : Json) : Except String Program := do
  let artifact ← decodeArtifact json
  if artifact.units.size != 1 then throw "Expected one source unit"
  let some unit := artifact.units[0]? | throw "Missing source unit"
  pure unit.program

private def returned (machine : Machine) : Except String Value :=
  match status machine with
  | .completion (.normal (some value)) | .value value => pure value
  | other => throw ("Source execution failed: " ++ reprStr other)

private def report (projected : Snapshot) : Json := Json.mkObj [
  ("projected",toJson true), ("complete",toJson (CookieClicker.FullGame.complete Pinned.requirements projected)),
  ("missingGoals",toJson ((goals Pinned.requirements).filter (fun goal => !satisfies projected goal)).length),
  ("accessed",toJson (Pinned.requirements.accessUpgrades.filter projected.accessedUpgrades))]

/-- Diagnostic metadata only: this is not a source operation or controller input. -/
private def markUnknown (machine : Machine) (game : Value) (json : Json) : Except String Machine := do
  let some marker := (json.getObjVal? "unknownOwn").toOption | pure machine
  let path ← (← marker.getObjVal? "path" >>= Json.getArr?).toList.mapM Json.getStr?
  let name ← marker.getObjVal? "name" >>= Json.getStr?
  let mut value := game
  for field in path do
    match Completion.field machine.heap value field with
    | .ok next => value := next
    | .error failure => throw ("Diagnostic unknown path: " ++ reprStr failure)
  let .object id := value | throw "Diagnostic unknown target must be an object"
  let some object := machine.heap.object? id | throw "Diagnostic unknown object missing"
  let some heap := machine.heap.writeObject id {object with
      unresolvedOwnNames := object.unresolvedOwnNames ++ [JSString.ofString name]} |
    throw "Diagnostic unknown write failed"
  pure {machine with heap}

private def evaluate (base : Machine) (json : Json) : Except String Json := do
  let programs ← (← json.getObjVal? "steps" >>= Json.getArr?).toList.mapM program
  let edition ← match json.getObjVal? "edition" with
    | .ok value => value.getStr?
    | .error _ => pure "steam"
  let mut machine := base
  let mut history := Completion.emptyHistory
  let mut output := Json.mkObj [("projected",toJson false), ("error",toJson "No source steps")]
  for step in programs do
    machine := Builtins.run 100000 (startProgram machine step)
    let game ← returned machine
    let marked ← markUnknown machine game json
    machine := marked
    match Completion.snapshot machine.heap game edition history with
    | .error error =>
      return Json.mkObj [("projected",toJson false), ("error",toJson (reprStr error))]
    | .ok projected =>
      history := Completion.recordAccess history projected
      output := report { projected with accessedUpgrades := history }
  pure output

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let output := do
    let json ← Json.parse input
    let baseProgram ← program (← json.getObjVal? "base")
    let base := Builtins.run 2000000 (startProgram Builtins.standardMachine baseProgram)
    let _ ← returned base
    let cases ← json.getObjVal? "cases" >>= Json.getArr?
    Json.arr <$> cases.mapM (evaluate base)
  match output with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok output => (← IO.getStdout).putStrLn output.compress; return 0

import CookieClicker.ObservationJson
import CookieClicker.Trace
import CookieClicker.GardenInvariant

open Lean CookieClicker.FullGame

def decodeTrace (j : Json) : Except String { trace : List Trace.Point // Trace.Chronological trace } := do
  if (← (← j.getObjVal? "schemaVersion").getNat?) != 1 then throw "Unsupported trace schema"
  if (← (← j.getObjVal? "checkpointSemantics").getStr?) != "native-action-and-timer-boundaries-v1" then
    throw "Unsupported checkpoint semantics"
  if (← (← j.getObjVal? "profileId").getStr?) != Pinned.profileId then throw "Wrong completion profile"
  if (← (← j.getObjVal? "requirementsSha256").getStr?) != Pinned.requirementsSha256 then
    throw "Completion requirements digest differs"
  let records ← (← j.getObjVal? "records").getArr?
  if records.isEmpty then throw "Trace must include an initial observation"
  let mut points := []
  for index in [:records.size] do
    let record := records[index]!
    let kind ← (← record.getObjVal? "kind").getStr?
    if index = 0 then
      if kind != "initial" then throw "First checkpoint must be initial"
    else if kind != "timer" && kind != "action" then throw "Unexpected checkpoint kind"
    let elapsedMs ← (← record.getObjVal? "elapsedMs").getNat?
    if elapsedMs > 9007199254740991 then throw "Unsafe clock value"
    if index = 0 && elapsedMs != 0 then throw "Initial clock must be zero"
    let observation ← decodeSnapshot (← record.getObjVal? "observation")
    if observation.schemaVersion != 1 || observation.gameVersion != Pinned.requirements.gameVersion ||
        observation.edition != Pinned.requirements.edition ||
        observation.historyGameVersion != Pinned.requirements.gameVersion ||
        observation.historyEdition != Pinned.requirements.edition then throw "Observation metadata differs from pinned profile"
    points := { elapsedMs, observation } :: points
  let orderedPoints := points.reverse
  if checked : Trace.orderedFrom 0 orderedPoints = true then
    return ⟨orderedPoints, (Trace.orderedFrom_sound 0 orderedPoints checked).2⟩
  else throw "Clock moved backwards"

private def evaluateTrace (j : Json) : Json :=
  match decodeTrace j with
  | .error error => Json.mkObj [("valid", Json.bool false), ("error", Json.str error)]
  | .ok checkedTrace =>
    let trace := checkedTrace.val
    let hit := match Trace.firstCompletion trace with
      | none => Json.null
      | some point => Json.mkObj [("elapsedMs", toJson point.elapsedMs)]
    let garden := match trace with
      | [] => Json.null
      | first :: rest =>
        let observations := rest.map (fun point => point.observation)
        Json.mkObj [("contractValid", toJson (Garden.validTrace first.observation observations)),
          ("juicyAcquisitions", toJson (Garden.acquisitions first.observation observations)),
          ("initialJuicyKnown", toJson (Garden.juicyKnown first.observation)),
          ("initialSeedlessWon", toJson (Garden.seedlessWon first.observation))]
    Json.mkObj [("valid", Json.bool true), ("observations", toJson trace.length),
      ("firstCompletion", hit), ("garden", garden)]

/-- Read an array of event traces and verify each first-completion calculation. -/
def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error error =>
    (← IO.getStderr).putStrLn error
    return 1
  | .ok json =>
    match json.getArr? with
    | .error error =>
      (← IO.getStderr).putStrLn error
      return 1
    | .ok traces =>
      (← IO.getStdout).putStrLn (Json.arr (traces.map evaluateTrace)).compress
      return 0

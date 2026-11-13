import CookieClicker.ObservationJson

open Lean CookieClicker.FullGame

private def evaluateSnapshot (j : Json) : Json :=
  match decodeSnapshot j with
  | .ok s => Json.mkObj [("decoded", Json.bool true), ("complete", Json.bool (complete Pinned.requirements s))]
  | .error _ => Json.mkObj [("decoded", Json.bool false), ("complete", Json.bool false)]

/-- Read an array of normalized snapshots and return decoding and completion results. -/
def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error e =>
    (← IO.getStderr).putStrLn e
    return 1
  | .ok json =>
    match json.getArr? with
    | .error e =>
      (← IO.getStderr).putStrLn e
      return 1
    | .ok snapshots =>
      (← IO.getStdout).putStrLn (Json.arr (snapshots.map evaluateSnapshot)).compress
      return 0

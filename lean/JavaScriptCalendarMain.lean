import Lean
import CookieClicker.JavaScriptCalendar

open Lean CookieClicker.JavaScript

private def integer (j : Json) : Except String Int := do
  let s ← j.getStr?
  match s.toInt? with
  | some value => pure value
  | none => throw "Invalid calendar integer"

private def evaluate (j : Json) : Except String Json := do
  let time ← if (← j.getObjVal? "op" >>= Json.getStr?) == "components" then do
      let args ← j.getObjVal? "values" >>= Json.getArr?
      if args.size != 7 then throw "Expected seven calendar fields"
      let values ← args.mapM integer
      pure (Calendar.fromComponents (values[0]!) (values[1]!) (values[2]!) (values[3]!) (values[4]!) (values[5]!) (values[6]!))
    else j.getObjVal? "time" >>= integer
  let f := Calendar.fields time
  return Json.mkObj [
    ("time",toJson (toString time)), ("year",toJson (toString f.year)),
    ("month",toJson f.month), ("day",toJson f.day), ("weekday",toJson f.weekday),
    ("hour",toJson f.hour), ("minute",toJson f.minute), ("second",toJson f.second), ("millisecond",toJson f.millisecond),
    ("utc",toJson (Calendar.toUTCString time)), ("date",toJson (Calendar.toDateString time)),
    ("clock",toJson (Calendar.toTimeString time)), ("iso",toJson (Calendar.toISOString time))]

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= fun requests => requests.mapM evaluate with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

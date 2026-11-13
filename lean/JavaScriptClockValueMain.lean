import Lean
import CookieClicker.JavaScriptClockValue

open Lean CookieClicker.JavaScript
open ClockValue

private def integer (j : Json) : Except String Int := do
  let text ← j.getStr?
  let some value := text.toInt? | throw "Expected exact integer string"
  return value

private def bits (j : Json) : Except String UInt64 := do
  let value ← integer j
  if value < 0 || value ≥ 2^64 then throw "Binary64 bits out of range"
  return UInt64.ofNat value.toNat

private def units (text : JSString) : Json := toJson (text.map UInt16.toNat)

private def time (j : Json) : Except String Timestamp := do
  let kind ← j.getObjVal? "kind" >>= Json.getStr?
  if kind == "native" then
    let value ← j.getObjVal? "bits" >>= bits
    let some result := Timestamp.ofNative value | throw "Timestamp is outside native prefix"
    return result
  else if kind == "exact" then
    let numerator ← j.getObjVal? "numerator" >>= integer
    let scale ← j.getObjVal? "scale" >>= Json.getNat?
    return Timestamp.ofDyadic ⟨numerator, scale⟩
  else throw "Unknown timestamp tag"

private def encode (t : Timestamp) : Json :=
  let normalized := t.exact.normalize
  Json.mkObj [
    ("kind", toJson (match t with | .native _ => "native" | .extended _ => "exact")),
    ("bits", match t with | .native bits => toJson (toString bits.toNat) | _ => Json.null),
    ("numerator", toJson (toString normalized.numerator)),
    ("scale", toJson normalized.scale),
    ("text", (Codec.render t).map units |>.getD Json.null),
    ("floor", toJson (toString t.exact.floor))]

private def evaluate (j : Json) : Except String Json := do
  let op ← j.getObjVal? "op" >>= Json.getStr?
  if op == "add" then
    let t ← j.getObjVal? "time" >>= time
    let duration ← j.getObjVal? "duration" >>= bits
    match Timestamp.addDuration t duration with
    | .timestamp result => return encode result
    | .ordinaryNonfinite result => return Json.mkObj [("kind", toJson "ordinary"), ("bits", toJson (toString result.toNat))]
  else if op == "difference" then
    let a ← j.getObjVal? "left" >>= time
    let b ← j.getObjVal? "right" >>= time
    return Json.mkObj [("bits", toJson (toString (Timestamp.difference a b).toNat))]
  else if op == "parse" then
    let input ← j.getObjVal? "text" >>= Json.getStr?
    match Codec.readFloat (JSString.ofString input) with
    | .ok result => return encode result
    | .error error => return Json.mkObj [("error", toJson (reprStr error))]
  else if op == "integer" then
    let n ← j.getObjVal? "value" >>= integer
    let rendered := Codec.renderInteger n
    return Json.mkObj [("text", toJson rendered), ("decoded", (Codec.readInteger rendered).map encode |>.getD Json.null)]
  else if op == "time" then
    return encode (← j.getObjVal? "time" >>= time)
  else throw "Unknown clock operation"

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= fun requests => requests.mapM evaluate with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok result => (← IO.getStdout).putStrLn (Json.arr result).compress; return 0

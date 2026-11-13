import Lean
import CookieClicker.JavaScriptUnicode

open Lean CookieClicker.JavaScript

private def units (json : Json) : Except String JSString := do
  let values ← json.getArr?
  let result ← values.mapM fun item => do
    let n ← item.getNat?
    if n > 65535 then throw "Invalid UTF16 unit"
    return UInt16.ofNat n
  return result.toList

private def emit (text : JSString) : Json := toJson (text.map UInt16.toNat)

private def evaluate (request : Json) : Except String Json := do
  let operation ← (← request.getObjVal? "op").getStr?
  if operation == "properties" then
    let properties := (List.range 0x110000).toArray.map fun point =>
      (if Unicode.isLetter point then 1 else 0) +
      (if Unicode.isCased point then 2 else 0) +
      (if Unicode.isCaseIgnorable point then 4 else 0)
    return toJson properties
  if operation == "fold" then
    let points ← (← request.getObjVal? "points").getArr?
    return toJson (← points.mapM fun point => do pure (Unicode.simpleFold (← point.getNat?)))
  let text ← units (← request.getObjVal? "text")
  if operation == "upper" then return emit (Unicode.upper text)
  if operation == "lower" then return emit (Unicode.lower text)
  if operation == "legacy" then return emit (text.map Unicode.legacyCanonicalize)
  if operation == "points" then return toJson (Unicode.fromUtf16 text)
  throw s!"Unknown Unicode operation: {operation}"

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= fun requests => requests.mapM evaluate with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

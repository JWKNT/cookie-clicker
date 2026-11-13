import Lean
import CookieClicker.JavaScriptEncoding

open Lean CookieClicker.JavaScript

private def evaluate (request : Json) : Except String Json := do
  let name ← (← request.getObjVal? "name").getStr?
  let raw ← (← request.getObjVal? "units").getArr?
  let input ← raw.mapM fun value => do
    let n ← value.getNat?
    if n > 65535 then throw "Invalid UTF16 unit"
    pure (UInt16.ofNat n)
  match Encoding.operate name input.toList with
  | .ok output => pure (Json.mkObj [("units",toJson (output.map UInt16.toNat))])
  | .error (name,_) => pure (Json.mkObj [("error",toJson name)])

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= fun requests => requests.mapM evaluate with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

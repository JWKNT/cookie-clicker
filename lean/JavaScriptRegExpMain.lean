import Lean
import CookieClicker.JavaScriptRegExp

open Lean CookieClicker.JavaScript

private def units (value : Json) : Except String JSString := do
  let numbers ← value.getArr? >>= fun values => values.mapM Json.getNat?
  if numbers.any (· > 65535) then throw "Invalid UTF-16 unit"
  return numbers.toList.map UInt16.ofNat

private def encodeError (error : RegExp.RegexError) : Json :=
  match error with
  | .syntax message => Json.mkObj [("status", toJson "syntax"), ("message", toJson message)]
  | .unsupported message => Json.mkObj [("status", toJson "unsupported"), ("message", toJson message)]
  | .fuel => Json.mkObj [("status", toJson "fuel")]

private def runCase (value : Json) : Except String Json := do
  let pattern ← units (← value.getObjVal? "pattern")
  let input ← units (← value.getObjVal? "input")
  let flags ← (← value.getObjVal? "flags").getStr?
  let start ← (← value.getObjVal? "start").getNat?
  match RegExp.compile pattern flags with
  | .error error => return encodeError error
  | .ok compiled => match RegExp.search compiled input start with
    | .error error => return encodeError error
    | .ok none => return Json.mkObj [("status", toJson "none")]
    | .ok (some found) =>
      let captures := found.captures.map fun range => match range with
        | none => Json.null
        | some (first, last) => toJson ((input.drop first |>.take (last - first)).map UInt16.toNat)
      return Json.mkObj [("status", toJson "match"), ("index", toJson found.start),
        ("end", toJson found.finish), ("captures", Json.arr captures)]

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= (fun values => values.mapM runCase) with
  | .error message => (← IO.getStderr).putStrLn message; return 1
  | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

import Lean
import CookieClicker.JavaScriptDomSyntax

open Lean CookieClicker.JavaScript

private def units (value : Json) : Except String JSString := do
  let numbers ← value.getArr? >>= fun values => values.mapM Json.getNat?
  if numbers.any (· > 65535) then throw "Invalid UTF-16 unit"
  return numbers.toList.map UInt16.ofNat

private def encodeNode : Nat → DomSyntax.Node → Json
  | 0, _ => Json.mkObj [("encodingBudgetExhausted", Json.bool true)]
  | _, .text value => Json.mkObj [("type", toJson "text"), ("units", toJson (value.map UInt16.toNat))]
  | _, .comment value => Json.mkObj [("type", toJson "comment"), ("units", toJson (value.map UInt16.toNat))]
  | fuel + 1, .element name attributes children => Json.mkObj [
      ("type", toJson "element"), ("name", toJson name),
      ("attributes", toJson (attributes.map fun attr => Json.mkObj [
        ("name", toJson attr.name), ("units", toJson (attr.value.map UInt16.toNat))])),
      ("children", toJson (children.map (encodeNode fuel)))]

private def encodeError : DomSyntax.ParseError → Json
  | .fuel => Json.mkObj [("status", toJson "fuel")]
  | .unsupported message offset => Json.mkObj [
      ("status", toJson "unsupported"), ("message", toJson message), ("offset", toJson offset)]

private def runCase (value : Json) : Except String Json := do
  let input ← units (← value.getObjVal? "units")
  let operation ← (← value.getObjVal? "operation").getStr?
  if operation == "decode" then
    let inAttribute ← (← value.getObjVal? "attribute").getBool?
    match DomSyntax.decodeEntities input inAttribute with
    | .error error => return encodeError error
    | .ok output => return Json.mkObj [("status", toJson "decoded"), ("units", toJson (output.map UInt16.toNat))]
  else if operation == "fragment" then
    let context ← (← value.getObjVal? "context").getStr?
    let fuel ← match value.getObjVal? "fuel" with | .ok n => n.getNat? | .error _ => pure 100000
    match DomSyntax.parseFragment context input fuel with
    | .error error => return encodeError error
    | .ok nodes => return Json.mkObj [("status", toJson "parsed"), ("nodes", toJson (nodes.map (encodeNode 10000)))]
  else if operation == "document" then
    let fuel ← match value.getObjVal? "fuel" with | .ok n => n.getNat? | .error _ => pure 100000
    match DomSyntax.parseDocument input fuel with
    | .error error => return encodeError error
    | .ok nodes => return Json.mkObj [("status", toJson "parsed"), ("nodes", toJson (nodes.map fun node =>
      match node with
      | .content node => encodeNode 10000 node
      | .doctype => Json.mkObj [("type", toJson "doctype"), ("name", toJson "html"),
          ("publicId", toJson ""), ("systemId", toJson "")]))]
  else throw "Unknown DOM syntax operation"

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= (fun values => values.mapM runCase) with
  | .error message => (← IO.getStderr).putStrLn message; return 1
  | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

import Lean
import CookieClicker.JavaScriptNumber
import CookieClicker.JavaScriptNumberString
import CookieClicker.JavaScriptMath

open Lean
open CookieClicker.JavaScript

private def bits (value : Json) : Except String UInt64 := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "Expected decimal bit string"
  if n ≥ 2 ^ 64 then throw "Binary64 bits exceed uint64"
  return UInt64.ofNat n

private def emit (value : UInt64) : Json := Json.str value.toNat.repr

private def units (value : Json) : Except String JSString := do
  let array ← value.getArr?
  let decoded ← array.mapM fun item => do
    let n ← item.getNat?
    if n > 65535 then throw "UTF16 unit exceeds uint16"
    return UInt16.ofNat n
  return decoded.toList

private def evaluate (input : Json) : Except String Json := do
  let operation ← (← input.getObjVal? "op").getStr?
  if ["parseNumber", "parseFloat", "parseInt"].contains operation then
    let text ← units (← input.getObjVal? "text")
    if operation == "parseNumber" then return emit (NumberString.toNumber text)
    if operation == "parseFloat" then return emit (NumberString.parseFloat text)
    let radix ← bits (← input.getObjVal? "radix")
    let some value := NumberString.parseInt text radix | return Json.str "unresolved"
    return emit value
  let a ← bits (← input.getObjVal? "a")
  if operation == "sin" || operation == "cos" then
    let value := if operation == "sin" then CookieClicker.JavaScript.Math.sin a
      else CookieClicker.JavaScript.Math.cos a
    let some value := value | return Json.str "unresolved"
    return emit value
  if operation == "toDecimal" then
    let some text := NumberString.toDecimal a | throw "No decimal candidate within 17 digits"
    return Json.arr (text.toArray.map (fun c => toJson c.toNat))
  if ["toFixed", "toPrecision", "toRadix"].contains operation then
    let parameter ← (← input.getObjVal? "parameter").getNat?
    let result := if operation == "toFixed" then NumberString.toFixed a parameter
      else if operation == "toPrecision" then NumberString.toPrecision a parameter
      else NumberString.toRadix a parameter
    let some text := result | throw s!"Unsupported {operation} conversion"
    return Json.arr (text.toArray.map (fun c => toJson c.toNat))
  let unary : Option (UInt64 → UInt64) := match operation with
    | "log" => some CookieClicker.JavaScript.Math.log
    | "atan" => some CookieClicker.JavaScript.Math.atan
    | "neg" => some Number.neg | "abs" => some Number.abs | "sqrt" => some Number.sqrt
    | "floor" => some Number.floor | "ceil" => some Number.ceil | "trunc" => some Number.trunc
    | "round" => some Number.round | "not" => some Number.bitNot
    | _ => none
  if let some op := unary then return emit (op a)
  if operation == "toInt32" then return Json.str (Number.toInt32 a).repr
  if operation == "toUInt32" then return Json.str (Number.toUInt32 a).toNat.repr
  if operation == "isNaN" then return toJson (Number.isNaN a)
  if operation == "isFinite" then return toJson (Number.isFinite a)
  if operation == "isInteger" then return toJson (Number.isInteger a)
  if operation == "isSafeInteger" then return toJson (Number.isSafeInteger a)
  let b ← bits (← input.getObjVal? "b")
  let binary : Option (UInt64 → UInt64 → UInt64) := match operation with
    | "pow" => some CookieClicker.JavaScript.Math.pow
    | "atan2" => some CookieClicker.JavaScript.Math.atan2
    | "add" => some Number.add | "sub" => some Number.sub | "mul" => some Number.mul
    | "div" => some Number.div | "rem" => some Number.remainder
    | "min" => some Number.minimum | "max" => some Number.maximum
    | "and" => some Number.bitAnd | "or" => some Number.bitOr | "xor" => some Number.bitXor
    | "shl" => some Number.shiftLeft | "shr" => some Number.shiftRight | "ushr" => some Number.unsignedShiftRight
    | _ => none
  if let some op := binary then return emit (op a b)
  match operation with
  | "eq" => return toJson (Number.equal a b)
  | "lt" => return toJson (Number.lessThan a b)
  | "le" => return toJson (Number.lessEqual a b)
  | "sameValue" => return toJson (Number.sameValue a b)
  | "sameValueZero" => return toJson (Number.sameValueZero a b)
  | _ => throw s!"Unsupported Number operation: {operation}"

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok cases =>
    match cases.mapM evaluate with
    | .error error => (← IO.getStderr).putStrLn error; return 1
    | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

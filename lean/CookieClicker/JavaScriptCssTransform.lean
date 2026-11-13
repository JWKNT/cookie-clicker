import CookieClicker.JavaScriptCssNumber

/-! A closed source-used 2D transform declaration grammar. Numeric arguments are
retained at full binary64 precision; CSSOM text uses the pinned %.6g formatter.
This module does not execute transforms or supply geometry/painting semantics. -/
namespace CookieClicker.JavaScript.CssTransform

structure Argument where
  bits : UInt64
  unit : String
  deriving Repr, DecidableEq

structure Operation where
  name : String
  arguments : List Argument
  deriving Repr, DecidableEq

private def whitespace (char : Char) : Bool := [9,10,12,13,32].contains char.toNat
private def trim (text : String) : String :=
  String.ofList (((text.toList.dropWhile whitespace).reverse.dropWhile whitespace).reverse)

private def number (text : String) : Except String (Option UInt64) := do
  let text := JSString.ofString text
  let (_,_,unsigned) := NumberString.takeSign text
  let some parsed := NumberString.decimalPrefix unsigned | return none
  if !parsed.rest.isEmpty then return none
  -- CSS requires at least one fractional digit after a decimal point.
  let mantissa := unsigned.takeWhile (fun c => c != 69 && c != 101)
  if mantissa.getLast? == some 46 then return none
  if parsed.exponent.natAbs > 4096 then throw "CSS transform exponent exceeds the diagnostic numeric budget"
  let bits := NumberString.toNumber text
  if !Number.isFinite bits || !Number.lessEqual (Number.abs bits) (Number.ofNat 1000000) then
    throw "CSS transform numeric value is outside the finite closed range"
  return some bits

private def argument (kind text : String) : Except String (Option Argument) := do
  let text := (trim text).toLower
  let unit := ["turn","grad","deg","rad","px","%"].find? (fun unit => text.endsWith unit) |>.getD ""
  if kind == "length" && ["vmin","vmax","rem","em","ex","ch","vw","vh","cm","mm","in","pc","pt","q"].any (fun suffix => text.endsWith suffix) then
    throw "Relative/physical transform length units require computed-style state"
  let raw := if unit.isEmpty then text else (text.dropEnd unit.length).toString
  let some bits ← number raw | return none
  if kind == "number" then
    if !unit.isEmpty then return none
    return some ⟨bits,""⟩
  if kind == "length" then
    if unit == "px" || unit == "%" then return some ⟨bits,unit⟩
    if unit.isEmpty && Number.isZero bits then return some ⟨bits,"px"⟩
    return none
  if kind == "angle" then
    if ["deg","rad","grad","turn"].contains unit then return some ⟨bits,unit⟩
    if unit.isEmpty && Number.isZero bits then return some ⟨bits,"deg"⟩
    return none
  throw "Unknown transform argument category"

private def functionName (name : String) : Option (String × String × List Nat) :=
  match name.toLower with
  | "scale" => some ("scale","number",[1,2])
  | "scalex" => some ("scaleX","number",[1])
  | "scaley" => some ("scaleY","number",[1])
  | "translate" => some ("translate","length",[1,2])
  | "translatex" => some ("translateX","length",[1])
  | "translatey" => some ("translateY","length",[1])
  | "rotate" => some ("rotate","angle",[1])
  | "matrix" => some ("matrix","number",[6])
  | _ => none

def parse (text : String) : Except String (Option (List Operation)) := do
  let text := trim text
  if text.toLower == "none" then return some []
  if text.isEmpty then return none
  if text.contains '\\' || (text.splitOn "/*").length > 1 then
    throw "Escaped or commented transform grammar is not implemented"
  let chunks := text.splitOn ")"
  -- CSS tokenization closes the final function at EOF. A trailing token after
  -- an already closed function still invalidates the declaration.
  let final := chunks.getLast?.getD ""
  let chunks ← if final.isEmpty then pure chunks.dropLast
    else if final.contains '(' then pure chunks else pure []
  if chunks.isEmpty then return none
  let mut output := []
  for chunk in chunks do
    let chunk := trim chunk
    let parts := chunk.splitOn "("
    if parts.length != 2 then
      if parts.length > 2 then throw "Nested transform functions require additional CSS grammar"
      return none
    let name := parts[0]!
    if name.isEmpty || name.toList.any whitespace then return none
    let some (name,kind,arities) := functionName name |
      throw ("Transform function is outside the source-used 2D grammar: " ++ name)
    let parameters := parts[1]!.splitOn ","
    if !arities.contains parameters.length then return none
    let mut arguments := []
    for parameter in parameters do
      let some value ← argument kind parameter | return none
      arguments := arguments ++ [value]
    output := output ++ [⟨name,arguments⟩]
  return some output

private def render (display : Bool) (operations : List Operation) : Except String String := do
  if operations.isEmpty then return "none"
  let chunks ← operations.mapM fun operation => do
    let arguments ← operation.arguments.mapM fun argument => do
      let numeric ← if display then
          match CssNumber.format argument.bits with
          | some text => pure text | none => throw "Nonfinite transform number"
        else match NumberString.toDecimal argument.bits with
          | some units => pure (String.ofList (units.map (Char.ofNat ∘ UInt16.toNat)))
          | none => throw "Transform number serialization is unavailable"
      pure (numeric ++ argument.unit)
    return operation.name ++ "(" ++ String.intercalate ", " arguments ++ ")"
  return String.intercalate " " chunks

/-- Lossless internal text. The Style cache retains this even though the DOM
style attribute and CSSOM getter serialize only six significant digits. -/
def normalize (text : String) : Except String (Option String) := do
  let some operations ← parse text | return none
  return some (← render false operations)

def serialize (text : String) : Except String String := do
  let some operations ← parse text | throw "Stored transform no longer parses"
  render true operations

end CookieClicker.JavaScript.CssTransform

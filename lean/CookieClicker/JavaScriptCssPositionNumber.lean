import CookieClicker.JavaScriptCssNumber

/-! Numeric px/percent position components. Internal text retains binary64
precision; native CSSOM formatting is applied only when the value is read.
This does not compute a background image position or layout geometry. -/
namespace CookieClicker.JavaScript.CssPositionNumber

/-- CSSParserToken clamps the double to the finite binary32 range without
rounding values inside that range to binary32. -/
def maximumMagnitude : UInt64 := 0x47efffffe0000000

def clamp (bits : UInt64) : UInt64 :=
  if Number.lessThan maximumMagnitude bits then maximumMagnitude
  else if Number.lessThan bits (Number.neg maximumMagnitude) then Number.neg maximumMagnitude
  else bits

private def parse (text : String) : Except String (Option (UInt64 × String)) := do
  let lower := text.toLower
  if lower.contains '(' || lower.contains '\\' then
    throw "Computed or escaped position value is not implemented"
  if ["vmin","vmax","rem","em","ex","ch","vw","vh","cm","mm","in","pc","pt","q"].any
      (fun unit => lower.endsWith unit) then
    throw "Relative or physical position units require computed-style state"
  let unit := if lower.endsWith "px" then "px" else if lower.endsWith "%" then "%" else ""
  let raw := if unit.isEmpty then lower else (lower.dropEnd unit.length).toString
  let units := JSString.ofString raw
  let (_,_,unsigned) := NumberString.takeSign units
  let some parsed := NumberString.decimalPrefix unsigned | return none
  if !parsed.rest.isEmpty then return none
  let mantissa := unsigned.takeWhile (fun c => c != 69 && c != 101)
  if mantissa.getLast? == some 46 then return none
  if parsed.exponent.natAbs > 4096 then throw "Position exponent exceeds the diagnostic numeric budget"
  let bits := clamp (NumberString.toNumber units)
  if !Number.isFinite bits then throw "Nonfinite CSS numeric parsing is outside the token grammar"
  if unit.isEmpty && !Number.isZero bits then return none
  return some (bits,if unit.isEmpty then "px" else unit)

def normalize (text : String) : Except String (Option String) := do
  let some (bits,unit) ← parse text | return none
  let some number := NumberString.toDecimal bits | throw "Position number cannot be represented"
  return some (String.ofList (number.map (Char.ofNat ∘ UInt16.toNat)) ++ unit)

def serialize (text : String) : Except String String := do
  let some (bits,unit) ← parse text | throw "Stored position number no longer parses"
  let some number := CssNumber.format bits | throw "Stored position number is nonfinite"
  return number ++ unit

end CookieClicker.JavaScript.CssPositionNumber

import CookieClicker.JavaScriptCssParser
import CookieClicker.JavaScriptCssPositionNumber

/-! The numeric branch of Chromium87 `ConsumeAlphaValue`. The token's double
is clamped to the native float range before percentage division. Values are
not clamped to [0,1] in the specified declaration; that is a computed-style
operation. Internal text retains the full binary64 value. CSSOM serialization
uses the existing pinned six-significant-digit formatter. Computed functions,
escapes and oversized diagnostic exponents remain explicit boundaries. -/
namespace CookieClicker.JavaScript.CssOpacity

private def trim (tokens : List Css.Token) :=
  ((tokens.dropWhile (· == .space)).reverse.dropWhile (· == .space)).reverse

private def parse (text : String) : Except String (Option UInt64) := do
  let tokens ← Css.Parser.tokenize 100000 (JSString.ofString text)
  let (raw,percent) ← match trim tokens with
    | [.number raw] => pure (raw,false)
    | [.percentage raw] => pure (raw,true)
    | .function _ :: _ => throw "Computed opacity requires CSS math semantics"
    | _ => return none
  let units := JSString.ofString raw
  let (_,_,unsigned) := NumberString.takeSign units
  let some parsed := NumberString.decimalPrefix unsigned | throw "CSS number token failed decimal parsing"
  if !parsed.rest.isEmpty then throw "CSS number token has an unparsed suffix"
  if parsed.exponent.natAbs > 4096 then throw "Opacity exponent exceeds the diagnostic numeric budget"
  let token := CssPositionNumber.clamp (NumberString.toNumber units)
  if !Number.isFinite token then throw "Nonfinite CSS number token"
  let bits := if percent then Number.div token (Number.ofNat 100) else token
  return some bits

def normalize (text : String) : Except String (Option String) := do
  let some bits ← parse text | return none
  let some digits := NumberString.toDecimal bits | throw "Opacity cannot be represented"
  return some (String.ofList (digits.map (Char.ofNat ∘ UInt16.toNat)))

def serialize (text : String) : Except String String := do
  let some bits ← parse text | throw "Stored opacity no longer parses"
  let some digits := CssNumber.format bits | throw "Stored opacity is nonfinite"
  return digits

end CookieClicker.JavaScript.CssOpacity

import CookieClicker.JavaScriptNumberString

/-! Pinned Chromium87 CSSNumericLiteralValue::CustomCSSText numeric formatting.
The source uses the small-integer path or C %.6g (nearest/even), not JavaScript
Number.toString or toPrecision. No native formatter is called by this code. -/
namespace CookieClicker.JavaScript.CssNumber

open Number
set_option exponentiation.threshold 4096

private def zeros := NumberString.zeros
private def trimFraction (text : String) : String :=
  if text.contains '.' then
    let value := String.ofList ((text.toList.reverse.dropWhile (· == '0')).reverse)
    if value.endsWith "." then (value.dropEnd 1).toString else value
  else text

def roundEvenRatio (numerator denominator : Nat) : Nat :=
  let q := numerator/denominator
  let r := numerator%denominator
  q + if 2*r > denominator || (2*r == denominator && q%2 == 1) then 1 else 0

def format (bits : Bits) : Option String := do
  if !isFinite bits then return ← none
  if isInteger bits && lessEqual (abs bits) (ofNat 999999) then
    return toString (truncateInt bits)
  let (n,d) := magnitudeFraction bits
  let order := NumberString.decimalOrder n d
  let exponent := order-6
  let rounded := roundEvenRatio (n*10^(-exponent).toNat) (d*10^exponent.toNat)
  let (mantissa,order) := if rounded ≥ 1000000 then (rounded/10,order+1) else (rounded,order)
  let digits := (zeros (6-mantissa.repr.length) ++ mantissa.repr).toList
  let scientificExponent := order-1
  let body := if scientificExponent < -4 || scientificExponent ≥ 6 then
      let significand := trimFraction (String.ofList (digits.take 1) ++ "." ++ String.ofList (digits.drop 1))
      let exponentDigits := scientificExponent.natAbs.repr
      significand ++ "e" ++ (if scientificExponent < 0 then "-" else "+") ++
        zeros (2-exponentDigits.length) ++ exponentDigits
    else if order ≤ 0 then trimFraction ("0." ++ zeros (-order).toNat ++ String.ofList digits)
    else trimFraction (String.ofList (digits.take order.toNat) ++ "." ++ String.ofList (digits.drop order.toNat))
  return (if signBit bits then "-" else "") ++ body

end CookieClicker.JavaScript.CssNumber

import CookieClicker.JavaScriptNumberString

/-! Closed Chromium87 color values. RGBA channels retain native eight-bit
storage. CSS declarations preserve admitted named keywords; Canvas text uses
Color::Serialized rather than the different CSSColorValue alpha formatter.
This is not the complete CSS color grammar or a native renderer refinement. -/
namespace CookieClicker.JavaScript.CssColor

structure RGBA where
  red : UInt8
  green : UInt8
  blue : UInt8
  alpha : UInt8 := 255
  deriving Repr, DecidableEq, Inhabited

structure Parsed where
  rgba : RGBA
  keyword : Option String := none
  deriving Repr, DecidableEq

private def whitespace (c : Char) : Bool := [9,10,12,13,32].contains c.toNat
private def trim (text : String) : String :=
  String.ofList (((text.toList.dropWhile whitespace).reverse.dropWhile whitespace).reverse)

private def digit (c : Char) : Option Nat :=
  if c ≥ '0' && c ≤ '9' then some (c.toNat-'0'.toNat)
  else if c ≥ 'a' && c ≤ 'f' then some (c.toNat-'a'.toNat+10)
  else none

private def hexadecimal (text : String) : Option RGBA := do
  let digits ← text.toList.mapM digit
  let byte := fun value => UInt8.ofNat value
  match digits with
  | [r,g,b] => return ⟨byte (r*17),byte (g*17),byte (b*17),255⟩
  | [r,g,b,a] => return ⟨byte (r*17),byte (g*17),byte (b*17),byte (a*17)⟩
  | [r1,r2,g1,g2,b1,b2] => return ⟨byte (r1*16+r2),byte (g1*16+g2),byte (b1*16+b2),255⟩
  | [r1,r2,g1,g2,b1,b2,a1,a2] =>
    return ⟨byte (r1*16+r2),byte (g1*16+g2),byte (b1*16+b2),byte (a1*16+a2)⟩
  | _ => none

private def names : List (String × RGBA) := [
  ("transparent",⟨0,0,0,0⟩),("black",⟨0,0,0,255⟩),("white",⟨255,255,255,255⟩),
  ("red",⟨255,0,0,255⟩),("lime",⟨0,255,0,255⟩),("blue",⟨0,0,255,255⟩),
  ("yellow",⟨255,255,0,255⟩),("aqua",⟨0,255,255,255⟩),("cyan",⟨0,255,255,255⟩),
  ("fuchsia",⟨255,0,255,255⟩),("magenta",⟨255,0,255,255⟩),
  ("gray",⟨128,128,128,255⟩),("grey",⟨128,128,128,255⟩),
  ("silver",⟨192,192,192,255⟩),("maroon",⟨128,0,0,255⟩),("olive",⟨128,128,0,255⟩),
  ("green",⟨0,128,0,255⟩),("purple",⟨128,0,128,255⟩),("teal",⟨0,128,128,255⟩),
  ("navy",⟨0,0,128,255⟩)]

private structure Decimal where
  negative : Bool
  magnitude : Number.Bits
  percent : Bool
  deriving Inhabited

private def decimal (text : String) : Except String (Option Decimal) := do
  let text := trim text
  let percent := text.endsWith "%"
  let text := if percent then (text.dropEnd 1).toString else text
  let negative := text.startsWith "-"
  let text := if negative then (text.drop 1).toString else text
  if text.contains '+' || text.contains 'e' || text.contains '(' then
    throw "CSS color numeric sign/exponent/computed grammar is outside the fragment"
  let parts := text.splitOn "."
  if parts.length > 2 || text.isEmpty then return none
  let whole := parts.headD ""
  let fraction := parts[1]?.getD ""
  if (whole.isEmpty && fraction.isEmpty) ||
      !whole.toList.all Char.isDigit || !fraction.toList.all Char.isDigit then return none
  if whole.length > 6 || fraction.length > 6 then
    throw "CSS color decimal exceeds the admitted six-digit fast-parser fragment"
  let whole := whole.toNat?.getD 0
  let fractionValue := fraction.toNat?.getD 0
  let magnitude := Number.add (Number.ofNat whole)
    (Number.div (Number.ofNat fractionValue) (Number.ofNat (10^fraction.length)))
  return some ⟨negative,magnitude,percent⟩

private def byte (value : Number.Bits) : UInt8 :=
  UInt8.ofNat (min 255 (Number.truncateInt (Number.round value)).toNat)

private def channel (value : Decimal) : UInt8 :=
  if value.negative then 0 else
  byte (if value.percent then Number.mul (Number.div value.magnitude (Number.ofNat 100))
      (Number.ofNat 255) else value.magnitude)

private def alpha (value : Decimal) : Except String UInt8 := do
  if value.percent then throw "CSS percentage alpha is outside the fast-parser fragment"
  if value.negative then return 0
  if Number.lessEqual Number.one value.magnitude then return 255
  return byte (Number.mul value.magnitude (Number.ofNat 255))

def parse (text : String) : Except String (Option Parsed) := do
  if text.toList.any (fun c => c.toNat ≥ 128 || c == '\\') || (text.splitOn "/*").length > 1 then
    throw "Escaped, commented or non-ASCII CSS color is outside the fragment"
  let text := (trim text).toLower
  if text.isEmpty then return none
  if text.startsWith "#" then return (hexadecimal (text.drop 1).toString).map fun rgba => ⟨rgba,none⟩
  if let some (_,rgba) := names.find? (·.1 == text) then return some ⟨rgba,some text⟩
  let prefixSize : Nat := if text.startsWith "rgb(" then 4 else if text.startsWith "rgba(" then 5 else 0
  if prefixSize == 0 then throw "CSS color keyword/function requires additional grammar or environment"
  if !text.endsWith ")" then throw "CSS color omitted closing delimiter requires general tokenization"
  let body := ((text.drop prefixSize).toString.dropEnd 1).toString
  if !body.contains ',' then throw "CSS space-separated color syntax is outside the fragment"
  let parts := body.splitOn ","
  if parts.length != 3 && parts.length != 4 then return none
  let mut values : List Decimal := []
  for part in parts do
    let some value ← decimal part | return none
    values := values ++ [value]
  let red := values[0]!
  let green := values[1]!
  let blue := values[2]!
  if red.percent != green.percent || red.percent != blue.percent then
    throw "Mixed channel percentage syntax needs the general CSS parser"
  let opacity ← if values.length == 4 then alpha values[3]! else pure 255
  return some ⟨⟨channel red,channel green,channel blue,opacity⟩,none⟩

private def fractionText (numerator denominatorDigits : Nat) : String :=
  let (coefficient,exponent) := NumberString.stripZeros 6 numerator (-(denominatorDigits : Int))
  if numerator == 0 then "0" else NumberString.formatDecimal coefficient exponent

/-- CSSOM picks two decimals if their round-trip gives the stored byte,
otherwise three. The finite UInt8 domain is compared with the pinned float32
native implementation; this definition contains no renderer output table. -/
def cssAlpha (value : UInt8) : String :=
  let a := value.toNat
  let hundred := NumberString.roundRatio (a*100) 255
  if NumberString.roundRatio (hundred*255) 100 == a then fractionText hundred 2
  else fractionText (NumberString.roundRatio (a*1000) 255) 3

private def channels (color : RGBA) : String :=
  toString color.red.toNat ++ ", " ++ toString color.green.toNat ++ ", " ++ toString color.blue.toNat

def cssText (parsed : Parsed) : String :=
  match parsed.keyword with
  | some keyword => keyword
  | none =>
    if parsed.rgba.alpha == 255 then "rgb(" ++ channels parsed.rgba ++ ")"
    else "rgba(" ++ channels parsed.rgba ++ ", " ++ cssAlpha parsed.rgba.alpha ++ ")"

private def hexByte (value : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[value.toNat/16]!,digits[value.toNat%16]!]

/-- Color::Serialized converts alpha/255 to ECMAScript shortest decimal and
then Decimal::ToString reduces it to DBL_DIG (15) digits, with an upward tie. -/
def canvasAlpha (value : UInt8) : Option String := do
  if value == 0 then return "0"
  let bits := Number.div (Number.ofNat value.toNat) (Number.ofNat 255)
  let (coefficient,exponent) ← NumberString.shortestDecimal bits
  let excess := coefficient.repr.length - 15
  let rounded := if excess == 0 then coefficient else
    NumberString.roundRatio coefficient (10^excess)
  let (coefficient,exponent) := NumberString.stripZeros 18 rounded (exponent+excess)
  return NumberString.formatDecimal coefficient exponent

def canvasText (color : RGBA) : Option String := do
  if color.alpha == 255 then return "#" ++ hexByte color.red ++ hexByte color.green ++ hexByte color.blue
  return "rgba(" ++ channels color ++ ", " ++ (← canvasAlpha color.alpha) ++ ")"

end CookieClicker.JavaScript.CssColor

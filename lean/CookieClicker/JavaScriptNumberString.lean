import CookieClicker.JavaScriptNumber
import CookieClicker.JavaScriptSyntax

/-! Numeric string conversions used by the source interpreter.
These are explicit integer algorithms over UTF-16 units. Decimal conversion uses
the closest, even-tie choice among the shortest round-tripping decimal candidates.
The 17-digit search fails closed if no candidate is found. That search bound and
the correspondence to the pinned V8 conversion implementation need a general
refinement proof; native boundary comparisons alone do not discharge it.
-/
namespace CookieClicker.JavaScript.NumberString

open Number
set_option exponentiation.threshold 4096

def whitespace (c : UInt16) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || (8192 ≤ n && n ≤ 8202) ||
    [32, 160, 5760, 8232, 8233, 8239, 8287, 12288, 65279].contains n

def trimLeft (text : JSString) : JSString := text.dropWhile whitespace
def trim (text : JSString) : JSString := ((trimLeft text).reverse.dropWhile whitespace).reverse
def decimalDigit (c : UInt16) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

def digit (c : UInt16) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 90 then some (n - 55)
  else if 97 ≤ n && n ≤ 122 then some (n - 87)
  else none

def digitsValue (base : Nat) (text : JSString) : Nat :=
  text.foldl (fun acc c => acc * base + (digit c).getD 0) 0

def takeSign : JSString → Bool × Bool × JSString
  | c :: rest => if c == 45 then (true, true, rest)
      else if c == 43 then (false, true, rest) else (false, false, c :: rest)
  | [] => (false, false, [])

structure DecimalPrefix where
  mantissa : Nat
  exponent : Int
  rest : JSString
  deriving Repr

/-- The maximal decimal prefix; a malformed exponent is left unconsumed. -/
def decimalPrefix (text : JSString) : Option DecimalPrefix := do
  let whole := text.takeWhile decimalDigit
  let tail := text.drop whole.length
  let (fractional, afterFraction) := match tail with
    | c :: rest => if c == 46 then
        let ds := rest.takeWhile decimalDigit
        (ds, rest.drop ds.length)
      else ([], tail)
    | [] => ([], [])
  if whole.isEmpty && fractional.isEmpty then none
  else
    let (exponent, rest) := match afterFraction with
      | c :: more => if c == 69 || c == 101 then
          let (negative, _, digits) := takeSign more
          let ds := digits.takeWhile decimalDigit
          if ds.isEmpty then (0, afterFraction)
          else (if negative then -(digitsValue 10 ds : Int) else (digitsValue 10 ds : Int),
            digits.drop ds.length)
        else (0, afterFraction)
      | [] => (0, [])
    some ⟨digitsValue 10 (whole ++ fractional), exponent - (fractional.length : Int), rest⟩

def infinityText : JSString := JSString.ofString "Infinity"

def toNumber (input : JSString) : Bits := Id.run do
  let text := trim input
  if text.isEmpty then return positiveZero
  let (negative, signed, unsigned) := takeSign text
  if unsigned == infinityText then return if negative then negativeInfinity else positiveInfinity
  if !signed then
    let basePrefix := match unsigned with
      | a :: b :: rest => if a == 48 then
          if b == 120 || b == 88 then some (16, rest)
          else if b == 98 || b == 66 then some (2, rest)
          else if b == 111 || b == 79 then some (8, rest)
          else none
        else none
      | _ => none
    if let some (base, rest) := basePrefix then
      if rest.isEmpty || !rest.all (fun c => (digit c).any (· < base)) then return nan
      return ofNat (digitsValue base rest)
  match decimalPrefix unsigned with
  | none => return nan
  | some result =>
    if !result.rest.isEmpty then return nan
    let value := ofScientific result.mantissa result.exponent
    return if negative then neg value else value

def parseFloat (input : JSString) : Bits :=
  let (negative, _, text) := takeSign (trimLeft input)
  let value := if text.take infinityText.length == infinityText then positiveInfinity
    else match decimalPrefix text with
      | none => nan
      | some result => ofScientific result.mantissa result.exponent
  if negative then neg value else value

/-- Generic non-power-of-two radices permit implementation approximations.
Those cases remain unresolved: exact integer conversion and even V8's C++
chunk algorithm with separately rounded multiply/add can disagree with the
installed native host. Pinned source uses omitted, 2, 10 and 16 radices. -/
def parseInt (input : JSString) (radix : Bits := positiveZero) : Option Bits :=
  let (negative, _, text) := takeSign (trimLeft input)
  let r := toInt32 radix
  if r != 0 && (r < 2 || r > 36) then some nan
  else
    let hasHexPrefix := match text with
      | a :: b :: _ => a == 48 && (b == 120 || b == 88)
      | _ => false
    let base := if r == 0 then if hasHexPrefix then 16 else 10 else r.toNat
    let digits := if base == 16 && hasHexPrefix then text.drop 2 else text
    let accepted := digits.takeWhile (fun c => (digit c).any (· < base))
    if accepted.isEmpty then some nan
    else if ![2, 4, 8, 10, 16, 32].contains base then none
    else let value := ofNat (digitsValue base accepted)
         some (if negative then neg value else value)

def decimalOrder (numerator denominator : Nat) : Int :=
  let estimate := (numerator.repr.length : Int) - (denominator.repr.length : Int)
  let below := numerator * 10 ^ (-estimate).toNat < denominator * 10 ^ estimate.toNat
  (if below then estimate - 1 else estimate) + 1

def stripZeros : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | fuel + 1, m, e =>
    if m != 0 && m % 10 == 0 then stripZeros fuel (m / 10) (e + 1) else (m, e)

def decimalCandidate (bits : Bits) (numerator denominator : Nat) (exponent : Int) : Option (Nat × Int) :=
  let n := numerator * 10 ^ (-exponent).toNat
  let d := denominator * 10 ^ exponent.toNat
  let q := n / d
  let lowerOK := ofScientific q exponent == bits
  let upperOK := ofScientific (q + 1) exponent == bits
  let chooseUpper := !lowerOK || (upperOK &&
    (2 * (n % d) > d || (2 * (n % d) == d && q % 2 == 1)))
  if !lowerOK && !upperOK then none
  else some (stripZeros 18 (if chooseUpper then q + 1 else q) exponent)

def shortestDecimal (bits : Bits) : Option (Nat × Int) :=
  let (numerator, denominator) := magnitudeFraction bits
  let order := decimalOrder numerator denominator
  (List.range 17).findSome? fun index =>
    decimalCandidate bits numerator denominator (order - (index + 1 : Nat))

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

def formatDecimal (mantissa : Nat) (exponent : Int) : String :=
  let digits := mantissa.repr.toList
  let k := digits.length
  let n := (k : Int) + exponent
  if (k : Int) ≤ n && n ≤ 21 then String.ofList digits ++ zeros (n - k).toNat
  else if 0 < n && n ≤ 21 then
    String.ofList (digits.take n.toNat) ++ "." ++ String.ofList (digits.drop n.toNat)
  else if -6 < n && n ≤ 0 then "0." ++ zeros (-n).toNat ++ String.ofList digits
  else
    let significand := if k == 1 then String.ofList digits
      else String.ofList (digits.take 1) ++ "." ++ String.ofList (digits.drop 1)
    let e := n - 1
    significand ++ "e" ++ (if e < 0 then "-" else "+") ++ e.natAbs.repr

def toDecimal (bits : Bits) : Option JSString := do
  let text ← if isNaN bits then pure "NaN"
    else if isZero bits then pure "0"
    else if isInfinite bits then pure (if signBit bits then "-Infinity" else "Infinity")
    else do
      let (m, e) ← shortestDecimal (abs bits)
      pure ((if signBit bits then "-" else "") ++ formatDecimal m e)
  pure (JSString.ofString text)

/-- Round a nonnegative rational to an integer, choosing the larger tie. -/
def roundRatio (n d : Nat) : Nat := n / d + (if 2 * (n % d) ≥ d then 1 else 0)

def scaledRound (bits : Bits) (exponent : Int) : Nat :=
  let (n, d) := magnitudeFraction bits
  roundRatio (n * 10 ^ (-exponent).toNat) (d * 10 ^ exponent.toNat)

/-- `fractionDigits` has already undergone ToIntegerOrInfinity and range
checking by the method caller. `none` reports an unsupported conversion. -/
def toFixed (bits : Bits) (fractionDigits : Nat) : Option JSString := do
  if fractionDigits > 100 then none
  else if !isFinite bits || !lessThan (abs bits) (ofScientific 1 21) then toDecimal bits
  else
    let digits := (scaledRound bits (-(fractionDigits : Int))).repr
    let padded := zeros (fractionDigits + 1 - digits.length) ++ digits
    let chars := padded.toList
    let body := if fractionDigits == 0 then padded else
      String.ofList (chars.take (chars.length - fractionDigits)) ++ "." ++
      String.ofList (chars.drop (chars.length - fractionDigits))
    pure (JSString.ofString ((if signBit bits && !isZero bits then "-" else "") ++ body))

/-- The caller handles undefined precision and the native RangeError cases. -/
def toPrecision (bits : Bits) (precision : Nat) : Option JSString := do
  if !isFinite bits then toDecimal bits
  else if precision == 0 || precision > 100 then none
  else
    let (n, d) := magnitudeFraction bits
    let order := if isZero bits then 1 else decimalOrder n d
    let rounded := scaledRound bits (order - (precision : Int))
    let (mantissa, adjustedOrder) := if rounded ≥ 10 ^ precision then
      (rounded / 10, order + 1) else (rounded, order)
    let text := zeros (precision - mantissa.repr.length) ++ mantissa.repr
    let digits := text.toList
    let exponent := adjustedOrder - 1
    let body := if exponent < -6 || exponent ≥ (precision : Int) then
        String.ofList (digits.take 1) ++
        (if precision == 1 then "" else "." ++ String.ofList (digits.drop 1)) ++
        "e" ++ (if exponent < 0 then "-" else "+") ++ exponent.natAbs.repr
      else if adjustedOrder ≤ 0 then "0." ++ zeros (-adjustedOrder).toNat ++ text
      else if adjustedOrder.toNat ≥ precision then text ++ zeros (adjustedOrder.toNat - precision)
      else String.ofList (digits.take adjustedOrder.toNat) ++ "." ++
        String.ofList (digits.drop adjustedOrder.toNat)
    pure (JSString.ofString ((if signBit bits && !isZero bits then "-" else "") ++ body))

def radixDigits (base : Nat) : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, value =>
    let digit := value % base
    let c := Char.ofNat (if digit < 10 then digit + 48 else digit + 87)
    if value < base then [c] else radixDigits base fuel (value / base) ++ [c]

/-- Nondecimal formatting is currently restricted to integral values in
power-of-two radices. The
pinned source's explicit radix calls use binary integer encodings and UTF-16
code units. Fractional radix formatting must not silently use decimal text. -/
def toRadix (bits : Bits) (base : Nat) : Option JSString := do
  if base < 2 || base > 36 then none
  else if base == 10 || !isFinite bits || isZero bits then toDecimal bits
  else if ![2, 4, 8, 16, 32].contains base || !isInteger bits then none
  else
    let magnitude := (truncateInt bits).natAbs
    let text := String.ofList (radixDigits base 1024 magnitude)
    pure (JSString.ofString ((if signBit bits then "-" else "") ++ text))

theorem signed_empty_invalid : isNaN (toNumber (JSString.ofString "+")) = true := by decide +kernel
theorem whitespace_zero : toNumber [32, 65279, 9] = positiveZero := by decide +kernel
theorem negative_string_zero : toNumber (JSString.ofString "-0") = negativeZero := by decide +kernel
theorem parse_float_prefix : parseFloat (JSString.ofString "1.25e+bad") = ofScientific 125 (-2) := by decide +kernel
theorem hex_parse : parseInt (JSString.ofString "-0xffsuffix") = some (ofInt (-255)) := by decide +kernel
theorem signed_hex_invalid : isNaN (toNumber (JSString.ofString "+0xff")) = true := by decide +kernel

end CookieClicker.JavaScript.NumberString

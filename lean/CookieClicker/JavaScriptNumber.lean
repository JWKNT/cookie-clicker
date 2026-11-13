import Std
import Init.Data.Float.Model.Float

/-! Number operations for the source interpreter. Values carry binary64 bits.
The arithmetic uses Lean's logical Float.Model, not opaque native Float operations.
NaN payloads are canonicalized. JavaScript has one Number NaN value; exposing its
payload through typed buffers would need a separate host-memory specification.
ECMAScript Number remainder is truncating remainder, not IEEE remainder.
Transcendental functions and decimal formatting are not supplied by this module.
-/
namespace CookieClicker.JavaScript.Number

set_option exponentiation.threshold 4096

abbrev Bits := UInt64

def positiveZero : Bits := 0
def negativeZero : Bits := 9223372036854775808
def positiveInfinity : Bits := 9218868437227405312
def negativeInfinity : Bits := 18442240474082181120
def nan : Bits := (Float.Model.pack .notANumber).toBits
def one : Bits := 4607182418800017408

def model (bits : Bits) : Float.Model := Float.Model.ofBits bits
def canonical (bits : Bits) : Bits := (model bits).toBits
def signBit (bits : Bits) : Bool := bits.toNat ≥ 2 ^ 63
def exponentField (bits : Bits) : Nat := bits.toNat / 2 ^ 52 % 2048
def fraction (bits : Bits) : Nat := bits.toNat % 2 ^ 52
def isNaN (bits : Bits) : Bool := exponentField bits == 2047 && fraction bits != 0
def isInfinite (bits : Bits) : Bool := exponentField bits == 2047 && fraction bits == 0
def isFinite (bits : Bits) : Bool := exponentField bits != 2047
def isZero (bits : Bits) : Bool := bits.toNat % 2 ^ 63 == 0

def add (a b : Bits) : Bits := ((model a).add (model b)).toBits
def sub (a b : Bits) : Bits := ((model a).sub (model b)).toBits
def mul (a b : Bits) : Bits := ((model a).mul (model b)).toBits
def div (a b : Bits) : Bits := ((model a).div (model b)).toBits
def neg (a : Bits) : Bits := (model a).neg.toBits
def abs (a : Bits) : Bits := (model a).abs.toBits
def sqrt (a : Bits) : Bits := (model a).sqrt.toBits
def ofNat (a : Nat) : Bits := (Float.Model.ofNat a).toBits
def ofInt (a : Int) : Bits := (Float.Model.ofInt a).toBits
def ofScientific (m : Nat) (e : Int) : Bits := (Float.Model.ofScientific m e).toBits
def equal (a b : Bits) : Bool := (model a).beq (model b)
def lessThan (a b : Bits) : Bool := (model a).lt (model b)
def lessEqual (a b : Bits) : Bool := (model a).le (model b)

def sameValue (a b : Bits) : Bool :=
  if isNaN a && isNaN b then true
  else if isZero a && isZero b then signBit a == signBit b
  else equal a b

def sameValueZero (a b : Bits) : Bool := (isNaN a && isNaN b) || equal a b

def minimum (a b : Bits) : Bits :=
  if isNaN a || isNaN b then nan
  else if isZero a && isZero b then if signBit a || signBit b then negativeZero else positiveZero
  else if lessThan a b then a else b

def maximum (a b : Bits) : Bits :=
  if isNaN a || isNaN b then nan
  else if isZero a && isZero b then if signBit a && signBit b then negativeZero else positiveZero
  else if lessThan a b then b else a

/-- Magnitude is mantissa * 2^exponent. Only finite inputs have this meaning. -/
def dyadic (bits : Bits) : Nat × Int :=
  if exponentField bits == 0 then (fraction bits, -1074)
  else (2 ^ 52 + fraction bits, (exponentField bits : Int) - 1075)

def ofDyadic (negative : Bool) (mantissa : Nat) (exponent : Int) : Bits :=
  (Float.Model.pack (Float.Model.UnpackedFloat.round Float.Model.Format.binary64
    (if negative then .negative else .positive) mantissa exponent)).toBits

/-- Exact nonnegative fraction for a finite magnitude. -/
def magnitudeFraction (bits : Bits) : Nat × Nat :=
  let (m, e) := dyadic bits
  if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)

/-- Truncation toward zero, with nonfinite inputs mapped to zero for ToInt32. -/
def truncateInt (bits : Bits) : Int :=
  if !isFinite bits then 0
  else
    let (n, d) := magnitudeFraction bits
    if signBit bits then -(n / d : Int) else (n / d : Int)

def signedInteger (negative : Bool) (n : Nat) : Bits :=
  if n == 0 then if negative then negativeZero else positiveZero
  else if negative then ofInt (-(n : Int)) else ofNat n

def trunc (bits : Bits) : Bits :=
  if !isFinite bits || isZero bits then canonical bits
  else
    let (n, d) := magnitudeFraction bits
    signedInteger (signBit bits) (n / d)

def floor (bits : Bits) : Bits :=
  if !isFinite bits || isZero bits then canonical bits
  else
    let (n, d) := magnitudeFraction bits
    let extra := if signBit bits && n % d != 0 then 1 else 0
    signedInteger (signBit bits) (n / d + extra)

def ceil (bits : Bits) : Bits :=
  if !isFinite bits || isZero bits then canonical bits
  else
    let (n, d) := magnitudeFraction bits
    let extra := if !signBit bits && n % d != 0 then 1 else 0
    signedInteger (signBit bits) (n / d + extra)

/-- Math.round selects the integer toward +infinity on halfway inputs. -/
def round (bits : Bits) : Bits :=
  if !isFinite bits || isZero bits then canonical bits
  else
    let (n, d) := magnitudeFraction bits
    let twiceRemainder := 2 * (n % d)
    let extra := if (if signBit bits then twiceRemainder > d else twiceRemainder ≥ d) then 1 else 0
    signedInteger (signBit bits) (n / d + extra)

def remainder (a b : Bits) : Bits :=
  if isNaN a || isNaN b || isInfinite a || isZero b then nan
  else if isInfinite b || isZero a then canonical a
  else
    let (ma, ea) := dyadic a
    let (mb, eb) := dyadic b
    let e := min ea eb
    let numerator := ma * 2 ^ (ea - e).toNat
    let denominator := mb * 2 ^ (eb - e).toNat
    ofDyadic (signBit a) (numerator % denominator) e

/-- ECMAScript wraps modulo 2^32; Float.Model.toUInt32 instead clamps. -/
def toUInt32 (bits : Bits) : UInt32 :=
  UInt32.ofNat ((truncateInt bits % (2 ^ 32 : Int)).toNat)

def signed32 (word : UInt32) : Int :=
  if word.toNat < 2 ^ 31 then (word.toNat : Int) else (word.toNat : Int) - 2 ^ 32

def toInt32 (bits : Bits) : Int := signed32 (toUInt32 bits)
def bitAnd (a b : Bits) : Bits := ofInt (signed32 (toUInt32 a &&& toUInt32 b))
def bitOr (a b : Bits) : Bits := ofInt (signed32 (toUInt32 a ||| toUInt32 b))
def bitXor (a b : Bits) : Bits := ofInt (signed32 (toUInt32 a ^^^ toUInt32 b))
def bitNot (a : Bits) : Bits := ofInt (signed32 (~~~toUInt32 a))
def shiftAmount (a : Bits) : Nat := (toUInt32 a).toNat % 32
def shiftLeft (a b : Bits) : Bits :=
  ofInt (signed32 (UInt32.ofNat ((toUInt32 a).toNat * 2 ^ shiftAmount b)))
def shiftRight (a b : Bits) : Bits := ofInt (toInt32 a / (2 ^ shiftAmount b : Int))
def unsignedShiftRight (a b : Bits) : Bits := ofNat ((toUInt32 a).toNat / 2 ^ shiftAmount b)

def isInteger (a : Bits) : Bool := isFinite a && equal a (trunc a)
def isSafeInteger (a : Bits) : Bool := isInteger a && lessEqual (abs a) (ofNat (2 ^ 53 - 1))

theorem negative_zero_equal : equal negativeZero positiveZero = true := by decide +kernel
theorem negative_zero_distinct : sameValue negativeZero positiveZero = false := by decide +kernel
theorem nan_not_equal : equal nan nan = false := by decide +kernel
theorem zero_div_zero : isNaN (div positiveZero positiveZero) = true := by decide +kernel
theorem signed_zero_division : div one negativeZero = negativeInfinity := by decide +kernel
theorem halfway_round_negative : round (div (neg one) (ofNat 2)) = negativeZero := by decide +kernel
theorem negative_remainder : remainder (ofInt (-5)) (ofNat 2) = ofInt (-1) := by decide +kernel
theorem wrapping_conversion : toInt32 (ofNat (2 ^ 32 - 1)) = -1 := by decide +kernel
theorem subnormal_survives : mul 1 one = 1 := by decide +kernel

end CookieClicker.JavaScript.Number

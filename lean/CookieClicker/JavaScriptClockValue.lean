import CookieClicker.JavaScriptNumberString
import CookieClicker.JavaScriptCalendar
import Std.Data.String.ToInt

/-!
The pure part of the selected unbounded-clock extension. This module does not
change the JavaScript Value type or execute an annotated source program.

Absolute times have a separate type. A finite-prefix value retains native
binary64 bits. Beyond that prefix, addition of a finite binary64 duration uses
its exact dyadic value. Subtracting two times returns an ordinary binary64
duration. Cookie counts, counters, timers' delay conversions, and other Numbers
are not changed. Calendar integers are a third, separate type.

The finite-prefix boundary is the native Date range. Agreement for an arithmetic
step requires its exact result to stay in that range, as well as valid input
tags. The extension is a selected mathematical rule outside that range; native
JavaScript does not specify it. In particular, returning to the native prefix
rounds the exact value once to binary64. This makes the region determine the
precision mode rather than an unrecorded history flag.

The codecs below are for annotated current-save timestamp fields. Ordinary
parseInt/parseFloat and ordinary strings retain their existing semantics. The
source-site annotations, typed-value propagation, and general string-codec
refinement are separate obligations. Storage quotas and failures are unchanged.
-/
namespace CookieClicker.JavaScript.ClockValue

set_option exponentiation.threshold 4096

/-- Exact finite dyadic number, numerator / 2^scale. Noncanonical forms are
permitted in arithmetic; normalization is used before extended formatting. -/
structure Dyadic where
  numerator : Int
  scale : Nat
  deriving Repr, DecidableEq

namespace Dyadic

def ofInt (n : Int) : Dyadic := ⟨n, 0⟩
def denominator (x : Dyadic) : Int := 2 ^ x.scale
def equivalent (x y : Dyadic) : Prop :=
  x.numerator * y.denominator = y.numerator * x.denominator

def scaledNumerator (x : Dyadic) (scale : Nat) : Int :=
  x.numerator * 2 ^ (scale - x.scale)

def add (x y : Dyadic) : Dyadic :=
  let scale := max x.scale y.scale
  ⟨x.scaledNumerator scale + y.scaledNumerator scale, scale⟩

def neg (x : Dyadic) : Dyadic := ⟨-x.numerator, x.scale⟩
def sub (x y : Dyadic) : Dyadic := add x y.neg
def less (x y : Dyadic) : Bool :=
  x.numerator * y.denominator < y.numerator * x.denominator
def lessEqual (x y : Dyadic) : Bool :=
  x.numerator * y.denominator ≤ y.numerator * x.denominator
def floor (x : Dyadic) : Int := x.numerator / x.denominator
def trunc (x : Dyadic) : Int :=
  if x.numerator < 0 then -((-x.numerator) / x.denominator)
  else x.numerator / x.denominator

/-- This conversion is only used with a finite binary64 input. -/
def ofFiniteBits (bits : UInt64) : Dyadic :=
  let (mantissa, exponent) := Number.dyadic bits
  let signed : Int := if Number.signBit bits then -(mantissa : Int) else mantissa
  if exponent ≥ 0 then ⟨signed * 2 ^ exponent.toNat, 0⟩
  else ⟨signed, (-exponent).toNat⟩

/-- Correctly rounded binary64 projection uses the logical Float.Model. -/
def toBits (x : Dyadic) : UInt64 :=
  Number.ofDyadic (x.numerator < 0) x.numerator.natAbs (-(x.scale : Int))

def normalize : Dyadic → Dyadic
  | ⟨n, 0⟩ => ⟨n, 0⟩
  | ⟨n, k + 1⟩ =>
    if n % 2 == 0 then normalize ⟨n / 2, k⟩ else ⟨n, k + 1⟩
termination_by x => x.scale

theorem denominator_pos (x : Dyadic) : 0 < x.denominator := by
  exact Int.pow_pos (by decide)

theorem equivalent_refl (x : Dyadic) : equivalent x x := rfl

theorem equivalent_symm {x y : Dyadic} (h : equivalent x y) : equivalent y x :=
  h.symm

theorem equivalent_trans {x y z : Dyadic} (xy : equivalent x y)
    (yz : equivalent y z) : equivalent x z := by
  apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (denominator_pos y))
  change (x.numerator * z.denominator) * y.denominator =
    (z.numerator * x.denominator) * y.denominator
  calc
    _ = (x.numerator * y.denominator) * z.denominator := by ac_rfl
    _ = (y.numerator * x.denominator) * z.denominator := by rw [xy]
    _ = (y.numerator * z.denominator) * x.denominator := by ac_rfl
    _ = (z.numerator * y.denominator) * x.denominator := by rw [yz]
    _ = _ := by ac_rfl

theorem scaled_denominator (x : Dyadic) (k : Nat) (h : x.scale ≤ k) :
    x.scaledNumerator k * x.denominator = x.numerator * 2 ^ k := by
  simp only [scaledNumerator, denominator, Int.mul_assoc, ← Int.pow_add]
  rw [Nat.sub_add_cancel h]

theorem add_scale (x y : Dyadic) : (add x y).scale = max x.scale y.scale := rfl

/-- Exact common-denominator addition. There is no binary64 rounding here. -/
theorem add_exact (x y : Dyadic) :
    (add x y).numerator * x.denominator * y.denominator =
      (x.numerator * y.denominator + y.numerator * x.denominator) *
        (add x y).denominator := by
  have hx := scaled_denominator x (max x.scale y.scale) (Nat.le_max_left ..)
  have hy := scaled_denominator y (max x.scale y.scale) (Nat.le_max_right ..)
  simp only [denominator] at hx hy
  simp only [add, denominator, Int.add_mul]
  rw [hx]
  have rearrange :
      y.scaledNumerator (max x.scale y.scale) * (2 : Int) ^ x.scale * 2 ^ y.scale =
      y.numerator * 2 ^ (max x.scale y.scale) * 2 ^ x.scale := by
    calc
      _ = y.scaledNumerator (max x.scale y.scale) * 2 ^ y.scale * 2 ^ x.scale := by ac_rfl
      _ = _ := congrArg (· * 2 ^ x.scale) hy
  rw [rearrange]
  ac_rfl

theorem add_zero (x : Dyadic) : add x (ofInt 0) = x := by
  cases x
  simp [add, ofInt, scaledNumerator]

theorem add_comm (x y : Dyadic) : add x y = add y x := by
  simp only [add, Nat.max_comm, Int.add_comm]

theorem sub_self (x : Dyadic) : (sub x x).numerator = 0 := by
  simp [sub, add, neg, scaledNumerator]
  omega

theorem floor_ofInt (n : Int) : floor (ofInt n) = n := by
  simp [floor, ofInt, denominator]

theorem normalize_equivalent (x : Dyadic) : equivalent (normalize x) x := by
  obtain ⟨n, k⟩ := x
  induction k generalizing n with
  | zero => simp [normalize, equivalent, denominator]
  | succ k ih =>
    simp only [normalize]
    split
    · rename_i even
      have he : n % 2 = 0 := by simpa using even
      have hn : n / 2 * 2 = n := by omega
      have prev := ih (n / 2)
      simp only [equivalent, denominator] at prev ⊢
      rw [Int.pow_succ]
      calc
        _ = ((normalize ⟨n / 2, k⟩).numerator * 2 ^ k) * 2 := by ac_rfl
        _ = (n / 2 * (2 : Int) ^ (normalize ⟨n / 2, k⟩).scale) * 2 := by rw [prev]
        _ = (n / 2 * 2) * (2 : Int) ^ (normalize ⟨n / 2, k⟩).scale := by ac_rfl
        _ = _ := by rw [hn]
    · rfl

def Normalized (x : Dyadic) : Prop := x.scale = 0 ∨ x.numerator % 2 ≠ 0

theorem normalize_normalized (x : Dyadic) : Normalized x.normalize := by
  obtain ⟨n, k⟩ := x
  induction k generalizing n with
  | zero => simp [normalize, Normalized]
  | succ k ih =>
    simp only [normalize]
    split
    · exact ih _
    · simp_all [Normalized]

theorem equivalent_scaled {x y : Dyadic} (equiv : equivalent x y)
    (scales : x.scale ≤ y.scale) : x.scaledNumerator y.scale = y.numerator := by
  apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (denominator_pos x))
  rw [scaled_denominator x y.scale scales]
  exact equiv

theorem larger_scaled_even (x : Dyadic) (k : Nat) (larger : x.scale < k) :
    x.scaledNumerator k % 2 = 0 := by
  have difference : k-x.scale = (k-x.scale-1)+1 := by omega
  rw [scaledNumerator, difference, Int.pow_succ]
  rw [← Int.mul_assoc]
  simp

theorem normalized_unique {x y : Dyadic} (hx : Normalized x) (hy : Normalized y)
    (equiv : equivalent x y) : x = y := by
  have scales : x.scale = y.scale := by
    by_cases same : x.scale = y.scale
    · exact same
    · cases Nat.lt_or_gt_of_ne same with
      | inl less =>
        have odd := hy.resolve_left (by omega)
        have even := larger_scaled_even x y.scale less
        rw [equivalent_scaled equiv (Nat.le_of_lt less)] at even
        contradiction
      | inr more =>
        have odd := hx.resolve_left (by omega)
        have even := larger_scaled_even y x.scale more
        rw [equivalent_scaled (equivalent_symm equiv) (Nat.le_of_lt more)] at even
        contradiction
  have numerators := equivalent_scaled equiv (Nat.le_of_eq scales)
  simp [scaledNumerator, scales] at numerators
  cases x
  cases y
  simp_all

theorem normalize_idempotent (x : Dyadic) : x.normalize.normalize = x.normalize :=
  normalized_unique (normalize_normalized _) (normalize_normalized _) (normalize_equivalent _)

theorem normalize_eq_of_equivalent {x y : Dyadic} (equiv : equivalent x y) :
    x.normalize = y.normalize :=
  normalized_unique (normalize_normalized _) (normalize_normalized _)
    (equivalent_trans (normalize_equivalent x)
      (equivalent_trans equiv (equivalent_symm (normalize_equivalent y))))

end Dyadic

def nativeDateLimit : Int := 8640000000000000
def inNativePrefix (x : Dyadic) : Bool :=
  x.numerator.natAbs ≤ nativeDateLimit.toNat * 2 ^ x.scale
def nativeBits (bits : UInt64) : Bool :=
  Number.isFinite bits && Number.lessEqual (Number.abs bits) (Number.ofInt nativeDateLimit)

/-- The constructors are exposed for proofs. Source integration must establish
Valid at each typed boundary; arbitrary raw tags are not permitted inputs. -/
inductive Timestamp where
  | native (bits : UInt64)
  | extended (value : Dyadic)
  deriving Repr, DecidableEq

namespace Timestamp

def exact : Timestamp → Dyadic
  | .native bits => Dyadic.ofFiniteBits bits
  | .extended value => value

def Valid : Timestamp → Prop
  | .native bits => nativeBits bits = true
  | .extended value => inNativePrefix value = false

/-- Entering the finite prefix rounds once. Outside it there is no new time
quantum. This operation does not prove the pending packing/range invariant. -/
def ofDyadic (value : Dyadic) : Timestamp :=
  if inNativePrefix value then .native value.toBits else .extended value

def ofInt (value : Int) : Timestamp := ofDyadic (Dyadic.ofInt value)

/-- The environment clock may have a rational phase; Date.now exposes its
integer millisecond floor without passing an unbounded integer through Number. -/
def now (epochMilliseconds : Int) (elapsedMilliseconds : Rat) : Timestamp :=
  ofInt (epochMilliseconds + elapsedMilliseconds.floor)

def ofNative (bits : UInt64) : Option Timestamp :=
  if nativeBits bits then some (.native bits) else none

def ordinaryBits : Timestamp → UInt64
  | .native bits => bits
  | .extended value => value.toBits

inductive AddResult where
  | timestamp (value : Timestamp)
  | ordinaryNonfinite (bits : UInt64)
  deriving Repr, DecidableEq

/-- The native branch is retained exactly while the exact result stays in the
native Date range. The extended branch adds the exact finite dyadic duration. -/
def addDuration (time : Timestamp) (duration : UInt64) : AddResult :=
  if Number.isFinite duration then
    let exactResult := time.exact.add (Dyadic.ofFiniteBits duration)
    let result := match time with
      | .native bits =>
        if inNativePrefix exactResult then .native (Number.add bits duration)
        else .extended exactResult
      | .extended _ => ofDyadic exactResult
    .timestamp result
  else .ordinaryNonfinite (Number.canonical duration)

def subtractDuration (time : Timestamp) (duration : UInt64) : AddResult :=
  addDuration time (Number.neg duration)

def difference (left right : Timestamp) : UInt64 :=
  match left, right with
  | .native a, .native b => Number.sub a b
  | _, _ => (left.exact.sub right.exact).toBits

def less (left right : Timestamp) : Bool := left.exact.less right.exact
def lessEqual (left right : Timestamp) : Bool := left.exact.lessEqual right.exact

def floor : Timestamp → Timestamp
  | .native bits => .native (Number.floor bits)
  | .extended value => ofInt value.floor
def trunc : Timestamp → Timestamp
  | .native bits => .native (Number.trunc bits)
  | .extended value => ofInt value.trunc

theorem ofNative_valid {bits : UInt64} {time : Timestamp}
    (h : ofNative bits = some time) : time.Valid := by
  simp only [ofNative] at h
  split at h
  · obtain rfl := Option.some.inj h
    assumption
  · contradiction

theorem add_finite_prefix (bits duration : UInt64)
    (finite : Number.isFinite duration = true)
    (inside : inNativePrefix ((Dyadic.ofFiniteBits bits).add
      (Dyadic.ofFiniteBits duration)) = true) :
    addDuration (.native bits) duration = .timestamp (.native (Number.add bits duration)) := by
  simp [addDuration, exact, finite, inside]

theorem add_extended_exact (value : Dyadic) (duration : UInt64)
    (finite : Number.isFinite duration = true)
    (outside : inNativePrefix (value.add (Dyadic.ofFiniteBits duration)) = false) :
    addDuration (.extended value) duration =
      .timestamp (.extended (value.add (Dyadic.ofFiniteBits duration))) := by
  simp [addDuration, exact, ofDyadic, finite, outside]

theorem difference_finite_prefix (a b : UInt64) :
    difference (.native a) (.native b) = Number.sub a b := rfl

theorem difference_extended (a b : Dyadic) :
    difference (.extended a) (.extended b) = (a.sub b).toBits := rfl

theorem floor_finite_prefix (bits : UInt64) :
    floor (.native bits) = .native (Number.floor bits) := rfl

/-- Every positive integral extended timestamp advances when one millisecond
is added. The stored dyadic need not have its factors of two canceled. -/
theorem extended_integer_successor (n : Int) (outside : nativeDateLimit < n) :
    addDuration (.extended ⟨n, 0⟩) Number.one =
      .timestamp (.extended ⟨(n+1)*2^52, 52⟩) := by
  have finite : Number.isFinite Number.one = true := by decide +kernel
  have unit : Dyadic.ofFiniteBits Number.one = ⟨2^52, 52⟩ := by decide +kernel
  have beyond : inNativePrefix (Dyadic.add ⟨n, 0⟩ ⟨2^52, 52⟩) = false := by
    simp [inNativePrefix, Dyadic.add, Dyadic.scaledNumerator, nativeDateLimit] at *
    omega
  rw [add_extended_exact ⟨n, 0⟩ Number.one finite (by simpa [unit] using beyond)]
  simp [unit, Dyadic.add, Dyadic.scaledNumerator, Int.add_mul]

theorem extended_integer_successor_strict (n : Int) :
    Dyadic.less ⟨n, 0⟩ ⟨(n+1)*2^52, 52⟩ = true := by
  simp [Dyadic.less, Dyadic.denominator]
  omega

end Timestamp

/-- Calendar-derived years and intermediate Easter arithmetic are not ordinary
cookie/counter Numbers and are not absolute timestamp values. -/
structure CalendarInteger where
  value : Int
  deriving Repr, DecidableEq

def calendarYear (time : Timestamp) : CalendarInteger :=
  ⟨(Calendar.fields time.exact.trunc).year⟩

namespace Codec

/-- Exact decimal significand / 10^fractionDigits. -/
structure Decimal where
  significand : Int
  fractionDigits : Nat
  deriving Repr, DecidableEq

def exactDecimal (x : Dyadic) : Decimal :=
  ⟨x.numerator * 5 ^ x.scale, x.scale⟩

def decimalDyadic (x : Decimal) : Option Dyadic :=
  if x.significand % 5 ^ x.fractionDigits == 0 then
    some ⟨x.significand / 5 ^ x.fractionDigits, x.fractionDigits⟩
  else none

theorem exact_decimal_value (x : Dyadic) :
    (exactDecimal x).significand * 2 ^ x.scale = x.numerator * 10 ^ x.scale := by
  simp only [exactDecimal, Int.mul_assoc, ← Int.mul_pow]
  rfl

/-- Universal arithmetic inverse, before character rendering/parsing. -/
theorem decimalDyadic_exactDecimal (x : Dyadic) :
    decimalDyadic (exactDecimal x) = some x := by
  obtain ⟨n, k⟩ := x
  have positive : (0 : Int) < 5 ^ k := Int.pow_pos (by decide)
  simp [decimalDyadic, exactDecimal, Int.mul_ediv_cancel,
    Int.ne_of_gt positive]

def renderDecimal (x : Decimal) : String :=
  let sign := if x.significand < 0 then "-" else ""
  let magnitude := x.significand.natAbs
  if x.fractionDigits == 0 then sign ++ magnitude.repr
  else
    let divisor := 10 ^ x.fractionDigits
    let fraction := (magnitude % divisor).repr
    sign ++ (magnitude / divisor).repr ++ "." ++
      String.ofList (List.replicate (x.fractionDigits - fraction.length) '0') ++ fraction

def renderExtended (x : Dyadic) : JSString :=
  JSString.ofString (renderDecimal (exactDecimal x.normalize))

/-- Extended timestamp strings depend on the exact value, not the sequence of
dyadic denominator choices used to reach it. This also applies to RNG seed text. -/
theorem renderExtended_eq_of_equivalent {x y : Dyadic} (equiv : x.equivalent y) :
    renderExtended x = renderExtended y := by
  simp only [renderExtended, Dyadic.normalize_eq_of_equivalent equiv]

def render : Timestamp → Option JSString
  | .native bits => NumberString.toDecimal bits
  | .extended x => some (renderExtended x)

/-- A strict decimal-field reader for current saves. It does not replace the
permissive JavaScript parsers on arbitrary strings. -/
def parseDecimal (input : JSString) : Option Decimal := do
  let (negative, _, unsigned) := NumberString.takeSign input
  let parsed ← NumberString.decimalPrefix unsigned
  if !parsed.rest.isEmpty then none
  else
    let signed : Int := if negative then -(parsed.mantissa : Int) else parsed.mantissa
    if parsed.exponent ≥ 0 then some ⟨signed * 10 ^ parsed.exponent.toNat, 0⟩
    else some ⟨signed, (-parsed.exponent).toNat⟩

inductive ReadError where
  | invalidDecimal
  | nonDyadicOutsideNativePrefix
  deriving Repr, DecidableEq

/-- Finite fields retain the existing native decimal conversion. An extended
current-save field must denote an exact dyadic, as the corresponding writer does. -/
def readFloat (input : JSString) : Except ReadError Timestamp := do
  let some decimal := parseDecimal input | throw .invalidDecimal
  let bits := NumberString.parseFloat input
  if decimal.significand.natAbs ≤ nativeDateLimit.toNat * 10 ^ decimal.fractionDigits then
    return .native bits
  let some dyadic := decimalDyadic decimal | throw .nonDyadicOutsideNativePrefix
  return Timestamp.ofDyadic dyadic

def renderInteger (value : Int) : String := value.repr
def readInteger (input : String) : Option Timestamp :=
  input.toInt?.map Timestamp.ofInt

theorem integer_text_roundtrip (value : Int) :
    readInteger (renderInteger value) = some (Timestamp.ofInt value) := by
  simp [readInteger, renderInteger]

/-- The lump writer deliberately floors before saving; it is not an identity
codec on fractional lump timestamps. -/
def renderFloored (time : Timestamp) : String := renderInteger time.exact.floor

theorem floored_text_roundtrip (time : Timestamp) :
    readInteger (renderFloored time) = some (Timestamp.ofInt time.exact.floor) :=
  integer_text_roundtrip _

end Codec

theorem extended_clock_does_not_stagnate :
    Timestamp.addDuration (.extended ⟨2^100, 0⟩) Number.one =
      .timestamp (.extended ⟨(2^100+1)*2^52, 52⟩) := by decide +kernel

theorem extended_fraction_is_retained :
    Timestamp.addDuration (.extended ⟨2^100, 0⟩) 4591870180066957722 =
      .timestamp (.extended ⟨(2^100)*2^56+7205759403792794, 56⟩) := by decide +kernel

theorem decimal_fraction_roundtrip :
    Codec.readFloat (Codec.renderExtended ⟨(2^100)*8+3, 3⟩) =
      .ok (.extended ⟨(2^100)*8+3, 3⟩) := by
  have h : (Codec.readFloat (Codec.renderExtended ⟨(2^100)*8+3, 3⟩)).toOption =
      some (.extended ⟨(2^100)*8+3, 3⟩) := by decide +kernel
  cases he : Codec.readFloat (Codec.renderExtended ⟨(2^100)*8+3, 3⟩) <;>
    simp only [he, Except.toOption] at h <;> simp_all

theorem negative_decimal_fraction_roundtrip :
    Codec.readFloat (Codec.renderExtended ⟨-((2^100)*8+3), 3⟩) =
      .ok (.extended ⟨-((2^100)*8+3), 3⟩) := by
  have h : (Codec.readFloat (Codec.renderExtended ⟨-((2^100)*8+3), 3⟩)).toOption =
      some (.extended ⟨-((2^100)*8+3), 3⟩) := by decide +kernel
  cases he : Codec.readFloat (Codec.renderExtended ⟨-((2^100)*8+3), 3⟩) <;>
    simp only [he, Except.toOption] at h <;> simp_all

theorem boundary_fraction_stays_extended :
    Codec.readFloat (JSString.ofString "8640000000000000.125") =
      .ok (.extended ⟨69120000000000001, 3⟩) := by
  have h : (Codec.readFloat (JSString.ofString "8640000000000000.125")).toOption =
      some (.extended ⟨69120000000000001, 3⟩) := by decide +kernel
  cases he : Codec.readFloat (JSString.ofString "8640000000000000.125") <;>
    simp only [he, Except.toOption] at h <;> simp_all

theorem ordinary_nonfinite_duration_remains_nonfinite :
    Timestamp.addDuration (.extended ⟨2^100, 0⟩) Number.positiveInfinity =
      .ordinaryNonfinite Number.positiveInfinity := by decide +kernel

end CookieClicker.JavaScript.ClockValue

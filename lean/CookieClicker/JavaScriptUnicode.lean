import CookieClicker.JavaScriptSyntax
import CookieClicker.JavaScriptUnicodeData

/-! Unicode 13 data operations for the installed engine's strings and regexes.
UTF-16 indexing is separate from code-point iteration. Unpaired surrogates are
retained. Default casing includes contextual final sigma; locale-specific casing
requires a separate operation. These definitions do not assume native ICU calls.
-/
namespace CookieClicker.JavaScript.Unicode

def highSurrogate (n : Nat) : Bool := 0xd800 ≤ n && n ≤ 0xdbff
def lowSurrogate (n : Nat) : Bool := 0xdc00 ≤ n && n ≤ 0xdfff

def fromUtf16 : JSString → List Nat
  | [] => []
  | [unit] => [unit.toNat]
  | a :: b :: rest =>
    if highSurrogate a.toNat && lowSurrogate b.toNat then
      (0x10000 + (a.toNat - 0xd800) * 1024 + (b.toNat - 0xdc00)) :: fromUtf16 rest
    else a.toNat :: fromUtf16 (b :: rest)

def encodePoint (n : Nat) : JSString :=
  if n ≤ 0xffff then [UInt16.ofNat n]
  else if n ≤ 0x10ffff then
    [UInt16.ofNat (0xd800 + (n - 0x10000) / 1024), UInt16.ofNat (0xdc00 + (n - 0x10000) % 1024)]
  else [0xfffd]

def toUtf16 (points : List Nat) : JSString := points.flatMap encodePoint

def findRange (ranges : Array (Nat × Nat)) (point : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, low, high =>
    if low ≥ high then false
    else
      let mid := (low + high) / 2
      match ranges[mid]? with
      | none => false
      | some (first, last) =>
        if point < first then findRange ranges point fuel low mid
        else if point > last then findRange ranges point fuel (mid + 1) high
        else true

def contains (ranges : Array (Nat × Nat)) (point : Nat) : Bool :=
  findRange ranges point (ranges.size + 1) 0 ranges.size

def isLetter (point : Nat) : Bool := contains Data.letterRanges point
def isCased (point : Nat) : Bool := contains Data.casedRanges point
def isCaseIgnorable (point : Nat) : Bool := contains Data.caseIgnorableRanges point

def findMapping (mappings : Array (Nat × List Nat)) (point : Nat) :
    Nat → Nat → Nat → Option (List Nat)
  | 0, _, _ => none
  | fuel + 1, low, high =>
    if low ≥ high then none
    else
      let mid := (low + high) / 2
      match mappings[mid]? with
      | none => none
      | some (key, value) =>
        if point < key then findMapping mappings point fuel low mid
        else if point > key then findMapping mappings point fuel (mid + 1) high
        else some value

def mapping (mappings : Array (Nat × List Nat)) (point : Nat) : List Nat :=
  (findMapping mappings point (mappings.size + 1) 0 mappings.size).getD [point]

def simpleFold (point : Nat) : Nat := (mapping Data.foldMappings point).headD point

def upper (text : JSString) : JSString :=
  toUtf16 ((fromUtf16 text).flatMap (mapping Data.upperMappings))

def lowerPoints : Bool → List Nat → List Nat
  | _, [] => []
  | beforeCased, point :: rest =>
    let afterCased := ((rest.dropWhile isCaseIgnorable).head?).any isCased
    let mapped := if point == 0x03a3 && beforeCased && !afterCased then [0x03c2]
      else mapping Data.lowerMappings point
    let nextBefore := if isCaseIgnorable point then beforeCased else isCased point
    mapped ++ lowerPoints nextBefore rest

def lower (text : JSString) : JSString := toUtf16 (lowerPoints false (fromUtf16 text))

def legacyCanonicalize (unit : UInt16) : UInt16 :=
  match upper [unit] with
  | [converted] => if unit.toNat ≥ 128 && converted.toNat < 128 then unit else converted
  | _ => unit

theorem supplementary_roundtrip : fromUtf16 (toUtf16 [0x1f600]) = [0x1f600] := by decide +kernel
theorem unpaired_surrogate_retained : fromUtf16 [0xd800, 65] = [0xd800, 65] := by decide +kernel

end CookieClicker.JavaScript.Unicode

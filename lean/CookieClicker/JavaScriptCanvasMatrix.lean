import CookieClicker.JavaScriptNumber

/-! Pinned Chromium87 AffineTransform and Canvas numeric transform operations.
Arithmetic keeps the native binary32 input clamp and binary64 evaluation order.
Nonzero C-library rotations need a separate trigonometric implementation.
-/
namespace CookieClicker.JavaScript.CanvasMatrix

structure Matrix where
  a : UInt64 := Number.one
  b : UInt64 := 0
  c : UInt64 := 0
  d : UInt64 := Number.one
  e : UInt64 := 0
  f : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

def identity : Matrix := {}
def values (m : Matrix) : List UInt64 := [m.a,m.b,m.c,m.d,m.e,m.f]
def same (m n : Matrix) : Bool := (values m |>.zip (values n)).all (fun (x,y) => Number.equal x y)
def determinant (m : Matrix) : UInt64 := Number.sub (Number.mul m.a m.d) (Number.mul m.b m.c)
def invertible (m : Matrix) : Bool := !Number.equal (determinant m) 0

def identityOrTranslation (m : Matrix) : Bool :=
  Number.equal m.a Number.one && Number.equal m.b 0 && Number.equal m.c 0 && Number.equal m.d Number.one

def clampFloat (bits : UInt64) : UInt64 :=
  let maximum := Number.ofDyadic false (2^24-1) 104
  let bits := if Number.lessThan maximum bits then maximum
    else if Number.lessThan bits (Number.neg maximum) then Number.neg maximum else bits
  let (mantissa,exponent) := Number.dyadic bits
  match Float.Model.UnpackedFloat.round Float.Model.Format.binary32
      (if Number.signBit bits then .negative else .positive) mantissa exponent with
  | .finite sign mantissa exponent _ => Number.ofDyadic (sign == .negative) mantissa exponent
  | .zero sign => if sign == .negative then Number.negativeZero else Number.positiveZero
  | .infinity sign => if sign == .negative then Number.negativeInfinity else Number.positiveInfinity
  | .notANumber => Number.nan

def translateMatrix (m : Matrix) (x y : UInt64) : Matrix :=
  if identityOrTranslation m then {m with e := Number.add m.e x, f := Number.add m.f y}
  else {m with
    e := Number.add m.e (Number.add (Number.mul x m.a) (Number.mul y m.c))
    f := Number.add m.f (Number.add (Number.mul x m.b) (Number.mul y m.d))}

def multiply (m n : Matrix) : Matrix :=
  if identityOrTranslation n then
    if Number.isZero n.e && Number.isZero n.f then m else translateMatrix m n.e n.f
  else {
    a := Number.add (Number.mul m.a n.a) (Number.mul m.c n.b)
    b := Number.add (Number.mul m.b n.a) (Number.mul m.d n.b)
    c := Number.add (Number.mul m.a n.c) (Number.mul m.c n.d)
    d := Number.add (Number.mul m.b n.c) (Number.mul m.d n.d)
    e := Number.add (Number.add (Number.mul m.a n.e) (Number.mul m.c n.f)) m.e
    f := Number.add (Number.add (Number.mul m.b n.e) (Number.mul m.d n.f)) m.f }

def retainEqual (old next : Matrix) : Matrix := if same old next then old else next

def translate (m : Matrix) (x y : UInt64) : Matrix :=
  if !invertible m || !Number.isFinite x || !Number.isFinite y then m
  else retainEqual m (translateMatrix m (clampFloat x) (clampFloat y))

def scale (m : Matrix) (x y : UInt64) : Matrix :=
  if !Number.isFinite x || !Number.isFinite y then m
  else
    let x := clampFloat x; let y := clampFloat y
    retainEqual m {m with
      a := Number.mul m.a x
      b := Number.mul m.b x
      c := Number.mul m.c y
      d := Number.mul m.d y}

def transform (m n : Matrix) : Matrix :=
  if !(values n).all Number.isFinite then m
  else retainEqual m (multiply m ⟨clampFloat n.a,clampFloat n.b,clampFloat n.c,
    clampFloat n.d,clampFloat n.e,clampFloat n.f⟩)

def setTransform (m n : Matrix) : Matrix :=
  if !(values n).all Number.isFinite then m else transform identity n

/-- Native invalid rotations are ignored; both zero signs leave the matrix
unchanged. Other rotations remain an explicit C-library modeling boundary. -/
def rotate (m : Matrix) (angle : UInt64) : Option Matrix :=
  if !Number.isFinite angle || Number.isZero angle then some m else none

theorem identity_invertible : invertible identity = true := by decide +kernel

theorem multiply_identity (m : Matrix) : multiply m identity = m := by
  have branch : identityOrTranslation identity = true := by decide +kernel
  simp only [multiply,branch,↓reduceIte]
  rfl

theorem zero_rotation (m : Matrix) : rotate m 0 = some m := by rfl

theorem singular_translation (m : Matrix) (x y : UInt64) (singular : invertible m = false) :
    translate m x y = m := by simp [translate,singular]

end CookieClicker.JavaScript.CanvasMatrix

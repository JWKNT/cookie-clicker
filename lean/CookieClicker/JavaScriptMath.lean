import CookieClicker.JavaScriptNumber

/-!
Binary64 operation-order translation of V8 8.7.220.31's `base::ieee754::pow`.
Source: https://github.com/v8/v8/blob/8.7.220.31/src/base/ieee754.cc
This is a concrete algorithm, not real exponentiation. Correspondence to the
compiled installed engine remains a proof obligation; finite comparisons are
regression evidence only.

The following is adapted from fdlibm.
Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
Developed at SunSoft, a Sun Microsystems, Inc. business.
Permission to use, copy, modify, and distribute this software is freely granted,
provided that this notice is preserved.
The original source code has been modified significantly by Google Inc.
Copyright 2016 the V8 project authors. All rights reserved.
The V8 license is retained in ../licenses/V8-LICENSE.
-/
namespace CookieClicker.JavaScript.Math

private structure F where
  bits : UInt64
  deriving Repr

private instance : Add F := ⟨fun a b => ⟨Number.add a.bits b.bits⟩⟩
private instance : Sub F := ⟨fun a b => ⟨Number.sub a.bits b.bits⟩⟩
private instance : Mul F := ⟨fun a b => ⟨Number.mul a.bits b.bits⟩⟩
private instance : Div F := ⟨fun a b => ⟨Number.div a.bits b.bits⟩⟩
private instance : Neg F := ⟨fun a => ⟨Number.neg a.bits⟩⟩
private instance (n : Nat) : OfNat F n := ⟨⟨Number.ofNat n⟩⟩
private instance : OfScientific F := ⟨fun m negative e =>
  ⟨Number.ofScientific m (if negative then -(e : Int) else e)⟩⟩
private instance : BEq F := ⟨fun a b => Number.equal a.bits b.bits⟩
private def lt (a b : F) : Bool := Number.lessThan a.bits b.bits
private def le (a b : F) : Bool := Number.lessEqual a.bits b.bits
private def b (bits : UInt64) : F := ⟨bits⟩
private def hi (x : F) : Nat := (x.bits >>> 32).toNat
private def lo (x : F) : Nat := (x.bits &&& 0xffffffff).toNat
private def cut (x : F) : F := b (x.bits &&& 0xffffffff00000000)
private def setHigh (x : F) (word : Nat) : F :=
  b ((x.bits &&& (0xffffffff : UInt64)) ||| (UInt64.ofNat word <<< (32 : UInt64)))
private def int (n : Int) : F := b (Number.ofInt n)
private def scale (x : F) (n : Int) : F :=
  let (m, e) := Number.dyadic x.bits
  b (Number.ofDyadic (Number.signBit x.bits) m (e + n))

private def powCore (x y : F) : F := Id.run do
  let hx := hi x
  let hy := hi y
  let mut ix := hx &&& 0x7fffffff
  let iy := hy &&& 0x7fffffff
  let lx := lo x
  let ly := lo y
  let negativeX := Number.signBit x.bits
  let negativeY := Number.signBit y.bits
  if Number.isZero y.bits then return 1
  if Number.isNaN x.bits || Number.isNaN y.bits then return b Number.nan
  let yInteger := if !negativeX || !Number.isInteger y.bits then 0
    else if (Number.truncateInt y.bits).natAbs % 2 == 1 then 1 else 2
  if ly == 0 then
    if iy == 0x7ff00000 then
      if ix == 0x3ff00000 && lx == 0 then return b Number.nan
      else if ix ≥ 0x3ff00000 then return if negativeY then 0 else y
      else return if negativeY then -y else 0
    if iy == 0x3ff00000 then return if negativeY then 1 / x else x
    if hy == 0x40000000 then return x * x
    if hy == 0x3fe00000 && !negativeX then return b (Number.sqrt x.bits)
  let mut ax := b (Number.abs x.bits)
  if lx == 0 && (ix == 0x7ff00000 || ix == 0 || ix == 0x3ff00000) then
    let mut z := if negativeY then 1 / ax else ax
    if negativeX then
      if ix == 0x3ff00000 && yInteger == 0 then z := b Number.nan
      else if yInteger == 1 then z := -z
    return z
  if negativeX && yInteger == 0 then return b Number.nan
  let s : F := if negativeX && yInteger == 1 then -1 else 1
  let huge : F := 1.0e300
  let tiny : F := 1.0e-300
  let ivln2 := b 0x3ff71547652b82fe
  let ivln2h := b 0x3ff7154760000000
  let ivln2l := b 0x3e54ae0bf85ddf44
  let cp := b 0x3feec709dc3a03fd
  let cph := b 0x3feec709e0000000
  let cpl := b 0xbe3e2fe0145b01f5
  let mut t1 : F := 0
  let mut t2 : F := 0
  if iy > 0x41e00000 then
    if iy > 0x43f00000 then
      if ix ≤ 0x3fefffff then return if negativeY then huge * huge else tiny * tiny
      if ix ≥ 0x3ff00000 then return if !negativeY then huge * huge else tiny * tiny
    if ix < 0x3fefffff then return if negativeY then s * huge * huge else s * tiny * tiny
    if ix > 0x3ff00000 then return if !negativeY then s * huge * huge else s * tiny * tiny
    let t := ax - 1
    let w := (t * t) * (0.5 - t * (0.3333333333333333333333 - t * 0.25))
    let u := ivln2h * t
    let v := t * ivln2l - w * ivln2
    t1 := cut (u + v)
    t2 := v - (t1 - u)
  else
    let mut n : Int := 0
    if ix < 0x00100000 then
      ax := ax * 9007199254740992
      n := n - 53
      ix := hi ax
    n := n + (ix >>> 20 : Nat) - 1023
    let j := ix &&& 0x000fffff
    ix := j ||| 0x3ff00000
    let mut k : Nat := 0
    if j ≤ 0x3988e then k := 0
    else if j < 0xbb67a then k := 1
    else
      k := 0
      n := n + 1
      ix := ix - 0x00100000
    ax := setHigh ax ix
    let bp : F := if k == 0 then 1 else 1.5
    let dph : F := if k == 0 then 0 else b 0x3fe2b80340000000
    let dpl : F := if k == 0 then 0 else b 0x3e4cfdeb43cfd006
    let u := ax - bp
    let v := 1 / (ax + bp)
    let ss := u * v
    let sh := cut ss
    let th := setHigh 0 (((ix >>> 1) ||| 0x20000000) + 0x00080000 + (k <<< 18))
    let tl := ax - (th - bp)
    let sl := v * ((u - sh * th) - sh * tl)
    let s2 := ss * ss
    let l1 := b 0x3fe3333333333303
    let l2 := b 0x3fdb6db6db6fabff
    let l3 := b 0x3fd55555518f264d
    let l4 := b 0x3fd17460a91d4101
    let l5 := b 0x3fcd864a93c9db65
    let l6 := b 0x3fca7e284a454eef
    let r := s2 * s2 * (l1 + s2 * (l2 + s2 * (l3 + s2 * (l4 + s2 * (l5 + s2 * l6)))))
    let r := r + sl * (sh + ss)
    let s2 := sh * sh
    let th := cut (3 + s2 + r)
    let tl := r - ((th - 3) - s2)
    let u := sh * th
    let v := sl * th + tl * ss
    let ph := cut (u + v)
    let pl := v - (ph - u)
    let zh := cph * ph
    let zl := cpl * ph + pl * cp + dpl
    let t := int n
    t1 := cut (((zh + zl) + dph) + t)
    t2 := zl - (((t1 - t) - dph) - zh)
  let y1 := cut y
  let pl := (y - y1) * t1 + y * t2
  let mut ph := y1 * t1
  let z := pl + ph
  let j := hi z
  let i := lo z
  if !Number.signBit z.bits && j ≥ 0x40900000 then
    if j != 0x40900000 || i != 0 then return s * huge * huge
    if lt (z - ph) (pl + 8.0085662595372944372e-17) then return s * huge * huge
  else if (j &&& 0x7fffffff) ≥ 0x4090cc00 then
    if j != 0xc090cc00 || i != 0 then return s * tiny * tiny
    if le pl (z - ph) then return s * tiny * tiny
  let i := j &&& 0x7fffffff
  let k : Int := (i >>> 20 : Nat) - (1023 : Int)
  let mut n : Int := 0
  if i > 0x3fe00000 then
    let nh := j + (0x00100000 >>> (k + 1).toNat)
    let k := ((nh &&& 0x7fffffff) >>> 20) - 1023
    let mask := 0xffffffff - (0x000fffff >>> k)
    let t := setHigh 0 (nh &&& mask)
    let magnitude := ((nh &&& 0x000fffff) ||| 0x00100000) >>> (20 - k)
    n := if Number.signBit z.bits then -(magnitude : Int) else magnitude
    ph := ph - t
  let t := cut (pl + ph)
  let lg2 := b 0x3fe62e42fefa39ef
  let lg2h := b 0x3fe62e4300000000
  let lg2l := b 0xbe205c610ca86c39
  let u := t * lg2h
  let v := (pl - (t - ph)) * lg2 + t * lg2l
  let z := u + v
  let w := v - (z - u)
  let t := z * z
  let p1 := b 0x3fc555555555553e
  let p2 := b 0xbf66c16c16bebd93
  let p3 := b 0x3f11566aaf25de2c
  let p4 := b 0xbebbbd41c5d26bf1
  let p5 := b 0x3e66376972bea4d0
  let finalPolynomial := z - t * (p1 + t * (p2 + t * (p3 + t * (p4 + t * p5))))
  let r := (z * finalPolynomial) / ((finalPolynomial - 2) - (w + z * w))
  let z := 1 - (r - z)
  return s * scale z n

def pow (x y : UInt64) : UInt64 := (powCore (b x) (b y)).bits

private def logCore (input : F) : F := Id.run do
  if Number.isZero input.bits then return b Number.negativeInfinity
  if Number.signBit input.bits then return b Number.nan
  if !Number.isFinite input.bits then return input + input
  let ln2hi := b 0x3fe62e42fee00000
  let ln2lo := b 0x3dea39ef35793c76
  let mut x := input
  let mut hx := hi x
  let mut k : Int := 0
  if hx < 0x00100000 then
    k := k - 54
    x := x * 18014398509481984
    hx := hi x
  k := k + (hx >>> 20 : Nat) - 1023
  hx := hx &&& 0x000fffff
  let i := (hx + 0x95f64) &&& 0x100000
  x := setHigh x (hx ||| (i ^^^ 0x3ff00000))
  k := k + (i >>> 20 : Nat)
  let f := x - 1
  let dk := int k
  if (0x000fffff &&& (2 + hx)) < 3 then
    if f == 0 then
      return if k == 0 then 0 else dk * ln2hi + dk * ln2lo
    let r := f * f * (0.5 - 0.33333333333333333 * f)
    return if k == 0 then f - r else dk * ln2hi - ((r - dk * ln2lo) - f)
  let s := f / (2 + f)
  let z := s * s
  let w := z * z
  let lg1 := b 0x3fe5555555555593
  let lg2 := b 0x3fd999999997fa04
  let lg3 := b 0x3fd2492494229359
  let lg4 := b 0x3fcc71c51d8e78af
  let lg5 := b 0x3fc7466496cb03de
  let lg6 := b 0x3fc39a09d078c69f
  let lg7 := b 0x3fc2f112df3e5244
  let t1 := w * (lg2 + w * (lg4 + w * lg6))
  let t2 := z * (lg1 + w * (lg3 + w * (lg5 + w * lg7)))
  let r := t2 + t1
  if 0x6147a ≤ hx && hx ≤ 0x6b851 then
    let hfsq := 0.5 * f * f
    return if k == 0 then f - (hfsq - s * (hfsq + r))
      else dk * ln2hi - ((hfsq - (s * (hfsq + r) + dk * ln2lo)) - f)
  else return if k == 0 then f - s * (f - r)
    else dk * ln2hi - ((s * (f - r) - dk * ln2lo) - f)

def log (x : UInt64) : UInt64 := (logCore (b x)).bits

private def atanHi : Nat → F
  | 0 => b 0x3fddac670561bb4f
  | 1 => b 0x3fe921fb54442d18
  | 2 => b 0x3fef730bd281f69b
  | _ => b 0x3ff921fb54442d18
private def atanLo : Nat → F
  | 0 => b 0x3c7a2b7f222f65e2
  | 1 => b 0x3c81a62633145c07
  | 2 => b 0x3c7007887af0cbbd
  | _ => b 0x3c91a62633145c07

private def atanCore (input : F) : F := Id.run do
  let negative := Number.signBit input.bits
  let ix := hi input &&& 0x7fffffff
  if ix ≥ 0x44100000 then
    if Number.isNaN input.bits then return input + input
    return if negative then -atanHi 3 - atanLo 3 else atanHi 3 + atanLo 3
  let mut x := input
  let mut index : Option Nat := none
  if ix < 0x3fdc0000 then
    if ix < 0x3e400000 then return x
  else
    x := b (Number.abs x.bits)
    if ix < 0x3ff30000 then
      if ix < 0x3fe60000 then
        index := some 0
        x := (2 * x - 1) / (2 + x)
      else
        index := some 1
        x := (x - 1) / (x + 1)
    else if ix < 0x40038000 then
      index := some 2
      x := (x - 1.5) / (1 + 1.5 * x)
    else
      index := some 3
      x := -1 / x
  let z := x * x
  let w := z * z
  let a0 := b 0x3fd555555555550d
  let a1 := b 0xbfc999999998ebc4
  let a2 := b 0x3fc24924920083ff
  let a3 := b 0xbfbc71c6fe231671
  let a4 := b 0x3fb745cdc54c206e
  let a5 := b 0xbfb3b0f2af749a6d
  let a6 := b 0x3fb10d66a0d03d51
  let a7 := b 0xbfadde2d52defd9a
  let a8 := b 0x3fa97b4b24760deb
  let a9 := b 0xbfa2b4442c6a6c2f
  let a10 := b 0x3f90ad3ae322da11
  let s1 := z * (a0 + w * (a2 + w * (a4 + w * (a6 + w * (a8 + w * a10)))))
  let s2 := w * (a1 + w * (a3 + w * (a5 + w * (a7 + w * a9))))
  match index with
  | none => return x - x * (s1 + s2)
  | some i =>
    let z := atanHi i - ((x * (s1 + s2) - atanLo i) - x)
    return if negative then -z else z

def atan (x : UInt64) : UInt64 := (atanCore (b x)).bits

private def atan2Core (y x : F) : F := Id.run do
  if Number.isNaN x.bits || Number.isNaN y.bits then return x + y
  if x == 1 then return atanCore y
  let negativeX := Number.signBit x.bits
  let negativeY := Number.signBit y.bits
  let pi := b 0x400921fb54442d18
  let piHalf := b 0x3ff921fb54442d18
  let piQuarter := b 0x3fe921fb54442d18
  let piLow := b 0x3ca1a62633145c07
  let tiny : F := 1.0e-300
  if Number.isZero y.bits then
    return if !negativeX then y else if negativeY then -pi - tiny else pi + tiny
  if Number.isZero x.bits then
    return if negativeY then -piHalf - tiny else piHalf + tiny
  if Number.isInfinite x.bits then
    if Number.isInfinite y.bits then
      if negativeX then return if negativeY then -3 * piQuarter - tiny else 3 * piQuarter + tiny
      else return if negativeY then -piQuarter - tiny else piQuarter + tiny
    else
      if negativeX then return if negativeY then -pi - tiny else pi + tiny
      else return if negativeY then b Number.negativeZero else 0
  if Number.isInfinite y.bits then
    return if negativeY then -piHalf - tiny else piHalf + tiny
  let ix := hi x &&& 0x7fffffff
  let iy := hi y &&& 0x7fffffff
  let k : Int := ((iy : Int) - (ix : Int)) / 1048576
  let mut useNegativeX := negativeX
  let mut z : F := 0
  if k > 60 then
    z := piHalf + 0.5 * piLow
    useNegativeX := false
  else if negativeX && k < -60 then z := 0
  else z := atanCore (b (Number.abs (y / x).bits))
  if !useNegativeX then return if negativeY then -z else z
  else return if negativeY then (z - piLow) - pi else pi - (z - piLow)

def atan2 (y x : UInt64) : UInt64 := (atan2Core (b y) (b x)).bits

private def kernelSin (x y : F) (hasTail : Bool) : F :=
  if (hi x &&& 0x7fffffff) < 0x3e400000 then x
  else
    let s1 := b 0xbfc5555555555549
    let s2 := b 0x3f8111111110f8a6
    let s3 := b 0xbf2a01a019c161d5
    let s4 := b 0x3ec71de357b1fe7d
    let s5 := b 0xbe5ae5e68a2b9ceb
    let s6 := b 0x3de5d93a5acfd57c
    let z := x * x
    let v := z * x
    let r := s2 + z * (s3 + z * (s4 + z * (s5 + z * s6)))
    if hasTail then x - ((z * (0.5 * y - v * r) - y) - v * s1)
    else x + v * (s1 + z * r)

private def kernelCos (x y : F) : F :=
  let ix := hi x &&& 0x7fffffff
  if ix < 0x3e400000 then 1
  else
    let c1 := b 0x3fa555555555554c
    let c2 := b 0xbf56c16c16c15177
    let c3 := b 0x3efa01a019cb1590
    let c4 := b 0xbe927e4f809c52ad
    let c5 := b 0x3e21ee9ebdb4b1c4
    let c6 := b 0xbda8fae9be8838d4
    let z := x * x
    let r := z * (c1 + z * (c2 + z * (c3 + z * (c4 + z * (c5 + z * c6)))))
    if ix < 0x3fd33333 then 1 - (0.5 * z - (z * r - x * y))
    else
      let qx : F := if ix > 0x3fe90000 then 0.28125 else setHigh 0 (ix - 0x00200000)
      let iz := 0.5 * z - qx
      let a := 1 - qx
      a - (iz - (z * r - x * y))

private def twoOverPi : Array Nat := #[
  0xa2f983,0x6e4e44,0x1529fc,0x2757d1,0xf534dd,0xc0db62,0x95993c,
  0x439041,0xfe5163,0xabdebb,0xc561b7,0x246e3a,0x424dd2,0xe00649,
  0x2eea09,0xd1921c,0xfe1deb,0x1cb129,0xa73ee8,0x8235f5,0x2ebb44,
  0x84e99c,0x7026b4,0x5f7e41,0x3991d6,0x398353,0x39f49c,0x845f8b,
  0xbdf928,0x3b1ff8,0x97ffde,0x05980f,0xef2f11,0x8b5a0a,0x6d1f6d,
  0x367ecf,0x27cb09,0xb74f46,0x3f669e,0x5fea2d,0x7527ba,0xc7ebe5,
  0xf17b3d,0x0739f7,0x8a5292,0xea6bfb,0x5fb11f,0x8d5d08,0x560330,
  0x46fc7b,0x6babf0,0xcfbc20,0x9af436,0x1da9e3,0x91615e,0xe61b08,
  0x659985,0x5f14a0,0x68408d,0xffd880,0x4d7327,0x310606,0x1556ca,
  0x73a8c9,0x60e27b,0xc08c6b]

private def piChunks : Array F := #[
  b 0x3ff921fb40000000,b 0x3e74442d00000000,b 0x3cf8469880000000,
  b 0x3b78cc5160000000,b 0x39f01b8380000000,b 0x387a252040000000,
  b 0x36e3822280000000,b 0x3569f31d00000000]

private def convolution (x : Array F) (jv i : Nat) : Option F := do
  let mut sum : F := 0
  for j in List.range x.size do
    let coefficientIndex : Int := (jv : Int) + i - j
    let coefficient ← if coefficientIndex < 0 then pure 0 else do
      let digit ← twoOverPi[coefficientIndex.toNat]?
      pure (b (Number.ofNat digit))
    sum := sum + (← x[j]?) * coefficient
  return sum

/-- One precision-two fdlibm reduction pass. Array bounds are explicit: a source
array overflow or exhausted constant table is unresolved, never filled by a
guessed mathematical remainder. -/
private def largePass (x : Array F) (jv : Nat) (initialQ0 : Int)
    (initialQ : Array F) (initialJz : Nat) :
    Option (Sum (Array F × Nat) (Int × F × F)) := do
  let mut q := initialQ
  let mut jz := initialJz
  if jz ≥ 20 then none else do
    let mut iq : Array Nat := Array.replicate 20 0
    let mut z ← q[jz]?
    for i in List.range jz do
      let fw := int (Number.truncateInt ((b 0x3e70000000000000) * z).bits)
      iq := iq.set! i (Number.truncateInt (z - 16777216 * fw).bits).toNat
      z := (← q[jz - i - 1]?) + fw
    let mut q0 := initialQ0
    z := scale z q0
    z := z - 8 * b (Number.floor (z * 0.125).bits)
    let mut n := Number.truncateInt z.bits
    z := z - int n
    let mut ih : Nat := 0
    if q0 > 0 then
      let digit ← iq[jz - 1]?
      let i := digit >>> (24 - q0).toNat
      n := n + i
      let digit := digit - (i <<< (24 - q0).toNat)
      iq := iq.set! (jz - 1) digit
      ih := digit >>> (23 - q0).toNat
    else if q0 == 0 then ih := (← iq[jz - 1]?) >>> 23
    else if le 0.5 z then ih := 2
    if ih > 0 then
      n := n + 1
      let mut carry := false
      for i in List.range jz do
        let digit ← iq[i]?
        if !carry then
          if digit != 0 then
            carry := true
            iq := iq.set! i (0x1000000 - digit)
        else iq := iq.set! i (0xffffff - digit)
      if q0 == 1 then iq := iq.set! (jz - 1) ((← iq[jz - 1]?) &&& 0x7fffff)
      else if q0 == 2 then iq := iq.set! (jz - 1) ((← iq[jz - 1]?) &&& 0x3fffff)
      if ih == 2 then
        z := 1 - z
        if carry then z := z - scale 1 q0
    if z == 0 then
      let needMore := ((List.range (jz - 4)).map (· + 4)).all (fun i => iq[i]?.getD 0 == 0)
      if needMore then
        let zeros := ((List.range 4).map (fun k => 3 - k)).takeWhile (fun i => iq[i]?.getD 0 == 0)
        let k := zeros.length + 1
        if jz + k ≥ 20 then none else do
          for offset in List.range k do
            let i := jz + 1 + offset
            q := q.set! i (← convolution x jv i)
          return .inl (q, jz + k)
      else
        if jz == 0 then none else do
          jz := jz - 1
          q0 := q0 - 24
          let zeroCount := ((List.range (jz + 1)).map (fun i => jz - i)).takeWhile
            (fun i => iq[i]?.getD 0 == 0) |>.length
          if zeroCount > jz then none else do
            jz := jz - zeroCount
            q0 := q0 - 24 * zeroCount
    else
      z := scale z (-q0)
      if le 16777216 z then
        let fw := int (Number.truncateInt ((b 0x3e70000000000000) * z).bits)
        iq := iq.set! jz (Number.truncateInt (z - 16777216 * fw).bits).toNat
        jz := jz + 1
        q0 := q0 + 24
        if jz ≥ 20 then none else
          iq := iq.set! jz (Number.truncateInt fw.bits).toNat
      else iq := iq.set! jz (Number.truncateInt z.bits).toNat
    let mut fw := scale 1 q0
    for offset in List.range (jz + 1) do
      let i := jz - offset
      q := q.set! i (fw * b (Number.ofNat (← iq[i]?)))
      fw := fw * b 0x3e70000000000000
    let mut fq : Array F := Array.replicate 20 0
    for offset in List.range (jz + 1) do
      let i := jz - offset
      let mut sum : F := 0
      for k in List.range (min 4 (jz - i) + 1) do
        sum := sum + (← piChunks[k]?) * (← q[i + k]?)
      fq := fq.set! (jz - i) sum
    let mut sum : F := 0
    for offset in List.range (jz + 1) do sum := sum + (← fq[jz - offset]?)
    let first := if ih == 0 then sum else -sum
    sum := (← fq[0]?) - sum
    for i in (List.range jz).map (· + 1) do sum := sum + (← fq[i]?)
    return .inr (n % 8, first, if ih == 0 then sum else -sum)

private def largeRepeat (x : Array F) (jv : Nat) (q0 : Int) :
    Nat → Array F → Nat → Option (Int × F × F)
  | 0, _, _ => none
  | fuel + 1, q, jz => do
    match ← largePass x jv q0 q jz with
    | .inr result => pure result
    | .inl (nextQ, nextJz) => largeRepeat x jv q0 fuel nextQ nextJz

private def largeReduction (x : F) : Option (Int × F × F) := do
  let ix := hi x &&& 0x7fffffff
  let e0 : Int := (ix >>> 20 : Nat) - (1046 : Int)
  let mut z := setHigh x ((ix : Int) - e0 * 1048576).toNat
  let mut chunks : Array F := #[]
  for _ in List.range 2 do
    let chunk := int (Number.truncateInt z.bits)
    chunks := chunks.push chunk
    z := (z - chunk) * 16777216
  chunks := chunks.push z
  let zeroCount := chunks.toList.reverse.takeWhile (fun n => n == 0) |>.length
  chunks := chunks.extract 0 (chunks.size - zeroCount)
  let jv := max 0 ((e0 - 3) / 24) |>.toNat
  let q0 := e0 - 24 * (jv + 1)
  let mut q : Array F := Array.replicate 20 0
  for i in List.range 5 do q := q.set! i (← convolution chunks jv i)
  let (n, first, second) ← largeRepeat chunks jv q0 20 q 4
  return if Number.signBit x.bits then (-n, -first, -second) else (n, first, second)

private def reduction (x : F) : Option (Int × F × F) := do
  let ix := hi x &&& 0x7fffffff
  let negative := Number.signBit x.bits
  let p1 := b 0x3ff921fb54400000
  let p1t := b 0x3dd0b4611a626331
  let p2 := b 0x3dd0b4611a600000
  let p2t := b 0x3ba3198a2e037073
  let p3 := b 0x3ba3198a2e000000
  let p3t := b 0x397b839a252049c1
  if ix ≤ 0x3fe921fb then return (0, x, 0)
  if ix < 0x4002d97c then
    if !negative then
      let z := x - p1
      let (z, tail) := if ix == 0x3ff921fb then (z - p2, p2t) else (z, p1t)
      let first := z - tail
      return (1, first, (z - first) - tail)
    else
      let z := x + p1
      let (z, tail) := if ix == 0x3ff921fb then (z + p2, p2t) else (z, p1t)
      let first := z + tail
      return (-1, first, (z - first) + tail)
  if ix > 0x413921fb then
    if !Number.isFinite x.bits then return (0, x - x, x - x)
    else largeReduction x
  else
    let t := b (Number.abs x.bits)
    let n := Number.truncateInt (t * b 0x3fe45f306dc9c883 + 0.5).bits
    let fn := int n
    let mut r := t - fn * p1
    let mut w := fn * p1t
    let mut first := r - w
    let nearMultiples : Array Nat := #[
      0x3ff921fb,0x400921fb,0x4012d97c,0x401921fb,0x401f6a7a,0x4022d97c,
      0x4025fdbb,0x402921fb,0x402c463a,0x402f6a7a,0x4031475c,0x4032d97c,
      0x40346b9c,0x4035fdbb,0x40378fdb,0x403921fb,0x403ab41b,0x403c463a,
      0x403dd85a,0x403f6a7a,0x40407e4c,0x4041475c,0x4042106c,0x4042d97c,
      0x4043a28c,0x40446b9c,0x404534ac,0x4045fdbb,0x4046c6cb,0x40478fdb,
      0x404858eb,0x404921fb]
    if !(n < 32 && ix != nearMultiples[n.toNat - 1]?.getD 0) then
      let j : Int := ix >>> 20
      if j - ((hi first >>> 20) &&& 0x7ff : Nat) > 16 then
        let t := r
        w := fn * p2
        r := t - w
        w := fn * p2t - ((t - r) - w)
        first := r - w
        if j - ((hi first >>> 20) &&& 0x7ff : Nat) > 49 then
          let t := r
          w := fn * p3
          r := t - w
          w := fn * p3t - ((t - r) - w)
          first := r - w
    let second := (r - first) - w
    return if negative then (-n, -first, -second) else (n, first, second)

def sin (bits : UInt64) : Option UInt64 := do
  let x := b bits
  if (hi x &&& 0x7fffffff) ≤ 0x3fe921fb then return (kernelSin x 0 false).bits
  if !Number.isFinite bits then return Number.nan
  let (n, first, second) ← reduction x
  return (match n % 4 with
    | 0 => kernelSin first second true
    | 1 => kernelCos first second
    | 2 => -kernelSin first second true
    | _ => -kernelCos first second).bits

def cos (bits : UInt64) : Option UInt64 := do
  let x := b bits
  if (hi x &&& 0x7fffffff) ≤ 0x3fe921fb then return (kernelCos x 0).bits
  if !Number.isFinite bits then return Number.nan
  let (n, first, second) ← reduction x
  return (match n % 4 with
    | 0 => kernelCos first second
    | 1 => -kernelSin first second true
    | 2 => -kernelCos first second
    | _ => kernelSin first second true).bits

theorem pow_nan_zero : pow Number.nan Number.positiveZero = Number.one := by decide +kernel
theorem pow_negative_half : Number.isNaN (pow (Number.ofInt (-2)) (Number.ofScientific 5 (-1))) = true := by decide +kernel
theorem pow_square : pow (Number.ofNat 3) (Number.ofNat 2) = Number.ofNat 9 := by decide +kernel
theorem log_one : log Number.one = Number.positiveZero := by decide +kernel
theorem log_negative_zero : log Number.negativeZero = Number.negativeInfinity := by decide +kernel

end CookieClicker.JavaScript.Math

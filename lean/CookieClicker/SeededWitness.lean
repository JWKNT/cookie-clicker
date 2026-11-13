import CookieClicker.UniformRandom

/-! Executable short-ASCII-seed projection of the pinned seedrandom algorithm.
The KSA, 256-byte discard, and random-output normalization are evaluated by the
kernel for one native seed. Checked normalization fails instead of silently
rounding an odd numerator or assuming arbitrary-loop termination. This is not
a proof of all JavaScript or every seedrandom input path.
-/
namespace CookieClicker.FullGame.SeededWitness

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

structure State where
  bytes : Array Nat
  i : Nat := 0
  j : Nat := 0
  deriving DecidableEq

def swap (bytes : Array Nat) (i j : Nat) : Array Nat :=
  let a := bytes[i]!
  let b := bytes[j]!
  (bytes.set! i b).set! j a

def nextByte (s : State) : Nat × State :=
  let i := (s.i + 1) % 256
  let a := s.bytes[i]!
  let j := (s.j + a) % 256
  let b := s.bytes[j]!
  let bytes := swap s.bytes i j
  (bytes[(a + b) % 256]!, { bytes, i, j })

def readBytes : Nat → State → Nat × State
  | 0, s => (0, s)
  | n + 1, s =>
    let (accum, state) := readBytes n s
    let (byte, after) := nextByte state
    (accum * 256 + byte, after)

def discard : Nat → State → State
  | 0, s => s
  | n + 1, s => discard n (nextByte s).2

/-- For this short ASCII path, each mixkey slot is initially absent. Its bitwise
contribution is zero and the stored byte is the character code. The native
flatten/mixkey correspondence is source-audited separately for the concrete seed.
-/
def shortAsciiKey (seed : String) : Array Nat :=
  seed.toList.toArray.map (fun c => c.toNat % 256)

def schedule (key : Array Nat) : State :=
  let key := if key.isEmpty then #[0] else key
  let initial : State := { bytes := (List.range 256).toArray }
  let shuffled := (List.range 256).foldl (fun s i =>
    let j := (s.j + key[i % key.size]! + s.bytes[i]!) % 256
    { s with bytes := swap s.bytes i j, j }) initial
  discard 256 { shuffled with i := 0, j := 0 }

def seedState (seed : String) : State := schedule (shortAsciiKey seed)

/-- Shift excess significant bits exactly; an odd numerator is rejected. -/
def shrink : Nat → Nat → Nat → Nat → Option Rat
  | 0, _, _, _ => none
  | fuel + 1, numerator, denominator, extra =>
    if numerator < 2 ^ 53 then some (((numerator + extra : Nat) : Rat) / (denominator : Rat))
    else if numerator % 2 = 0 ∧ denominator % 2 = 0 then
      shrink fuel (numerator / 2) (denominator / 2) (extra / 2)
    else none

/-- Supply enough significant bits. Fuel is an explicit checked bound for this
finite witness, not a statement that every generator run takes this many steps.
-/
def fill : Nat → Nat → Nat → Nat → State → Option (Rat × State)
  | 0, _, _, _, _ => none
  | fuel + 1, numerator, denominator, extra, state =>
    if numerator < 2 ^ 52 then
      let (byte, after) := nextByte state
      fill fuel ((numerator + extra) * 256) (denominator * 256) byte after
    else (shrink 16 numerator denominator extra).map (fun value => (value, state))

def random (state : State) : Option (Rat × State) :=
  let (numerator, after) := readBytes 6 state
  fill 16 numerator (256 ^ 6) 0 after

def randoms : Nat → State → Option (List Rat)
  | 0, _ => some []
  | n + 1, state => do
    let (value, after) ← random state
    let tail ← randoms n after
    pure (value :: tail)

def helperDraws : Option (List Rat) := randoms 3 (seedState "aaaao 1 0")

/-- Exact outputs of the translated generator, proved by kernel reduction. -/
theorem helper_draws_exact : helperDraws = some
    [7103933198431415 / 18014398509481984,
     6524103155113467 / 9007199254740992,
     8931643759593147 / 9007199254740992] := by
  decide +kernel

theorem helper_third_draw_above_nineteen_twentieths :
    (19 / 20 : Rat) < 8931643759593147 / 9007199254740992 ∧
    (8931643759593147 / 9007199254740992 : Rat) < 1 := by
  decide +kernel

/-- Exact-rational choose(list) selects the last element for every audited
Grandma artwork list length. Binary64 multiplication is checked independently.
-/
theorem helper_selects_last (length : Nat) (low : 2 ≤ length) (high : length ≤ 20) :
    8931643759593147 * length / 9007199254740992 = length - 1 := by
  omega

end CookieClicker.FullGame.SeededWitness

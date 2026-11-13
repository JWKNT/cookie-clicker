import CookieClicker.JavaScriptNumber
/-! Time-lattice facts for a Number-valued wait interface.

A finite binary64 duration is an integer multiple of 2^-1074 milliseconds.
An unbounded clock that adds those durations exactly, and HTML integer timer
intervals, therefore stays on a discrete rational lattice. This does not restrict
elapsed time to whole milliseconds.

The theorem applies to the existing JSON/JavaScript action interface. It does
not identify arbitrary real-valued external timing policies with that interface,
normalize zero-time action histories, or establish full-game optimality. Native
clock arithmetic and source-to-interpreter correspondence remain separate.
-/
namespace CookieClicker.JavaScript.WaitLattice
open Number
set_option exponentiation.threshold 4096

/-- Number of minimum positive binary64 units in one millisecond. -/
def denominator : Nat := 2 ^ 1074

/-- Exact magnitude in minimum positive binary64 units; finite values are intended. -/
def ticks (bits : Bits) : Nat :=
  if exponentField bits = 0 then fraction bits
  else (2 ^ 52 + fraction bits) * 2 ^ (exponentField bits - 1)

theorem exact_cross_product (bits : Bits) :
    (magnitudeFraction bits).1 * denominator = ticks bits * (magnitudeFraction bits).2 := by
  unfold magnitudeFraction dyadic ticks
  by_cases zero : exponentField bits = 0
  · simp [zero, denominator, Nat.mul_comm]
  · have positive : 1 ≤ exponentField bits := by omega
    simp only [beq_iff_eq, zero, ↓reduceIte]
    by_cases large : 1075 ≤ exponentField bits
    · have nonnegative : (0 : Int) ≤ (exponentField bits : Int) - 1075 := by omega
      have cast : ((exponentField bits : Int) - 1075).toNat = exponentField bits - 1075 := by omega
      simp only [nonnegative, ↓reduceIte, cast, Nat.mul_one]
      unfold denominator
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      omega
    · have negative : ¬(0 : Int) ≤ (exponentField bits : Int) - 1075 := by omega
      have cast : (-((exponentField bits : Int) - 1075)).toNat = 1075 - exponentField bits := by omega
      simp only [negative, ↓reduceIte, cast]
      unfold denominator
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      omega

theorem denominator_positive : 0 < denominator := Nat.pow_pos (by decide)

theorem native_denominator_positive (bits : Bits) : 0 < (magnitudeFraction bits).2 := by
  unfold magnitudeFraction
  split
  split <;> simp [Nat.pow_pos]

def elapsed (count : Nat) : Rat := (count : Rat) / denominator

theorem exact_magnitude (bits : Bits) :
    (magnitudeFraction bits).1 / ((magnitudeFraction bits).2 : Rat) = elapsed (ticks bits) := by
  have dp := Rat.natCast_pos.mpr denominator_positive
  have np := Rat.natCast_pos.mpr (native_denominator_positive bits)
  have d0 : (denominator : Rat) ≠ 0 := by grind
  have n0 : ((magnitudeFraction bits).2 : Rat) ≠ 0 := by grind
  have cross := congrArg (fun n : Nat => (n : Rat)) (exact_cross_product bits)
  simp only [Rat.natCast_mul] at cross
  have left := Rat.div_mul_cancel (a := ((magnitudeFraction bits).1 : Rat)) n0
  have right := Rat.div_mul_cancel (a := (ticks bits : Rat)) d0
  unfold elapsed
  grind

theorem elapsed_add (a b : Nat) : elapsed (a + b) = elapsed a + elapsed b := by
  have d0 : (denominator : Rat) ≠ 0 := by
    have positive := Rat.natCast_pos.mpr denominator_positive
    grind
  have ha := Rat.div_mul_cancel (a := (a : Rat)) d0
  have hb := Rat.div_mul_cancel (a := (b : Rat)) d0
  have hab := Rat.div_mul_cancel (a := ((a+b : Nat) : Rat)) d0
  simp only [Rat.natCast_add] at hab
  unfold elapsed
  grind

theorem html_delay_is_lattice (milliseconds : Nat) :
    elapsed (milliseconds * denominator) = (milliseconds : Rat) := by
  unfold elapsed
  rw [Rat.natCast_mul]
  apply Rat.mul_div_cancel
  have positive := Rat.natCast_pos.mpr denominator_positive
  grind


theorem elapsed_le_iff (a b : Nat) : elapsed a ≤ elapsed b ↔ a ≤ b := by
  have positive := Rat.natCast_pos.mpr denominator_positive
  have d0 : (denominator : Rat) ≠ 0 := by grind
  have ha := Rat.div_mul_cancel (a := (a : Rat)) d0
  have hb := Rat.div_mul_cancel (a := (b : Rat)) d0
  unfold elapsed
  constructor
  · intro bound
    have multiplied := Rat.mul_le_mul_of_nonneg_right bound (Rat.le_of_lt positive)
    have castBound : (a : Rat) ≤ (b : Rat) := by simpa only [ha, hb] using multiplied
    exact Rat.natCast_le_natCast.mp castBound
  · intro bound
    have castBound := Rat.natCast_le_natCast.mpr bound
    apply Rat.le_of_mul_le_mul_right (c := (denominator : Rat)) _ positive
    simpa only [ha, hb] using castBound

def OnLattice (time : Rat) : Prop := ∃ n, time = elapsed n

theorem lattice_add {a b : Rat} (ha : OnLattice a) (hb : OnLattice b) : OnLattice (a + b) := by
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  exact ⟨n + m, (elapsed_add n m).symm⟩

theorem magnitude_is_lattice (bits : Bits) :
    OnLattice ((magnitudeFraction bits).1 / ((magnitudeFraction bits).2 : Rat)) :=
  ⟨ticks bits, exact_magnitude bits⟩

def acceptedWait (bits : Bits) : Option Rat :=
  if isFinite bits && (!signBit bits || isZero bits) then
    some ((magnitudeFraction bits).1 / ((magnitudeFraction bits).2 : Rat))
  else none

theorem accepted_wait_is_lattice (bits : Bits) (time : Rat)
    (accepted : acceptedWait bits = some time) : OnLattice time := by
  unfold acceptedWait at accepted
  split at accepted
  · cases accepted
    exact magnitude_is_lattice bits
  · contradiction

theorem minimum_positive_number_has_one_tick : ticks 1 = 1 := by decide +kernel

theorem bounded_horizon_ticks (n horizon : Nat) (bound : elapsed n ≤ (horizon : Rat)) :
    n < horizon * denominator + 1 := by
  rw [← html_delay_is_lattice horizon] at bound
  have := (elapsed_le_iff n (horizon * denominator)).mp bound
  omega

/-- Explicit finite set of all lattice times up to an integer-millisecond horizon. -/
def boundedTime (horizon : Nat) (index : Fin (horizon * denominator + 1)) : Rat := elapsed index.val

theorem bounded_horizon_enumeration (time : Rat) (horizon : Nat)
    (lattice : OnLattice time) (bound : time ≤ (horizon : Rat)) :
    ∃ index : Fin (horizon * denominator + 1), time = boundedTime horizon index := by
  obtain ⟨n, rfl⟩ := lattice
  exact ⟨⟨n, bounded_horizon_ticks n horizon bound⟩, rfl⟩

theorem zero_elapsed : elapsed 0 = 0 := by simp [elapsed, Rat.div_def, Rat.zero_mul]

theorem least_positive_lattice_wait (n : Nat) (positive : 0 < elapsed n) :
    elapsed 1 ≤ elapsed n := by
  apply (elapsed_le_iff 1 n).mpr
  have nonzero : n ≠ 0 := by intro equal; subst n; simp [zero_elapsed] at positive
  omega

end CookieClicker.JavaScript.WaitLattice

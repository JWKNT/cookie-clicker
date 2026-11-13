import CookieClicker.JavaScriptBuiltins

/-! Connections from the selected clock carrier to actual interpreter operations.
These statements concern operator/host dispatch, not a proof of the entire
JavaScript frontend, all source clock fields, or the full game transition model.
-/
namespace CookieClicker.JavaScript.ClockSemantics

open ClockValue

/-- Ordinary economic addition is still the existing logical binary64 addition. -/
theorem ordinary_add (a b : UInt64) :
    binary .add (.number a) (.number b) = .ok (.number (Number.add a b)) := rfl

theorem ordinary_subtract (a b : UInt64) :
    binary .subtract (.number a) (.number b) = .ok (.number (Number.sub a b)) := rfl

theorem ordinary_multiply (a b : UInt64) :
    binary .multiply (.number a) (.number b) = .ok (.number (Number.mul a b)) := rfl

theorem ordinary_divide (a b : UInt64) :
    binary .divide (.number a) (.number b) = .ok (.number (Number.div a b)) := rfl

theorem ordinary_remainder (a b : UInt64) :
    binary .remainder (.number a) (.number b) = .ok (.number (Number.remainder a b)) := rfl

/-- A native-prefix timestamp sum has the same binary64 operation as native JS
when the exact sum remains in the native prefix. -/
theorem timestamp_add_native (a b : UInt64)
    (finite : Number.isFinite b = true)
    (inside : inNativePrefix ((ClockValue.Dyadic.ofFiniteBits a).add (ClockValue.Dyadic.ofFiniteBits b)) = true) :
    binary .add (.timestamp (.native a)) (.number b) =
      .ok (.timestamp (.native (Number.add a b))) := by
  change Except.ok (timestampAddValue (Timestamp.addDuration (.native a) b)) = _
  rw [Timestamp.add_finite_prefix a b finite inside]
  rfl

theorem timestamp_difference_native (a b : UInt64) :
    binary .subtract (.timestamp (.native a)) (.timestamp (.native b)) =
      .ok (.number (Number.sub a b)) := rfl

/-- The actual interpreter addition advances every positive extended integral
clock; it cannot stagnate at a binary64 spacing threshold. -/
theorem timestamp_successor (n : Int) (outside : nativeDateLimit < n) :
    binary .add (.timestamp (.extended ⟨n,0⟩)) (.number Number.one) =
      .ok (.timestamp (.extended ⟨(n+1)*2^52,52⟩)) := by
  change Except.ok (timestampAddValue (Timestamp.addDuration (.extended ⟨n,0⟩) Number.one)) = _
  rw [Timestamp.extended_integer_successor n outside]
  rfl

theorem timestamp_successor_strict (n : Int) :
    binary .less (.timestamp (.extended ⟨n,0⟩))
      (.timestamp (.extended ⟨(n+1)*2^52,52⟩)) = .ok (.boolean true) := by
  change Except.ok (Value.boolean (ClockValue.Dyadic.less ⟨n,0⟩ ⟨(n+1)*2^52,52⟩)) = _
  rw [Timestamp.extended_integer_successor_strict]

/-- Exact subtraction occurs before the duration is projected to binary64. -/
theorem timestamp_successor_duration (n : Int) :
    binary .subtract (.timestamp (.extended ⟨(n+1)*2^52,52⟩))
      (.timestamp (.extended ⟨n,0⟩)) = .ok (.number Number.one) := by
  have difference : (ClockValue.Dyadic.mk ((n+1)*2^52) 52).sub ⟨n,0⟩ = ⟨2^52,52⟩ := by
    simp [ClockValue.Dyadic.sub, ClockValue.Dyadic.add, ClockValue.Dyadic.neg, ClockValue.Dyadic.scaledNumerator]
    congr 1
    omega
  change Except.ok (Value.number (((ClockValue.Dyadic.mk ((n+1)*2^52) 52).sub ⟨n,0⟩).toBits)) = _
  rw [difference]
  have one : (ClockValue.Dyadic.mk (2^52) 52).toBits = Number.one := by decide +kernel
  rw [one]

/-- The actual Date.now host uses the selected epoch and elapsed clock, without
a binary64 conversion of their sum. -/
theorem date_now (machine : Machine) :
    Date.dispatch machine ⟨"Date","now"⟩ .undefined [] false =
      result machine (.timestamp (Timestamp.now machine.epochMilliseconds machine.elapsed)) := rfl

/-- Exact civil-year arithmetic is separate from ordinary Number arithmetic. -/
theorem calendar_add (a b : Rat) :
    binary .add (.calendar a) (.calendar b) = .ok (.calendar (a+b)) := rfl

theorem timestamp_division_projects (a : Timestamp) (b : UInt64) :
    binary .divide (.timestamp a) (.number b) =
      .ok (.number (Number.div a.ordinaryBits b)) := by
  cases a <;> rfl

end CookieClicker.JavaScript.ClockSemantics

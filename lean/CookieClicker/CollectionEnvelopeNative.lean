import CookieClicker.CollectionEnvelope
import CookieClicker.JavaScriptDyadicArithmeticBridge

/-! Native binary64 addition preserves the collection-route counter barriers.
The premises identify exact integer-valued normal inputs. Source callbacks must
still establish their credit bounds and the integer-valued phase invariant.
This module does not infer those premises from the route catalogue audit.
-/
namespace CookieClicker.FullGame.CollectionEnvelopeNative
open Float.Model Float.Model.UnpackedFloat
open CookieClicker.JavaScript CookieClicker.JavaScript.RoundingBridge
open CookieClicker.JavaScript.DyadicArithmeticBridge
open GodzamokRounding CollectionEnvelope
set_option exponentiation.threshold 2048

def NativeCounterBound (bits : Number.Bits) (bound : Nat) : Prop :=
  Number.isFinite bits = true ∧ Number.signBit bits = false ∧
    ∃ value : Nat, Number.magnitudeFraction bits = (value,1) ∧ value ≤ bound

/-- The cross-product form includes small integers and zero, whose native
dyadic representation can have a nontrivial denominator. -/
def NativeIntegralCounterBound (bits : Number.Bits) (bound : Nat) : Prop :=
  ∃ value : Nat, RepresentsNatBits bits value ∧ value ≤ bound

theorem number_add_preserves_phase_cap (phase : EpochPhase)
    (m₁ m₂ old credit : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) old)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) credit)
    (large : 2^52 ≤ old+credit)
    (oldBound : old ≤ phaseCap phase) (creditBound : credit ≤ ordinaryCreditCap) :
    NativeCounterBound
      (Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (phaseCap phase) := by
  have sumBound : old+credit < 2^1023 := by
    cases phase <;> simp only [phaseCap, phaseExponent, ordinaryCreditCap] at * <;> omega
  obtain ⟨finite,sign,magnitude⟩ := number_add_integer_projection m₁ m₂ old credit e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
    represents₁ represents₂ large sumBound
  exact ⟨finite,sign,roundedInteger (old+credit),magnitude,
    ordinary_credit_preserves_phase_cap phase old credit oldBound creditBound⟩

theorem number_add_preserves_reset_cap
    (m₁ m₂ old earned : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) old)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) earned)
    (large : 2^52 ≤ old+earned)
    (oldBound : old ≤ resetCap) (earnedBound : earned ≤ epochEarnedCap) :
    NativeCounterBound
      (Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      resetCap := by
  have sumBound : old+earned < 2^1023 := by
    simp only [resetCap,epochEarnedCap] at *
    omega
  obtain ⟨finite,sign,magnitude⟩ := number_add_integer_projection m₁ m₂ old earned e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
    represents₁ represents₂ large sumBound
  exact ⟨finite,sign,roundedInteger (old+earned),magnitude,
    reset_step_preserves_cap old earned oldBound earnedBound⟩

theorem number_sub_preserves_phase_cap (phase : EpochPhase)
    (m₁ m₂ old debit : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) old)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) debit)
    (large : 2^52 ≤ old-debit) (oldBound : old ≤ phaseCap phase) :
    NativeCounterBound
      (Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (phaseCap phase) := by
  have differenceBound : old-debit < 2^1023 := by
    cases phase <;> simp only [phaseCap,phaseExponent] at * <;> omega
  obtain ⟨finite,sign,magnitude⟩ := number_sub_integer_projection m₁ m₂ old debit e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
    represents₁ represents₂ large differenceBound
  exact ⟨finite,sign,roundedInteger (old-debit),magnitude,
    ordinary_debit_preserves_phase_cap phase old debit oldBound⟩

theorem number_sub_preserves_phase_cap_all_results (phase : EpochPhase)
    (m₁ m₂ old debit : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (represents₁ : RepresentsNat (.finite .positive m₁ e₁ positive₁) old)
    (represents₂ : RepresentsNat (.finite .positive m₂ e₂ positive₂) debit)
    (affordable : debit ≤ old) (oldBound : old ≤ phaseCap phase) :
    NativeIntegralCounterBound
      (Number.sub (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (phaseCap phase) := by
  have differenceBound : old-debit < 2^1023 := by
    cases phase <;> simp only [phaseCap,phaseExponent] at * <;> omega
  refine ⟨roundedInteger (old-debit),?_,ordinary_debit_preserves_phase_cap phase old debit oldBound⟩
  exact number_sub_integer_represents m₁ m₂ old debit e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
    represents₁ represents₂ affordable differenceBound

end CookieClicker.FullGame.CollectionEnvelopeNative

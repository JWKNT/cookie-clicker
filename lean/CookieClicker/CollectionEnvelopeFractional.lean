import CookieClicker.CollectionEnvelopeNative
import CookieClicker.JavaScriptFractionalArithmeticBridge

/-! Actual native-addition counter barriers with fractional credits.
The source route must establish the bounds on production and each credit.
These statements cover positive normal operands and a bank of at least2^52.
-/
namespace CookieClicker.FullGame.CollectionEnvelopeFractional
open Float.Model Float.Model.UnpackedFloat
open CookieClicker.JavaScript CookieClicker.JavaScript.FractionalArithmeticBridge
open CollectionEnvelope CollectionEnvelopeNative
set_option exponentiation.threshold 2048

theorem fractional_credit_preserves_phase_cap (phase : EpochPhase)
    (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (bankBound : DyadicLE m₁ e₁ (phaseCap phase))
    (creditBound : DyadicLE m₂ e₂ ordinaryCreditCap)
    (bankLarge : DyadicGE m₁ e₁ (2^52)) :
    NativeCounterBound
      (Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      (phaseCap phase) := by
  have creditSmall : 880+53 ≤ phaseExponent phase := by cases phase <;> decide +kernel
  have capUpper : phaseExponent phase ≤ 1021 := by cases phase <;> decide +kernel
  exact number_add_dyadic_barrier m₁ m₂ (phaseExponent phase) 880 e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
    bankBound creditBound bankLarge creditSmall capUpper

theorem fractional_earnings_preserve_reset_cap
    (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (expLower₁ : -1074 ≤ e₁) (expUpper₁ : e₁ ≤ 971)
    (expLower₂ : -1074 ≤ e₂) (expUpper₂ : e₂ ≤ 971)
    (bankBound : DyadicLE m₁ e₁ resetCap)
    (creditBound : DyadicLE m₂ e₂ epochEarnedCap)
    (bankLarge : DyadicGE m₁ e₁ (2^52)) :
    NativeCounterBound
      (Number.add (Float.Model.pack (.finite .positive m₁ e₁ positive₁)).toBits
        (Float.Model.pack (.finite .positive m₂ e₂ positive₂)).toBits)
      resetCap := by
  exact number_add_dyadic_barrier m₁ m₂ 1000 940 e₁ e₂
    positive₁ positive₂ lower₁ upper₁ lower₂ upper₂ expLower₁ expUpper₁ expLower₂ expUpper₂
    bankBound creditBound bankLarge (by decide +kernel) (by decide +kernel)

end CookieClicker.FullGame.CollectionEnvelopeFractional

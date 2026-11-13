import CookieClicker.FullCompletionChecks

/-! Checked arithmetic for the source-audited first Hand-picked maturity gate.
The engine's binary64 calculation and integer-clock observation are tested in
JavaScript. This file does not prove JavaScript evaluation or RNG probabilities.
-/
namespace CookieClicker.FullGame.Pinned

/-- Best audited maturity expression, in milliseconds, interpreted over rationals. -/
def minimumHandPickedMaturity : Rat :=
  ((20 * 60 * 60 * 1000 : Rat) - 60 * 60 * 1000 - 7 * 60 * 1000) /
    (1 + (11 / 10) * (5 / 100))

theorem hand_picked_required : "Hand-picked" ∈ requirements.achievements := by
  decide +kernel

theorem completion_requires_hand_picked (s : Snapshot) (done : complete requirements s = true) :
    s.achievements "Hand-picked" = true :=
  complete_requires_achievement hand_picked_required done

theorem minimum_maturity_exact :
    minimumHandPickedMaturity = 13596000000 / 211 := by decide +kernel

theorem minimum_maturity_integer_ceiling :
    minimumHandPickedMaturity.ceil = 64436019 := by decide +kernel

/-- For this exact threshold, an eligible integer clock difference is at least this large. -/
theorem eligible_integer_clock_difference (milliseconds : Nat)
    (eligible : minimumHandPickedMaturity ≤ (milliseconds : Rat)) :
    64436019 ≤ milliseconds := by
  have ceiling : minimumHandPickedMaturity.ceil ≤ (milliseconds : Int) := Rat.ceil_le_iff.mpr eligible
  rw [minimum_maturity_integer_ceiling] at ceiling
  omega

end CookieClicker.FullGame.Pinned

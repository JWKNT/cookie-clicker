import CookieClicker.Waiting

namespace CookieClicker

/-- The paper's pairwise exchange index, evaluated at a positive current rate. -/
def exchangeIndex (rate : Rat) (i : Offer) : Rat := i.price / rate + i.price / i.gain

/-- Every greedy choice in the counterexample is strict. -/
theorem counterexample_greedy_choices :
    exchangeIndex 1 ⟨3, 1⟩ < exchangeIndex 1 ⟨5, 4⟩ ∧
    exchangeIndex 1 ⟨3, 1⟩ < exchangeIndex 1 ⟨6, 6⟩ ∧
    exchangeIndex 2 ⟨5, 4⟩ < exchangeIndex 2 ⟨6, 6⟩ := by
  decide +kernel

/-- The exact time advantage is 3/110, with no floating-point approximation. -/
theorem counterexample_gap :
    orderTime ⟨0, 1⟩ counterexampleOffers -
      (complete 3 ⟨0, 1⟩ counterexampleOffers).time = 3 / 110 := by
  decide +kernel

/-- Finishing all purchases already affordable needs no time. -/
theorem affordable_completion :
    (complete 3 ⟨14, 1⟩ counterexampleOffers).time = 0 := by
  decide +kernel

/-- A delay followed by a permanent multiplier pays only below this exact bound.
The remaining horizon includes the delay. -/
theorem achievement_break_even (horizon delay gain : Rat) (gain_nonneg : 0 ≤ gain) :
    horizon < (horizon - delay) * (1 + gain) ↔
      delay < horizon * gain / (1 + gain) := by
  have denominator_pos : (0 : Rat) < 1 + gain := by grind
  rw [Rat.lt_div_iff denominator_pos]
  have expand : (horizon - delay) * (1 + gain) =
      horizon + horizon * gain - delay * (1 + gain) := by grind
  rw [expand]
  grind

/-- Residual bank after an earliest-affordable purchase. -/
def residualBank (bank price : Rat) : Rat :=
  if price ≤ bank then bank - price else 0

/-- The remaining bank depends on the sum of prices, not their order. -/
theorem residualBank_add (bank p q : Rat) (hq : 0 ≤ q) :
    residualBank (residualBank bank p) q = residualBank bank (p + q) := by
  unfold residualBank
  split <;> split <;> (try split) <;> grind

/-- This identity supports the reference solver's use of a purchased-item subset. -/
theorem residualBank_commutes (bank p q : Rat) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    residualBank (residualBank bank p) q = residualBank (residualBank bank q) p := by
  rw [residualBank_add bank p q hq, residualBank_add bank q p hp, Rat.add_comm p q]

end CookieClicker

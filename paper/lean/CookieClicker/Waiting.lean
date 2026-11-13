import CookieClicker.Completion

namespace CookieClicker

/-- Any affordable nonnegative wait is at least the earliest affordable wait. -/
theorem waitFor_le {s : State} {amount delay : Rat}
    (rate_pos : 0 < s.rate) (delay_nonneg : 0 ≤ delay)
    (affordable : amount ≤ s.bank + s.rate * delay) :
    waitFor s amount ≤ delay := by
  unfold waitFor
  split
  · exact delay_nonneg
  · apply Rat.le_of_mul_le_mul_right (c := s.rate) _ rate_pos
    rw [Rat.div_mul_cancel (Rat.ne_of_gt rate_pos)]
    grind

/-- Earliest waiting takes nonnegative time in a positive-rate economy. -/
theorem waitFor_nonneg {s : State} {amount : Rat} (rate_pos : 0 < s.rate) :
    0 ≤ waitFor s amount := by
  unfold waitFor
  split
  · exact Rat.le_refl
  · apply Rat.le_of_mul_le_mul_right (c := s.rate) _ rate_pos
    rw [Rat.div_mul_cancel (Rat.ne_of_gt rate_pos)]
    grind

/-- The earliest wait supplies enough cookies for the purchase. -/
theorem waitFor_affordable {s : State} {amount : Rat} (rate_pos : 0 < s.rate) :
    amount ≤ s.bank + s.rate * waitFor s amount := by
  unfold waitFor
  split
  · simpa [Rat.mul_zero, Rat.add_zero] using ‹amount ≤ s.bank›
  · rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt rate_pos)]
    grind

/-- This is the residual-bank formula used by the JavaScript reference solver. -/
theorem afterBuy_bank {s : State} {i : Offer} (rate_pos : 0 < s.rate) :
    (afterBuy s i).bank = if i.price ≤ s.bank then s.bank - i.price else 0 := by
  simp only [afterBuy, waitFor]
  split
  · simp [Rat.mul_zero, Rat.add_zero]
  · rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt rate_pos)]
    grind

def delayedAfter (s : State) (i : Offer) (delay : Rat) : State :=
  ⟨s.bank + s.rate * delay - i.price, s.rate + i.gain⟩

/-- A completion with arbitrary nonnegative waits and affordable purchases. -/
inductive DelayedCompletion : State → List Offer → Rat → Prop
  | done (s) : DelayedCompletion s [] 0
  | buy {s offers i rest delay tailTime}
      (available : (i, rest) ∈ picks offers)
      (delay_nonneg : 0 ≤ delay)
      (affordable : i.price ≤ s.bank + s.rate * delay)
      (gain_nonneg : 0 ≤ i.gain)
      (continuation : DelayedCompletion (delayedAfter s i delay) rest tailTime) :
      DelayedCompletion s offers (delay + tailTime)

/-- Every earliest-affordable completion is a legal delayed completion. -/
theorem Completion.toDelayed {s : State} {offers : List Offer} {r : Result}
    (h : Completion s offers r) (rate_pos : 0 < s.rate)
    (gains : ∀ i, i ∈ offers → 0 ≤ i.gain) :
    DelayedCompletion s offers r.time := by
  induction h with
  | done s => exact DelayedCompletion.done s
  | @buy s offers i rest tail hp continuation ih =>
    obtain ⟨hi, hr⟩ := picks_members hp
    have hg := gains i hi
    have next_pos : 0 < (afterBuy s i).rate := by
      simp only [afterBuy]
      grind
    have next := ih next_pos (fun j hj => gains j (hr j hj))
    exact DelayedCompletion.buy hp (waitFor_nonneg rate_pos)
      (waitFor_affordable rate_pos) hg next

/-- Earlier purchases preserve time and bank dominance at the next purchase. -/
theorem purchase_dominance {early late : State} {e t delay : Rat} {i : Offer}
    (rate_pos : 0 < early.rate) (time_le : e ≤ t)
    (rate_eq : early.rate = late.rate)
    (bank_le : late.bank ≤ early.bank + early.rate * (t - e))
    (delay_nonneg : 0 ≤ delay)
    (affordable : i.price ≤ late.bank + late.rate * delay)
    (gain_nonneg : 0 ≤ i.gain) :
    let w := waitFor early i.price
    e + w ≤ t + delay ∧
    (afterBuy early i).rate = (delayedAfter late i delay).rate ∧
    (delayedAfter late i delay).bank ≤ (afterBuy early i).bank +
      (afterBuy early i).rate * ((t + delay) - (e + w)) := by
  have room : 0 ≤ t + delay - e := by grind
  have distribute : early.bank + early.rate * (t + delay - e) =
      early.bank + early.rate * (t - e) + late.rate * delay := by grind
  have affordable_early : i.price ≤ early.bank + early.rate * (t + delay - e) := by
    rw [distribute]
    grind
  have hw := waitFor_le rate_pos room affordable_early
  have elapsed_le : e + waitFor early i.price ≤ t + delay := by grind
  have improvement := Rat.mul_nonneg gain_nonneg
    (show 0 ≤ (t + delay) - (e + waitFor early i.price) from by grind)
  dsimp
  refine ⟨elapsed_le, ?_, ?_⟩
  · simp [afterBuy, delayedAfter, rate_eq]
  · simp only [afterBuy, delayedAfter]
    have distribute2 : early.bank + early.rate * waitFor early i.price - i.price +
        (early.rate + i.gain) * (t + delay - (e + waitFor early i.price)) =
        early.bank + early.rate * (t - e) + late.rate * delay - i.price +
        i.gain * (t + delay - (e + waitFor early i.price)) := by grind
    rw [distribute2]
    grind

/-- Moving each purchase to its first affordable time cannot delay completion. -/
theorem earliest_dominates_delayed {late : State} {offers : List Offer} {total : Rat}
    (h : DelayedCompletion late offers total) :
    ∀ early e t, 0 < early.rate → e ≤ t → early.rate = late.rate →
      late.bank ≤ early.bank + early.rate * (t - e) →
      ∃ r, Completion early offers r ∧ e + r.time ≤ t + total := by
  induction h with
  | done s =>
    intro early e t rate_pos time_le rate_eq bank_le
    refine ⟨⟨[], 0⟩, Completion.done early, ?_⟩
    simpa [Rat.add_zero] using time_le
  | @buy late offers i rest delay tailTime available delay_nonneg affordable gain_nonneg continuation ih =>
    intro early e t rate_pos time_le rate_eq bank_le
    obtain ⟨next_time, next_rate, next_bank⟩ := purchase_dominance rate_pos time_le
      rate_eq bank_le delay_nonneg affordable gain_nonneg
    have next_pos : 0 < (afterBuy early i).rate := by
      simp only [afterBuy]
      grind
    obtain ⟨r, hr, ht⟩ := ih (afterBuy early i) (e + waitFor early i.price)
      (t + delay) next_pos next_time next_rate next_bank
    refine ⟨⟨i :: r.purchases, waitFor early i.price + r.time⟩,
      Completion.buy available hr, ?_⟩
    dsimp
    grind

/-- Global minimum over all affordable orders and all nonnegative waiting times.
Each one-shot offer is required. All purchased gains are nonnegative.
-/
theorem complete_optimal_all_waits (s : State) (offers : List Offer)
    (rate_pos : 0 < s.rate) :
    Completion s offers (complete offers.length s offers) ∧
    ∀ total, DelayedCompletion s offers total →
      (complete offers.length s offers).time ≤ total := by
  refine ⟨complete_feasible _ _ _ (Nat.le_refl _), ?_⟩
  intro total h
  obtain ⟨r, hr, ht⟩ := earliest_dominates_delayed h s 0 0 rate_pos Rat.le_refl rfl
    (by simp [Rat.sub_self, Rat.mul_zero, Rat.add_zero])
  have hc := complete_le_completion offers.length (Nat.le_refl _) hr
  have : r.time ≤ total := by simpa [Rat.zero_add] using ht
  exact Rat.le_trans hc this

/-- The planner attains the minimum over all legal rational-time schedules. -/
theorem complete_global_optimal (s : State) (offers : List Offer)
    (rate_pos : 0 < s.rate) (gains : ∀ i, i ∈ offers → 0 ≤ i.gain) :
    DelayedCompletion s offers (complete offers.length s offers).time ∧
    ∀ total, DelayedCompletion s offers total →
      (complete offers.length s offers).time ≤ total := by
  obtain ⟨feasible, optimal⟩ := complete_optimal_all_waits s offers rate_pos
  exact ⟨feasible.toDelayed rate_pos gains, optimal⟩

end CookieClicker

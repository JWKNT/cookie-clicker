import CookieClicker.BootstrapArithmetic

/-! Concrete arithmetic bounds for the proposed full-game retry route.
`model/collection-envelope-witness.json` extracts the catalogue counts and hashes
the source functions used in the factor ledger. This module checks that ledger's
numerical inequalities and proves a uniform reset-counter barrier. It does not
prove the JavaScript callbacks satisfy the production or per-epoch premises.
The integer rounding projection applies after native finite counters exceed
2^53; correspondence with the JavaScript Number evaluator is still required.
-/
namespace CookieClicker.FullGame.CollectionEnvelope
open GodzamokRounding BootstrapArithmetic
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

theorem cookie_product_budget :
    (5 : Nat)^248 < 2^83 * 4^248 := by decide +kernel

theorem dirt_neighbor_budget : (6 : Nat)^8 < 8 * 5^8 := by decide +kernel

theorem dirt_effect_budgets :
    1 + (36 : Rat) * (4 / 100) * 8 < 16 ∧
    1 + (36 : Rat) * (2 / 1000) * 8 < 2 ∧
    (15 / 100 : Rat) * (6 / 5)^8 < 1 := by decide +kernel

theorem milk_and_kitten_budgets :
    (643 / 25 : Rat) < 26 ∧
    (105 / 100 : Rat) * (1055 / 1000) * (11 / 10) * 2 < 3 ∧
    (1 : Rat) + 26 * (1 / 5) * 3 < 32 ∧
    (32 : Nat)^18 = 2^90 := by decide +kernel

def ordinaryBuildingSumBound : Nat :=
  2^49 * 4^15 * 128^5 * 2 * 32 * 2 * 2 * 2048 * 32

theorem ordinary_building_sum_budget : ordinaryBuildingSumBound = 2^138 := by decide +kernel

def cursorSumBound : Rat :=
  ((1 / 10) * 8 + (1 / 10) * 5 * 10 * 20^9 * 25 * 38000) *
    128 * 2 * 16 * 2 * 2 * 2048 * 32

def grandmaSumBound : Rat :=
  (1 + 2 * 2000 * (2 / 100) + 2000 * (5 / 100)) *
    2^18 * 4 * 2 * 2 * (102 / 100) * 16 * (129 / 100)^18 *
    4^15 * 128 * 2 * (1 + (11 / 10) * (1 / 100) * 38000) *
    2 * 2 * 2048 * 32

theorem special_building_sum_budgets :
    cursorSumBound < 2^138 ∧ grandmaSumBound < 2^138 := by decide +kernel

theorem building_sum_with_egg_budget :
    (2^138 + 2^138 + 2^138 + 9 : Nat) < 2^140 := by decide +kernel

/-- These37 exponent bits name the remaining raw-production factors in source
order. The four extra factors after raw CpS (switch/veil/buffs/shimmer aura) are
not part of this calculation and must be bounded separately. -/
theorem other_raw_factors_budget :
    (4 + 1 + 5 + 4 + 2 + 1 + 1 + 1 + 1 + 14 + 1 + 2 : Nat) = 37 ∧
    (37 : Nat) ≤ 40 := by decide +kernel

theorem raw_product_budget :
    (2^140 * 2^83 * 2^90 * 2^40 : Nat) = 2^353 ∧
    (2^353 * 2^47 : Nat) = 2^400 := by decide +kernel

theorem golden_phase_buff_budget :
    (101 * 71^19 * 7 * 2 : Nat) < 2^128 := by decide +kernel

theorem golden_phase_credit_coefficients :
    (86400 * 2^863 : Nat) < 2^880 ∧
    (21600 * 2 * 2^863 + 13 : Nat) < 2^880 ∧
    (900 * 2 * 2^863 + 13 : Nat) < 2^880 := by decide +kernel

theorem collection_credit_coefficients :
    (250180 * 1000 * 2^734 : Nat) < 2^762 ∧
    (7200 * 2^741 : Nat) < 2^755 ∧
    (8 * 2^850 : Nat) < 2^854 ∧
    (2^800 : Nat) < 2^880 := by decide +kernel

def resetCap : Nat := 2^1000
def epochEarnedCap : Nat := 2^940

theorem reset_cap_finite : resetCap < 2^1024 := by decide +kernel

theorem spacing_below_reset_cap (n : Nat) (below : n < resetCap) :
    0 < integerSpacing n ∧ integerSpacing n ∣ resetCap := by
  unfold integerSpacing
  split
  · simp [resetCap]
  · rename_i notSmall
    have nonzero : n ≠ 0 := by omega
    have logarithm : n.log2 < 1000 := (Nat.log2_lt nonzero).mpr below
    refine ⟨Nat.two_pow_pos _, ?_⟩
    exact Nat.pow_dvd_pow 2 (by omega)

theorem below_cap_rounding (n : Nat) (below : n < resetCap) :
    roundedInteger n ≤ resetCap := by
  obtain ⟨positive, multiple⟩ := spacing_below_reset_cap n below
  exact roundMultiple_le_multiple _ _ _ positive (Nat.le_of_lt below) multiple

theorem near_reset_cap (n : Nat) (lower : resetCap ≤ n)
    (upper : n ≤ resetCap + epochEarnedCap) : roundedInteger n = resetCap := by
  have positive : n ≠ 0 := by unfold resetCap at *; omega
  have logarithm : n.log2 = 1000 := (Nat.log2_eq_iff positive).mpr
    ⟨lower, by unfold resetCap epochEarnedCap at *; omega⟩
  have notSmall : ¬ n < 2^53 := by unfold resetCap at *; omega
  have quotient : n / 2^948 = 2^52 := by unfold resetCap epochEarnedCap at *; omega
  have remainder : n % 2^948 = n - resetCap := by unfold resetCap epochEarnedCap at *; omega
  have notAbove : ¬ 2^948 < 2 * (n - resetCap) := by unfold resetCap epochEarnedCap at *; omega
  simp only [roundedInteger, integerSpacing, if_neg notSmall, logarithm]
  change roundMultiple (2^948) n = resetCap
  simp only [roundMultiple, quotient, remainder]
  have even : ((2^52) % 2 == 1) = false := by decide +kernel
  simp only [even, Bool.and_false, Bool.or_false, decide_eq_true_eq,
    if_neg notAbove, Nat.add_zero]
  rfl

/-- Unlike a bound on the number of retries, this invariant covers every finite
retry prefix, including arbitrarily long random-failure tails. -/
theorem reset_step_preserves_cap (old earned : Nat)
    (oldBound : old ≤ resetCap) (earnedBound : earned ≤ epochEarnedCap) :
    roundedInteger (old + earned) ≤ resetCap := by
  by_cases below : old + earned < resetCap
  · exact below_cap_rounding _ below
  · rw [near_reset_cap _ (by omega) (by omega)]
    exact Nat.le_refl _

def resetPrefixes : List Nat → Nat → Nat
  | [], old => old
  | earned :: rest, old => resetPrefixes rest (roundedInteger (old + earned))

theorem all_reset_prefixes_bounded (earnings : List Nat) (old : Nat)
    (oldBound : old ≤ resetCap)
    (earnedBounds : ∀ earned ∈ earnings, earned ≤ epochEarnedCap) :
    resetPrefixes earnings old ≤ resetCap := by
  induction earnings generalizing old with
  | nil => exact oldBound
  | cons earned rest ih =>
    apply ih
    · exact reset_step_preserves_cap old earned oldBound (earnedBounds earned (by simp))
    · intro amount member
      exact earnedBounds amount (by simp [member])

theorem reset_step_no_overflow (old earned : Nat)
    (oldBound : old ≤ resetCap) (earnedBound : earned ≤ epochEarnedCap) :
    roundBinary64Integer (old + earned) = some (roundedInteger (old + earned)) := by
  have finite := Nat.lt_of_le_of_lt (reset_step_preserves_cap old earned oldBound earnedBound) reset_cap_finite
  simp [roundBinary64Integer, finite]

theorem native_barrier_endpoint :
    JavaScript.Number.add (JavaScript.Number.ofNat resetCap)
      (JavaScript.Number.ofNat epochEarnedCap) = JavaScript.Number.ofNat resetCap := by decide +kernel

theorem proposed_market_garden_time_budget :
    ((231 + 1 + 122445 * 1032) * 60 + 4925 * 300 : Nat) < 2^50 := by decide +kernel

inductive EpochPhase where
  | beforeChocolate
  | afterChocolate

def phaseExponent : EpochPhase → Nat
  | .beforeChocolate => 936
  | .afterChocolate => 938

def phaseCap (phase : EpochPhase) : Nat := 2^(phaseExponent phase)
def ordinaryCreditCap : Nat := 2^880

theorem spacing_below_phase_cap (phase : EpochPhase) (n : Nat) (below : n < phaseCap phase) :
    0 < integerSpacing n ∧ integerSpacing n ∣ phaseCap phase := by
  unfold integerSpacing
  split
  · simp [phaseCap]
  · rename_i notSmall
    have nonzero : n ≠ 0 := by omega
    have logarithm : n.log2 < phaseExponent phase := (Nat.log2_lt nonzero).mpr below
    refine ⟨Nat.two_pow_pos _, ?_⟩
    exact Nat.pow_dvd_pow 2 (by omega)

theorem below_phase_cap_rounding (phase : EpochPhase) (n : Nat) (below : n < phaseCap phase) :
    roundedInteger n ≤ phaseCap phase := by
  obtain ⟨positive, multiple⟩ := spacing_below_phase_cap phase n below
  exact roundMultiple_le_multiple _ _ _ positive (Nat.le_of_lt below) multiple

theorem near_phase_cap (phase : EpochPhase) (n : Nat) (lower : phaseCap phase ≤ n)
    (upper : n ≤ phaseCap phase + ordinaryCreditCap) : roundedInteger n = phaseCap phase := by
  have positive : n ≠ 0 := by cases phase <;> simp [phaseCap, phaseExponent] at * <;> omega
  have logarithm : n.log2 = phaseExponent phase := (Nat.log2_eq_iff positive).mpr
    ⟨lower, by cases phase <;> simp [phaseCap, phaseExponent, ordinaryCreditCap] at * <;> omega⟩
  have notSmall : ¬n < 2^53 := by cases phase <;> simp [phaseCap, phaseExponent] at * <;> omega
  have quotient : n / 2^(phaseExponent phase - 52) = 2^52 := by
    cases phase <;> simp [phaseCap, phaseExponent, ordinaryCreditCap] at * <;> omega
  have remainder : n % 2^(phaseExponent phase - 52) = n - phaseCap phase := by
    cases phase <;> simp [phaseCap, phaseExponent, ordinaryCreditCap] at * <;> omega
  have notAbove : ¬2^(phaseExponent phase - 52) < 2 * (n - phaseCap phase) := by
    cases phase <;> simp [phaseCap, phaseExponent, ordinaryCreditCap] at * <;> omega
  simp only [roundedInteger, integerSpacing, if_neg notSmall, logarithm]
  simp only [roundMultiple, quotient, remainder]
  have even : ((2^52) % 2 == 1) = false := by decide +kernel
  simp only [even, Bool.and_false, Bool.or_false, decide_eq_true_eq,
    if_neg notAbove, Nat.add_zero]
  cases phase <;> rfl

theorem ordinary_credit_preserves_phase_cap (phase : EpochPhase) (old credit : Nat)
    (oldBound : old ≤ phaseCap phase) (creditBound : credit ≤ ordinaryCreditCap) :
    roundedInteger (old + credit) ≤ phaseCap phase := by
  by_cases below : old + credit < phaseCap phase
  · exact below_phase_cap_rounding phase _ below
  · rw [near_phase_cap phase _ (by omega) (by omega)]
    exact Nat.le_refl _

theorem ordinary_debit_preserves_phase_cap (phase : EpochPhase) (old debit : Nat)
    (oldBound : old ≤ phaseCap phase) : roundedInteger (old - debit) ≤ phaseCap phase := by
  by_cases below : old - debit < phaseCap phase
  · exact below_phase_cap_rounding phase _ below
  · have same : old - debit = phaseCap phase := by omega
    rw [same, near_phase_cap phase _ (Nat.le_refl _) (by omega)]
    exact Nat.le_refl _

structure CookieCounters where
  bank : Nat
  earned : Nat

def CookieCounters.bounded (state : CookieCounters) (phase : EpochPhase) : Prop :=
  state.bank ≤ phaseCap phase ∧ state.earned ≤ phaseCap phase

inductive CounterStep where
  | earn (credit : Nat)
  | refund (credit : Nat)
  | spend (debit : Nat)
  | dissolve (debit : Nat)

def CounterStep.small : CounterStep → Prop
  | .earn credit | .refund credit => credit ≤ ordinaryCreditCap
  | .spend _ | .dissolve _ => True

def CounterStep.apply : CounterStep → CookieCounters → CookieCounters
  | .earn credit, state => ⟨roundedInteger (state.bank + credit), roundedInteger (state.earned + credit)⟩
  | .refund credit, state =>
    let bank := roundedInteger (state.bank + credit)
    ⟨bank, max bank state.earned⟩
  | .spend debit, state => ⟨roundedInteger (state.bank - debit), state.earned⟩
  | .dissolve debit, state => ⟨roundedInteger (state.bank - debit), roundedInteger (state.earned - debit)⟩

/-- Refunds use the actual counter topology: the bank receives the credit and
earned becomes max(bank,earned), rather than receiving the refund a second time.
The spend cases use rounded nonnegative integer differences; native subtraction
and affordable-debit refinement are open. -/
theorem counter_step_preserves_phase_cap (phase : EpochPhase) (state : CookieCounters)
    (bounded : state.bounded phase) (step : CounterStep) (small : step.small) :
    (step.apply state).bounded phase := by
  obtain ⟨bankBound, earnedBound⟩ := bounded
  cases step with
  | earn credit => exact ⟨ordinary_credit_preserves_phase_cap phase _ _ bankBound small,
      ordinary_credit_preserves_phase_cap phase _ _ earnedBound small⟩
  | refund credit =>
    have bank := ordinary_credit_preserves_phase_cap phase _ _ bankBound small
    exact ⟨bank, Nat.max_le.mpr ⟨bank, earnedBound⟩⟩
  | spend debit => exact ⟨ordinary_debit_preserves_phase_cap phase _ _ bankBound, earnedBound⟩
  | dissolve debit => exact ⟨ordinary_debit_preserves_phase_cap phase _ _ bankBound,
      ordinary_debit_preserves_phase_cap phase _ _ earnedBound⟩

def counterSteps : List CounterStep → CookieCounters → CookieCounters
  | [], state => state
  | step :: rest, state => counterSteps rest (step.apply state)

theorem all_counter_prefixes_bounded (phase : EpochPhase) (steps : List CounterStep)
    (state : CookieCounters) (bounded : state.bounded phase)
    (small : ∀ step ∈ steps, step.small) : (counterSteps steps state).bounded phase := by
  induction steps generalizing state with
  | nil => exact bounded
  | cons step rest ih =>
    apply ih
    · exact counter_step_preserves_phase_cap phase state bounded step (small step (by simp))
    · intro step member
      exact small step (by simp [member])

/-- One Chocolate egg credit is allowed to exceed the ordinary-credit bound.
The source multiplier0.05 still needs refinement to the supplied2^932 bound. -/
theorem chocolate_changes_phase (state : CookieCounters)
    (bounded : state.bounded .beforeChocolate) (credit : Nat) (small : credit ≤ 2^932) :
    (CounterStep.apply (.earn credit) state).bounded .afterChocolate := by
  obtain ⟨bankBound, earnedBound⟩ := bounded
  constructor
  · apply below_phase_cap_rounding
    simp [phaseCap, phaseExponent] at *
    omega
  · apply below_phase_cap_rounding
    simp [phaseCap, phaseExponent] at *
    omega

theorem final_phase_implies_epoch_bound (state : CookieCounters)
    (bounded : state.bounded .afterChocolate) : state.earned ≤ epochEarnedCap := by
  have bound := bounded.2
  simp [phaseCap, phaseExponent, epochEarnedCap] at *
  omega

end CookieClicker.FullGame.CollectionEnvelope

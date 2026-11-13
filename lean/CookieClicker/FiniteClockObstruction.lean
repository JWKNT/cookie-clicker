import CookieClicker.SugarClock

/-! A diagnostic for incompatible clock and probability assumptions.
If all sugar runs have a common finite clock ceiling, their eligible attempt
counts are bounded. A positive conditional failure probability then leaves
positive mass on paths which never reach the required Hand-picked goal.
Their completion hitting time, with unsuccessful paths assigned infinity, has
no finite expected value. This is not an optimal strategy result, and neither
the installed engine nor the runtime adapter is asserted to satisfy all inputs.
-/
namespace CookieClicker.FullGame.FiniteClockObstruction

open SugarClock HandPickedExpectation

theorem half_survival_positive (n : Nat) : 0 < halfSurvival n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    change 0 < halfSurvival n / 2
    apply (Rat.lt_div_iff (by decide +kernel : (0 : Rat) < 2)).mpr
    simpa only [Rat.zero_mul] using ih

/-- A finite elapsed-clock ceiling gives an explicit eligible-attempt cap. -/
theorem bounded_clock_attempt_cap (run : Run) (ceiling : Nat)
    (bounded : ∀ i, (run.state i).clock ≤ ceiling) (i : Nat) :
    (run.state i).attempts ≤ ceiling / 64436019 := by
  have timing := attempts_times_spacing_le_clock (run.reachable i)
  have bound := bounded i
  omega

/-- Once every possible eligible attempt has failed, no checkpoint can complete.
This includes runs that stop attempting. First-hit history is not discarded.
-/
theorem capped_failure_excludes_completion (run : Run) (observations : Nat → Snapshot)
    (projection : ∀ i, (run.state i).handPicked =
      (observations i).achievements "Hand-picked")
    (ceiling : Nat) (bounded : ∀ i, (run.state i).clock ≤ ceiling)
    (failed : NoSuccessInFirst run (ceiling / 64436019)) (time : Nat) :
    NoCompletionBy run observations time := by
  intro i _
  have absent := failed i (bounded_clock_attempt_cap run ceiling bounded i)
  cases done : complete Pinned.requirements (observations i) with
  | false => rfl
  | true =>
    have won := Pinned.completion_requires_hand_picked (observations i) done
    rw [projection] at absent
    simp_all

/-- The finite-attempt failure mass remains in every completion-survival tail. -/
theorem bounded_clock_persistent_tail {Ω : Type} (bounds : EventBounds Ω)
    (runs : Ω → Run) (observations : Ω → Nat → Snapshot)
    (projection : ∀ outcome i, ((runs outcome).state i).handPicked =
      (observations outcome i).achievements "Hand-picked")
    (ceiling : Nat) (bounded : ∀ outcome i, ((runs outcome).state i).clock ≤ ceiling)
    (fairFailure : ∀ n,
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) n) / 2 ≤
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) (n + 1)))
    (time : Nat) :
    halfSurvival (ceiling / 64436019) ≤
      (fullTailCertificate bounds runs observations).survival time := by
  have lower := attempt_survival_lower
    (bridge_from_sugar_runs bounds runs observations projection fairFailure)
    (ceiling / 64436019)
  have inclusion := bounds.monotone
    (fun outcome => NoSuccessInFirst (runs outcome) (ceiling / 64436019))
    (fun outcome => NoCompletionBy (runs outcome) (observations outcome) time)
    (fun outcome failed => capped_failure_excludes_completion (runs outcome)
      (observations outcome) (projection outcome) ceiling (bounded outcome) failed time)
  exact Rat.le_trans lower inclusion

/-- A common finite clock ceiling and the stated failure law force infinite
expected completion hitting time. The actual expectation bridge is still explicit.
This theorem diagnoses a degenerate model; it does not recommend a policy.
-/
theorem bounded_clock_infinite_expected_completion {Ω : Type} (bounds : EventBounds Ω)
    (runs : Ω → Run) (observations : Ω → Nat → Snapshot)
    (projection : ∀ outcome i, ((runs outcome).state i).handPicked =
      (observations outcome i).achievements "Hand-picked")
    (ceiling : Nat) (bounded : ∀ outcome i, ((runs outcome).state i).clock ≤ ceiling)
    (fairFailure : ∀ n,
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) n) / 2 ≤
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) (n + 1)))
    (actual : Rat → Prop)
    (sound : FiniteTailsSound (fullTailCertificate bounds runs observations) actual) :
    ∀ lower : Rat, actual lower := by
  intro lower
  apply certificate_cut_refines sound
  apply positive_noncompletion_mass_infinite
    (half_survival_positive (ceiling / 64436019))
  exact bounded_clock_persistent_tail bounds runs observations projection ceiling bounded fairFailure

/-- Arithmetic only: this is the attempt cap if the Date range is imposed as
a global clock ceiling from the runtime's fixed start. No such ceiling is assumed
for the adapter by this calculation.
-/
theorem date_range_attempt_cap :
    (8640000000000000 - 1793275200000) / 64436019 = (134058665 : Nat) := by
  decide +kernel

end CookieClicker.FullGame.FiniteClockObstruction

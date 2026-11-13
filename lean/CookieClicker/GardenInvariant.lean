import CookieClicker.FullCompletionChecks

/-! A full-target consequence of the source-audited Garden sacrifice rule.
This file checks the rule on normalized observations. The source-to-all-runtime-
executions correspondence is an explicit remaining obligation.
-/
namespace CookieClicker.FullGame.Garden
open Pinned

def juicyKnown (s : Snapshot) : Bool := s.gardenSeeds "queenbeetLump"
def seedlessWon (s : Snapshot) : Bool := s.achievements "Seedless to nay"
def fullSeedLog (s : Snapshot) : Bool := requirements.seeds.all s.gardenSeeds

theorem juicy_is_required : "queenbeetLump" ∈ requirements.seeds := by decide +kernel
theorem seedless_is_required : "Seedless to nay" ∈ requirements.achievements := by decide +kernel

theorem full_log_has_juicy {s : Snapshot} (full : fullSeedLog s = true) : juicyKnown s = true :=
  List.all_eq_true.mp full _ juicy_is_required

/-- At the first Seedless award, convert requires a full log and resets JQB.
Other transitions can change either flag; they cannot first award Seedless
without this condition. Native source tests check convert and seed unlock paths.
-/
def sacrificeContract (before after : Snapshot) : Bool :=
  if !seedlessWon before && seedlessWon after then fullSeedLog before && !juicyKnown after else true

def acquisition (before after : Snapshot) : Nat :=
  if !juicyKnown before && juicyKnown after then 1 else 0

def score (s : Snapshot) : Nat := (if juicyKnown s then 1 else 0) + (if seedlessWon s then 1 else 0)

theorem first_award_requires_full_log {before after : Snapshot}
    (checked : sacrificeContract before after = true)
    (not_yet : seedlessWon before = false) (awarded : seedlessWon after = true) :
    fullSeedLog before = true ∧ juicyKnown after = false := by
  simpa [sacrificeContract, not_yet, awarded] using checked

theorem step_acquisition_budget (before after : Snapshot)
    (checked : sacrificeContract before after = true) :
    score after ≤ score before + acquisition before after := by
  have first_rule : seedlessWon before = false → seedlessWon after = true →
      juicyKnown before = true ∧ juicyKnown after = false := by
    intro absent awarded
    obtain ⟨full, reset⟩ := first_award_requires_full_log checked absent awarded
    exact ⟨full_log_has_juicy full, reset⟩
  cases hb : juicyKnown before <;> cases ha : juicyKnown after <;>
    cases sb : seedlessWon before <;> cases sa : seedlessWon after <;>
    simp_all [score, acquisition]

def validTrace : Snapshot → List Snapshot → Bool
  | _, [] => true
  | before, after :: rest => sacrificeContract before after && validTrace after rest

def acquisitions : Snapshot → List Snapshot → Nat
  | _, [] => 0
  | before, after :: rest => acquisition before after + acquisitions after rest

def lastState : Snapshot → List Snapshot → Snapshot
  | s, [] => s
  | _, s :: rest => lastState s rest

theorem trace_acquisition_budget (initial : Snapshot) (rest : List Snapshot)
    (checked : validTrace initial rest = true) :
    score (lastState initial rest) ≤ score initial + acquisitions initial rest := by
  induction rest generalizing initial with
  | nil => simp [lastState, acquisitions]
  | cons next rest ih =>
    have conditions : sacrificeContract initial next = true ∧ validTrace next rest = true := by
      simpa only [validTrace, Bool.and_eq_true] using checked
    have first := step_acquisition_budget initial next conditions.1
    have tail := ih next conditions.2
    simp only [lastState, acquisitions]
    omega

theorem every_checkpoint_acquisition_budget (initial : Snapshot) (rest : List Snapshot)
    (checked : validTrace initial rest = true) :
    ∀ checkpoint, checkpoint ∈ initial :: rest →
      score checkpoint ≤ score initial + acquisitions initial rest := by
  induction rest generalizing initial with
  | nil =>
    intro checkpoint member
    have same : checkpoint = initial := by simpa using member
    subst checkpoint
    simp [acquisitions]
  | cons next rest ih =>
    have conditions : sacrificeContract initial next = true ∧ validTrace next rest = true := by
      simpa only [validTrace, Bool.and_eq_true] using checked
    have first := step_acquisition_budget initial next conditions.1
    intro checkpoint member
    rcases List.mem_cons.mp member with same | later
    · subst checkpoint
      omega
    · have tail := ih next conditions.2 checkpoint later
      simp only [acquisitions]
      omega

/-- The bound survives later goal loss after the first complete checkpoint. -/
theorem any_full_completion_requires_two_juicy_acquisitions
    (initial : Snapshot) (rest : List Snapshot)
    (fresh_juicy : juicyKnown initial = false) (fresh_seedless : seedlessWon initial = false)
    (checked : validTrace initial rest = true) (checkpoint : Snapshot)
    (observed : checkpoint ∈ initial :: rest) (done : complete requirements checkpoint = true) :
    2 ≤ acquisitions initial rest := by
  have juicy : juicyKnown checkpoint = true := complete_requires_seed juicy_is_required done
  have seedless : seedlessWon checkpoint = true := complete_requires_achievement seedless_is_required done
  have budget := every_checkpoint_acquisition_budget initial rest checked checkpoint observed
  simpa [score, fresh_juicy, fresh_seedless, juicy, seedless] using budget

/-- The actual full-game goal needs two JQB seed acquisitions across the reset. -/
theorem full_completion_requires_two_juicy_acquisitions
    (initial : Snapshot) (rest : List Snapshot)
    (fresh_juicy : juicyKnown initial = false) (fresh_seedless : seedlessWon initial = false)
    (checked : validTrace initial rest = true)
    (done : complete requirements (lastState initial rest) = true) :
    2 ≤ acquisitions initial rest := by
  have juicy : juicyKnown (lastState initial rest) = true := complete_requires_seed juicy_is_required done
  have seedless : seedlessWon (lastState initial rest) = true := complete_requires_achievement seedless_is_required done
  have budget := trace_acquisition_budget initial rest checked
  simpa [score, fresh_juicy, fresh_seedless, juicy, seedless] using budget

theorem earlier_full_log (initial : Snapshot) (rest : List Snapshot)
    (fresh_seedless : seedlessWon initial = false)
    (checked : validTrace initial rest = true)
    (awarded : seedlessWon (lastState initial rest) = true) :
    ∃ earlier, earlier ∈ initial :: rest ∧ fullSeedLog earlier = true ∧ seedlessWon earlier = false := by
  induction rest generalizing initial with
  | nil => simp [lastState, fresh_seedless] at awarded
  | cons next rest ih =>
    have conditions : sacrificeContract initial next = true ∧ validTrace next rest = true := by
      simpa only [validTrace, Bool.and_eq_true] using checked
    cases hnext : seedlessWon next with
    | true =>
      have full := (first_award_requires_full_log conditions.1 fresh_seedless hnext).1
      exact ⟨initial, by simp, full, fresh_seedless⟩
    | false =>
      obtain ⟨earlier, member, full, absent⟩ := ih next hnext conditions.2 awarded
      exact ⟨earlier, by simp [member], full, absent⟩

/-- A full log before the first sacrifice and a distinct full log at completion. -/
theorem full_completion_requires_two_full_logs (initial : Snapshot) (rest : List Snapshot)
    (fresh_seedless : seedlessWon initial = false)
    (checked : validTrace initial rest = true)
    (done : complete requirements (lastState initial rest) = true) :
    fullSeedLog (lastState initial rest) = true ∧
    ∃ earlier, earlier ∈ initial :: rest ∧ fullSeedLog earlier = true ∧
      earlier ≠ lastState initial rest := by
  have awarded : seedlessWon (lastState initial rest) = true :=
    complete_requires_achievement seedless_is_required done
  have full_end : fullSeedLog (lastState initial rest) = true :=
    List.all_eq_true.mpr (fun name required => complete_requires_seed required done)
  obtain ⟨earlier, member, full, absent⟩ := earlier_full_log initial rest fresh_seedless checked awarded
  refine ⟨full_end, earlier, member, full, ?_⟩
  intro same
  rw [same, awarded] at absent
  contradiction

end CookieClicker.FullGame.Garden

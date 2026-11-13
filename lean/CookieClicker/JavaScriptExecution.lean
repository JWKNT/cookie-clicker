import CookieClicker.JavaScriptBrowserRuntime
import CookieClicker.JavaScriptCompletion
import CookieClicker.HittingTime

/-! Stochastic source execution with no diagnostic random tape.

Each actual free-random request branches over the selected IID53 law. Seeded
source calls remain interpreter operations. A finite prefix can return, remain
pending, or report a missing model operation. Pending and missing results are
not game failure or player observations. This module does not supply the still
missing player-input, public-observation, and unbounded-clock refinements.
-/
namespace CookieClicker.JavaScript.Execution

open CookieClicker.FullGame
abbrev Draw := UniformRandom.Draw 53
abbrev RandomProgram := HittingTime.Program

/-- This is an interpreter checkpoint, not a terminal game state. -/
def atBoundary (state : Browser.State) : Bool :=
  Browser.taskFinished state.machine && state.activeResource.isNone && state.activeTimer.isNone &&
    state.animation.active.isNone && state.textSelection.active.isNone && state.eventDispatches.isEmpty && state.focus.transitions.isEmpty

/-- A frozen rendering-event batch is one host procedure. Its intermediate
source returns cannot create controller or completion-observation boundaries. -/
theorem active_animation_not_boundary (state : Browser.State) (events : List Nat)
    (active : state.animation.active = some events) : atBoundary state = false := by
  simp [atBoundary,active]

theorem active_selection_not_boundary (state : Browser.State) (event : Nat)
    (active : state.textSelection.active = some event) : atBoundary state = false := by
  simp [atBoundary,active]

/-- A fresh draw is private environment input. It is never a controller input. -/
def afterDraw (state : Browser.State) (draw : Draw) : Browser.State :=
  Browser.result { state with
    randomInputs := []
    machine := { state.machine with freeDrawCount := state.machine.freeDrawCount + 1 } }
    (.number (Random.encode draw))

theorem afterDraw_elapsed (state : Browser.State) (draw : Draw) :
    (afterDraw state draw).machine.elapsed = state.machine.elapsed := rfl

theorem afterDraw_count (state : Browser.State) (draw : Draw) :
    (afterDraw state draw).machine.freeDrawCount = state.machine.freeDrawCount + 1 := rfl

theorem afterDraw_no_tape (state : Browser.State) (draw : Draw) :
    (afterDraw state draw).randomInputs = [] := rfl

theorem afterDraw_result (state : Browser.State) (draw : Draw) :
    (afterDraw state draw).machine.control = .expressionResult (.value (.number (Random.encode draw))) := rfl

/-- Only deterministic source work, a fresh draw, or a real task boundary can
advance this kernel. A missing operation has its own explicit result. -/
inductive Tick (before : Browser.State) where
  | internal (next : Browser.State)
      (sameTime : next.machine.elapsed = before.machine.elapsed)
  | random (next : Draw → Browser.State)
      (sameTime : ∀ draw, (next draw).machine.elapsed = before.machine.elapsed)
  | boundary (finished : atBoundary before = true)
  | missing (failure : EvalFailure)

def tick (state : Browser.State) : Tick state :=
  if !state.randomInputs.isEmpty then
    .missing (.fault (.invalidContinuation "Diagnostic random tapes are not stochastic source semantics"))
  else match state.machine.control with
  | .unresolved .freeRandom => .random (afterDraw state) (afterDraw_elapsed state)
  | .fault failure => .missing (.fault failure)
  | _ =>
    if finished : atBoundary state = true then .boundary finished
    else
      let next := BrowserRuntime.step state
      match status next.machine with
      | .fault failure => .missing (.fault failure)
      | .unresolved request =>
        if status state.machine == .unresolved request then .missing (.unresolved request)
        else .internal next (BrowserRuntime.step_preserves_elapsed state)
      | _ => .internal next (BrowserRuntime.step_preserves_elapsed state)

inductive Outcome where
  | pending (state : Browser.State)
  | returned (state : Browser.State)
  | missing (state : Browser.State) (failure : EvalFailure)

def Outcome.state : Outcome → Browser.State
  | .pending state | .returned state | .missing state _ => state

/-- Fuel truncates a private mathematical approximation. It does not limit the
admissible policy or turn unfinished source execution into a failed path. -/
def runPrefix : Nat → Browser.State → RandomProgram Outcome
  | 0, state => .pure (.pending state)
  | fuel + 1, state => match tick state with
    | .internal next _ => runPrefix fuel next
    | .random next _ => .draw (fun draw => runPrefix fuel (next draw))
    | .boundary _ => .pure (.returned state)
    | .missing failure => .pure (.missing state failure)

/-- More mathematical work resumes only pending source execution. It does not
repeat a finished callback or skip a missing model operation. -/
def resumePrefix (fuel : Nat) : Outcome → RandomProgram Outcome
  | .pending state => runPrefix fuel state
  | other => .pure other

theorem prefix_add (first more : Nat) (state : Browser.State) :
    runPrefix (first + more) state = (runPrefix first state).bind (resumePrefix more) := by
  induction first generalizing state with
  | zero => simp [runPrefix, HittingTime.Program.bind, resumePrefix]
  | succ first ih =>
    simp only [Nat.succ_add, runPrefix]
    cases tick state with
    | internal next sameTime => exact ih next
    | random next sameTime =>
      simp only [HittingTime.Program.bind]
      congr 1
      funext draw
      exact ih (next draw)
    | boundary finished => rfl
    | missing failure => rfl

theorem prefix_elapsed (fuel : Nat) (state : Browser.State) :
    (runPrefix fuel state).All (fun outcome => outcome.state.machine.elapsed = state.machine.elapsed) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [runPrefix]
    cases tick state with
    | internal next sameTime => simpa [sameTime] using ih next
    | random next sameTime =>
      intro draw
      simpa [sameTime draw] using ih (next draw)
    | boundary _ => rfl
    | missing failure => rfl

def Outcome.ValidBoundary : Outcome → Prop
  | .returned state => atBoundary state = true
  | _ => True

theorem prefix_returns_at_boundary (fuel : Nat) (state : Browser.State) :
    (runPrefix fuel state).All Outcome.ValidBoundary := by
  induction fuel generalizing state with
  | zero => trivial
  | succ fuel ih =>
    simp only [runPrefix]
    cases tick state with
    | internal next _ => exact ih next
    | random next _ => exact fun draw => ih (next draw)
    | boundary finished => exact finished
    | missing failure => trivial

/-- The finite source prefix has total probability one, including its pending
and missing-model leaves. Neither type of leaf may be silently discarded. -/
theorem prefix_mass_one (fuel : Nat) (state : Browser.State) :
    (runPrefix fuel state).expect (fun _ => 1) = 1 :=
  HittingTime.program_constant _ 1

theorem prefix_expectation_bounds (fuel : Nat) (state : Browser.State)
    (value : Outcome → Rat) (lower upper : Rat)
    (bounded : ∀ outcome, lower ≤ value outcome ∧ value outcome ≤ upper) :
    lower ≤ (runPrefix fuel state).expect value ∧ (runPrefix fuel state).expect value ≤ upper :=
  HittingTime.program_bounds _ _ _ _ bounded

/-- Source completion is checked separately from successful callback return.
Projection errors remain errors and never become a `false` completion flag. -/
def projectedCompletion (outcome : Outcome) (game : Value) (edition : String)
    (history : Completion.AccessHistory) : Checked Bool :=
  match outcome with
  | .returned state => Completion.complete state.machine.heap game edition history
  | .pending _ => .error (.unresolved (.unsupportedSyntax "Source prefix is still pending"))
  | .missing _ failure => .error failure

theorem pending_is_not_completion (state : Browser.State) (game : Value) (edition : String)
    (history : Completion.AccessHistory) :
    projectedCompletion (.pending state) game edition history ≠ .ok true := by
  simp [projectedCompletion]

theorem missing_is_not_completion (state : Browser.State) (failure : EvalFailure)
    (game : Value) (edition : String) (history : Completion.AccessHistory) :
    projectedCompletion (.missing state failure) game edition history ≠ .ok true := by
  simp [projectedCompletion]

theorem completed_source_has_all_goals (outcome : Outcome) (game : Value) (edition : String)
    (history : Completion.AccessHistory)
    (done : projectedCompletion outcome game edition history = .ok true) :
    ∃ state projected, outcome = .returned state ∧
      Completion.snapshot state.machine.heap game edition history = .ok projected ∧
      ∀ goal ∈ FullGame.goals Pinned.requirements, satisfies projected goal = true := by
  cases outcome with
  | pending state => exact False.elim (pending_is_not_completion state game edition history done)
  | missing state failure => exact False.elim (missing_is_not_completion state failure game edition history done)
  | returned state =>
    obtain ⟨projected,fromHeap,allGoals⟩ := Completion.completion_has_all_goals
      state.machine.heap game edition history done
    exact ⟨state,projected,rfl,fromHeap,allGoals⟩

/-- The game root comes from the actual source global object. A missing root,
unknown host property, or accessor remains an explicit projection error. -/
def gameRoot (state : Browser.State) : Checked Value :=
  Completion.field state.machine.heap (.object state.machine.globalObject) "Game"

structure AccessLog where
  snapshots : List Snapshot
  history : Completion.AccessHistory
  recorded : Completion.Recorded snapshots history

def emptyAccessLog : AccessLog := ⟨[], Completion.emptyHistory, .initial⟩

def AccessLog.record (log : AccessLog) (snapshot : Snapshot) : AccessLog := {
  snapshots := snapshot :: log.snapshots
  history := Completion.recordAccess log.history snapshot
  recorded := .observe log.recorded snapshot }

theorem accessLog_has_recorded_snapshot (log : AccessLog) (name : String)
    (accessed : log.history name = true) :
    ∃ snapshot ∈ log.snapshots, Completion.currentAccess snapshot name = true :=
  Completion.recorded_access_has_witness log.recorded name accessed

/-- A returned callback updates the access log from its own heap. This is a
boundary observation, not yet a proof that all transient completion/access
checkpoints of the full source have been included. -/
def recordReturned (state : Browser.State) (edition : String) (log : AccessLog) :
    Checked (AccessLog × Snapshot) := do
  if !atBoundary state then
    .error (.unresolved (.unsupportedSyntax "Cannot project an unfinished source callback"))
  else do
    let game ← gameRoot state
    let projected ← Completion.snapshot state.machine.heap game edition log.history
    let next := log.record projected
    pure (next, { projected with accessedUpgrades := next.history })

end CookieClicker.JavaScript.Execution

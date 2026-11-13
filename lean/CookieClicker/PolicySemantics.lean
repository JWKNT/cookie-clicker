import Lean
import CookieClicker.FullCompletionChecks

/-! Observation-history and action-time semantics for the evaluation wrapper.
The actual VM supplies JSON observation, action suggestions, and remembered JSON.
This formal controller has exactly those inputs. The native JavaScript VM is not
formally verified by this interface. No input-rate limit for all controls is
inferred from the cookie-click throttle or finite experiment budgets.
-/
namespace CookieClicker.FullGame.PolicySemantics
open Lean

/-- Exact serialized JSON preserves object order as observed by JavaScript code.
The supplied strings are produced by the runtime JSON serializer; parsing and
VM execution are separate, tested implementation obligations.
-/
structure PublicFrame where
  observation : String
  actions : String

/-- Actions and memory are serialized JSON; missing wrapped memory is the text `null`. -/
inductive Decision where
  | bare (action : String)
  | remember (action memory : String)

def Controller := PublicFrame → String → Except String Decision

def Decision.action : Decision → String
  | .bare action => action
  | .remember action _ => action

def Decision.nextMemory (prior : String) : Decision → String
  | .bare _ => prior
  | .remember _ memory => memory

/-- This reproduces the evaluator's memory handoff, before action execution. -/
def runController (policy : Controller) (memory : String) : List PublicFrame → Except String (List String × String)
  | [] => .ok ([], memory)
  | frame :: rest => do
    let decision ← policy frame memory
    let (actions, lastMemory) ← runController policy (decision.nextMemory memory) rest
    return (decision.action :: actions, lastMemory)

/-- Environment state can contain arbitrary private information; projection selects the input. -/
def runProjected {Private : Type} (policy : Controller) (memory : String)
    (history : List (PublicFrame × Private)) : Except String (List String × String) :=
  runController policy memory (history.map Prod.fst)

theorem private_history_noninterference {Left Right : Type} (policy : Controller) (memory : String)
    (left : List (PublicFrame × Left)) (right : List (PublicFrame × Right))
    (samePublic : left.map Prod.fst = right.map Prod.fst) :
    runProjected policy memory left = runProjected policy memory right := by
  unfold runProjected
  rw [samePublic]

def runPrefix (policy : Controller) (memory : String) (observations : Nat → PublicFrame) (length : Nat) :
    Except String (List String × String) :=
  runController policy memory (List.ofFn (fun i : Fin length => observations i.val))

/-- Future observations and private environment information cannot affect earlier decisions. -/
theorem same_public_prefix_same_decisions (policy : Controller) (memory : String)
    (left right : Nat → PublicFrame) (length : Nat)
    (same : ∀ i, i < length → left i = right i) :
    runPrefix policy memory left length = runPrefix policy memory right length := by
  unfold runPrefix
  have functions : (fun i : Fin length => left i.val) = (fun i : Fin length => right i.val) := by
    funext i
    exact same i.val i.isLt
  rw [functions]

theorem bare_action_preserves_memory (action prior : String) :
    (Decision.bare action).nextMemory prior = prior := rfl

theorem wrapped_action_replaces_memory (action memory prior : String) :
    (Decision.remember action memory).nextMemory prior = memory := rfl

/-- An infinite active action stream is non-Zeno when every finite clock horizon is passed. -/
def NonZeno (clock : Nat → Nat) : Prop :=
  ∀ horizon, ∃ index, ∀ later, index ≤ later → horizon < clock later

/-- Raw wait(0) actions satisfy the runtime's wait guard and need not advance the clock. -/
def zeroWaitClock : Nat → Nat := fun _ => 0

theorem zero_wait_not_nonZeno : ¬NonZeno zeroWaitClock := by
  intro progress
  obtain ⟨index, later⟩ := progress 0
  have impossible := later index (Nat.le_refl _)
  simp [zeroWaitClock] at impossible

/-- A uniform action bound within each integer clock horizon does ensure progress. -/
theorem bounded_actions_imply_nonZeno (clock : Nat → Nat) (bound : Nat)
    (counts : ∀ n, n ≤ bound * (clock n + 1)) : NonZeno clock := by
  intro horizon
  refine ⟨bound * (horizon + 1) + 1, ?_⟩
  intro later after
  apply Nat.lt_of_not_ge
  intro before
  have multiplied := Nat.mul_le_mul_left bound (Nat.add_le_add_right before 1)
  have limit := Nat.le_trans (counts later) multiplied
  omega

/-- Clock and a ghost total of accepted cookie clicks; other controls are outside this model. -/
structure ClickState where
  clock : Nat
  lastAccepted : Nat
  accepted : Nat
  deriving DecidableEq

def freshClicks : ClickState := ⟨0, 0, 0⟩

inductive ClickStep : ClickState → ClickState → Prop where
  | wait (s : ClickState) (now : Nat) (monotone : s.clock ≤ now) :
      ClickStep s { s with clock := now }
  | rejected (s : ClickState) : ClickStep s s
  | accepted (s : ClickState)
      (spacing : s.accepted = 0 ∨ s.lastAccepted + 20 ≤ s.clock) :
      ClickStep s { s with lastAccepted := s.clock, accepted := s.accepted + 1 }

def ClickInvariant (s : ClickState) : Prop :=
  20 * s.accepted ≤ s.lastAccepted + 20 ∧ s.lastAccepted ≤ s.clock

theorem click_step_preserves {s t : ClickState} (before : ClickInvariant s)
    (step : ClickStep s t) : ClickInvariant t := by
  have count := before.1
  have clock := before.2
  cases step with
  | wait now monotone => exact ⟨count, Nat.le_trans clock monotone⟩
  | rejected => exact before
  | accepted spacing =>
    constructor
    · change 20 * (s.accepted + 1) ≤ s.clock + 20
      rcases spacing with first | later <;> omega
    · exact Nat.le_refl _

inductive ClickReachable : ClickState → Prop where
  | initial : ClickReachable freshClicks
  | next {s t : ClickState} : ClickReachable s → ClickStep s t → ClickReachable t

theorem click_invariant {s : ClickState} (reachable : ClickReachable s) : ClickInvariant s := by
  induction reachable with
  | initial => unfold ClickInvariant freshClicks; decide
  | next _ step ih => exact click_step_preserves ih step

/-- Native accepted clicks have a finite per-horizon bound despite free raw action calls. -/
theorem accepted_click_rate_bound {s : ClickState} (reachable : ClickReachable s) :
    s.accepted ≤ s.clock / 20 + 1 := by
  have inv := click_invariant reachable
  have count := inv.1
  have clock := inv.2
  omega

/-- The native adapter's non-wait commands do not advance its simulated clock. -/
def rawActionTime (before : Nat) (waitMilliseconds : Option Nat) : Nat :=
  match waitMilliseconds with
  | none => before
  | some duration => before + duration

theorem raw_click_time_zero (before : Nat) : rawActionTime before none = before := rfl

theorem raw_zero_wait_time_zero (before : Nat) : rawActionTime before (some 0) = before := by
  simp [rawActionTime]

/-- The decision limit censors an experiment; it is not an elapsed-time guarantee. -/
def repeatedSameTimeAllowed (maximum count : Nat) : Bool := count < maximum

theorem same_time_budget_stops (maximum : Nat) : repeatedSameTimeAllowed maximum maximum = false := by
  simp [repeatedSameTimeAllowed]

/-- Rank of a nonnegative finite binary64 elapsed time, with negative zero normalized.
The native bit encoding/order correspondence is checked separately in JavaScript.
-/
structure ClockBudgetState where
  rank : Nat
  decisions : Nat
  sameTime : Nat
  deriving DecidableEq

def initialBudget : ClockBudgetState := ⟨0, 0, 0⟩

def advanceBudget (s : ClockBudgetState) (nextRank : Nat) : ClockBudgetState :=
  ⟨nextRank, s.decisions + 1, if nextRank = s.rank then s.sameTime + 1 else 0⟩

def ClockBudgetStep (cap : Nat) (before after : ClockBudgetState) : Prop :=
  before.sameTime < cap ∧ before.rank ≤ after.rank ∧ after = advanceBudget before after.rank

def BudgetInvariant (cap : Nat) (s : ClockBudgetState) : Prop :=
  s.sameTime ≤ cap ∧ s.decisions ≤ (cap + 1) * s.rank + s.sameTime

theorem budget_step_preserves {cap : Nat} {s t : ClockBudgetState}
    (inv : BudgetInvariant cap s) (step : ClockBudgetStep cap s t) : BudgetInvariant cap t := by
  obtain ⟨room, monotone, target⟩ := step
  obtain ⟨same, count⟩ := inv
  by_cases equal : t.rank = s.rank
  · rw [target]
    simp only [BudgetInvariant, advanceBudget, equal, ↓reduceIte]
    constructor <;> omega
  · have rankGap : s.rank + 1 ≤ t.rank := by omega
    have multiplied := Nat.mul_le_mul_left (cap + 1) rankGap
    rw [Nat.mul_add, Nat.mul_one] at multiplied
    rw [target]
    simp only [BudgetInvariant, advanceBudget, equal, ↓reduceIte, Nat.add_zero]
    constructor <;> omega

/-- A finite representable clock interval and same-time cap permit only finitely many decisions. -/
theorem finite_clock_decision_bound {cap rankBound : Nat} {s : ClockBudgetState}
    (inv : BudgetInvariant cap s) (finiteClock : s.rank < rankBound) :
    s.decisions < (cap + 1) * rankBound := by
  obtain ⟨same, count⟩ := inv
  have rankGap : s.rank + 1 ≤ rankBound := finiteClock
  have multiplied := Nat.mul_le_mul_left (cap + 1) rankGap
  rw [Nat.mul_add, Nat.mul_one] at multiplied
  omega

theorem budget_decisions_increment {cap : Nat} {s t : ClockBudgetState}
    (step : ClockBudgetStep cap s t) : t.decisions = s.decisions + 1 := by
  rw [step.2.2]
  rfl

/-- No infinite execution can stay in a finite clock interval while passing the budget guard. -/
theorem no_infinite_bounded_clock_execution (cap rankBound : Nat) (states : Nat → ClockBudgetState)
    (initial : states 0 = initialBudget)
    (steps : ∀ n, ClockBudgetStep cap (states n) (states (n + 1)))
    (bounded : ∀ n, (states n).rank < rankBound) : False := by
  have invariants : ∀ n, BudgetInvariant cap (states n) := by
    intro n
    induction n with
    | zero => rw [initial]; simp [BudgetInvariant, initialBudget]
    | succ n ih => exact budget_step_preserves ih (steps n)
  have counts : ∀ n, (states n).decisions = n := by
    intro n
    induction n with
    | zero => rw [initial]; rfl
    | succ n ih => rw [budget_decisions_increment (steps n), ih]
  let limit := (cap + 1) * rankBound
  have impossible := finite_clock_decision_bound (invariants limit) (bounded limit)
  rw [counts] at impossible
  exact Nat.lt_irrefl _ impossible

end CookieClicker.FullGame.PolicySemantics

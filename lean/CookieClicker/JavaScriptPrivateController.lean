import CookieClicker.JavaScriptControlledExecution

/-! Private decision machines for controlled native source execution.
A decision can perform arbitrarily many private computation steps or IID53 draws
before an action. Such work does not advance game time, expose source internals,
or append public actions. Infinite private work receives the same noncompletion
cost as other resolved divergent runs. No finiteness restriction is imposed on
one decision computation or its total random draws.
-/
namespace CookieClicker.JavaScript.PrivateController
open CookieClicker.FullGame
open ControlledExecution
abbrev Action := ControlledExecution.Control

inductive Decision (Memory : Type) where
  | action (control : Action) (next : Memory)
  | compute (next : Memory)
  | draw (next : Execution.Draw → Memory)

abbrev Controller (Observation Memory : Type) :=
  Memory → List (Observation × Action) → Observation → Decision Memory

/-- Source work is the same actual controlled kernel. The policy is evaluated
only while the game is at its decision boundary; private work retains that
same immutable browser state and public history. -/
def step {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) : Execution.RandomProgram (ControlledState O M) :=
  match state.source.phase with
  | .decision => match policy state.memory state.history (observe state.source.browser) with
    | .action control memory => .pure {
        source := submit state.source control
        memory
        history := state.history ++ [(observe state.source.browser,control)] }
    | .compute memory => .pure {state with memory}
    | .draw next => .draw (fun draw => .pure {state with memory := next draw})
  | _ => (ControlledExecution.step tie state.source).bind fun source => .pure {state with source}

def runPrefix {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) : Nat → ControlledState O M → Execution.RandomProgram (ControlledState O M)
  | 0,state => .pure state
  | fuel+1,state => (step observe policy tie state).bind (runPrefix observe policy tie fuel)

def FullyDefined {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (fuel : Nat) (state : ControlledState O M) : Prop :=
  (runPrefix observe policy tie fuel state).All fun next =>
    ControlledExecution.unresolved next.source = false

def FullyResolved {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) : Prop :=
  ∀ fuel, FullyDefined observe policy tie fuel state

def expectedPrefix {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (horizon fuel : Nat) (state : ControlledState O M)
    (_resolved : FullyDefined observe policy tie fuel state) : Rat :=
  (runPrefix observe policy tie fuel state).expect fun next =>
    (ControlledExecution.cappedCost horizon next.source).getD 0

def Expected {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M)
    (resolved : FullyResolved observe policy tie state) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧ ∀ fuel,
    bound + margin ≤ expectedPrefix observe policy tie horizon fuel state (resolved fuel)

theorem compute_step {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) (memory : M)
    (boundary : state.source.phase = .decision)
    (computation : policy state.memory state.history (observe state.source.browser) = .compute memory) :
    step observe policy tie state = .pure {state with memory} := by simp [step,boundary,computation]

theorem draw_step {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) (next : Execution.Draw → M)
    (boundary : state.source.phase = .decision)
    (random : policy state.memory state.history (observe state.source.browser) = .draw next) :
    step observe policy tie state = .draw (fun draw => .pure {state with memory := next draw}) := by
  simp [step,boundary,random]

theorem private_source_step {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) (notDecision : state.source.phase ≠ .decision) :
    step observe policy tie state =
      (ControlledExecution.step tie state.source).bind (fun source => .pure {state with source}) := by
  cases h : state.source.phase <;> simp [step,h] at *

theorem no_policy_during_source {O M : Type} (observe₁ observe₂ : Browser.State → O)
    (policy₁ policy₂ : Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (notDecision : state.source.phase ≠ .decision) :
    step observe₁ policy₁ tie state = step observe₂ policy₂ tie state := by
  rw [private_source_step observe₁ policy₁ tie state notDecision,
    private_source_step observe₂ policy₂ tie state notDecision]

private theorem bind_assoc {X Y Z : Type} (p : Execution.RandomProgram X)
    (f : X → Execution.RandomProgram Y) (g : Y → Execution.RandomProgram Z) :
    (p.bind f).bind g = p.bind (fun x => (f x).bind g) := by
  induction p with
  | pure x => rfl
  | draw next ih =>
    simp only [HittingTime.Program.bind]
    congr 1
    funext draw
    exact ih draw

theorem prefix_add {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (first more : Nat) (state : ControlledState O M) :
    runPrefix observe policy tie (first+more) state =
      (runPrefix observe policy tie first state).bind (runPrefix observe policy tie more) := by
  induction first generalizing state with
  | zero => simp [runPrefix,HittingTime.Program.bind]
  | succ first ih =>
    simp only [Nat.succ_add,runPrefix]
    rw [bind_assoc]
    apply congrArg (fun f => (step observe policy tie state).bind f)
    funext next
    exact ih next

theorem prefix_mass_one {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (fuel : Nat) (state : ControlledState O M) :
    (runPrefix observe policy tie fuel state).expect (fun _ => 1) = 1 := HittingTime.program_constant _ 1

/-- A finite sampler is embedded as private instruction memory. The initial
step stores its program without drawing or performing a game action. -/
inductive EmbeddedMemory (Memory : Type) where
  | ready (memory : Memory)
  | sampling (program : Execution.RandomProgram (Action × Memory))

def embed {O M : Type} (policy : ControlledExecution.Controller O M) : Controller O (EmbeddedMemory M) :=
  fun memory history observation => match memory with
  | .ready remembered => .compute (.sampling (policy remembered history observation))
  | .sampling (.pure (control,next)) => .action control (.ready next)
  | .sampling (.draw next) => .draw (fun draw => .sampling (next draw))

def lift {O M : Type} (state : ControlledState O M) : ControlledState O (EmbeddedMemory M) :=
  {source := state.source,memory := .ready state.memory,history := state.history}

def sampling {O M : Type} (state : ControlledState O M)
    (program : Execution.RandomProgram (Action × M)) : ControlledState O (EmbeddedMemory M) :=
  {source := state.source,memory := .sampling program,history := state.history}

def emitted {O M : Type} (observe : Browser.State → O) (state : ControlledState O M)
    (decision : Action × M) : ControlledState O (EmbeddedMemory M) := {
  source := submit state.source decision.1
  memory := .ready decision.2
  history := state.history ++ [(observe state.source.browser,decision.1)] }

theorem embedding_entry {O M : Type} (observe : Browser.State → O)
    (policy : ControlledExecution.Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (boundary : state.source.phase = .decision) :
    step observe (embed policy) tie (lift state) = .pure
      (sampling state (policy state.memory state.history (observe state.source.browser))) := by
  simp [step,embed,lift,sampling,boundary]

theorem embedding_draw {O M : Type} (observe : Browser.State → O)
    (policy : ControlledExecution.Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (next : Execution.Draw → Execution.RandomProgram (Action × M))
    (boundary : state.source.phase = .decision) :
    step observe (embed policy) tie (sampling state (.draw next)) =
      .draw (fun draw => .pure (sampling state (next draw))) := by
  simp [step,embed,sampling,boundary]

theorem embedding_action {O M : Type} (observe : Browser.State → O)
    (policy : ControlledExecution.Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (decision : Action × M) (boundary : state.source.phase = .decision) :
    step observe (embed policy) tie (sampling state (.pure decision)) =
      .pure (emitted observe state decision) := by
  rcases decision with ⟨control,memory⟩
  simp [step,embed,sampling,emitted,boundary]

/-- Variable-length private execution until this embedded finite sampler emits.
The pure and draw equations above connect each operation to the actual private
kernel. This definition inserts no input, source callback, or observed step. -/
def finishEmbedded {O M : Type} (observe : Browser.State → O) (state : ControlledState O M) :
    Execution.RandomProgram (Action × M) → Execution.RandomProgram (ControlledState O (EmbeddedMemory M))
  | .pure decision => .pure (emitted observe state decision)
  | .draw next => .draw (fun draw => finishEmbedded observe state (next draw))

theorem finite_sampler_law {O M : Type} (observe : Browser.State → O) (state : ControlledState O M)
    (program : Execution.RandomProgram (Action × M)) :
    finishEmbedded observe state program = program.bind (fun decision => .pure (emitted observe state decision)) := by
  induction program with
  | pure decision => rfl
  | draw next ih =>
    simp only [finishEmbedded,HittingTime.Program.bind]
    congr 1
    funext draw
    exact ih draw

theorem embedded_decision_law {O M : Type} (observe : Browser.State → O)
    (policy : ControlledExecution.Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (boundary : state.source.phase = .decision) :
    finishEmbedded observe state (policy state.memory state.history (observe state.source.browser)) =
      (ControlledExecution.controlledStep observe policy tie state).bind (fun next => .pure (lift next)) := by
  rw [finite_sampler_law]
  simp only [ControlledExecution.controlledStep,boundary]
  rw [bind_assoc]
  rfl

/-- The controller may diverge without emitting an action. This is allowed in
its representation and is never confused with a missing host operation. -/
def loop {O M : Type} : Controller O M := fun memory _ _ => .compute memory

theorem loop_step {O M : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O M) (boundary : state.source.phase = .decision) :
    step observe loop tie state = .pure state := by simp [step,loop,boundary]

theorem loop_prefix {O M : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O M) (boundary : state.source.phase = .decision) (fuel : Nat) :
    runPrefix observe loop tie fuel state = .pure state := by
  induction fuel with
  | zero => rfl
  | succ n ih => simp [runPrefix,loop_step observe tie state boundary,HittingTime.Program.bind,ih]

theorem loop_is_resolved {O M : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O M) (boundary : state.source.phase = .decision) :
    FullyResolved observe loop tie state := by
  intro fuel
  simp [FullyDefined,loop_prefix observe tie state boundary fuel,
    HittingTime.Program.All,ControlledExecution.unresolved,boundary]

theorem loop_capped_cost {O M : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O M) (boundary : state.source.phase = .decision) (horizon fuel : Nat) :
    expectedPrefix observe loop tie horizon fuel state (loop_is_resolved observe tie state boundary fuel) = horizon := by
  simp [expectedPrefix,loop_prefix observe tie state boundary fuel,HittingTime.Program.expect,
    ControlledExecution.cappedCost,boundary]

private theorem exists_nat_above (q : Rat) : ∃ n : Nat, q < (n : Rat) := by
  let z := q.ceil + 1
  have hceil : q ≤ (q.ceil : Rat) := Rat.le_ceil
  have hz : (q.ceil : Rat) < (z : Rat) := Rat.intCast_lt_intCast.mpr (by dsimp [z]; omega)
  have hnat : (z : Rat) ≤ (z.toNat : Rat) := Rat.intCast_le_intCast.mpr (Int.self_le_toNat z)
  exact ⟨z.toNat,by grind⟩

theorem loop_expected_infinite {O M : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O M) (boundary : state.source.phase = .decision) (bound : Rat) :
    Expected observe loop tie state (loop_is_resolved observe tie state boundary) bound := by
  obtain ⟨horizon,large⟩ := exists_nat_above bound
  refine ⟨horizon,(horizon : Rat)-bound,by grind,?_⟩
  intro fuel
  rw [loop_capped_cost observe tie state boundary]
  grind

/-- A concrete sampler with no finite draw bound at one decision. It emits the
chosen action on the next private step after a high-half IID53 draw. -/
def geometric {O : Type} (control : Action) : Controller O Bool :=
  fun ready _ _ => if ready then .action control false
    else .draw (fun draw => decide (2^52 ≤ draw.val))

def zeroDraw : Execution.Draw := ⟨0,by decide +kernel⟩

theorem geometric_draw {O : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O Bool) (boundary : state.source.phase = .decision)
    (sampling : state.memory = false) (control : Action) :
    step observe (geometric control) tie state = .draw (fun draw => .pure
      {state with memory := decide (2^52 ≤ draw.val)}) := by simp [step,geometric,boundary,sampling]

theorem geometric_no_finite_draw_bound {O : Type} (observe : Browser.State → O) (tie : DeadlineTie)
    (state : ControlledState O Bool) (boundary : state.source.phase = .decision)
    (sampling : state.memory = false) (control : Action) (fuel : Nat) :
    (runPrefix observe (geometric control) tie fuel state).Reaches state := by
  induction fuel with
  | zero => exact .pure
  | succ fuel ih =>
    rw [runPrefix,geometric_draw observe tie state boundary sampling control]
    simp only [HittingTime.Program.bind]
    apply HittingTime.Program.Reaches.draw zeroDraw
    have unchanged : {state with memory := decide (2^52 ≤ zeroDraw.val)} = state := by
      simp [zeroDraw]
      cases state
      simp_all
    simpa only [unchanged] using ih

/-- Every emitted finite-sampler leaf keeps the original source transition,
public action, and private next memory. Thus any leaf cost has the same law;
private instruction depth itself is deliberately not equated. -/
theorem embedded_cost_law {O M : Type} (observe : Browser.State → O)
    (policy : ControlledExecution.Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (boundary : state.source.phase = .decision) (value : ControlledState O M → Rat) :
    (finishEmbedded observe state (policy state.memory state.history (observe state.source.browser))).expect
      (fun next => match next.memory with
        | .ready memory => value {source := next.source,memory,history := next.history}
        | .sampling _ => 0) =
      (ControlledExecution.controlledStep observe policy tie state).expect value := by
  rw [embedded_decision_law observe policy tie state boundary]
  rw [HittingTime.program_bind_expect]
  rfl

end CookieClicker.JavaScript.PrivateController

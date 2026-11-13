import CookieClicker.JavaScriptExternalInput
import CookieClicker.RandomizedHittingTime
import CookieClicker.JavaScriptBrowserTime

/-! Controlled source execution at rational deadlines.

This composes the actual stochastic interpreter prefixes, native timer/resource
selection, and heap completion projection. Missing native input, event ordering,
and host behavior remain explicit. Fuel approximates private work; it is never
an admissible-action limit. A full native-input refinement and a full-game
attaining policy remain separate obligations.
-/
namespace CookieClicker.JavaScript.ControlledExecution
open CookieClicker.FullGame
open Execution
abbrev RandomProgram := HittingTime.Program

/-- Equal-time native task versus controller ordering is explicit. The current
adapter uses tasksFirst. This parameter is not a native priority proof. -/
inductive DeadlineTie where
  | tasksFirst | controlFirst
  deriving DecidableEq, Repr

def DeadlineTie.taskBefore (tie : DeadlineTie) (task deadline : Rat) : Bool :=
  task < deadline || (task == deadline && tie == .tasksFirst)

/-- The selection is exactly the resource/timer comparison in BrowserRuntime.
This does not erase task identities, captured callbacks, or registration order. -/
inductive NativeTask where
  | timer (timer : Browser.Timer)
  | resource (task : Browser.ResourceTask)

def NativeTask.due : NativeTask → Rat
  | .timer item => item.due
  | .resource task => task.due

def selectedTask (browser : Browser.State) : Option NativeTask :=
  match BrowserResources.nextTask browser, Browser.nextTimer browser with
  | none, none => none
  | some resource, none => some (.resource resource)
  | none, some timer => some (.timer timer)
  | some resource, some timer =>
    if resource.due < timer.due ||
      (resource.due == timer.due && resource.request.order < timer.order) then
      some (.resource resource)
    else some (.timer timer)

/-- Rendering opportunities and selection task priority are not configured by
this timer/resource selector; they must not be skipped as though absent. -/
def prepare (browser : Browser.State) : Checked Browser.State :=
  if !atBoundary browser then
    .error (.fault (.invalidContinuation "Controlled scheduling requires a returned native boundary"))
  else if !browser.animation.pending.isEmpty || browser.animation.active.isSome ||
      !browser.textSelection.pending.isEmpty || browser.textSelection.active.isSome then
    .error (.unresolved (.unsupportedSyntax
      "Rendering-event or MiscPlatformAPI event opportunity and native task ordering are not configured"))
  else BrowserResources.prepare browser

theorem prepare_conditions (browser prepared : Browser.State) (success : prepare browser = .ok prepared) :
    atBoundary browser = true ∧
    (!browser.animation.pending.isEmpty || browser.animation.active.isSome ||
      !browser.textSelection.pending.isEmpty || browser.textSelection.active.isSome) = false ∧
    BrowserResources.prepare browser = .ok prepared := by
  unfold prepare at success
  split at success
  · contradiction
  next boundary =>
    split at success
    · contradiction
    next events => exact ⟨by simpa using boundary,by simpa using events,success⟩

theorem selected_deadline (browser : Browser.State) :
    (selectedTask browser).map NativeTask.due = BrowserTime.selectedDeadline browser := by
  unfold selectedTask BrowserTime.selectedDeadline
  cases BrowserResources.nextTask browser <;> cases Browser.nextTimer browser <;>
    simp only [Option.map_none,Option.map_some,NativeTask.due]
  split <;> rfl

theorem selected_task_clock (browser prepared : Browser.State) (task : NativeTask)
    (success : prepare browser = .ok prepared) (selected : selectedTask prepared = some task) :
    (BrowserRuntime.fireNextTask browser).machine.elapsed = max browser.machine.elapsed task.due := by
  obtain ⟨boundary,events,resources⟩ := prepare_conditions browser prepared success
  have ready : Browser.taskFinished browser.machine = true := by simp_all [atBoundary]
  have timer : browser.activeTimer = none := by simp_all [atBoundary]
  have resource : browser.activeResource = none := by simp_all [atBoundary]
  have due : BrowserTime.selectedDeadline prepared = some task.due := by
    rw [←selected_deadline,selected]
    rfl
  rw [BrowserTime.fire_next_task_elapsed browser prepared ready timer resource events resources,due]

inductive WaitMode where
  | committed | interruptible
  deriving DecidableEq, Repr

inductive Phase where
  | source
  | checkpoint
  | decision
  | waiting (deadline : Rat)
  | waitingNext
  | quiescent
  | complete (time : Rat)
  | missing (failure : EvalFailure)
  | invalid (reason : String)

structure State where
  browser : Browser.State
  log : AccessLog := emptyAccessLog
  edition : String := "steam"
  phase : Phase := .source
  /-- The original player deadline survives any intervening native callbacks. -/
  resumeDeadline : Option Rat := none
  waitMode : WaitMode := .committed

/-- Entry resumes actual source initialization; no generated catalogue or
completion snapshot is substituted for the initialized heap. -/
def initial (browser : Browser.State) (edition : String := "steam") : State :=
  { browser,edition }

def checkpoint (state : State) : State :=
  match recordReturned state.browser state.edition state.log with
  | .error failure => {state with phase := .missing failure}
  | .ok (log,snapshot) =>
    {state with log,phase :=
      if FullGame.complete Pinned.requirements snapshot then .complete state.browser.machine.elapsed
      else match state.resumeDeadline with
        | none => .decision
        | some deadline => .waiting deadline}

/-- Waiting to a deadline does not execute callbacks past it. At or before it,
the actual native next-task procedure runs and the original deadline is kept. -/
def waitStep (tie : DeadlineTie) (state : State) (deadline : Rat) : State :=
  if deadline < state.browser.machine.elapsed then
    {state with phase := .invalid "A wait deadline must not precede the current elapsed time"}
  else match prepare state.browser with
  | .error failure => {state with phase := .missing failure}
  | .ok prepared =>
    match selectedTask prepared with
    | some task =>
      if tie.taskBefore task.due deadline then
        {state with
          browser := BrowserRuntime.fireNextTask state.browser
          phase := .source
          resumeDeadline := if state.waitMode == .committed then some deadline else none}
      else
        {state with
          browser := {state.browser with machine := {state.browser.machine with elapsed := deadline}}
          phase := .checkpoint
          resumeDeadline := none}
    | none =>
      {state with
        browser := {state.browser with machine := {state.browser.machine with elapsed := deadline}}
        phase := .checkpoint
        resumeDeadline := none}

/-- A reactive wait returns after one native task. With no remaining native
work it stays quiescent; this is not invented completion or a model failure. -/
def nextEventStep (state : State) : State :=
  match prepare state.browser with
  | .error failure => {state with phase := .missing failure}
  | .ok prepared => match selectedTask prepared with
    | none => {state with phase := .quiescent,resumeDeadline := none}
    | some _ => {state with
        browser := BrowserRuntime.fireNextTask state.browser
        phase := .source
        resumeDeadline := none}

/-- One private kernel step. No internal source state or free draw becomes a
controller observation. Terminal, decision, missing, and invalid states pause. -/
def step (tie : DeadlineTie) (state : State) : RandomProgram State :=
  match state.phase with
  | .source => match Execution.tick state.browser with
    | .internal next _ => .pure {state with browser := next}
    | .random next _ => .draw (fun draw => .pure {state with browser := next draw})
    | .boundary _ => .pure {state with phase := .checkpoint}
    | .missing failure => .pure {state with phase := .missing failure}
  | .checkpoint => .pure (checkpoint state)
  | .waiting deadline => .pure (waitStep tie state deadline)
  | .waitingNext => .pure (nextEventStep state)
  | _ => .pure state

def adoptSourceOutcome (state : State) : Execution.Outcome → State
  | .pending browser => {state with browser}
  | .returned browser => {state with browser,phase := .checkpoint}
  | .missing browser failure => {state with browser,phase := .missing failure}

theorem source_step_is_native_prefix (tie : DeadlineTie) (state : State)
    (source : state.phase = .source) :
    step tie state = (Execution.runPrefix 1 state.browser).bind
      (fun outcome => .pure (adoptSourceOutcome state outcome)) := by
  simp only [step,source,Execution.runPrefix]
  cases Execution.tick state.browser <;> simp [HittingTime.Program.bind,adoptSourceOutcome,source]

/-- A mathematical approximation. Exhausting this parameter leaves a pending
state; it neither advances time nor permits a policy decision mid-callback. -/
def runPrefix (tie : DeadlineTie) : Nat → State → RandomProgram State
  | 0,state => .pure state
  | fuel+1,state => (step tie state).bind (runPrefix tie fuel)

/-- Submit only at a completed source checkpoint. The deadline itself is not
rounded: fractional timer phases can change native economic execution. -/
def submitWait (state : State) (deadline : Rat) (mode : WaitMode := .committed) : State :=
  match state.phase with
  | .decision => if deadline < state.browser.machine.elapsed then
      {state with phase := .invalid "A wait deadline must not precede the current elapsed time"}
    else {state with phase := .waiting deadline,resumeDeadline := none,waitMode := mode}
  | _ => {state with phase := .invalid "A controller input requires a completed public decision boundary"}

def submitNextEvent (state : State) : State :=
  match state.phase with
  | .decision => {state with phase := .waitingNext,resumeDeadline := none}
  | _ => {state with phase := .invalid "A controller input requires a completed public decision boundary"}

/-- Raw physical inputs and both kinds of rational wait. This is a kernel
interface, not a proof that every requested physical input is native-admissible. -/
inductive Control where
  | waitUntil (deadline : Rat) (mode : WaitMode)
  | nextEvent
  | input (request : ExternalInput.Input)

def submit (state : State) : Control → State
  | .waitUntil deadline mode => submitWait state deadline mode
  | .nextEvent => submitNextEvent state
  | .input input => match state.phase with
    | .decision => match ExternalInput.inject state.browser input with
      | .error failure => {state with phase := .missing failure}
      | .ok browser => {state with browser,phase := .source,resumeDeadline := none}
    | _ => {state with phase := .invalid "A controller input requires a completed public decision boundary"}

/-- The source machine and access log stay private. Observation refinement is
an explicit argument; it is never the internal instruction count or draw tape. -/
structure ControlledState (Observation Memory : Type) where
  source : State
  memory : Memory
  history : List (Observation × Control) := []

abbrev Controller (Observation Memory : Type) :=
  RandomizedHittingTime.Controller Observation Control Memory

/-- Only a real decision phase calls the controller. All private source steps,
IID draws, scheduling and completion projection preserve its history/memory. -/
def controlledStep {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) : RandomProgram (ControlledState O M) :=
  match state.source.phase with
  | .decision => (policy state.memory state.history (observe state.source.browser)).bind fun decision =>
      .pure {
        source := submit state.source decision.1
        memory := decision.2
        history := state.history ++ [(observe state.source.browser,decision.1)]}
  | _ => (step tie state.source).bind fun source => .pure {state with source}

def runControlledPrefix {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) : Nat → ControlledState O M → RandomProgram (ControlledState O M)
  | 0,state => .pure state
  | fuel+1,state => (controlledStep observe policy tie state).bind
      (runControlledPrefix observe policy tie fuel)

/-- Missing semantics have no numerical capped value. They are not assigned a
failure penalty or silently discarded from the stochastic computation. -/
def cappedCost (horizon : Rat) (state : State) : Option Rat := match state.phase with
  | .missing _ | .invalid _ => none
  | .complete time => some (min time horizon)
  | _ => some horizon

def cappedOutcomes {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (horizon : Rat) (fuel : Nat) (state : ControlledState O M) :
    RandomProgram (Option Rat) :=
  (runControlledPrefix observe policy tie fuel state).bind fun next =>
    .pure (cappedCost horizon next.source)

/-- Expected values are used only on fully defined prefixes. Any unresolved
positive-mass leaf remains an explicit separate proof obligation. -/
def FullyDefined {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (fuel : Nat) (state : ControlledState O M) : Prop :=
  (runControlledPrefix observe policy tie fuel state).All fun next =>
    match next.source.phase with | .missing _ | .invalid _ => False | _ => True

/-- Resolution is not strategy admissibility: an unimplemented legal input
cannot be excluded from the requested optimum merely because this is unproved. -/
def FullyResolved {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) : Prop :=
  ∀ fuel, FullyDefined observe policy tie fuel state

def expectedPrefix {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (horizon fuel : Nat) (state : ControlledState O M)
    (_resolved : FullyDefined observe policy tie fuel state) : Rat :=
  (runControlledPrefix observe policy tie fuel state).expect fun next =>
    (cappedCost horizon next.source).getD 0

/-- The depth limit is private execution work, followed by an unbounded elapsed
cap. All source callbacks and decision samplers must be represented; a missing
host branch cannot receive a numerical expected-time value through this API. -/
def Expected {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M)
    (resolved : FullyResolved observe policy tie state) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧ ∀ fuel,
    bound + margin ≤ expectedPrefix observe policy tie horizon fuel state (resolved fuel)

/-- Support relation for infinite executions. Private steps and player choices
share the same composed kernel, without injecting diagnostic fuel decisions. -/
def ValidRun {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (run : Nat → ControlledState O M) : Prop :=
  ∀ n, (controlledStep observe policy tie (run n)).Reaches (run (n+1))

theorem task_before_strict (tie : DeadlineTie) {task deadline : Rat} (h : task < deadline) :
    tie.taskBefore task deadline = true := by simp [DeadlineTie.taskBefore,h]

theorem equal_tasks_first (time : Rat) :
    DeadlineTie.tasksFirst.taskBefore time time = true := by simp [DeadlineTie.taskBefore]

theorem equal_control_first (time : Rat) :
    DeadlineTie.controlFirst.taskBefore time time = false := by simp [DeadlineTie.taskBefore]

theorem selected_timer_only (browser : Browser.State) (timer : Browser.Timer)
    (r : BrowserResources.nextTask browser = none) (t : Browser.nextTimer browser = some timer) :
    selectedTask browser = some (.timer timer) := by simp [selectedTask,r,t]

theorem selected_resource_only (browser : Browser.State) (resource : Browser.ResourceTask)
    (r : BrowserResources.nextTask browser = some resource) (t : Browser.nextTimer browser = none) :
    selectedTask browser = some (.resource resource) := by simp [selectedTask,r,t]

theorem selected_resource_first (browser : Browser.State) (resource : Browser.ResourceTask) (timer : Browser.Timer)
    (r : BrowserResources.nextTask browser = some resource) (t : Browser.nextTimer browser = some timer)
    (before : resource.due < timer.due ∨ resource.due = timer.due ∧ resource.request.order < timer.order) :
    selectedTask browser = some (.resource resource) := by
  simp only [selectedTask,r,t]
  rcases before with h | ⟨h,ho⟩
  · simp [h]
  · simp [h,ho]

theorem submit_wait_preserves_heap (state : State) (deadline : Rat) (mode : WaitMode) :
    (submitWait state deadline mode).browser = state.browser := by
  unfold submitWait
  split <;> try rfl
  split <;> rfl

theorem submit_wait_exact (state : State) (deadline : Rat) (mode : WaitMode)
    (decision : state.phase = .decision) (future : state.browser.machine.elapsed ≤ deadline) :
    (submitWait state deadline mode).phase = .waiting deadline := by
  simp [submitWait,decision,show ¬deadline < state.browser.machine.elapsed by grind]

theorem wait_native_task (tie : DeadlineTie) (state : State) (deadline : Rat)
    (future : state.browser.machine.elapsed ≤ deadline) (prepared : Browser.State) (task : NativeTask)
    (ready : prepare state.browser = .ok prepared) (selected : selectedTask prepared = some task)
    (before : tie.taskBefore task.due deadline = true) :
    waitStep tie state deadline = {state with
      browser := BrowserRuntime.fireNextTask state.browser
      phase := .source
      resumeDeadline := if state.waitMode == .committed then some deadline else none} := by
  simp [waitStep,show ¬deadline < state.browser.machine.elapsed by grind,ready,selected,before]

theorem wait_step_monotone (tie : DeadlineTie) (state : State) (deadline : Rat) :
    state.browser.machine.elapsed ≤ (waitStep tie state deadline).browser.machine.elapsed := by
  unfold waitStep
  split
  · exact Rat.le_refl
  next future =>
    split
    · exact Rat.le_refl
    · split
      · split
        · exact BrowserTime.fire_next_task_monotone _
        · dsimp only
          grind
      · dsimp only
        grind

theorem wait_task_exact_time (tie : DeadlineTie) (state : State) (deadline : Rat)
    (future : state.browser.machine.elapsed ≤ deadline) (prepared : Browser.State) (task : NativeTask)
    (ready : prepare state.browser = .ok prepared) (selected : selectedTask prepared = some task)
    (before : tie.taskBefore task.due deadline = true) :
    (waitStep tie state deadline).browser.machine.elapsed = max state.browser.machine.elapsed task.due := by
  rw [wait_native_task tie state deadline future prepared task ready selected before]
  exact selected_task_clock state.browser prepared task ready selected

theorem wait_task_no_overshoot (tie : DeadlineTie) (state : State) (deadline : Rat)
    (future : state.browser.machine.elapsed ≤ deadline) (prepared : Browser.State) (task : NativeTask)
    (ready : prepare state.browser = .ok prepared) (selected : selectedTask prepared = some task)
    (before : tie.taskBefore task.due deadline = true) :
    state.browser.machine.elapsed ≤ (waitStep tie state deadline).browser.machine.elapsed ∧
      (waitStep tie state deadline).browser.machine.elapsed ≤ deadline := by
  rw [wait_task_exact_time tie state deadline future prepared task ready selected before]
  have bound : task.due ≤ deadline := by
    unfold DeadlineTie.taskBefore at before
    simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at before
    grind
  exact ⟨BrowserTime.le_max_left _ _,BrowserTime.max_le _ _ _ future bound⟩

theorem reactive_task_returns_control (tie : DeadlineTie) (state : State) (deadline : Rat)
    (future : state.browser.machine.elapsed ≤ deadline) (prepared : Browser.State) (task : NativeTask)
    (ready : prepare state.browser = .ok prepared) (selected : selectedTask prepared = some task)
    (before : tie.taskBefore task.due deadline = true) (reactive : state.waitMode = .interruptible) :
    (waitStep tie state deadline).resumeDeadline = none := by
  rw [wait_native_task tie state deadline future prepared task ready selected before]
  simp [reactive]

theorem checkpoint_reactive (state : State) (log : AccessLog) (snapshot : Snapshot)
    (read : recordReturned state.browser state.edition state.log = .ok (log,snapshot))
    (unfinished : FullGame.complete Pinned.requirements snapshot = false)
    (reactive : state.resumeDeadline = none) :
    (checkpoint state).phase = .decision := by simp [checkpoint,read,unfinished,reactive]

theorem wait_no_task (tie : DeadlineTie) (state : State) (deadline : Rat)
    (future : state.browser.machine.elapsed ≤ deadline) (prepared : Browser.State)
    (ready : prepare state.browser = .ok prepared) (empty : selectedTask prepared = none) :
    waitStep tie state deadline = {state with
      browser := {state.browser with machine := {state.browser.machine with elapsed := deadline}},
      phase := .checkpoint,resumeDeadline := none} := by
  simp [waitStep,show ¬deadline < state.browser.machine.elapsed by grind,ready,empty]

theorem wait_stops_before_task (tie : DeadlineTie) (state : State) (deadline : Rat)
    (future : state.browser.machine.elapsed ≤ deadline) (prepared : Browser.State) (task : NativeTask)
    (ready : prepare state.browser = .ok prepared) (selected : selectedTask prepared = some task)
    (afterDeadline : tie.taskBefore task.due deadline = false) :
    (waitStep tie state deadline).browser.machine.elapsed = deadline ∧
      (waitStep tie state deadline).browser.machine.heap = state.browser.machine.heap := by
  simp [waitStep,show ¬deadline < state.browser.machine.elapsed by grind,ready,selected,afterDeadline]

theorem checkpoint_preserves_browser (state : State) : (checkpoint state).browser = state.browser := by
  unfold checkpoint
  split <;> rfl

theorem next_event_monotone (state : State) :
    state.browser.machine.elapsed ≤ (nextEventStep state).browser.machine.elapsed := by
  unfold nextEventStep
  split
  · exact Rat.le_refl
  · split
    · exact Rat.le_refl
    · exact BrowserTime.fire_next_task_monotone _

theorem step_monotone (tie : DeadlineTie) (state : State) :
    (step tie state).All (fun next => state.browser.machine.elapsed ≤ next.browser.machine.elapsed) := by
  unfold step
  cases phase : state.phase with
  | source =>
    cases Execution.tick state.browser with
    | internal next same => simp [HittingTime.Program.All,same]
    | random next same => exact fun draw => by simp [HittingTime.Program.All,same draw]
    | boundary h => exact Rat.le_refl
    | missing failure => exact Rat.le_refl
  | checkpoint => simp only [HittingTime.Program.All,checkpoint_preserves_browser]; exact Rat.le_refl
  | waiting deadline => exact wait_step_monotone tie state deadline
  | waitingNext => exact next_event_monotone state
  | decision | quiescent | complete _ | missing _ | invalid _ => exact Rat.le_refl

theorem source_random_private (tie : DeadlineTie) (state : State)
    (source : state.phase = .source) (next : Draw → Browser.State)
    (same : ∀ draw, (next draw).machine.elapsed = state.browser.machine.elapsed)
    (random : Execution.tick state.browser = .random next same) :
    step tie state = .draw (fun draw => .pure {state with browser := next draw}) := by
  simp [step,source,random]

theorem checkpoint_native_projection (state : State) (log : AccessLog) (snapshot : Snapshot)
    (read : recordReturned state.browser state.edition state.log = .ok (log,snapshot)) :
    (checkpoint state).log = log := by simp [checkpoint,read]

theorem checkpoint_completed (state : State) (log : AccessLog) (snapshot : Snapshot)
    (read : recordReturned state.browser state.edition state.log = .ok (log,snapshot))
    (done : FullGame.complete Pinned.requirements snapshot = true) :
    (checkpoint state).phase = .complete state.browser.machine.elapsed := by simp [checkpoint,read,done]

theorem checkpoint_sound (state : State) (time : Rat)
    (done : (checkpoint state).phase = .complete time) :
    ∃ log snapshot, recordReturned state.browser state.edition state.log = .ok (log,snapshot) ∧
      FullGame.complete Pinned.requirements snapshot = true ∧ time = state.browser.machine.elapsed := by
  unfold checkpoint at done
  cases read : recordReturned state.browser state.edition state.log with
  | error failure => simp [read] at done
  | ok result =>
    rcases result with ⟨log,snapshot⟩
    simp only [read] at done
    split at done
    next complete => exact ⟨log,snapshot,rfl,complete,by cases done; rfl⟩
    next incomplete => cases resume : state.resumeDeadline <;> simp [resume] at done

theorem checkpoint_all_goals (state : State) (time : Rat)
    (done : (checkpoint state).phase = .complete time) :
    ∃ log snapshot, recordReturned state.browser state.edition state.log = .ok (log,snapshot) ∧
      ∀ goal ∈ FullGame.goals Pinned.requirements, FullGame.satisfies snapshot goal = true := by
  obtain ⟨log,snapshot,read,complete,_⟩ := checkpoint_sound state time done
  exact ⟨log,snapshot,read,(FullGame.complete_iff_all_goals _ _).mp complete⟩

theorem checkpoint_missing (state : State) (failure : EvalFailure)
    (read : recordReturned state.browser state.edition state.log = .error failure) :
    (checkpoint state).phase = .missing failure := by simp [checkpoint,read]

theorem step_decision (tie : DeadlineTie) (state : State) (h : state.phase = .decision) :
    step tie state = .pure state := by simp [step,h]

theorem step_complete (tie : DeadlineTie) (state : State) (time : Rat) (h : state.phase = .complete time) :
    step tie state = .pure state := by simp [step,h]

theorem step_missing (tie : DeadlineTie) (state : State) (failure : EvalFailure) (h : state.phase = .missing failure) :
    step tie state = .pure state := by simp [step,h]

theorem submit_elapsed (state : State) (control : Control) :
    (submit state control).browser.machine.elapsed = state.browser.machine.elapsed := by
  cases control with
  | waitUntil deadline mode =>
    change (submitWait state deadline mode).browser.machine.elapsed = state.browser.machine.elapsed
    exact congrArg (fun (browser : Browser.State) => browser.machine.elapsed)
      (submit_wait_preserves_heap state deadline mode)
  | nextEvent => cases h : state.phase <;> simp [submit,submitNextEvent,h]
  | input request =>
    cases h : state.phase <;> cases b : atBoundary state.browser <;> simp [submit,h,ExternalInput.inject,b]

theorem input_missing_preserves_state (state : State) (input : ExternalInput.Input)
    (decision : state.phase = .decision) (boundary : Execution.atBoundary state.browser = true) :
    submit state (.input input) = {state with phase := .missing (.unresolved (ExternalInput.requirement input).request)} := by
  simp [submit,decision,ExternalInput.inject,boundary]

theorem controlled_private {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) (notDecision : state.source.phase ≠ .decision) :
    controlledStep observe policy tie state =
      (step tie state.source).bind (fun source => .pure {state with source}) := by
  cases h : state.source.phase <;> simp [controlledStep,h] at *

theorem controller_not_called_inside_source {O M : Type} (observe₁ observe₂ : Browser.State → O)
    (policy₁ policy₂ : Controller O M) (tie : DeadlineTie) (state : ControlledState O M)
    (notDecision : state.source.phase ≠ .decision) :
    controlledStep observe₁ policy₁ tie state = controlledStep observe₂ policy₂ tie state := by
  rw [controlled_private observe₁ policy₁ tie state notDecision,controlled_private observe₂ policy₂ tie state notDecision]

theorem controlled_random_keeps_history {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M)
    (source : state.source.phase = .source) (next : Draw → Browser.State)
    (same : ∀ draw, (next draw).machine.elapsed = state.source.browser.machine.elapsed)
    (random : Execution.tick state.source.browser = .random next same) :
    controlledStep observe policy tie state = .draw (fun draw => .pure
      {state with source := {state.source with browser := next draw}}) := by
  simp [controlledStep,source,step,random,HittingTime.Program.bind]

theorem controlled_complete_absorbing {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) (time : Rat)
    (done : state.source.phase = .complete time) :
    controlledStep observe policy tie state = .pure state := by
  simp [controlledStep,step,done,HittingTime.Program.bind]

private theorem pure_reaches_eq {X : Type} (value result : X)
    (leaf : (HittingTime.Program.pure value).Reaches result) : result = value := by
  cases leaf
  rfl

theorem valid_run_complete_stable {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (run : Nat → ControlledState O M) (valid : ValidRun observe policy tie run)
    (n : Nat) (time : Rat) (done : (run n).source.phase = .complete time) (more : Nat) :
    run (n+more) = run n := by
  induction more with
  | zero => simp
  | succ more ih =>
    have leaf := valid (n+more)
    rw [ih,controlled_complete_absorbing observe policy tie (run n) time done] at leaf
    simpa [Nat.add_assoc] using pure_reaches_eq (run n) (run (n+more+1)) leaf

theorem capped_missing (horizon : Rat) (state : State) (failure : EvalFailure)
    (h : state.phase = .missing failure) : cappedCost horizon state = none := by simp [cappedCost,h]

theorem capped_unfinished_source (horizon : Rat) (state : State)
    (h : state.phase = .source) : cappedCost horizon state = some horizon := by simp [cappedCost,h]

private theorem bind_pure_all {X Y : Type} (program : RandomProgram X) (f : X → Y) (p : Y → Prop)
    (all : ∀ x, p (f x)) : (program.bind (fun x => .pure (f x))).All p := by
  induction program with
  | pure x => exact all x
  | draw next ih => exact fun draw => ih draw

theorem private_history_memory_preserved {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (state : ControlledState O M) (notDecision : state.source.phase ≠ .decision) :
    (controlledStep observe policy tie state).All (fun next =>
      next.history = state.history ∧ next.memory = state.memory) := by
  rw [controlled_private observe policy tie state notDecision]
  exact bind_pure_all _ _ _ (fun _ => ⟨rfl,rfl⟩)

theorem fully_defined_capped_leaf {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (fuel : Nat) (state next : ControlledState O M)
    (resolved : FullyDefined observe policy tie fuel state)
    (reachable : (runControlledPrefix observe policy tie fuel state).Reaches next) (horizon : Rat) :
    (cappedCost horizon next.source).isSome = true := by
  have good := HittingTime.program_all_reaches _ _ resolved next reachable
  cases h : next.source.phase <;> simp [cappedCost,h] at *

private theorem bind_associative {X Y Z : Type} (p : RandomProgram X) (f : X → RandomProgram Y) (g : Y → RandomProgram Z) :
    (p.bind f).bind g = p.bind (fun x => (f x).bind g) := by
  induction p with
  | pure x => rfl
  | draw next ih =>
    simp only [HittingTime.Program.bind]
    congr 1
    funext draw
    exact ih draw

theorem prefix_add (tie : DeadlineTie) (first more : Nat) (state : State) :
    runPrefix tie (first+more) state = (runPrefix tie first state).bind (runPrefix tie more) := by
  induction first generalizing state with
  | zero => simp [runPrefix,HittingTime.Program.bind]
  | succ first ih =>
    simp only [Nat.succ_add,runPrefix]
    rw [bind_associative]
    apply congrArg (fun f => (step tie state).bind f)
    funext next
    exact ih next

theorem controlled_prefix_add {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (first more : Nat) (state : ControlledState O M) :
    runControlledPrefix observe policy tie (first+more) state =
      (runControlledPrefix observe policy tie first state).bind (runControlledPrefix observe policy tie more) := by
  induction first generalizing state with
  | zero => simp [runControlledPrefix,HittingTime.Program.bind]
  | succ first ih =>
    simp only [Nat.succ_add,runControlledPrefix]
    rw [bind_associative]
    apply congrArg (fun f => (controlledStep observe policy tie state).bind f)
    funext next
    exact ih next

theorem controlled_prefix_mass_one {O M : Type} (observe : Browser.State → O) (policy : Controller O M)
    (tie : DeadlineTie) (fuel : Nat) (state : ControlledState O M) :
    (runControlledPrefix observe policy tie fuel state).expect (fun _ => 1) = 1 := HittingTime.program_constant _ 1

theorem prefix_mass_one (tie : DeadlineTie) (fuel : Nat) (state : State) :
    (runPrefix tie fuel state).expect (fun _ => 1) = 1 := HittingTime.program_constant _ 1

/-- Unknown host work is never assigned infinite completion time as though it
were a genuine noncompleting game path. -/
def unresolved (state : State) : Bool := match state.phase with
  | .missing _ | .invalid _ => true
  | _ => false

def completed (state : State) : Option Rat := match state.phase with
  | .complete time => some time
  | _ => none

inductive Cost where
  | finite (time : Rat)
  | infinity
  deriving DecidableEq, Repr

/-- Runs are infinite prefix chains. Their transition validity is a separate
relation; this functional gives infinite cost to every resolved noncompletion,
including internal divergence and Zeno action sequences. -/
def firstThrough (run : Nat → State) : Nat → Option Rat
  | 0 => completed (run 0)
  | n+1 => (firstThrough run n).or (completed (run (n+1)))

noncomputable def hittingCost (run : Nat → State) : Option Cost := by
  classical
  exact if ∃ n, unresolved (run n) = true then none
  else if done : ∃ n, (completed (run n)).isSome = true then
    some (.finite ((firstThrough run (Classical.choose done)).getD 0))
  else some .infinity

theorem first_through_has_witness (run : Nat → State) (n : Nat) (time : Rat)
    (found : firstThrough run n = some time) :
    ∃ i, i ≤ n ∧ completed (run i) = some time := by
  induction n with
  | zero => exact ⟨0,Nat.le_refl _,found⟩
  | succ n ih =>
    cases previous : firstThrough run n with
    | none =>
      have last : completed (run (n+1)) = some time := by simpa [firstThrough,previous] using found
      exact ⟨n+1,Nat.le_refl _,last⟩
    | some before =>
      have equal : before = time := by simpa [firstThrough,previous] using found
      subst before
      obtain ⟨i,bound,hit⟩ := ih previous
      exact ⟨i,Nat.le_trans bound (Nat.le_succ _),hit⟩

theorem first_through_some (run : Nat → State) (n : Nat)
    (done : (completed (run n)).isSome = true) : (firstThrough run n).isSome = true := by
  cases n with
  | zero => exact done
  | succ n =>
    cases previous : firstThrough run n <;> simp [firstThrough,previous,done]

theorem finite_cost_has_native_checkpoint (run : Nat → State) (time : Rat)
    (finite : hittingCost run = some (.finite time)) : ∃ i, completed (run i) = some time := by
  classical
  unfold hittingCost at finite
  split at finite
  · contradiction
  next resolved =>
    split at finite
    · rename_i done
      have existsValue := first_through_some run (Classical.choose done) (Classical.choose_spec done)
      cases read : firstThrough run (Classical.choose done) with
      | none => simp [read] at existsValue
      | some value =>
        have equal : value = time := by simpa [read] using finite
        subst value
        obtain ⟨i,_,hit⟩ := first_through_has_witness run (Classical.choose done) time read
        exact ⟨i,hit⟩
    · simp at finite

theorem missing_has_no_cost (run : Nat → State) (n : Nat) (h : unresolved (run n) = true) :
    hittingCost run = none := by simp [hittingCost,show ∃ n, unresolved (run n) = true from ⟨n,h⟩]

theorem never_complete_cost (run : Nat → State)
    (resolved : ∀ n, unresolved (run n) = false) (unfinished : ∀ n, completed (run n) = none) :
    hittingCost run = some .infinity := by
  simp [hittingCost,resolved,unfinished]

/-- No lower bound on elapsed increments is assumed. Finite accumulated time
cannot give a finite completion cost to a path that never completes. -/
theorem zeno_noncompletion_cost (run : Nat → State) (bound : Rat)
    (_bounded : ∀ n, (run n).browser.machine.elapsed ≤ bound)
    (resolved : ∀ n, unresolved (run n) = false) (unfinished : ∀ n, completed (run n) = none) :
    hittingCost run = some .infinity := never_complete_cost run resolved unfinished

end CookieClicker.JavaScript.ControlledExecution

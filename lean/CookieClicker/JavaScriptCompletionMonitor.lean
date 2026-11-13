import CookieClicker.JavaScriptPrivateController

/-! Private completion checks at source microstates.
The monitor reads data descriptors without running getters or changing the heap.
Known absent startup fields are distinct from unknown host behavior. Recording a
first hit creates no controller observation or mid-callback input opportunity.
-/
namespace CookieClicker.JavaScript.CompletionMonitor
open CookieClicker.FullGame

private def problem (operation : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Completion monitor: " ++ operation)))

/-- Access history needs only the named upgrade. It does not require that the
rest of the catalogue or the minigames have finished initialization. -/
def currentAccess (heap : Heap) (game : Value) (name : String) : Checked Bool := do
  if game == .undefined then pure false
  else
    let table ← Completion.field heap game "Upgrades"
    if table == .undefined then pure false
    else
      let .object tableId := table | problem "upgrade table is not an object"
      let object ← checkedObject heap tableId
      let key := JSString.ofString name
      if object.unresolvedOwnNames.contains key then problem "unknown upgrade descriptor"
      else match ownProperty object key with
      | none => if object.propertiesComplete then pure false else problem "incomplete upgrade table"
      | some (.accessor _ _ _ _) => problem "upgrade entry uses an accessor"
      | some (.data item _ enumerable _) =>
        if !enumerable then pure false
        else
          let .object _ := item | problem "upgrade entry is not an object"
          let actual ← Completion.field heap item "name"
          if actual != .string key then pure false
          else
            let bought ← Completion.field heap item "bought"
            let unlocked ← Completion.field heap item "unlocked"
            pure (Completion.nativeFlag bought || Completion.nativeFlag unlocked)

theorem absent_game_has_no_access (heap : Heap) (name : String) :
    currentAccess heap .undefined name = .ok false := by
  simp [currentAccess,pure,Except.pure]

theorem absent_table_has_no_access (heap : Heap) (game : Value) (name : String)
    (absent : Completion.field heap game "Upgrades" = .ok .undefined) :
    currentAccess heap game name = .ok false := by
  unfold currentAccess
  split
  · rfl
  · simp [absent,bind,Except.bind,pure,Except.pure]

/-- Each retained bit includes its actual descriptor read. An unknown read
cannot enter this log as a false bit. -/
structure Entry where
  state : Browser.State
  game : Value
  name : String
  value : Bool
  root : Execution.gameRoot state = .ok game
  read : currentAccess state.machine.heap game name = .ok value

abbrev Log := List Entry

def history (log : Log) : Completion.AccessHistory :=
  fun name => log.any (fun entry => entry.name == name && entry.value)

theorem history_has_source_witness (log : Log) (name : String)
    (access : history log name = true) :
    ∃ entry ∈ log, entry.name = name ∧
      Execution.gameRoot entry.state = .ok entry.game ∧
      currentAccess entry.state.machine.heap entry.game name = .ok true := by
  obtain ⟨entry,mem,hit⟩ := List.any_eq_true.mp access
  have both : entry.name=name ∧ entry.value=true := by simpa using hit
  have equal := both.1
  have value := both.2
  exact ⟨entry,mem,equal,entry.root,by simpa [equal,value] using entry.read⟩

theorem history_retained (log : Log) (entry : Entry) (name : String)
    (access : history log name=true) : history (entry::log) name=true := by
  simp [history,List.any_cons,show log.any (fun item => item.name == name && item.value)=true from access]

def scan (state : Browser.State) (game : Value)
    (root : Execution.gameRoot state = .ok game) : List String → Log → Checked Log
  | [],log => .ok log
  | name::names,log =>
    match read : currentAccess state.machine.heap game name with
    | .error failure => .error failure
    | .ok value => scan state game root names (⟨state,game,name,value,root,read⟩::log)

theorem scan_extends (state : Browser.State) (game : Value)
    (root : Execution.gameRoot state = .ok game) (names : List String) (before after : Log)
    (scanned : scan state game root names before = .ok after) :
    ∃ added, after=added++before ∧ ∀ entry ∈ added, entry.state=state := by
  induction names generalizing before after with
  | nil =>
    have equal : before=after := Except.ok.inj scanned
    subst after
    exact ⟨[],rfl,by simp⟩
  | cons name names ih =>
    simp only [scan] at scanned
    split at scanned
    · contradiction
    next value read =>
      obtain ⟨added,equal,origin⟩ := ih _ _ scanned
      refine ⟨added++[⟨state,game,name,value,root,read⟩],?_,?_⟩
      · simpa [List.append_assoc] using equal
      · intro entry member
        rcases List.mem_append.mp member with old | fresh
        · exact origin entry old
        · simpa using congrArg Entry.state (List.mem_singleton.mp fresh)

theorem scan_preserves_access (state : Browser.State) (game : Value)
    (root : Execution.gameRoot state = .ok game) (names : List String) (before after : Log)
    (scanned : scan state game root names before = .ok after) (name : String)
    (access : history before name=true) : history after name=true := by
  obtain ⟨added,equal,_⟩ := scan_extends state game root names before after scanned
  rw [equal]
  simp [history,List.any_append,show before.any (fun entry => entry.name == name && entry.value)=true from access]

/-- Completion is checked after recording access at this same source state.
The counter gate has a proof that its false branch excludes completion. -/
def probe (state : Browser.State) (edition : String) (log : Log) : Checked (Log × Bool) :=
  match root : Execution.gameRoot state with
  | .error failure => .error failure
  | .ok game => do
    let log ← scan state game root Pinned.requirements.accessUpgrades log
    if ← Completion.counterEligible state.machine.heap game then
      pure (log,← Completion.complete state.machine.heap game edition (history log))
    else pure (log,false)

theorem probe_extends (state : Browser.State) (edition : String) (before after : Log) (done : Bool)
    (checked : probe state edition before = .ok (after,done)) :
    ∃ added, after=added++before ∧ ∀ entry ∈ added, entry.state=state := by
  unfold probe at checked
  split at checked
  · contradiction
  next game root =>
    simp only [bind,Except.bind,pure,Except.pure] at checked
    repeat first
      | contradiction
      | split at checked
      | (cases checked; exact scan_extends state game root _ _ _ (by assumption))

theorem probe_completed (state : Browser.State) (edition : String) (before after : Log)
    (hit : probe state edition before = .ok (after,true)) :
    ∃ game, Execution.gameRoot state = .ok game ∧
      Completion.complete state.machine.heap game edition (history after) = .ok true := by
  unfold probe at hit
  split at hit
  · contradiction
  next game root =>
    simp only [bind,Except.bind,pure,Except.pure] at hit
    repeat first
      | contradiction
      | (have wrong : false=true := congrArg Prod.snd (Except.ok.inj hit); cases wrong)
      | split at hit
      | (cases hit; exact ⟨game,root,by assumption⟩)

theorem probe_has_all_goals (state : Browser.State) (edition : String) (before after : Log)
    (hit : probe state edition before = .ok (after,true)) :
    ∃ game projected, Execution.gameRoot state = .ok game ∧
      Completion.snapshot state.machine.heap game edition (history after) = .ok projected ∧
      ∀ goal ∈ FullGame.goals Pinned.requirements, satisfies projected goal = true := by
  obtain ⟨game,root,done⟩ := probe_completed state edition before after hit
  obtain ⟨projected,read,all⟩ := Completion.completion_has_all_goals _ _ _ _ done
  exact ⟨game,projected,root,read,all⟩

theorem probe_incomplete (state : Browser.State) (edition : String) (before after : Log)
    (miss : probe state edition before = .ok (after,false)) :
    ∃ game, Execution.gameRoot state = .ok game ∧
      Completion.complete state.machine.heap game edition (history after) ≠ .ok true := by
  unfold probe at miss
  split at miss
  · contradiction
  next game root =>
    simp only [bind,Except.bind,pure,Except.pure] at miss
    split at miss
    · contradiction
    next log scanned =>
      split at miss
      · contradiction
      next eligible gate =>
        split at miss
        · split at miss
          · contradiction
          next flag checked =>
            have pair := Except.ok.inj miss
            have same := congrArg Prod.fst pair
            have flagFalse := congrArg Prod.snd pair
            change log=after at same
            change flag=false at flagFalse
            subst after
            subst flag
            exact ⟨game,root,by rw [checked]; intro impossible; cases impossible⟩
        next notEligible =>
          have same := congrArg Prod.fst (Except.ok.inj miss)
          change log=after at same
          subst after
          have no : eligible=false := by cases eligible <;> simp_all
          exact ⟨game,root,Completion.ineligible_not_complete _ _ _ _ (by simpa [no] using gate)⟩

structure State (Observation Memory : Type) where
  controlled : ControlledExecution.ControlledState Observation Memory
  log : Log := []

def initial {O M : Type} (browser : Browser.State) (memory : M) (edition : String := "steam") : State O M :=
  { controlled := { source := ControlledExecution.initial browser edition, memory } }

/-- The old returned-boundary projection is replaced here. All source steps,
waits and private decision computations still use their actual existing kernel.
This branch creates a decision only after the source has returned. -/
def advance {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) : Execution.RandomProgram (State O M) :=
  match state.controlled.source.phase with
  | .checkpoint => .pure {state with controlled := {state.controlled with source :=
      {state.controlled.source with phase := match state.controlled.source.resumeDeadline with
        | none => .decision
        | some deadline => .waiting deadline}}}
  | _ => (PrivateController.step observe policy tie state.controlled).bind
      (fun controlled => .pure {state with controlled})

def setPhase {O M : Type} (state : State O M) (phase : ControlledExecution.Phase) : State O M :=
  {state with controlled := {state.controlled with source := {state.controlled.source with phase}}}

/-- A source microstate is checked before its next transition. A true check
records the first hit and stops this cost computation, not the native event loop
or a user callback. It grants no action at that private state. -/
def step {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) : Execution.RandomProgram (State O M) :=
  match state.controlled.source.phase with
  | .complete _ | .missing _ | .invalid _ => .pure state
  | _ => match probe state.controlled.source.browser state.controlled.source.edition state.log with
    | .error failure => .pure (setPhase state (.missing failure))
    | .ok (log,true) => .pure (setPhase {state with log} (.complete state.controlled.source.browser.machine.elapsed))
    | .ok (log,false) => advance observe policy tie {state with log}

def runPrefix {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) : Nat → State O M → Execution.RandomProgram (State O M)
  | 0,state => .pure state
  | fuel+1,state => (step observe policy tie state).bind (runPrefix observe policy tie fuel)

def live {O M : Type} (state : State O M) : Bool := match state.controlled.source.phase with
  | .complete _ | .missing _ | .invalid _ => false
  | _ => true

theorem first_hit_step {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) (log : Log)
    (active : live state=true)
    (hit : probe state.controlled.source.browser state.controlled.source.edition state.log = .ok (log,true)) :
    step observe policy tie state =
      .pure (setPhase {state with log} (.complete state.controlled.source.browser.machine.elapsed)) := by
  cases phase : state.controlled.source.phase <;> simp [live,phase] at active <;> simp [step,phase,hit]

theorem first_hit_preserves_source {O M : Type} (state : State O M) (log : Log) :
    (setPhase {state with log} (.complete state.controlled.source.browser.machine.elapsed)).controlled.source.browser =
      state.controlled.source.browser := rfl

theorem first_hit_preserves_information {O M : Type} (state : State O M) (log : Log) :
    (setPhase {state with log} (.complete state.controlled.source.browser.machine.elapsed)).controlled.history = state.controlled.history ∧
    (setPhase {state with log} (.complete state.controlled.source.browser.machine.elapsed)).controlled.memory = state.controlled.memory := ⟨rfl,rfl⟩

theorem complete_step_stable {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) (time : Rat)
    (done : state.controlled.source.phase = .complete time) : step observe policy tie state=.pure state := by
  simp [step,done]

theorem complete_prefix_stable {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) (time : Rat) (fuel : Nat)
    (done : state.controlled.source.phase = .complete time) : runPrefix observe policy tie fuel state=.pure state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [runPrefix,complete_step_stable observe policy tie state time done,HittingTime.Program.bind,ih]

theorem first_hit_persists {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) (log : Log) (fuel : Nat)
    (active : live state=true)
    (hit : probe state.controlled.source.browser state.controlled.source.edition state.log = .ok (log,true)) :
    runPrefix observe policy tie (fuel+1) state=
      .pure (setPhase {state with log} (.complete state.controlled.source.browser.machine.elapsed)) := by
  rw [runPrefix,first_hit_step observe policy tie state log active hit]
  exact complete_prefix_stable observe policy tie _ _ fuel rfl

theorem source_does_not_query_policy {O M : Type} (observe₁ observe₂ : Browser.State → O)
    (policy₁ policy₂ : PrivateController.Controller O M) (tie : ControlledExecution.DeadlineTie)
    (state : State O M) (source : state.controlled.source.phase = .source) :
    step observe₁ policy₁ tie state=step observe₂ policy₂ tie state := by
  simp only [step,source]
  split
  · rfl
  · rfl
  · simp [advance,source,PrivateController.step]

theorem unresolved_probe_retained {O M : Type} (observe : Browser.State → O)
    (policy : PrivateController.Controller O M) (tie : ControlledExecution.DeadlineTie)
    (state : State O M) (failure : EvalFailure) (active : live state=true)
    (unknown : probe state.controlled.source.browser state.controlled.source.edition state.log = .error failure) :
    step observe policy tie state=.pure (setPhase state (.missing failure)) := by
  cases phase : state.controlled.source.phase <;> simp [live,phase] at active <;> simp [step,phase,unknown]

theorem missing_has_no_cost {O M : Type} (state : State O M) (failure : EvalFailure) (horizon : Rat) :
    ControlledExecution.cappedCost horizon (setPhase state (.missing failure)).controlled.source=none := rfl

/-- Every newly recorded state is the source state of this actual transition.
The controller cannot supply an access-history entry. -/
def ExtendsFrom {O M : Type} (before after : State O M) : Prop :=
  ∃ added, after.log=added++before.log ∧
    ∀ entry ∈ added, entry.state=before.controlled.source.browser

theorem unchanged_log_extends {O M : Type} (before after : State O M) (same : after.log=before.log) :
    ExtendsFrom before after := ⟨[],by simpa using same,by simp⟩

private theorem all_lifted {X Y : Type} (program : Execution.RandomProgram X)
    (f : X → Y) (predicate : Y → Prop) (holds : ∀ x, predicate (f x)) :
    (program.bind (fun x => .pure (f x))).All predicate := by
  induction program with
  | pure value => exact holds value
  | draw next ih => exact fun draw => ih draw

private theorem all_mono {X : Type} (program : Execution.RandomProgram X) (P Q : X → Prop)
    (holds : program.All P) (implies : ∀ x, P x → Q x) : program.All Q := by
  induction program with
  | pure value => exact implies value holds
  | draw next ih => exact fun draw => ih draw (holds draw)

theorem advance_preserves_log {O M : Type} (observe : Browser.State → O)
    (policy : PrivateController.Controller O M) (tie : ControlledExecution.DeadlineTie) (state : State O M) :
    (advance observe policy tie state).All (fun next => next.log=state.log) := by
  unfold advance
  split
  · rfl
  · exact all_lifted _ _ _ (fun _ => rfl)

theorem step_log_origin {O M : Type} (observe : Browser.State → O)
    (policy : PrivateController.Controller O M) (tie : ControlledExecution.DeadlineTie) (state : State O M) :
    (step observe policy tie state).All (ExtendsFrom state) := by
  unfold step
  split <;> try exact unchanged_log_extends _ _ rfl
  split
  · exact unchanged_log_extends _ _ rfl
  next log checked => exact probe_extends _ _ _ _ true checked
  next log checked =>
    obtain ⟨added,equal,origin⟩ := probe_extends _ _ _ _ false checked
    have preserved := advance_preserves_log observe policy tie {state with log}
    exact all_mono _ _ _ preserved (fun next same => ⟨added,same.trans equal,origin⟩)

def ValidRun {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (run : Nat → State O M) : Prop :=
  ∀ n, (step observe policy tie (run n)).Reaches (run (n+1))

theorem recorded_state_was_visited {O M : Type} (observe : Browser.State → O)
    (policy : PrivateController.Controller O M) (tie : ControlledExecution.DeadlineTie)
    (run : Nat → State O M) (valid : ValidRun observe policy tie run)
    (empty : (run 0).log=[]) (n : Nat) (entry : Entry) (recorded : entry ∈ (run n).log) :
    ∃ k, k<n ∧ entry.state=(run k).controlled.source.browser := by
  induction n with
  | zero => simp [empty] at recorded
  | succ n ih =>
    obtain ⟨added,equal,origin⟩ := HittingTime.program_all_reaches _ _
      (step_log_origin observe policy tie (run n)) _ (valid n)
    rw [equal] at recorded
    rcases List.mem_append.mp recorded with fresh | old
    · exact ⟨n,Nat.lt_succ_self n,origin entry fresh⟩
    · obtain ⟨k,before,seen⟩ := ih old
      exact ⟨k,Nat.lt_trans before (Nat.lt_succ_self n),seen⟩

theorem historical_access_was_real {O M : Type} (observe : Browser.State → O)
    (policy : PrivateController.Controller O M) (tie : ControlledExecution.DeadlineTie)
    (run : Nat → State O M) (valid : ValidRun observe policy tie run)
    (empty : (run 0).log=[]) (n : Nat) (name : String) (access : history (run n).log name=true) :
    ∃ k game, k<n ∧ Execution.gameRoot (run k).controlled.source.browser=.ok game ∧
      currentAccess (run k).controlled.source.browser.machine.heap game name=.ok true := by
  obtain ⟨entry,recorded,_,root,read⟩ := history_has_source_witness (run n).log name access
  obtain ⟨k,before,seen⟩ := recorded_state_was_visited observe policy tie run valid empty n entry recorded
  exact ⟨k,entry.game,before,by simpa [seen] using root,by simpa [seen] using read⟩

theorem prefix_mass_one {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (fuel : Nat) (state : State O M) :
    (runPrefix observe policy tie fuel state).expect (fun _ => 1)=1 := HittingTime.program_constant _ 1

def FullyDefined {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (fuel : Nat) (state : State O M) : Prop :=
  (runPrefix observe policy tie fuel state).All fun next => ControlledExecution.unresolved next.controlled.source=false

def FullyResolved {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M) : Prop :=
  ∀ fuel, FullyDefined observe policy tie fuel state

def expectedPrefix {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (horizon fuel : Nat) (state : State O M)
    (_resolved : FullyDefined observe policy tie fuel state) : Rat :=
  (runPrefix observe policy tie fuel state).expect fun next =>
    (ControlledExecution.cappedCost horizon next.controlled.source).getD 0

def Expected {O M : Type} (observe : Browser.State → O) (policy : PrivateController.Controller O M)
    (tie : ControlledExecution.DeadlineTie) (state : State O M)
    (resolved : FullyResolved observe policy tie state) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧ ∀ fuel,
    bound + margin ≤ expectedPrefix observe policy tie horizon fuel state (resolved fuel)

end CookieClicker.JavaScript.CompletionMonitor

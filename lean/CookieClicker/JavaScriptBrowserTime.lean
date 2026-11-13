import CookieClicker.JavaScriptBrowserRuntime

/-! Elapsed-time laws for the actual browser task dispatcher. Private source
work does not advance time; the selected timer or resource deadline does. -/
namespace CookieClicker.JavaScript.BrowserTime
open Browser
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

theorem fail_elapsed (state : State) (failure : EvalFailure) :
    (Browser.fail state failure).machine.elapsed=state.machine.elapsed := by
  cases failure <;> rfl

theorem checked_elapsed (state : State) (value : Checked α) (next : α → State)
    (preserves : ∀ value, (next value).machine.elapsed=state.machine.elapsed) :
    (Browser.checked state value next).machine.elapsed=state.machine.elapsed := by
  cases value <;> simp [Browser.checked,fail_elapsed,preserves]

theorem checked_elapsed_of_success (state : State) (value : Checked α) (next : α → State)
    (preserves : ∀ result, value=.ok result → (next result).machine.elapsed=state.machine.elapsed) :
    (Browser.checked state value next).machine.elapsed=state.machine.elapsed := by
  cases found : value with
  | error failure => exact fail_elapsed state failure
  | ok result => exact preserves result found

theorem finish_timer_elapsed (state : State) :
    (Browser.finishTimer state).machine.elapsed=state.machine.elapsed := by
  unfold Browser.finishTimer
  split
  · rfl
  · split <;> rfl

theorem finish_timer_timers (state : State) :
    (Browser.finishTimer state).timers=state.timers := by
  unfold Browser.finishTimer
  split
  · rfl
  · split <;> rfl

theorem fire_timer_elapsed (state : State)
    (ready : Browser.taskFinished state.machine=true) (resources : state.resourceRequests=[])
    (timer : Timer) (selected : Browser.nextTimer state=some timer) :
    (Browser.fireNextTimer state).machine.elapsed=max state.machine.elapsed timer.due := by
  have same : Browser.nextTimer (Browser.finishTimer state)=Browser.nextTimer state := by
    simp only [Browser.nextTimer,finish_timer_timers]
  simp only [Browser.fireNextTimer,ready,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    resources,List.isEmpty_nil,same,selected]
  exact congrArg (fun time=>max time timer.due) (finish_timer_elapsed state)

theorem fire_timer_monotone (state : State) :
    state.machine.elapsed≤(Browser.fireNextTimer state).machine.elapsed := by
  unfold Browser.fireNextTimer
  split
  · exact Rat.le_refl
  · split
    · exact Rat.le_refl
    · dsimp only
      split
      · rw [finish_timer_elapsed]; exact Rat.le_refl
      · change state.machine.elapsed≤max (Browser.finishTimer state).machine.elapsed _
        rw [finish_timer_elapsed]
        rw [Rat.max_def]
        split
        · assumption
        · exact Rat.le_refl

theorem prepare_elapsed (state next : State) (success : BrowserResources.prepare state=.ok next) :
    next.machine.elapsed=state.machine.elapsed := by
  simp only [BrowserResources.prepare,bind,Except.bind,pure,Except.pure] at success
  split at success
  · contradiction
  · cases success
    rfl


theorem checked_fold_elapsed (f : State → α → Checked State)
    (preserves : ∀ before item after, f before item=.ok after → after.machine.elapsed=before.machine.elapsed)
    (items : List α) (state next : State) (success : items.foldlM f state=.ok next) :
    next.machine.elapsed=state.machine.elapsed := by
  induction items generalizing state with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at success
    cases success
    rfl
  | cons item items ih =>
    simp only [List.foldlM_cons,bind,Except.bind] at success
    cases found : f state item with
    | error failure => rw [found] at success; cases success
    | ok after =>
      rw [found] at success
      exact (ih after success).trans (preserves state item after found)

theorem replace_node_elapsed (state next : State) (id : Nat) (node : Node)
    (success : Browser.replaceNode state id node=.ok next) :
    next.machine.elapsed=state.machine.elapsed := by
  unfold Browser.replaceNode at success
  simp only [bind,Except.bind] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · split at success
      · contradiction
      · apply (checked_fold_elapsed _ ?_ _ _ _ success).trans
        · rfl
        · intro before index after read
          change ((do
            let node ← checkedNode before index
            if node.kind != .element "textarea" || node.textarea.dirty then pure before else
            let text ← node.children.foldlM (fun text child => do
              let child ← checkedNode before child
              pure (text ++ (match child.kind with | .text value => value | _ => []))) []
            let updated := {node with textarea := TextControl.childrenChanged node.textarea text}
            pure {before with nodes:=before.nodes.set! index updated}) : Checked State)=.ok after at read
          simp only [bind,Except.bind,pure,Except.pure] at read
          split at read
          · contradiction
          · split at read
            · cases read; rfl
            · split at read
              · contradiction
              · cases read; rfl

theorem allocate_event_elapsed (state next : State) (kind : JSString) (target value : Value)
    (success : BrowserEventData.allocateEvent state kind target=.ok (value,next)) :
    next.machine.elapsed=state.machine.elapsed := by
  unfold BrowserEventData.allocateEvent at success
  simp only [bind,Except.bind,pure,Except.pure] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · split at success
      · contradiction
      · cases success; rfl

theorem dispatch_elapsed (state : State) (target : Value) (arguments : List Value) (trusted : Bool) :
    (BrowserEvents.dispatchEvent state target arguments trusted).machine.elapsed=state.machine.elapsed := by
  unfold BrowserEvents.dispatchEvent
  apply checked_elapsed
  intro target
  split
  · exact fail_elapsed _ _
  · apply checked_elapsed
    intro id
    apply checked_elapsed
    intro event
    split
    · exact fail_elapsed _ _
    · split
      · rfl
      · apply checked_elapsed
        intro path
        apply checked_elapsed
        intro requireCancel
        apply checked_elapsed
        intro targetValue
        rfl

theorem begin_trusted_elapsed (state : State) (target : Value) (kind : JSString) :
    (BrowserEvents.beginTrusted state target kind).machine.elapsed=state.machine.elapsed := by
  unfold BrowserEvents.beginTrusted
  apply checked_elapsed_of_success
  intro result found
  exact (dispatch_elapsed result.2 target [result.1] true).trans
    (allocate_event_elapsed state result.2 kind .null result.1 found)

theorem begin_callback_elapsed (state : State) (task : ResourceTask) (kind : JSString) :
    (BrowserResources.beginCallback state task kind).machine.elapsed=state.machine.elapsed := by
  unfold BrowserResources.beginCallback
  apply checked_elapsed
  intro node
  apply checked_elapsed
  intro _
  exact begin_trusted_elapsed _ _ _

theorem fire_resource_elapsed (state : State) (task : ResourceTask) :
    (BrowserResources.fire state task).machine.elapsed=state.machine.elapsed := by
  unfold BrowserResources.fire
  apply checked_elapsed
  intro current
  split
  · rfl
  · apply checked_elapsed
    intro path
    apply checked_elapsed
    intro node
    split
    · split
      · rfl
      · apply checked_elapsed_of_success
        intro next found
        change next.machine.elapsed=state.machine.elapsed
        exact replace_node_elapsed state next _ _ found
    · split
      · rfl
      · apply checked_elapsed_of_success
        intro next found
        exact (begin_callback_elapsed _ _ _).trans (replace_node_elapsed _ _ _ _ found)


theorem le_max_left (a b : Rat) : a≤max a b := by
  rw [Rat.max_def]
  split
  · assumption
  · exact Rat.le_refl

theorem max_le (a b c : Rat) (left : a≤c) (right : b≤c) : max a b≤c := by
  rw [Rat.max_def]
  split <;> assumption

theorem prepare_shape (state next : State) (success : BrowserResources.prepare state=.ok next) :
    ∃ tasks, next={state with resourceRequests:=[],resourceTasks:=state.resourceTasks++tasks} := by
  simp only [BrowserResources.prepare,bind,Except.bind,pure,Except.pure] at success
  split at success
  · contradiction
  · cases success
    exact ⟨_,rfl⟩

theorem prepare_empty (state : State) (empty : state.resourceRequests=[]) :
    BrowserResources.prepare state=.ok state := by
  simp only [BrowserResources.prepare,empty,List.filterMapM_nil,bind,Except.bind,pure,Except.pure,List.append_nil]
  rw [←empty]

theorem finish_resource_elapsed (state : State) :
    (BrowserResources.finish state).machine.elapsed=state.machine.elapsed := by
  unfold BrowserResources.finish
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · rfl
        · exact begin_callback_elapsed _ _ _
      · split <;> rfl

theorem finish_resource_idle (state : State) (idle : state.activeResource=none) :
    BrowserResources.finish state=state := by
  simp only [BrowserResources.finish,idle]
  split <;> rfl

theorem finish_timer_idle (state : State) (idle : state.activeTimer=none) :
    Browser.finishTimer state=state := by
  simp only [Browser.finishTimer,idle]
  split <;> rfl

theorem fire_resource_selected (state : State) (task : ResourceTask)
    (ready : Browser.taskFinished state.machine=true) (idle : state.activeResource=none)
    (requests : state.resourceRequests=[]) (selected : BrowserResources.nextTask state=some task) :
    (BrowserResources.fireNextTask state).machine.elapsed=max state.machine.elapsed task.due := by
  simp only [BrowserResources.fireNextTask,ready,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    finish_resource_idle state idle,prepare_empty state requests,Browser.checked,selected]
  exact fire_resource_elapsed _ _

theorem checked_monotone (state : State) (value : Checked α) (next : α → State)
    (preserves : ∀ result, value=.ok result → state.machine.elapsed≤(next result).machine.elapsed) :
    state.machine.elapsed≤(Browser.checked state value next).machine.elapsed := by
  cases found : value with
  | error failure => rw [Browser.checked,fail_elapsed]; exact Rat.le_refl
  | ok result => exact preserves result found

theorem fire_next_resource_monotone (state : State) :
    state.machine.elapsed≤(BrowserResources.fireNextTask state).machine.elapsed := by
  unfold BrowserResources.fireNextTask
  split
  · exact Rat.le_refl
  · dsimp only
    split
    · rw [finish_resource_elapsed]; exact Rat.le_refl
    · rw [←finish_resource_elapsed state]
      apply checked_monotone
      intro prepared success
      have elapsed := prepare_elapsed (BrowserResources.finish state) prepared success
      split
      · rw [elapsed]; exact Rat.le_refl
      · rw [fire_resource_elapsed]
        change (BrowserResources.finish state).machine.elapsed≤max prepared.machine.elapsed _
        rw [elapsed]
        exact le_max_left _ _

theorem fire_next_task_monotone (state : State) :
    state.machine.elapsed≤(BrowserRuntime.fireNextTask state).machine.elapsed := by
  unfold BrowserRuntime.fireNextTask
  split
  · exact Rat.le_refl
  · split
    · exact Rat.le_refl
    · dsimp only
      have elapsed : (BrowserResources.finish (Browser.finishTimer state)).machine.elapsed=state.machine.elapsed :=
        (finish_resource_elapsed _).trans (finish_timer_elapsed _)
      split
      · rw [elapsed]; exact Rat.le_refl
      · rw [←elapsed]
        apply checked_monotone
        intro prepared success
        have time := prepare_elapsed (BrowserResources.finish (Browser.finishTimer state)) prepared success
        split
        · rw [time]; exact Rat.le_refl
        · rw [←time]; exact fire_next_resource_monotone prepared
        · rw [←time]; exact fire_timer_monotone prepared
        · split
          · rw [←time]; exact fire_next_resource_monotone prepared
          · rw [←time]; exact fire_timer_monotone prepared


/-- The deadline of exactly the task selected by BrowserRuntime, including
native registration-order ties between the resource and timer queues. -/
def selectedDeadline (state : State) : Option Rat :=
  match BrowserResources.nextTask state, Browser.nextTimer state with
  | none,none => none
  | some resource,none => some resource.due
  | none,some timer => some timer.due
  | some resource,some timer =>
    if resource.due<timer.due || (resource.due==timer.due && resource.request.order<timer.order) then
      some resource.due else some timer.due

theorem fire_next_task_elapsed (state prepared : State)
    (ready : Browser.taskFinished state.machine=true)
    (timerIdle : state.activeTimer=none) (resourceIdle : state.activeResource=none)
    (eventIdle : (!state.animation.pending.isEmpty || state.animation.active.isSome ||
      !state.textSelection.pending.isEmpty || state.textSelection.active.isSome)=false)
    (success : BrowserResources.prepare state=.ok prepared) :
    (BrowserRuntime.fireNextTask state).machine.elapsed=
      match selectedDeadline prepared with
      | none => state.machine.elapsed
      | some due => max state.machine.elapsed due := by
  have dispatched : BrowserRuntime.fireNextTask state=
      match BrowserResources.nextTask prepared,Browser.nextTimer prepared with
      | none,none => prepared
      | some _,none => BrowserResources.fireNextTask prepared
      | none,some _ => Browser.fireNextTimer prepared
      | some resource,some timer =>
        if resource.due<timer.due || (resource.due==timer.due && resource.request.order<timer.order) then
          BrowserResources.fireNextTask prepared else Browser.fireNextTimer prepared := by
    simp only [BrowserRuntime.fireNextTask,ready,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      eventIdle,finish_timer_idle state timerIdle,finish_resource_idle state resourceIdle,
      success,Browser.checked]
    rfl
  obtain ⟨tasks,shape⟩ := prepare_shape state prepared success
  have sameTime : prepared.machine.elapsed=state.machine.elapsed := prepare_elapsed _ _ success
  have preparedReady : Browser.taskFinished prepared.machine=true := by rw [shape]; exact ready
  have preparedResource : prepared.activeResource=none := by rw [shape]; exact resourceIdle
  have preparedRequests : prepared.resourceRequests=[] := by rw [shape]
  rw [dispatched]
  unfold selectedDeadline
  cases resourceSelected : BrowserResources.nextTask prepared with
  | none =>
    cases timerSelected : Browser.nextTimer prepared with
    | none => exact sameTime
    | some timer =>
      change (Browser.fireNextTimer prepared).machine.elapsed=max state.machine.elapsed timer.due
      rw [fire_timer_elapsed prepared preparedReady preparedRequests timer timerSelected,sameTime]
  | some resource =>
    cases timerSelected : Browser.nextTimer prepared with
    | none =>
      change (BrowserResources.fireNextTask prepared).machine.elapsed=max state.machine.elapsed resource.due
      rw [fire_resource_selected prepared resource preparedReady preparedResource preparedRequests resourceSelected,sameTime]
    | some timer =>
      dsimp only
      split
      · rw [fire_resource_selected prepared resource preparedReady preparedResource preparedRequests resourceSelected,sameTime]
      · rw [fire_timer_elapsed prepared preparedReady preparedRequests timer timerSelected,sameTime]

theorem fire_next_task_before_deadline (state prepared : State) (due deadline : Rat)
    (ready : Browser.taskFinished state.machine=true)
    (timerIdle : state.activeTimer=none) (resourceIdle : state.activeResource=none)
    (eventIdle : (!state.animation.pending.isEmpty || state.animation.active.isSome ||
      !state.textSelection.pending.isEmpty || state.textSelection.active.isSome)=false)
    (success : BrowserResources.prepare state=.ok prepared)
    (selected : selectedDeadline prepared=some due)
    (currentBound : state.machine.elapsed≤deadline) (taskBound : due≤deadline) :
    state.machine.elapsed≤(BrowserRuntime.fireNextTask state).machine.elapsed ∧
      (BrowserRuntime.fireNextTask state).machine.elapsed≤deadline := by
  rw [fire_next_task_elapsed state prepared ready timerIdle resourceIdle eventIdle success,selected]
  exact ⟨le_max_left _ _,max_le _ _ _ currentBound taskBound⟩

end CookieClicker.JavaScript.BrowserTime

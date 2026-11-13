import CookieClicker.JavaScriptReloadGateSource

/-! The actual Chromium87 timer creation and firing keep the Steam restoration
callback behind its source100ms gate. No global navigation or alternative-load
coverage is assumed here. Source startup/caller/clock refinement is explicit. -/
namespace CookieClicker.JavaScript.ReloadGateTime
open Browser
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def hundred : UInt64 := 4636737291354636288

theorem delay_exact (nesting:Option Nat) : Browser.timerDelay nesting hundred=100 := by
 have native : Number.toInt32 hundred=100 := by decide +kernel
 unfold Browser.timerDelay
 rw [native]
 split <;> rfl

def timer (state:Browser.State) (callback:Value) (id:Nat) : Browser.Timer := {
 id,due:=state.machine.elapsed+100,order:=state.nextOrder,
 nesting:=state.currentTimerNesting.getD 0+1,repeating:=false,
 delay:=hundred,callback,arguments:=[]}

def registered (state:Browser.State) (callback:Value) (id:Nat) : Browser.State :=
 Browser.result {state with
   timers:=state.timers++[timer state callback id]
   nextTimer:=Browser.nextTimerIdentifier id
   nextOrder:=state.nextOrder+1} (.number (Number.ofNat id))

attribute [local cbv_opaque] Builtins.isCallable Browser.unusedTimerIdentifier Browser.timerDelay Browser.result Number.ofNat List.length List.append Rat.add registered timer

theorem native_registration (state:Browser.State) (callback:Value) (id:Nat)
    (callable:Builtins.isCallable state.machine callback=.ok true)
    (available:Browser.unusedTimerIdentifier state (state.timers.length+1) state.nextTimer=some id) :
 Browser.timerCall state "setTimeout" [callback,.number hundred]=registered state callback id := by
 cbv
 rw [callable]
 cbv
 rw [available]
 have delay : Browser.timerDelay state.currentTimerNesting 4636737291354636288=100 := delay_exact _
 rw [delay]
 rfl

theorem registered_elapsed (state:Browser.State) (callback:Value) (id:Nat) :
 (registered state callback id).machine.elapsed=state.machine.elapsed := rfl

theorem registered_timer (state:Browser.State) (callback:Value) (id:Nat) :
 (registered state callback id).timers=state.timers++[timer state callback id] := rfl

theorem registered_due (state:Browser.State) (callback:Value) (id:Nat) :
 (timer state callback id).due=state.machine.elapsed+100 := rfl

theorem restoration_fire_lower (state entry:Browser.State) (callback:Value) (id:Nat)
    (ready:Browser.taskFinished state.machine=true) (resources:state.resourceRequests=[])
    (selected:Browser.nextTimer state=some (timer entry callback id)) :
 entry.machine.elapsed+100≤(Browser.fireNextTimer state).machine.elapsed := by
 rw [BrowserTime.fire_timer_elapsed state ready resources (timer entry callback id) selected]
 rw [registered_due, Rat.max_def]
 split
 · exact Rat.le_refl
 · grind

/-- Even instant navigation/asset/IPC delivery cannot erase this source timer.
The completed restoration must be the invocation selected from the registered
startup timer, not a merely ready fresh state or another LoadSave entry path. -/
theorem completed_restoration_positive (state entry:Browser.State) (callback:Value) (id:Nat)
    (navigation:Rat) (registeredAfter:navigation≤entry.machine.elapsed)
    (ready:Browser.taskFinished state.machine=true) (resources:state.resourceRequests=[])
    (selected:Browser.nextTimer state=some (timer entry callback id)) :
 navigation+100≤(Browser.fireNextTimer state).machine.elapsed := by
 have h:=restoration_fire_lower state entry callback id ready resources selected
 grind

/-- The composed resource/timer dispatcher has the same gate, with its exact
selection queue and pending-host contracts retained. -/
theorem composed_restoration_fire_lower (state prepared:Browser.State) (registeredAt:Rat)
    (ready:Browser.taskFinished state.machine=true)
    (timerIdle:state.activeTimer=none) (resourceIdle:state.activeResource=none)
    (eventIdle:(!state.animation.pending.isEmpty || state.animation.active.isSome ||
      !state.textSelection.pending.isEmpty || state.textSelection.active.isSome)=false)
    (success:BrowserResources.prepare state=.ok prepared)
    (selected:BrowserTime.selectedDeadline prepared=some (registeredAt+100)) :
 registeredAt+100≤(BrowserRuntime.fireNextTask state).machine.elapsed := by
 rw [BrowserTime.fire_next_task_elapsed state prepared ready timerIdle resourceIdle eventIdle success,selected]
 dsimp only
 rw [Rat.max_def]
 split
 · exact Rat.le_refl
 · grind

/-- Tie the universal timer deadline to the exact parsed startup prefix. -/
theorem source_registration_due (saved:Value) (elapsed:Rat) (browser:Browser.State) (id:Nat) :
 (timer {browser with machine:=ReloadGateSource.stage saved elapsed 28} (.object 2) id).due=elapsed+100 := by
 simp only [registered_due,ReloadGateSource.native_elapsed]


/-- The arithmetic consequence applies to completed sequential restorations.
It does not discard overlapping abandoned navigations or their source effects. -/
theorem sequential_restoration_bound (time:Nat→Rat)
    (gate:∀n,time n+100≤time (n+1)) (n:Nat) : time 0+100*(n:Rat)≤time n := by
 induction n with
 | zero => simp [Rat.mul_zero,Rat.add_zero]
 | succ n ih =>
   have step:=gate n
   simp only [Rat.natCast_add,Rat.natCast_ofNat]
   grind

end CookieClicker.JavaScript.ReloadGateTime

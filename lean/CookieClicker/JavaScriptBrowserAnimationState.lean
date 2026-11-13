import CookieClicker.JavaScriptState

/-! The event portion of Chromium87 ScriptedAnimationController. EnqueueEvent
appends without coalescing. DispatchEvents swaps the queue before callbacks;
events enqueued by a callback therefore belong to a later rendering stage.
The rendering-opportunity schedule is an environment input, not a timer or a
restriction on source actions. This state does not select a display cadence.
-/
namespace CookieClicker.JavaScript.BrowserAnimationState

structure State where
  pending : List Nat := []
  active : Option (List Nat) := none
  deriving Repr, DecidableEq, Inhabited

def enqueue (state : State) (event : Nat) : State :=
  {state with pending := state.pending ++ [event]}

def beginDispatch (state : State) : State :=
  {pending := [], active := some state.pending}

theorem enqueue_pending (state : State) (event : Nat) :
    (enqueue state event).pending = state.pending ++ [event] := rfl

theorem enqueue_preserves_active (state : State) (event : Nat) :
    (enqueue state event).active = state.active := rfl

theorem begin_freezes_queue (state : State) :
    (beginDispatch state).active = some state.pending ∧
    (beginDispatch state).pending = [] := ⟨rfl,rfl⟩

end CookieClicker.JavaScript.BrowserAnimationState

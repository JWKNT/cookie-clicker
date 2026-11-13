import CookieClicker.JavaScriptUnlockPairCall

namespace CookieClicker.JavaScript.UnlockPair
open UnlockArrayWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def finalState {base : Machine} {first second : JSString} (i : Inputs base first second) : LocalState :=
  runRows (UnlockArrayCall.afterRows (rows i)) (UnlockArrayCall.initial (world i))

def addedEnvironments {base : Machine} {first second : JSString} (i : Inputs base first second) : Array LexicalEnvironment :=
  #[⟨.declarative (UnlockArrayLocals.bindings (finalState i).values),some i.scopes.closureScope⟩]++(finalState i).suffix

theorem returned_environments {base : Machine} {first second : JSString} (i : Inputs base first second) :
    (returned i).heap.environments=base.heap.environments++addedEnvironments i := by
  change i.scopes.environments.push
    ⟨.declarative (UnlockArrayLocals.bindings (finalState i).values),some i.scopes.closureScope⟩++
      (finalState i).suffix=_
  rw [i.environments]
  simp only [addedEnvironments,Array.push_eq_append,Array.append_assoc]

theorem retained_path {base : Machine} {first second : JSString} (i : Inputs base first second)
    (name : String) (start target depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments name start target depth) :
    HasEnvironment.DeclarativePath (returned i).heap.environments name start target depth := by
  rw [returned_environments]
  exact TieredAllocation.append_path _ _ name start target depth path

theorem retained_environment {base : Machine} {first second : JSString} (i : Inputs base first second)
    (id : EnvId) (environment : LexicalEnvironment)
    (found : base.heap.environments[id]?=some environment) :
    (returned i).heap.environments[id]?=some environment := by
  rw [returned_environments]
  exact TieredAllocation.append_read _ _ id environment found

def withContinuation {base : Machine} {first second : JSString} (i : Inputs base first second)
    (continuation : List Frame) : Inputs {base with continuation} first second := {
  i with gameRead:=i.gameRead }

theorem returned_with_continuation {base : Machine} {first second : JSString} (i : Inputs base first second)
    (continuation : List Frame) :
    returned (withContinuation i continuation)={returned i with continuation} := by
  rfl

end CookieClicker.JavaScript.UnlockPair

import CookieClicker.JavaScriptCursorBuyAllocation
import CookieClicker.JavaScriptCursorBuyCall

namespace CookieClicker.JavaScript.CursorBuyOriginal
open SourceRead TieredRead CursorBuyInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def returned {base : Machine} {display : JSString} (i : CursorBuyComplete.Inputs base display)
    (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) : Machine :=
  CursorBuyCall.returned base scope cursor function display
    (CursorBuyAllocation.bodyInputs i scope cursor function depth path bound)

/-- Original catalogue, closure paths and receiver data determine every later
frame. No post-call heap or helper return value is supplied. -/
theorem actual_prepared {base : Machine} {display : JSString} (i : CursorBuyComplete.Inputs base display)
    (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (757+fuel) (prepared base scope cursor (some function))=
      Builtins.run fuel (returned i scope cursor function depth path bound) :=
  CursorBuyCall.actual_prepared base scope cursor function display
    (CursorBuyAllocation.bodyInputs i scope cursor function depth path bound)
    (CursorBuyWorld.extendEdge base _ cursor (JSString.ofString "amount") (.number Number.one) edge
      (CursorBuyAllocation.extends_original base scope cursor function)) fuel

theorem actual_dispatch (base : Machine) (scope cursor function : Nat)
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) :
    Builtins.builtinStep {base with control:=.invoke (.object function) (.object cursor) [] false}=
      prepared base scope cursor (some function) := by
  change {invoke {base with control:=.invoke (.object function) (.object cursor) [] false}
    (.object function) (.object cursor) [] false with elapsed:=base.elapsed}=_
  simp only [invoke,present,kind,checked,CursorBuyInvocation.actual_prepare]
  rfl

/-- Complete actual invocation, native allocation and hoisting, all clauses,
recursive calls, and return to the original caller. -/
theorem actual_source_call {base : Machine} {display : JSString} (i : CursorBuyComplete.Inputs base display)
    (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one))
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) (fuel : Nat) :
    Builtins.run (758+fuel) {base with control:=.invoke (.object function) (.object cursor) [] false}=
      Builtins.run fuel (returned i scope cursor function depth path bound) := by
  rw [show 758+fuel=1+(757+fuel) by omega,Nat.add_comm 1 (757+fuel)]
  change Builtins.run (757+fuel)
    (Builtins.builtinStep {base with control:=.invoke (.object function) (.object cursor) [] false})=_
  rw [actual_dispatch base scope cursor function source object present kind]
  exact actual_prepared i scope cursor function depth path bound edge fuel

theorem returned_extends {base : Machine} {display : JSString} (i : CursorBuyComplete.Inputs base display)
    (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) :
    HeapExtension.Extends base.heap (returned i scope cursor function depth path bound).heap :=
  HeapExtension.trans (CursorBuyAllocation.extends_original base scope cursor function)
    (CursorBuyComplete.completed_extends (CursorBuyAllocation.bodyInputs i scope cursor function depth path bound))

theorem returned_elapsed {base : Machine} {display : JSString} (i : CursorBuyComplete.Inputs base display)
    (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) :
    (returned i scope cursor function depth path bound).elapsed=base.elapsed := rfl

theorem returned_draws {base : Machine} {display : JSString} (i : CursorBuyComplete.Inputs base display)
    (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) :
    (returned i scope cursor function depth path bound).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.CursorBuyOriginal

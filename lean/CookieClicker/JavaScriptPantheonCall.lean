import CookieClicker.JavaScriptPantheonBody
import CookieClicker.JavaScriptMemberCall

/-! The full actual hasGod('creation') call for the fixed diamond-Godzamok
slot profile. Source setup, all three comparisons, increments and return
are retained; no absent-god result is supplied as an assumption. -/
namespace CookieClicker.JavaScript.PantheonCall
open SourceRead PantheonRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def values (base : Machine) : PantheonLocals.Values :=
  ⟨.string creation,.object base.heap.objects.size,.undefined,.undefined⟩
def bodyBase (base : Machine) (game : ObjectId) : Machine := {base with
  context:={base.context with thisValue:=.object game}
  continuation:=.callBoundary base.context none::base.continuation}
def state (base : Machine) (scope game function : ObjectId) (god : Value := .undefined)
    (i : Value := .undefined) : Machine :=
  PantheonLocals.start (bodyBase base game)
    (base.heap.objects.push (PantheonSource.argumentObject base (.string creation) (some function)))
    base.heap.environments scope {values base with god,i} #[]

def returned (base : Machine) (scope game function god : ObjectId) : Machine := {base with
  heap:=(state base scope game function (.object god) (.number (Number.ofNat 3))).heap
  control:=.expressionResult (.value (.boolean false)) }

theorem hoisted_state (base : Machine) (scope game function : ObjectId) :
    PantheonSource.hoisted base scope game (.string creation) (some function)=
      {state base scope game function with control:=.declarationFunctions [] PantheonSource.body} := by
  simp only [PantheonSource.hoisted,PantheonSource.prepared,PantheonSource.allocatedHeap,
    PantheonSource.locals,PantheonSource.localIndex,PantheonSource.argumentIndex,state,
    PantheonLocals.start,PantheonLocals.heap,PantheonLocals.slotIndex,PantheonLocals.bindings,
    values,bodyBase,Array.append_empty]
  rfl

theorem prepared_returns (base : Machine) (scope game function : ObjectId)
    (world : World (state base scope game function))
    (capture : CapturedM base.heap.environments scope world.m) (fuel : Nat) :
    Builtins.run (193+fuel) (PantheonSource.prepared base scope game (.string creation) (some function))=
      Builtins.run fuel (returned base scope game function world.god) := by
  rw [show 193+fuel=13+(179+(1+fuel)) by omega,
    PantheonSource.actual_hoist_prefix (callee:=some function)]
  have body : Builtins.run (179+(1+fuel)) (PantheonSource.hoisted base scope game (.string creation) (some function))=
      Builtins.run (179+(1+fuel)) (state base scope game function) := by
    rw [hoisted_state,Nat.add_comm 179 (1+fuel)]
    rfl
  rw [body]
  unfold state
  rw [PantheonBody.native_body _ _ _ _ _ world capture rfl,Nat.add_comm 1 fuel]
  rfl

theorem native_invoke (base : Machine) (scope game function : ObjectId)
    (world : World (state base scope game function))
    (capture : CapturedM base.heap.environments scope world.m)
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (PantheonSource.closure scope source)) (fuel : Nat) :
    Builtins.run (193+fuel) (invoke base (.object function) (.object game) [.string creation] false)=
      Builtins.run fuel (returned base scope game function world.god) := by
  simp only [invoke,present,kind,checked,PantheonSource.actual_prepare]
  exact prepared_returns base scope game function world capture fuel

theorem returned_extends (base : Machine) (scope game function god : ObjectId) :
    HeapExtension.Extends base.heap (returned base scope game function god).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (PantheonSource.argumentObject base (.string creation) (some function)))
    (HeapExtension.same_objects rfl)

theorem source_call (base : Machine) (scope game function : ObjectId)
    (world : World (state base scope game function))
    (capture : CapturedM base.heap.environments scope world.m)
    (source : Option JSString) (gameObject functionObject : JSObject)
    (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "hasGod")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (PantheonSource.closure scope source))
    (gameRead : Reads base (.identifier "Game") (.object game) 3) (fuel : Nat) :
    Builtins.run (205+fuel) {base with
      control:=.expression (MemberCall.expression "hasGod" (.literal (.string creation)))}=
      Builtins.run fuel (returned base scope game function world.god) := by
  rw [show 205+fuel=1+10+(1+(193+fuel)) by omega,
    MemberCall.source_invoke base "hasGod" (.literal (.string creation)) (.string creation)
      game function gameObject 1 gamePresent gameKind method gameRead (literal base (.string creation)),
    Nat.add_comm 1 (193+fuel)]
  change Builtins.run (193+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.string creation] false}
    (.object function) (.object game) [.string creation] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [.string creation] false}
      (.object function) (.object game) [.string creation] false=
      PantheonSource.prepared base scope game (.string creation) (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,PantheonSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope game function world capture fuel

end CookieClicker.JavaScript.PantheonCall

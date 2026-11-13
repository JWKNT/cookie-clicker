import CookieClicker.JavaScriptModHookBody
import CookieClicker.JavaScriptModHookSource
import CookieClicker.JavaScriptMemberCallTwo
import CookieClicker.JavaScriptAllocatedGameRead

/-! Full source invocation of an empty runModHookOnValue list.
The argument value is returned unchanged, with native allocations retained. -/
namespace CookieClicker.JavaScript.ModHookCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def values (base : Machine) (name : JSString) (value : Value)
    (index : Value := .undefined) : ModHookLocals.Values :=
  ⟨.string name,value,.object base.heap.objects.size,index⟩
def state (base : Machine) (scope game : ObjectId) (name : JSString) (value : Value)
    (function : ObjectId) (index : Value := .undefined) : Machine :=
  ModHookLocals.start {base with
      context:={base.context with thisValue:=.object game}
      continuation:=.callBoundary base.context none::base.continuation}
    (base.heap.objects.push (ModHookSource.argumentObject base (.string name) value (some function)))
    base.heap.environments scope (values base name value index) #[]
def returned (base : Machine) (scope game : ObjectId) (name : JSString) (value : Value)
    (function : ObjectId) : Machine := {base with
  heap:=(state base scope game name value function (.number 0)).heap
  control:=.expressionResult (.value value)}

theorem state_extends (base : Machine) (scope game : ObjectId) (name : JSString) (value : Value)
    (function : ObjectId) (index : Value) :
    HeapExtension.Extends base.heap (state base scope game name value function index).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (ModHookSource.argumentObject base (.string name) value (some function)))
    (HeapExtension.same_objects rfl)

def extendWorld {before after : Machine} {name : JSString} (world : ModHookBody.EmptyHook before name)
    (extension : HeapExtension.Extends before.heap after.heap) : ModHookBody.EmptyHook after name := {
  game:=world.game,table:=world.table,hooks:=world.hooks
  tableEdge:=world.tableEdge.extend extension,selectedEdge:=world.selectedEdge.extend extension
  array:=world.array,present:=HeapExtension.checked_object extension _ _ world.present
  kind:=world.kind,length:=HeapExtension.lookup_property extension _ _ _ world.length }

theorem hoisted_state (base : Machine) (scope game : ObjectId) (name : JSString) (value : Value)
    (function : ObjectId) :
    ModHookSource.hoisted base scope game (.string name) value (some function)=
      {state base scope game name value function with
        control:=.declarationFunctions [] ModHookSource.body} := by
  simp only [ModHookSource.hoisted,ModHookSource.prepared,ModHookSource.allocatedHeap,ModHookSource.locals,
    ModHookSource.localIndex,ModHookSource.argumentIndex,state,ModHookLocals.start,ModHookLocals.heap,
    ModHookLocals.slotIndex,ModHookLocals.bindings,values,Array.append_empty]
  rfl

theorem hoist_to_body (base : Machine) (scope game : ObjectId) (name : JSString) (value : Value)
    (function : ObjectId) (fuel : Nat) :
    Builtins.run (7+1+fuel) (ModHookSource.prepared base scope game (.string name) value (some function))=
      Builtins.run (1+fuel) (state base scope game name value function) := by
  rw [show 7+1+fuel=7+(1+fuel) by omega,ModHookSource.actual_hoist (callee:=some function),
    hoisted_state,Nat.add_comm 1 fuel]
  rfl

theorem prepared_returns (base : Machine) (scope : EnvId) (name : JSString)
    (world : ModHookBody.EmptyHook base name) (value : Value) (function : ObjectId)
    (game : Reads (state base scope world.game name value function (.number 0))
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (49+fuel) (ModHookSource.prepared base scope world.game (.string name) value (some function))=
      Builtins.run fuel (returned base scope world.game name value function) := by
  rw [show 49+fuel=7+1+(41+fuel) by omega,hoist_to_body,
    show 1+(41+fuel)=41+(1+fuel) by omega]
  dsimp only [state]
  rw [ModHookBody.native_body
    {base with
      context:={base.context with thisValue:=.object world.game}
      continuation:=.callBoundary base.context none::base.continuation}
    (base.heap.objects.push (ModHookSource.argumentObject base (.string name) value (some function)))
    base.heap.environments scope (values base name value) #[] name rfl
    (extendWorld world (state_extends base scope world.game name value function (.number 0))) game,
    Nat.add_comm 1 fuel]
  rfl

theorem source_call (base : Machine) (scope : EnvId) (name : JSString)
    (world : ModHookBody.EmptyHook base name) (argument : Expr) (value : Value) (ticks : Nat)
    (function : ObjectId) (source : Option JSString) (gameObject functionObject : JSObject)
    (gamePresent : checkedObject base.heap world.game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap world.game (JSString.ofString "runModHookOnValue")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (ModHookSource.closure scope source))
    (callerGame : Reads base (.identifier "Game") (.object world.game) 3)
    (argumentRead : Reads base argument value ticks)
    (calleeGame : Reads (state base scope world.game name value function (.number 0))
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (ticks+62+fuel) {base with control:=.expression (MemberCallTwo.expression "runModHookOnValue" (.literal (.string name)) argument)}=
      Builtins.run fuel (returned base scope world.game name value function) := by
  rw [show ticks+62+fuel=1+ticks+11+(1+(49+fuel)) by omega,
    MemberCallTwo.source_invoke base "runModHookOnValue" (.literal (.string name)) argument
      (.string name) value world.game function gameObject 1 ticks gamePresent gameKind method callerGame
      (literal base (.string name)) argumentRead,Nat.add_comm 1 (49+fuel)]
  change Builtins.run (49+fuel) {invoke {base with
    control:=.invoke (.object function) (.object world.game) [.string name,value] false}
    (.object function) (.object world.game) [.string name,value] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with
      control:=.invoke (.object function) (.object world.game) [.string name,value] false}
      (.object function) (.object world.game) [.string name,value] false=
      ModHookSource.prepared base scope world.game (.string name) value (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,ModHookSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope name world value function calleeGame fuel

theorem returned_extends (base : Machine) (scope game : ObjectId) (name : JSString)
    (value : Value) (function : ObjectId) :
    HeapExtension.Extends base.heap (returned base scope game name value function).heap :=
  state_extends base scope game name value function (.number 0)

theorem callee_game (base : Machine) (scopes : HasEnvironment.Scopes base.globalObject)
    (game : ObjectId) (name : JSString) (value : Value) (function : ObjectId) (index : Value)
    (window : JSObject) (environments : scopes.environments=base.heap.environments)
    (present : checkedObject base.heap base.globalObject=.ok window)
    (kind : window.kind=.host "Window" 0) (writable enumerable configurable : Bool)
    (property : lookupProperty base.heap base.globalObject (JSString.ofString "Game")=
      .ok (some (.data (.object game) writable enumerable configurable)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (state base scopes.closureScope game name value function index)
      (.identifier "Game") (.object game) 3 := by
  apply AllocatedGameRead.appended base _ scopes (ModHookLocals.bindings (values base name value index))
    game window environments (writable:=writable) (enumerable:=enumerable) (configurable:=configurable)
  · simp only [state,ModHookLocals.start,ModHookLocals.heap,Array.append_empty]
  · rfl
  · simp [ModHookLocals.bindings]
  · exact state_extends base scopes.closureScope game name value function index
  · exact present
  · exact kind
  · exact property
  · exact exclusions

end CookieClicker.JavaScript.ModHookCall

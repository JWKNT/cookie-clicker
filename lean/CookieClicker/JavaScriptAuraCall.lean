import CookieClicker.JavaScriptAuraBody
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptAllocatedGameRead

/-! Complete source call to auraMult with both selectors at No aura.
The native arguments object, local environment and caller return are retained. -/
namespace CookieClicker.JavaScript.AuraCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def values (base : Machine) (what : JSString) (n : Value := .undefined) : AuraLocals.Values :=
  ⟨.string what,.object base.heap.objects.size,n⟩

def state (base : Machine) (scope game : ObjectId) (what : JSString)
    (function : ObjectId) (n : Value := .undefined) : Machine :=
  AuraLocals.start {base with
      context:={base.context with thisValue:=.object game}
      continuation:=.callBoundary base.context none::base.continuation}
    (base.heap.objects.push (AuraSource.argumentObject base (.string what) (some function)))
    base.heap.environments scope (values base what n) #[]

def returned (base : Machine) (scope game : ObjectId) (what : JSString)
    (function : ObjectId) : Machine := {base with
  heap:=(state base scope game what function (.number 0)).heap
  control:=.expressionResult (.value (.number 0))}

theorem state_extends (base : Machine) (scope game : ObjectId) (what : JSString)
    (function : ObjectId) (n : Value) :
    HeapExtension.Extends base.heap (state base scope game what function n).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (AuraSource.argumentObject base (.string what) (some function)))
    (HeapExtension.same_objects rfl)

def extendWorld {before after : Machine} (world : AuraRead.World before)
    (extension : HeapExtension.Extends before.heap after.heap) : AuraRead.World after := {
  game:=world.game,auras:=world.auras,emptyAura:=world.emptyAura
  table:=world.table.extend extension,first:=world.first.extend extension
  second:=world.second.extend extension,zeroEntry:=world.zeroEntry.extend extension
  name:=world.name.extend extension }

theorem hoisted_state (base : Machine) (scope game : ObjectId) (what : JSString)
    (function : ObjectId) :
    AuraSource.hoisted base scope game (.string what) (some function)=
      {state base scope game what function with
        control:=.declarationFunctions [] AuraSource.body} := by
  simp only [AuraSource.hoisted,AuraSource.prepared,AuraSource.allocatedHeap,AuraSource.locals,
    AuraSource.localIndex,AuraSource.argumentIndex,state,AuraLocals.start,AuraLocals.heap,
    AuraLocals.slotIndex,AuraLocals.bindings,values,Array.append_empty]
  rfl

theorem hoist_to_body (base : Machine) (scope game : ObjectId) (what : JSString)
    (function : ObjectId) (fuel : Nat) :
    Builtins.run (9+1+fuel) (AuraSource.prepared base scope game (.string what) (some function))=
      Builtins.run (1+fuel) (state base scope game what function) := by
  rw [show 9+1+fuel=9+(1+fuel) by omega,AuraSource.actual_hoist_prefix (callee:=some function),
    hoisted_state,Nat.add_comm 1 fuel]
  rfl

theorem prepared_returns (base : Machine) (scope : EnvId) (world : AuraRead.World base)
    (what : JSString) (function : ObjectId) (other : AuraRead.noAura ≠ what)
    (game : Reads (state base scope world.game what function (.number 0))
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (149+fuel) (AuraSource.prepared base scope world.game (.string what) (some function))=
      Builtins.run fuel (returned base scope world.game what function) := by
  rw [show 149+fuel=9+1+(139+fuel) by omega,hoist_to_body]
  rw [show 1+(139+fuel)=139+(1+fuel) by omega]
  change Builtins.run (139+(1+fuel)) (state base scope world.game what function)=_
  dsimp only [state]
  rw [AuraBody.native_body
    {base with
      context:={base.context with thisValue:=.object world.game}
      continuation:=.callBoundary base.context none::base.continuation}
    (base.heap.objects.push (AuraSource.argumentObject base (.string what) (some function)))
    base.heap.environments scope (values base what) #[] what rfl other
    (extendWorld world (state_extends base scope world.game what function (.number 0))) game]
  rw [Nat.add_comm 1 fuel]
  rfl

theorem source_call (base : Machine) (scope : EnvId) (world : AuraRead.World base)
    (what : JSString) (function : ObjectId) (source : Option JSString)
    (gameObject functionObject : JSObject)
    (other : AuraRead.noAura ≠ what)
    (gamePresent : checkedObject base.heap world.game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap world.game (JSString.ofString "auraMult")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (AuraSource.closure scope source))
    (callerGame : Reads base (.identifier "Game") (.object world.game) 3)
    (calleeGame : Reads (state base scope world.game what function (.number 0))
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (161+fuel) {base with
      control:=.expression (MemberCall.expression "auraMult" (.literal (.string what)))}=
      Builtins.run fuel (returned base scope world.game what function) := by
  rw [show 161+fuel=1+10+(1+(149+fuel)) by omega,
    MemberCall.source_invoke base "auraMult" (.literal (.string what)) (.string what)
      world.game function gameObject 1 gamePresent gameKind method callerGame
      (literal base (.string what)),Nat.add_comm 1 (149+fuel)]
  change Builtins.run (149+fuel) {invoke {base with
    control:=.invoke (.object function) (.object world.game) [.string what] false}
    (.object function) (.object world.game) [.string what] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with
      control:=.invoke (.object function) (.object world.game) [.string what] false}
      (.object function) (.object world.game) [.string what] false=
      AuraSource.prepared base scope world.game (.string what) (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,AuraSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope world what function other calleeGame fuel

theorem returned_extends (base : Machine) (scope game : ObjectId) (what : JSString)
    (function : ObjectId) : HeapExtension.Extends base.heap (returned base scope game what function).heap :=
  state_extends base scope game what function (.number 0)

theorem callee_game (base : Machine) (scopes : HasEnvironment.Scopes base.globalObject)
    (game : ObjectId) (what : JSString) (function : ObjectId) (n : Value) (window : JSObject)
    (environments : scopes.environments=base.heap.environments)
    (present : checkedObject base.heap base.globalObject=.ok window)
    (kind : window.kind=.host "Window" 0) (writable enumerable configurable : Bool)
    (property : lookupProperty base.heap base.globalObject (JSString.ofString "Game")=
      .ok (some (.data (.object game) writable enumerable configurable)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (state base scopes.closureScope game what function n)
      (.identifier "Game") (.object game) 3 := by
  apply AllocatedGameRead.appended base _ scopes (AuraLocals.bindings (values base what n))
    game window environments (writable:=writable) (enumerable:=enumerable) (configurable:=configurable)
  · simp only [state,AuraLocals.start,AuraLocals.heap,Array.append_empty]
  · rfl
  · simp [AuraLocals.bindings]
  · exact state_extends base scopes.closureScope game what function n
  · exact present
  · exact kind
  · exact property
  · exact exclusions

end CookieClicker.JavaScript.AuraCall

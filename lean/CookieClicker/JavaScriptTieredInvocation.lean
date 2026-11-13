import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptTieredSource

/-! Real GetTieredCpsMult invocation through its native declaration scan and
initial multiplier write. The remaining source statements stay in the actual
continuation, with the arguments object and lexical scope retained. -/
namespace CookieClicker.JavaScript.TieredInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def values (base : Machine) (me : Value) : TieredLocals.Values := {
  me, arguments := .object (TieredSource.argumentIndex base) }

def objects (base : Machine) (me : Value) (callee : ObjectId) : Array JSObject :=
  base.heap.objects.push (TieredSource.argumentObject (callee:=some callee) base me)

def beforeBody (base : Machine) (scope game : ObjectId) (me : Value) (callee : ObjectId) : Machine :=
  TieredLocals.start (TieredSource.hoisted (callee:=some callee) base scope game me)
    (objects base me callee) base.heap.environments scope (values base me) #[]

def afterMult (base : Machine) (scope game : ObjectId) (me : Value) (callee : ObjectId) : Machine := {
  beforeBody base scope game me callee with
  heap := TieredLocals.heap (objects base me callee) base.heap.environments scope
    {values base me with mult:=.number Number.one} #[]
  control := .completion (.normal none)
  continuation := .statementList TieredSource.body.tail none::
    .callBoundary base.context none::base.continuation }

theorem body_state (base : Machine) (scope game : ObjectId) (me : Value) (callee : ObjectId) :
    beforeBody base scope game me callee =
      {TieredSource.hoisted (callee:=some callee) base scope game me with
        control:=.statement ProductionSyntax.GetTieredCpsMultBody} := by
  simp [beforeBody,TieredLocals.start,TieredLocals.heap,TieredLocals.bindings,
    TieredLocals.slotIndex,TieredSource.hoisted,TieredSource.prepared,TieredSource.allocatedHeap,
    TieredSource.localIndex,TieredSource.locals,values,objects]

theorem hoisted_mult (base : Machine) (scope game : ObjectId) (me : Value) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (6+fuel) (TieredSource.hoisted (callee:=some callee) base scope game me)=
      Builtins.run fuel (afterMult base scope game me callee) := by
  have same : Builtins.run (6+fuel) (TieredSource.hoisted (callee:=some callee) base scope game me)=
      Builtins.run (6+fuel) (beforeBody base scope game me callee) := by
    rw [body_state,Nat.add_comm 6 fuel]
    change Builtins.run (fuel+5) (Builtins.builtinStep (TieredSource.hoisted (callee:=some callee) base scope game me))=_
    rw [TieredSource.hoisted_starts_body (callee:=some callee) base scope game me]
    rfl
  rw [same]
  exact TieredLocals.actual_initial_mult_prefix _ (objects base me callee) base.heap.environments scope
    (values base me) #[] fuel

theorem prepared_mult (base : Machine) (scope game : ObjectId) (me : Value) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (36+fuel) (TieredSource.prepared (callee:=some callee) base scope game me)=
      Builtins.run fuel (afterMult base scope game me callee) := by
  rw [show 36+fuel=30+(6+fuel) by omega,
    TieredSource.actual_hoist_prefix (callee:=some callee) base scope game me (6+fuel),
    hoisted_mult]

theorem invoke (base : Machine) (scope game function : ObjectId) (source : Option JSString)
    (me : Value) (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (TieredSource.closure scope source)) :
    JavaScript.invoke base (.object function) (.object game) [me] false=
      TieredSource.prepared (callee:=some function) base scope game me := by
  simp only [JavaScript.invoke,present,kind,checked,TieredSource.actual_prepare]
  rfl

theorem source_entry (base : Machine) (argument : Expr) (me : Value)
    (game function scope : ObjectId) (source : Option JSString) (gameObject functionObject : JSObject)
    (ticks : Nat) (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "GetTieredCpsMult")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (TieredSource.closure scope source))
    (gameRead : SourceRead.Reads base (.identifier "Game") (.object game) 3)
    (argumentRead : SourceRead.Reads base argument me ticks) (fuel : Nat) :
    Builtins.run (ticks+47+fuel) {base with
      control:=.expression (MemberCall.expression "GetTieredCpsMult" argument)}=
      Builtins.run fuel (afterMult base scope game me function) := by
  rw [show ticks+47+fuel=ticks+10+(1+(36+fuel)) by omega,
    MemberCall.source_invoke base "GetTieredCpsMult" argument me game function gameObject ticks
      gamePresent gameKind property gameRead argumentRead,Nat.add_comm 1 (36+fuel)]
  change Builtins.run (36+fuel) {JavaScript.invoke {base with
    control:=.invoke (.object function) (.object game) [me] false}
    (.object function) (.object game) [me] false with elapsed:=base.elapsed}=_
  have invoked : JavaScript.invoke {base with
      control:=.invoke (.object function) (.object game) [me] false}
      (.object function) (.object game) [me] false =
      TieredSource.prepared (callee:=some function) base scope game me := by
    simp only [JavaScript.invoke,functionPresent,functionKind,checked,TieredSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_mult base scope game me function fuel

end CookieClicker.JavaScript.TieredInvocation

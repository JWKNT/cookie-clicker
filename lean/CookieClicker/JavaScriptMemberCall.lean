import CookieClicker.JavaScriptSourceRead
import CookieClicker.JavaScriptProductionLeaf

/-! Native Game member calls with a source-computed argument. These prefixes
retain the receiver and continuation and end at actual invocation. The magicCpS
composition also executes its full retained closure and caller return. -/
namespace CookieClicker.JavaScript.MemberCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def expression (method : String) (argument : Expr) : Expr :=
  .call (.member (.identifier "Game") (.identifier method) false) [argument]

def atFunction (base : Machine) (argument : Expr) (game function : ObjectId) : Machine := {
  base with
  control := .expressionResult (.value (.object function))
  continuation := .callResolved (.object game) [argument] false::base.continuation }

theorem callee_data (base : Machine) (method : String) (argument : Expr)
    (game function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value (.object game))
      continuation := .memberObject (.identifier method) false::
        .callCallee [argument] false::base.continuation}=
      Builtins.run fuel (atFunction base argument game function) := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control := .getValue ⟨.property (.object game) (JSString.ofString method),base.context.strict⟩
    continuation := .callResolved (.object game) [argument] false::base.continuation}
      (.object game) (JSString.ofString method) with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control := .getValue ⟨.property (.object game) (JSString.ofString method),base.context.strict⟩
    continuation := .callResolved (.object game) [argument] false::base.continuation}
    game (JSString.ofString method) (.object function) object
    present (Or.inl kind) property]
  rfl

attribute [local cbv_opaque] invoke

theorem argument_value (base : Machine) (argument : Expr) (value : Value)
    (game function : ObjectId) (ticks : Nat) (argumentRead : Reads base argument value ticks) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) (atFunction base argument game function)=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [value] false} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control := .expression argument
    continuation := .callArguments (.object function) (.object game) [] [] false::base.continuation}=_
  rw [argumentRead _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem source_invoke (base : Machine) (method : String) (argument : Expr) (value : Value)
    (game function : ObjectId) (object : JSObject) (ticks : Nat)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (argumentRead : Reads base argument value ticks) (fuel : Nat) :
    Builtins.run (ticks+10+fuel) {base with control:=.expression (expression method argument)}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [value] false} := by
  rw [show ticks+10+fuel=2+(3+(3+(ticks+2+fuel))) by omega,Nat.add_comm 2 (3+(3+(ticks+2+fuel)))]
  change Builtins.run (3+(3+(ticks+2+fuel))) {base with
    control := .expression (.identifier "Game")
    continuation := .memberObject (.identifier method) false::
      .callCallee [argument] false::base.continuation}=_
  rw [gameRead _ (by rfl),callee_data base method argument game function object present kind property,
    argument_value base argument value game function ticks argumentRead]

theorem source_magic (base : Machine) (argument : Expr) (value : Value)
    (game function scope : ObjectId) (source : Option JSString) (gameObject functionObject : JSObject)
    (ticks : Nat) (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "magicCpS")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (ProductionLeaf.magicClosure scope source))
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (argumentRead : Reads base argument value ticks) (fuel : Nat) :
    Builtins.run (ticks+20+fuel) {base with control:=.expression (expression "magicCpS" argument)}=
      Builtins.run fuel (ProductionLeaf.magicReturned (callee:=some function) base scope value) := by
  rw [show ticks+20+fuel=ticks+10+(1+(9+fuel)) by omega,
    source_invoke base "magicCpS" argument value game function gameObject ticks gamePresent gameKind property
      gameRead argumentRead,Nat.add_comm 1 (9+fuel)]
  change Builtins.run (9+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [value] false}
    (.object function) (.object game) [value] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [value] false}
      (.object function) (.object game) [value] false =
      ProductionLeaf.magicPrepared (callee:=some function) base scope game value := by
    simp only [invoke,functionPresent,functionKind,checked,ProductionLeaf.actual_magic_prepare]
    rfl
  rw [invoked]
  exact ProductionLeaf.actual_magic_prepared_prefix base scope game value fuel (some function)

end CookieClicker.JavaScript.MemberCall

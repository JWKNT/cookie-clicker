import CookieClicker.JavaScriptDescriptorRead
import CookieClicker.JavaScriptProductionLeaf

/-! Native Math member calls with two source-computed arguments. The native
nonenumerable method descriptor and all caller state remain intact. -/
namespace CookieClicker.JavaScript.MathMemberCallTwo
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def expression (method : String) (argument second : Expr) : Expr :=
  .call (.member (.identifier "Math") (.identifier method) false) [argument,second]

def atFunction (base : Machine) (argument second : Expr) (game function : ObjectId) : Machine := {
  base with
  control := .expressionResult (.value (.object function))
  continuation := .callResolved (.object game) [argument,second] false::base.continuation }

theorem callee_data (base : Machine) (method : String) (argument second : Expr)
    (game function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true false true))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value (.object game))
      continuation := .memberObject (.identifier method) false::
        .callCallee [argument,second] false::base.continuation}=
      Builtins.run fuel (atFunction base argument second game function) := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control := .getValue ⟨.property (.object game) (JSString.ofString method),base.context.strict⟩
    continuation := .callResolved (.object game) [argument,second] false::base.continuation}
      (.object game) (JSString.ofString method) with elapsed:=base.elapsed}=_
  rw [read_data_descriptor {base with
    control := .getValue ⟨.property (.object game) (JSString.ofString method),base.context.strict⟩
    continuation := .callResolved (.object game) [argument,second] false::base.continuation}
    game (JSString.ofString method) (.object function) object true false true
    present (Or.inl kind) property]
  rfl

attribute [local cbv_opaque] invoke

theorem argument_value (base : Machine) (argument second : Expr) (value secondValue : Value)
    (game function : ObjectId) (ticks secondTicks : Nat)
    (argumentRead : Reads base argument value ticks)
    (secondRead : Reads base second secondValue secondTicks) (fuel : Nat) :
    Builtins.run (ticks+secondTicks+3+fuel) (atFunction base argument second game function)=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [value,secondValue] false} := by
  rw [show ticks+secondTicks+3+fuel=1+(ticks+(1+(secondTicks+(1+fuel)))) by omega,
    Nat.add_comm 1 (ticks+(1+(secondTicks+(1+fuel))))]
  change Builtins.run (ticks+(1+(secondTicks+(1+fuel)))) {base with
    control:=.expression argument
    continuation:=.callArguments (.object function) (.object game) [] [second] false::base.continuation}=_
  rw [argumentRead _ (by rfl),Nat.add_comm 1 (secondTicks+(1+fuel))]
  change Builtins.run (secondTicks+(1+fuel)) {base with
    control:=.expression second
    continuation:=.callArguments (.object function) (.object game) [value] [] false::base.continuation}=_
  rw [secondRead _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem source_invoke (base : Machine) (method : String) (argument second : Expr) (value secondValue : Value)
    (game function : ObjectId) (object : JSObject) (ticks secondTicks : Nat)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true false true)))
    (gameRead : Reads base (.identifier "Math") (.object game) 3)
    (argumentRead : Reads base argument value ticks)
    (secondRead : Reads base second secondValue secondTicks) (fuel : Nat) :
    Builtins.run (ticks+secondTicks+11+fuel) {base with control:=.expression (expression method argument second)}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [value,secondValue] false} := by
  rw [show ticks+secondTicks+11+fuel=2+(3+(3+(ticks+secondTicks+3+fuel))) by omega,Nat.add_comm 2 (3+(3+(ticks+secondTicks+3+fuel)))]
  change Builtins.run (3+(3+(ticks+secondTicks+3+fuel))) {base with
    control := .expression (.identifier "Math")
    continuation := .memberObject (.identifier method) false::
      .callCallee [argument,second] false::base.continuation}=_
  rw [gameRead _ (by rfl),callee_data base method argument second game function object present kind property,
    argument_value base argument second value secondValue game function ticks secondTicks argumentRead secondRead]

end CookieClicker.JavaScript.MathMemberCallTwo

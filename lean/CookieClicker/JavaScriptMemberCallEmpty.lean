import CookieClicker.JavaScriptMemberCall

/-! Native Game member calls with no arguments. The source receiver,
property lookup and caller continuation remain in the machine. -/
namespace CookieClicker.JavaScript.MemberCallEmpty
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 400000

def expression (method : String) : Expr :=
  .call (.member (.identifier "Game") (.identifier method) false) []

theorem callee_data (base : Machine) (method : String)
    (game function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value (.object game))
      continuation:=.memberObject (.identifier method) false::.callCallee [] false::base.continuation}=
      Builtins.run fuel {base with
        control:=.expressionResult (.value (.object function))
        continuation:=.callResolved (.object game) [] false::base.continuation} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control:=.getValue ⟨.property (.object game) (JSString.ofString method),base.context.strict⟩
    continuation:=.callResolved (.object game) [] false::base.continuation}
      (.object game) (JSString.ofString method) with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control:=.getValue ⟨.property (.object game) (JSString.ofString method),base.context.strict⟩
    continuation:=.callResolved (.object game) [] false::base.continuation}
    game (JSString.ofString method) (.object function) object present (Or.inl kind) property]

theorem source_invoke (base : Machine) (method : String)
    (game function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object game) 3) (fuel : Nat) :
    Builtins.run (9+fuel) {base with control:=.expression (expression method)}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [] false} := by
  rw [show 9+fuel=2+(3+(3+(1+fuel))) by omega,Nat.add_comm 2 (3+(3+(1+fuel)))]
  change Builtins.run (3+(3+(1+fuel))) {base with
    control:=.expression (.identifier "Game")
    continuation:=.memberObject (.identifier method) false::.callCallee [] false::base.continuation}=_
  rw [gameRead _ (by rfl),callee_data base method game function object present kind property,
    Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.MemberCallEmpty

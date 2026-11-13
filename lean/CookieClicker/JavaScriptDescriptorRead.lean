import CookieClicker.JavaScriptSourceRead

/-! Native data reads retain arbitrary writable/enumerable/configurable flags.
This includes the nonenumerable, nonconfigurable length of a real array. -/
namespace CookieClicker.JavaScript.SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem read_data_descriptor (base : Machine) (id : ObjectId) (key : JSString)
    (value : Value) (object : JSObject) (writable enumerable configurable : Bool)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=
      .ok (some (.data value writable enumerable configurable))) :
    readProperty base (.object id) key={base with control:=.expressionResult (.value value)} := by
  rcases ordinary with kind|kind <;>
    simp [readProperty,toObject,checked,readObjectProperty,present,kind,property,result]

theorem select_descriptor_dot (base : Machine) (id : ObjectId) (name : String)
    (value : Value) (object : JSObject) (writable enumerable configurable : Bool)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id (JSString.ofString name)=
      .ok (some (.data value writable enumerable configurable)))
    (consumer : ordinaryContinuation base.continuation=true) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value (.object id))
      continuation:=.memberObject (.identifier name) false::base.continuation}=
      Builtins.run fuel {base with control:=.expressionResult (.value value)} := by
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with
    control:=.expressionResult (.reference ⟨.property (.object id) (JSString.ofString name),base.context.strict⟩)}=_
  apply reference_value _ _ _ consumer
  exact read_data_descriptor _ id (JSString.ofString name) value object
    writable enumerable configurable present ordinary property

theorem dot_descriptor (base : Machine) (expression : Expr) (id : ObjectId) (name : String)
    (value : Value) (object : JSObject) (writable enumerable configurable : Bool) (ticks : Nat)
    (child : Reads base expression (.object id) ticks)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id (JSString.ofString name)=
      .ok (some (.data value writable enumerable configurable))) :
    Reads base (.member expression (.identifier name) false) value (ticks+4) := by
  intro continuation consumer fuel
  rw [show ticks+4+fuel=1+(ticks+(3+fuel)) by omega,Nat.add_comm 1 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {base with
    control:=.expression expression
    continuation:=.memberObject (.identifier name) false::continuation}=_
  rw [child _ (by rfl)]
  exact select_descriptor_dot {base with continuation} id name value object
    writable enumerable configurable present ordinary property consumer fuel

end CookieClicker.JavaScript.SourceRead

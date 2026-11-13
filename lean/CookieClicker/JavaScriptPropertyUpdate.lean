import CookieClicker.JavaScriptPropertyAssign

/-! Native numeric increment and decrement of an existing data property.
The receiver runs once. Prefix and postfix results, rounding, and other state
are retained by the source step equation. -/
namespace CookieClicker.JavaScript.PropertyUpdate
open SourceRead PropertyAssign
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def changedNumber (operator : UpdateOp) (old : UInt64) : UInt64 :=
  if operator==.increment then Number.add old Number.one else Number.sub old Number.one

def after (base : Machine) (id : ObjectId) (object : JSObject) (name : String)
    (operator : UpdateOp) (isPrefix : Bool) (old : UInt64) (enumerable configurable : Bool) : Machine := {
  base with
  heap:=PropertyFrame.write base.heap id object (JSString.ofString name)
    (.number (changedNumber operator old)) enumerable configurable
  control:=.completion (.normal (some (.number (if isPrefix then changedNumber operator old else old)))) }

theorem source_update (base : Machine) (receiver : Expr) (id : ObjectId) (object : JSObject)
    (name : String) (operator : UpdateOp) (isPrefix : Bool) (old : UInt64)
    (enumerable configurable : Bool) (ticks : Nat)
    (read : Reads base receiver (.object id) ticks)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (own : ownProperty object (JSString.ofString name)=some (.data (.number old) true enumerable configurable))
    (lookup : lookupProperty base.heap id (JSString.ofString name)=
      .ok (some (.data (.number old) true enumerable configurable))) (fuel : Nat) :
    Builtins.run (ticks+10+fuel) {base with
      control:=.statement (.expression (.update operator (.member receiver (.identifier name) false) isPrefix))}=
      Builtins.run fuel (after base id object name operator isPrefix old enumerable configurable) := by
  have checkedObjectRead : checkedObject base.heap id=.ok object := by simp [checkedObject,present]
  rw [show ticks+10+fuel=3+(ticks+(7+fuel)) by omega,Nat.add_comm 3 (ticks+(7+fuel))]
  change Builtins.run (ticks+(7+fuel)) {base with
    control:=.expression receiver
    continuation:=.memberObject (.identifier name) false::.update operator isPrefix::
      .expressionStatement::base.continuation}=_
  rw [read _ (by rfl),show 7+fuel=2+(5+fuel) by omega,Nat.add_comm 2 (5+fuel)]
  change Builtins.run (5+fuel) {base with
    control:=.getValue (reference base id name)
    continuation:=.updateRead operator (reference base id name) isPrefix::
      .expressionStatement::base.continuation}=_
  rw [show 5+fuel=1+(4+fuel) by omega,Nat.add_comm 1 (4+fuel)]
  change Builtins.run (4+fuel) {readProperty {base with
    control:=.getValue (reference base id name)
    continuation:=.updateRead operator (reference base id name) isPrefix::
      .expressionStatement::base.continuation} (.object id) (JSString.ofString name)
    with elapsed:=base.elapsed}=_
  simp only [readProperty,toObject,readObjectProperty,checkedObjectRead,ordinary,lookup,checked,result]
  rw [show 4+fuel=1+(3+fuel) by omega,Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) {base with
    control:=.putValue (reference base id name) (.number (changedNumber operator old))
    continuation:=.putResult (.number (if isPrefix then changedNumber operator old else old))::
      .expressionStatement::base.continuation}=_
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {writeProperty {base with
    control:=.putValue (reference base id name) (.number (changedNumber operator old))
    continuation:=.putResult (.number (if isPrefix then changedNumber operator old else old))::
      .expressionStatement::base.continuation} (.object id) (JSString.ofString name)
      (.number (changedNumber operator old)) base.context.strict with elapsed:=base.elapsed}=_
  rw [PropertyFrame.native_write {base with
    control:=.putValue (reference base id name) (.number (changedNumber operator old))
    continuation:=.putResult (.number (if isPrefix then changedNumber operator old else old))::
      .expressionStatement::base.continuation}
    id object (JSString.ofString name) (.number old)
    (.number (changedNumber operator old)) enumerable configurable base.context.strict
    present ordinary own lookup,Nat.add_comm 2 fuel]
  rfl

end CookieClicker.JavaScript.PropertyUpdate

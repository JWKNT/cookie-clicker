import CookieClicker.JavaScriptPropertyCreate
import CookieClicker.JavaScriptPropertyAssign
import CookieClicker.JavaScriptPropertyComputed

/-! Native assignment to a previously absent own field. This includes the
first post-reset CpS cache population and newly constructed Note fields. -/
namespace CookieClicker.JavaScript.PropertyAssignCreate
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem key_suffix (base : Machine) (id : ObjectId) (name : JSString)
    (object : JSObject) (value : Value)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (extensible : object.extensible=true)
    (own : ownProperty object name=none) (lookup : lookupProperty base.heap id name=.ok none)
    (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value value)
      continuation:=.assignmentRight .assign (PropertyComputed.reference base id name) none::
        .expressionStatement::base.continuation}=
    Builtins.run fuel {base with
      heap:=PropertyFrame.write base.heap id object name value true true
      control:=.completion (.normal (some value))} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run (fuel+1) {putReference {base with
    control:=.putValue (PropertyComputed.reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    (PropertyComputed.reference base id name) value with elapsed:=base.elapsed}=_
  change Builtins.run (fuel+1) {writeProperty {base with
    control:=.putValue (PropertyComputed.reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    (.object id) name value base.context.strict with elapsed:=base.elapsed}=_
  rw [PropertyCreate.native_create {base with
    control:=.putValue (PropertyComputed.reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    id object name value base.context.strict present ordinary extensible own lookup]
  rfl

theorem dot_suffix (base : Machine) (id : ObjectId) (name : String)
    (object : JSObject) (value : Value)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (extensible : object.extensible=true)
    (own : ownProperty object (JSString.ofString name)=none)
    (lookup : lookupProperty base.heap id (JSString.ofString name)=.ok none) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value value)
      continuation:=.assignmentRight .assign (PropertyAssign.reference base id name) none::
        .expressionStatement::base.continuation}=
    Builtins.run fuel {base with
      heap:=PropertyFrame.write base.heap id object (JSString.ofString name) value true true
      control:=.completion (.normal (some value))} :=
  key_suffix base id (JSString.ofString name) object value present ordinary extensible own lookup fuel

theorem dot_statement (base : Machine) (receiver expression : Expr) (id : ObjectId)
    (name : String) (object : JSObject) (value : Value) (leftTicks rightTicks : Nat)
    (receiverRead : Reads base receiver (.object id) leftTicks)
    (valueRead : Reads base expression value rightTicks)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (extensible : object.extensible=true)
    (own : ownProperty object (JSString.ofString name)=none)
    (lookup : lookupProperty base.heap id (JSString.ofString name)=.ok none) (fuel : Nat) :
    Builtins.run (leftTicks+rightTicks+8+fuel) {base with
      control:=.statement (.expression (.assignment .assign
        (.member receiver (.identifier name) false) expression))}=
    Builtins.run fuel {base with
      heap:=PropertyFrame.write base.heap id object (JSString.ofString name) value true true
      control:=.completion (.normal (some value))} := by
  rw [show leftTicks+rightTicks+8+fuel=(leftTicks+5)+(rightTicks+(3+fuel)) by omega,
    PropertyAssign.dot_prefix base receiver expression id name leftTicks receiverRead]
  refine (valueRead _ (by rfl) (3+fuel)).trans ?_
  exact dot_suffix base id name object value present ordinary extensible own lookup fuel

end CookieClicker.JavaScript.PropertyAssignCreate

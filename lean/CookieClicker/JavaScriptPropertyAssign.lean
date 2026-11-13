import CookieClicker.JavaScriptPropertyFrame

namespace CookieClicker.JavaScript.PropertyAssign
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def reference (base : Machine) (id : ObjectId) (name : String) : Reference :=
  ⟨.property (.object id) (JSString.ofString name),base.context.strict⟩

def right (base : Machine) (id : ObjectId) (name : String) (value : Expr) : Machine := {
  base with
  control:=.expression value
  continuation:=.assignmentRight .assign (reference base id name) none::.expressionStatement::base.continuation }

/-- The actual dot-assignment prelude evaluates its receiver once, then leaves
its native reference on the stack while the complete right-hand expression runs. -/
theorem dot_prefix (base : Machine) (receiver value : Expr) (id : ObjectId)
    (name : String) (ticks : Nat) (read : Reads base receiver (.object id) ticks) (fuel : Nat) :
    Builtins.run (ticks+5+fuel) {base with
      control:=.statement (.expression (.assignment .assign (.member receiver (.identifier name) false) value))}=
    Builtins.run fuel (right base id name value) := by
  rw [show ticks+5+fuel=3+(ticks+(2+fuel)) by omega,Nat.add_comm 3 (ticks+(2+fuel))]
  change Builtins.run (ticks+(2+fuel)) {base with
    control:=.expression receiver
    continuation:=.memberObject (.identifier name) false::
      .assignmentLeft .assign value::.expressionStatement::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 2 fuel]
  rfl

/-- Native assignment writes the value returned by the right-hand expression;
all its heap allocations and prior effects are retained. -/
theorem dot_suffix (base : Machine) (id : ObjectId) (name : String)
    (object : JSObject) (old value : Value) (en config : Bool)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (own : ownProperty object (JSString.ofString name)=some (.data old true en config))
    (lookup : lookupProperty base.heap id (JSString.ofString name)=.ok (some (.data old true en config)))
    (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value value)
      continuation:=.assignmentRight .assign (reference base id name) none::.expressionStatement::base.continuation}=
    Builtins.run fuel {base with
      heap:=PropertyFrame.write base.heap id object (JSString.ofString name) value en config
      control:=.completion (.normal (some value))} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run (fuel+1) {putReference {base with
    control:=.putValue (reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    (reference base id name) value with elapsed:=base.elapsed}=_
  change Builtins.run (fuel+1) {writeProperty {base with
    control:=.putValue (reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    (.object id) (JSString.ofString name) value base.context.strict with elapsed:=base.elapsed}=_
  rw [PropertyFrame.native_write {base with
    control:=.putValue (reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    id object (JSString.ofString name) old value en config
    base.context.strict present ordinary own lookup]
  rfl

end CookieClicker.JavaScript.PropertyAssign

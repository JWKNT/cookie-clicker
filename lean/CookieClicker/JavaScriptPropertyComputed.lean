import CookieClicker.JavaScriptPropertyFrame

namespace CookieClicker.JavaScript.PropertyComputed
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def reference (base : Machine) (id : ObjectId) (name : JSString) : Reference :=
  ⟨.property (.object id) name,base.context.strict⟩

def right (base : Machine) (id : ObjectId) (name : JSString) (value : Expr) : Machine := {
  base with
  control:=.expression value
  continuation:=.assignmentRight .assign (reference base id name) none::.expressionStatement::base.continuation }

/-- Computed assignment retains the exact public string key and evaluates
both receiver and key once before entering its right-hand expression. -/
theorem key_prefix (base : Machine) (receiver keyExpression value : Expr) (id : ObjectId)
    (name : JSString) (leftTicks rightTicks : Nat)
    (left : Reads base receiver (.object id) leftTicks)
    (key : Reads base keyExpression (.string name) rightTicks) (fuel : Nat) :
    Builtins.run (leftTicks+rightTicks+6+fuel) {base with
      control:=.statement (.expression (.assignment .assign (.member receiver keyExpression true) value))}=
    Builtins.run fuel (right base id name value) := by
  rw [show leftTicks+rightTicks+6+fuel=3+(leftTicks+(1+(rightTicks+(2+fuel)))) by omega,
    Nat.add_comm 3 (leftTicks+(1+(rightTicks+(2+fuel))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(2+fuel)))) {base with
    control:=.expression receiver
    continuation:=.memberObject keyExpression true::
      .assignmentLeft .assign value::.expressionStatement::base.continuation}=_
  rw [left _ (by rfl),Nat.add_comm 1 (rightTicks+(2+fuel))]
  change Builtins.run (rightTicks+(2+fuel)) {base with
    control:=.expression keyExpression
    continuation:=.memberProperty (.object id)::
      .assignmentLeft .assign value::.expressionStatement::base.continuation}=_
  rw [key _ (by rfl),Nat.add_comm 2 fuel]
  rfl

/-- Native assignment writes the value returned by the right-hand expression;
all its heap allocations and prior effects are retained. -/
theorem key_suffix (base : Machine) (id : ObjectId) (name : JSString)
    (object : JSObject) (old value : Value) (en config : Bool)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (own : ownProperty object name=some (.data old true en config))
    (lookup : lookupProperty base.heap id name=.ok (some (.data old true en config)))
    (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value value)
      continuation:=.assignmentRight .assign (reference base id name) none::.expressionStatement::base.continuation}=
    Builtins.run fuel {base with
      heap:=PropertyFrame.write base.heap id object name value en config
      control:=.completion (.normal (some value))} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run (fuel+1) {putReference {base with
    control:=.putValue (reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    (reference base id name) value with elapsed:=base.elapsed}=_
  change Builtins.run (fuel+1) {writeProperty {base with
    control:=.putValue (reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    (.object id) name value base.context.strict with elapsed:=base.elapsed}=_
  rw [PropertyFrame.native_write {base with
    control:=.putValue (reference base id name) value
    continuation:=.expressionStatement::base.continuation}
    id object name old value en config
    base.context.strict present ordinary own lookup]
  rfl

end CookieClicker.JavaScript.PropertyComputed

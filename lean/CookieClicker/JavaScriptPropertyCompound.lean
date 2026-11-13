import CookieClicker.JavaScriptPropertyAssign
import CookieClicker.JavaScriptReadCombinators

namespace CookieClicker.JavaScript.PropertyCompound
open SourceRead PropertyAssign
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def right (base : Machine) (id : ObjectId) (name : String) (operator : AssignmentOp)
    (old : Value) (value : Expr) : Machine := {
  base with
  control:=.expression value
  continuation:=.assignmentRight operator (reference base id name) (some old)::
    .expressionStatement::base.continuation }

theorem dot_prefix (base : Machine) (receiver value : Expr) (id : ObjectId)
    (name : String) (operator : AssignmentOp) (notAssign : operator≠.assign)
    (old : Value) (object : JSObject) (ticks : Nat)
    (read : Reads base receiver (.object id) ticks)
    (present : checkedObject base.heap id=.ok object) (ordinary : object.kind=.ordinary)
    (lookup : lookupProperty base.heap id (JSString.ofString name)=.ok (some (.data old true true true)))
    (fuel : Nat) :
    Builtins.run (ticks+7+fuel) {base with
      control:=.statement (.expression (.assignment operator (.member receiver (.identifier name) false) value))}=
    Builtins.run fuel (right base id name operator old value) := by
  rw [show ticks+7+fuel=3+(ticks+(4+fuel)) by omega,Nat.add_comm 3 (ticks+(4+fuel))]
  change Builtins.run (ticks+(4+fuel)) {base with
    control:=.expression receiver
    continuation:=.memberObject (.identifier name) false::
      .assignmentLeft operator value::.expressionStatement::base.continuation}=_
  rw [read _ (by rfl),show 4+fuel=(3+fuel)+1 by omega]
  change Builtins.run (3+fuel) {base with
    control:=.expressionResult (.reference (reference base id name))
    continuation:=.assignmentLeft operator value::.expressionStatement::base.continuation}=_
  have first : Builtins.builtinStep {base with
      control:=.expressionResult (.reference (reference base id name))
      continuation:=.assignmentLeft operator value::.expressionStatement::base.continuation}=
      {base with
        control:=.getValue (reference base id name)
        continuation:=.assignmentRead operator (reference base id name) value::.expressionStatement::base.continuation} := by
    cases operator <;> first | contradiction | rfl
  rw [show 3+fuel=(2+fuel)+1 by omega]
  change Builtins.run (2+fuel) (Builtins.builtinStep _) =_
  rw [first,show 2+fuel=(1+fuel)+1 by omega]
  change Builtins.run (1+fuel) {getReference {base with
    control:=.getValue (reference base id name)
    continuation:=.assignmentRead operator (reference base id name) value::.expressionStatement::base.continuation}
    (reference base id name) with elapsed:=base.elapsed}=_
  have get := read_data_property {base with
    control:=.getValue (reference base id name)
    continuation:=.assignmentRead operator (reference base id name) value::.expressionStatement::base.continuation}
    id (JSString.ofString name) old object present (Or.inl ordinary) lookup
  change Builtins.run (1+fuel) {readProperty {base with
    control:=.getValue (reference base id name)
    continuation:=.assignmentRead operator (reference base id name) value::.expressionStatement::base.continuation}
    (.object id) (JSString.ofString name) with elapsed:=base.elapsed}=_
  rw [get]
  rw [Nat.add_comm 1 fuel]
  rfl

theorem dot_suffix (base : Machine) (id : ObjectId) (name : String)
    (operator : AssignmentOp) (binaryOperator : BinaryOp)
    (assigned : assignmentBinary operator=some binaryOperator)
    (object : JSObject) (old credit value : Value)
    (oldPrimitive : isObject old=false) (creditPrimitive : isObject credit=false)
    (notIn : binaryOperator≠.inOp)
    (computed : binaryWithHeap base.heap binaryOperator old credit=.ok value)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (own : ownProperty object (JSString.ofString name)=some (.data old true true true))
    (lookup : lookupProperty base.heap id (JSString.ofString name)=.ok (some (.data old true true true)))
    (fuel : Nat) :
    Builtins.run (4+fuel) {base with
      control:=.expressionResult (.value credit)
      continuation:=.assignmentRight operator (reference base id name) (some old)::
        .expressionStatement::base.continuation}=
    Builtins.run fuel {base with
      heap:=PropertyFrame.write base.heap id object (JSString.ofString name) value true true
      control:=.completion (.normal (some value))} := by
  rw [show 4+fuel=(3+fuel)+1 by omega]
  change Builtins.run (3+fuel) (Builtins.builtinStep _) =_
  have first : Builtins.builtinStep {base with
      control:=.expressionResult (.value credit)
      continuation:=.assignmentRight operator (reference base id name) (some old)::
        .expressionStatement::base.continuation}=
      {base with
        control:=.expressionResult (.value value)
        continuation:=.assignmentConverted (reference base id name)::.expressionStatement::base.continuation} := by
    simp [Builtins.builtinStep,step,internalStep,consumeValue,assigned,beginBinary,
      oldPrimitive,creditPrimitive,notIn,computed,checked,result]
  rw [first]
  have suffix := PropertyAssign.dot_suffix base id name object old value true true
    present ordinary own lookup fuel
  rw [show 3+fuel=(2+fuel)+1 by omega]
  change Builtins.run (2+fuel) (Builtins.builtinStep _) =_
  rw [show Builtins.builtinStep {base with
      control:=.expressionResult (.value value)
      continuation:=.assignmentConverted (reference base id name)::.expressionStatement::base.continuation}=
      Builtins.builtinStep {base with
        control:=.expressionResult (.value value)
        continuation:=.assignmentRight .assign (reference base id name) none::
          .expressionStatement::base.continuation} from rfl]
  rw [show 3+fuel=(2+fuel)+1 by omega] at suffix
  change Builtins.run (2+fuel) (Builtins.builtinStep _) =_ at suffix
  exact suffix

end CookieClicker.JavaScript.PropertyCompound

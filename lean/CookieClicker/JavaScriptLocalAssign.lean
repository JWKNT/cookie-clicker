import CookieClicker.JavaScriptSourceBinding
import CookieClicker.JavaScriptReadCombinators

namespace CookieClicker.JavaScript.LocalAssign
open SourceRead SourceBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem source_assignment (base : Machine) (name : String) (slot : Slot base name)
    (expression : Expr) (value : Value) (ticks : Nat)
    (read : Reads base expression value ticks)
    (noName : nameFrames expression (JSString.ofString name)=[]) (fuel : Nat) :
    Builtins.run (ticks+7+fuel) {base with
      control:=.statement (.expression (.assignment .assign (.identifier name) expression))}=
    Builtins.run fuel {slot.after value with control:=.completion (.normal (some value))} := by
  conv => lhs;arg 1;rw [show ticks+7+fuel=3+(1+(ticks+(3+fuel))) by omega,Nat.add_comm 3 (1+(ticks+(3+fuel)))]
  change Builtins.run (1+(ticks+(3+fuel))) (Environment.identifier {base with
    control:=.expression (.identifier name)
    continuation:=.assignmentLeft .assign expression::.expressionStatement::base.continuation} name)=_
  simp only [Environment.identifier,Environment.resolve,slot.present,slot.exists,checked]
  conv => lhs;arg 1;rw [Nat.add_comm 1 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {base with
    control:=.expression expression
    continuation:=nameFrames expression (JSString.ofString name) ++
      (.assignmentRight .assign ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ none::
      .expressionStatement::base.continuation)}=_
  rw [noName,List.nil_append,read _ (by rfl)]
  conv => lhs;arg 1;rw [show 3+fuel=2+(1+fuel) by omega,Nat.add_comm 2 (1+fuel)]
  change Builtins.run (1+fuel) {putReference {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ value
    continuation:=.expressionStatement::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ value with elapsed:=base.elapsed}=_
  simp only [putReference,slot.present,checked,slot.write,result]
  conv => lhs;arg 1;rw [Nat.add_comm 1 fuel]
  rfl

theorem true_and (base : Machine) (left right : Expr) (a value : Value)
    (leftTicks rightTicks : Nat) (readLeft : Reads base left a leftTicks)
    (readRight : Reads base right value rightTicks) (truth : truthy a=true) :
    Reads base (.logical .and left right) value (leftTicks+rightTicks+3) := by
  intro continuation consumer fuel
  conv => lhs;arg 1;rw [show leftTicks+rightTicks+3+fuel=1+(leftTicks+(1+(rightTicks+(1+fuel)))) by omega,
    Nat.add_comm 1 (leftTicks+(1+(rightTicks+(1+fuel))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(1+fuel)))) {base with
    control:=.expression left,continuation:=.logical .and right::continuation}=_
  rw [readLeft _ (by rfl)]
  conv => lhs;arg 1;rw [Nat.add_comm 1 (rightTicks+(1+fuel))]
  have step : Builtins.builtinStep {base with
      control:=.expressionResult (.value a),continuation:=.logical .and right::continuation}=
      {base with control:=.expression right,continuation:=.valueBoundary::continuation} := by
    simp [Builtins.builtinStep,JavaScript.step,internalStep,consumeValue,truth,pushExpression]
  change Builtins.run (rightTicks+(1+fuel)) (Builtins.builtinStep _) =_
  rw [step,readRight _ (by rfl)]
  conv => lhs;arg 1;rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.LocalAssign

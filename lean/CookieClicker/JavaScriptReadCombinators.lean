import CookieClicker.JavaScriptSourceRead

/-! Native composition of pure source reads. Every rule retains the full
machine and evaluates through the actual operator/continuation semantics. -/
namespace CookieClicker.JavaScript.SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem binary_value (base : Machine) (operator : BinaryOp) (left right : Expr)
    (a b value : Value) (leftTicks rightTicks : Nat)
    (readLeft : Reads base left a leftTicks) (readRight : Reads base right b rightTicks)
    (leftPrimitive : isObject a=false) (rightPrimitive : isObject b=false)
    (notIn : operator≠.inOp)
    (computed : binaryWithHeap base.heap operator a b=.ok value) :
    Reads base (.binary operator left right) value (leftTicks+rightTicks+3) := by
  intro continuation consumer fuel
  rw [show leftTicks+rightTicks+3+fuel=1+(leftTicks+(1+(rightTicks+(1+fuel)))) by omega,
    Nat.add_comm 1 (leftTicks+(1+(rightTicks+(1+fuel))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(1+fuel)))) {base with
    control:=.expression left,continuation:=.binaryLeft operator right::continuation}=_
  rw [readLeft _ (by rfl),Nat.add_comm 1 (rightTicks+(1+fuel))]
  change Builtins.run (rightTicks+(1+fuel)) {base with
    control:=.expression right,continuation:=.binaryRight operator a::continuation}=_
  rw [readRight _ (by rfl),Nat.add_comm 1 fuel]
  change Builtins.run fuel {beginBinary {base with
    control:=.expressionResult (.value b),continuation} operator a b with elapsed:=base.elapsed}=_
  simp [beginBinary,leftPrimitive,rightPrimitive,notIn,computed,checked,result]

theorem string_equal (base : Machine) (left right : Expr) (a b : JSString)
    (leftTicks rightTicks : Nat)
    (readLeft : Reads base left (.string a) leftTicks)
    (readRight : Reads base right (.string b) rightTicks) :
    Reads base (.binary .equal left right) (.boolean (decide (a=b))) (leftTicks+rightTicks+3) := by
  apply binary_value base .equal left right (.string a) (.string b) (.boolean (decide (a=b)))
    leftTicks rightTicks readLeft readRight rfl rfl (by decide)
  simp [binaryWithHeap,binary,abstractEqual,sameType,strictEqual,Except.bind,bind,Except.pure,pure]

theorem false_or (base : Machine) (left right : Expr) (a value : Value)
    (leftTicks rightTicks : Nat) (readLeft : Reads base left a leftTicks)
    (readRight : Reads base right value rightTicks) (falsy : truthy a=false) :
    Reads base (.logical .or left right) value (leftTicks+rightTicks+3) := by
  intro continuation consumer fuel
  rw [show leftTicks+rightTicks+3+fuel=1+(leftTicks+(1+(rightTicks+(1+fuel)))) by omega,
    Nat.add_comm 1 (leftTicks+(1+(rightTicks+(1+fuel))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(1+fuel)))) {base with
    control:=.expression left,continuation:=.logical .or right::continuation}=_
  rw [readLeft _ (by rfl),Nat.add_comm 1 (rightTicks+(1+fuel))]
  have step : Builtins.builtinStep {base with
      control:=.expressionResult (.value a),continuation:=.logical .or right::continuation}=
      {base with control:=.expression right,continuation:=.valueBoundary::continuation} := by
    simp [Builtins.builtinStep,step,internalStep,consumeValue,falsy,pushExpression]
  change Builtins.run (rightTicks+(1+fuel)) (Builtins.builtinStep _) =_
  rw [step,readRight _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem return_read (base : Machine) (expression : Expr) (value : Value) (ticks : Nat)
    (read : Reads base expression value ticks) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) {base with control:=.statement (.return (some expression))}=
      Builtins.run fuel {base with control:=.completion (.return value)} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression expression,continuation:=.returnValue::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.SourceRead

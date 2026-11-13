import CookieClicker.JavaScriptNativeMemberCall
import CookieClicker.JavaScriptArrayQueueInvocation

/-! Source expressions invoke the native dense-array methods. Receiver,
argument and inherited-method evaluation precede the complete builtin call. -/
namespace CookieClicker.JavaScript.SourceArrayQueue
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def unshiftExpression (receiver argument : Expr) : Expr :=
  .call (.member receiver (.identifier "unshift") false) [argument]

theorem unshift (base : Machine) (receiver argument : Expr) (array function : ObjectId)
    (frame : DenseArrayState.Frame base.heap array) (value : Value) (small : frame.length<256)
    (functionObject : JSObject) (functionRead : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.builtin ArrayUnshift.id)
    (property : lookupProperty base.heap array (JSString.ofString "unshift")=
      .ok (some (.data (.object function) true false true)))
    (receiverTicks argumentTicks : Nat)
    (receiverRead : Reads base receiver (.object array) receiverTicks)
    (argumentRead : Reads base argument value argumentTicks) (fuel : Nat) :
    Builtins.run (receiverTicks+argumentTicks+16+5*frame.length+fuel)
      {base with control:=.expression (unshiftExpression receiver argument)}=
      Builtins.run fuel (ArrayUnshiftLoop.returned base array frame value small) := by
  rw [show receiverTicks+argumentTicks+16+5*frame.length+fuel=
      (receiverTicks+argumentTicks+7)+(9+5*frame.length+fuel) by omega]
  rw [unshiftExpression,NativeMemberCall.one base receiver "unshift" argument array function frame.object value
    true false true receiverTicks argumentTicks frame.present (Or.inr frame.shape.kind) property
    receiverRead argumentRead]
  exact ArrayQueueInvocation.unshift base function array functionObject functionRead functionKind
    frame value small fuel

def unshiftDone (base : Machine) (array : ObjectId) (frame : DenseArrayState.Frame base.heap array)
    (value : Value) (small : frame.length<256) : Machine := {
  ArrayUnshiftLoop.returned base array frame value small with
  control:=.completion (.normal (some (.number (Number.ofNat (frame.length+1))))) }

theorem unshift_statement (base : Machine) (receiver argument : Expr) (array function : ObjectId)
    (frame : DenseArrayState.Frame base.heap array) (value : Value) (small : frame.length<256)
    (functionObject : JSObject) (functionRead : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.builtin ArrayUnshift.id)
    (property : lookupProperty base.heap array (JSString.ofString "unshift")=
      .ok (some (.data (.object function) true false true)))
    (receiverTicks argumentTicks : Nat)
    (receiverRead : Reads base receiver (.object array) receiverTicks)
    (argumentRead : Reads base argument value argumentTicks) (fuel : Nat) :
    Builtins.run (receiverTicks+argumentTicks+18+5*frame.length+fuel)
      {base with control:=.statement (.expression (unshiftExpression receiver argument))}=
      Builtins.run fuel (unshiftDone base array frame value small) := by
  rw [show receiverTicks+argumentTicks+18+5*frame.length+fuel=
      1+((receiverTicks+argumentTicks+16+5*frame.length)+(1+fuel)) by omega,
    Nat.add_comm 1 ((receiverTicks+argumentTicks+16+5*frame.length)+(1+fuel))]
  change Builtins.run ((receiverTicks+argumentTicks+16+5*frame.length)+(1+fuel))
    {base with
      control:=.expression (unshiftExpression receiver argument)
      continuation:=.expressionStatement::base.continuation}=_
  rw [unshift {base with continuation:=.expressionStatement::base.continuation}
    receiver argument array function frame value small functionObject functionRead functionKind
    property receiverTicks argumentTicks receiverRead argumentRead,Nat.add_comm 1 fuel]
  rfl

def popExpression (receiver : Expr) : Expr :=
  .call (.member receiver (.identifier "pop") false) []

theorem pop (i : ArrayPop.Inputs) (receiver : Expr) (function : ObjectId)
    (functionObject : JSObject) (functionRead : checkedObject i.base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.builtin ArrayPop.method)
    (property : lookupProperty i.base.heap i.array (JSString.ofString "pop")=
      .ok (some (.data (.object function) true false true)))
    (receiverTicks : Nat) (receiverRead : Reads i.base receiver (.object i.array) receiverTicks)
    (fuel : Nat) :
    Builtins.run (receiverTicks+16+fuel) {i.base with control:=.expression (popExpression receiver)}=
      Builtins.run fuel (ArrayPop.returned i) := by
  rw [popExpression,show receiverTicks+16+fuel=(receiverTicks+6)+(10+fuel) by omega,
    NativeMemberCall.empty i.base receiver "pop" i.array function i.frame.object true false true
      receiverTicks i.frame.present (Or.inr i.frame.shape.kind) property receiverRead]
  exact ArrayQueueInvocation.pop i function functionObject functionRead functionKind fuel

def popDone (i : ArrayPop.Inputs) : Machine := {
  ArrayPop.returned i with control:=.completion (.normal (some (ArrayPop.selected i))) }

theorem pop_statement (i : ArrayPop.Inputs) (receiver : Expr) (function : ObjectId)
    (functionObject : JSObject) (functionRead : checkedObject i.base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.builtin ArrayPop.method)
    (property : lookupProperty i.base.heap i.array (JSString.ofString "pop")=
      .ok (some (.data (.object function) true false true)))
    (receiverTicks : Nat) (receiverRead : Reads i.base receiver (.object i.array) receiverTicks)
    (fuel : Nat) :
    Builtins.run (receiverTicks+18+fuel)
      {i.base with control:=.statement (.expression (popExpression receiver))}=
      Builtins.run fuel (popDone i) := by
  rw [show receiverTicks+18+fuel=1+((receiverTicks+16)+(1+fuel)) by omega,
    Nat.add_comm 1 ((receiverTicks+16)+(1+fuel))]
  let withStack : ArrayPop.Inputs := {i with
    base:={i.base with continuation:=.expressionStatement::i.base.continuation}}
  change Builtins.run ((receiverTicks+16)+(1+fuel))
    {withStack.base with control:=.expression (popExpression receiver)}=_
  rw [pop withStack receiver function functionObject functionRead functionKind property
    receiverTicks receiverRead,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.SourceArrayQueue

import CookieClicker.JavaScriptDescriptorRead
import CookieClicker.JavaScriptMemberCall

/-! Calls through ordinary and array receivers retain native descriptor flags,
receiver evaluation and argument evaluation. Inherited methods are included. -/
namespace CookieClicker.JavaScript.NativeMemberCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem callee (base : Machine) (name : String) (arguments : List Expr)
    (receiver function : ObjectId) (object : JSObject) (writable enumerable configurable : Bool)
    (present : checkedObject base.heap receiver=.ok object)
    (kind : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap receiver (JSString.ofString name)=
      .ok (some (.data (.object function) writable enumerable configurable))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value (.object receiver))
      continuation:=.memberObject (.identifier name) false::
        .callCallee arguments false::base.continuation}=
      Builtins.run fuel {base with
        control:=.expressionResult (.value (.object function))
        continuation:=.callResolved (.object receiver) arguments false::base.continuation} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control:=.getValue ⟨.property (.object receiver) (JSString.ofString name),base.context.strict⟩
    continuation:=.callResolved (.object receiver) arguments false::base.continuation}
    (.object receiver) (JSString.ofString name) with elapsed:=base.elapsed}=_
  rw [read_data_descriptor {base with
    control:=.getValue ⟨.property (.object receiver) (JSString.ofString name),base.context.strict⟩
    continuation:=.callResolved (.object receiver) arguments false::base.continuation}
    receiver (JSString.ofString name) (.object function) object writable enumerable configurable
    present kind property]

theorem one (base : Machine) (expression : Expr) (name : String) (argument : Expr)
    (receiver function : ObjectId) (object : JSObject) (value : Value)
    (writable enumerable configurable : Bool) (receiverTicks argumentTicks : Nat)
    (present : checkedObject base.heap receiver=.ok object)
    (kind : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap receiver (JSString.ofString name)=
      .ok (some (.data (.object function) writable enumerable configurable)))
    (receiverRead : Reads base expression (.object receiver) receiverTicks)
    (argumentRead : Reads base argument value argumentTicks) (fuel : Nat) :
    Builtins.run (receiverTicks+argumentTicks+7+fuel) {base with
      control:=.expression (.call (.member expression (.identifier name) false) [argument])}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object receiver) [value] false} := by
  rw [show receiverTicks+argumentTicks+7+fuel=2+(receiverTicks+(3+(argumentTicks+2+fuel))) by omega,
    Nat.add_comm 2 (receiverTicks+(3+(argumentTicks+2+fuel)))]
  change Builtins.run (receiverTicks+(3+(argumentTicks+2+fuel))) {base with
    control:=.expression expression
    continuation:=.memberObject (.identifier name) false::.callCallee [argument] false::base.continuation}=_
  rw [receiverRead _ (by rfl),callee base name [argument] receiver function object
    writable enumerable configurable present kind property]
  exact MemberCall.argument_value base argument value receiver function argumentTicks argumentRead fuel

theorem empty (base : Machine) (expression : Expr) (name : String)
    (receiver function : ObjectId) (object : JSObject) (writable enumerable configurable : Bool)
    (receiverTicks : Nat) (present : checkedObject base.heap receiver=.ok object)
    (kind : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap receiver (JSString.ofString name)=
      .ok (some (.data (.object function) writable enumerable configurable)))
    (receiverRead : Reads base expression (.object receiver) receiverTicks) (fuel : Nat) :
    Builtins.run (receiverTicks+6+fuel) {base with
      control:=.expression (.call (.member expression (.identifier name) false) [])}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object receiver) [] false} := by
  rw [show receiverTicks+6+fuel=2+(receiverTicks+(3+(1+fuel))) by omega,
    Nat.add_comm 2 (receiverTicks+(3+(1+fuel)))]
  change Builtins.run (receiverTicks+(3+(1+fuel))) {base with
    control:=.expression expression
    continuation:=.memberObject (.identifier name) false::.callCallee [] false::base.continuation}=_
  rw [receiverRead _ (by rfl),callee base name [] receiver function object
    writable enumerable configurable present kind property,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.NativeMemberCall

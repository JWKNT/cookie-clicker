import CookieClicker.JavaScriptMemberCall

namespace CookieClicker.JavaScript.GlobalCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

structure Callee (base : Machine) (name : String) (function : ObjectId) where
  target : EnvId
  depth : Nat
  window : ObjectId
  object : JSObject
  writable : Bool
  enumerable : Bool
  configurable : Bool
  chain : HasEnvironment.DeclarativePath base.heap.environments name base.context.lexicalEnvironment target depth
  room : depth≤base.heap.environments.size
  globalRead : checkedEnvironment base.heap target=.ok ⟨.object window false,none⟩
  objectRead : checkedObject base.heap window=.ok object
  kind : object.kind=.host "Window" 0
  property : lookupProperty base.heap window (JSString.ofString name)=
    .ok (some (.data (.object function) writable enumerable configurable))
  exclusions : base.objectEnvironmentExclusions=[]

def atFunction (base : Machine) (function : ObjectId) (arguments : List Expr) : Machine := {
  base with
  control:=.expressionResult (.value (.object function))
  continuation:=.callResolved .undefined arguments false::base.continuation }

theorem callee_prefix (base : Machine) (name : String) (function : ObjectId)
    (input : Callee base name function) (arguments : List Expr) (fuel : Nat) :
    Builtins.run (4+fuel) {base with
    control:=.expression (.call (.identifier name) arguments)}=
      Builtins.run fuel (atFunction base function arguments) := by
  rw [show 4+fuel=1+(1+(2+fuel)) by omega,Nat.add_comm 1 (1+(2+fuel))]
  change Builtins.run (1+(2+fuel)) {base with
    control:=.expression (.identifier name)
    continuation:=.callCallee arguments false::base.continuation}=_
  rw [Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) (Environment.identifier {base with
    control:=.expression (.identifier name)
    continuation:=.callCallee arguments false::base.continuation} name)=_
  rw [IdentifierPath.identifier {base with
      control:=.expression (.identifier name)
      continuation:=.callCallee arguments false::base.continuation} name input.target input.depth input.window _
    input.chain input.room input.globalRead input.property input.exclusions]
  have receiver : referenceThis base ⟨.environment input.target name,base.context.strict⟩=.ok .undefined := by
    simp [referenceThis,input.globalRead,Except.bind,Except.pure,bind,pure]
  rw [Nat.add_comm 2 fuel]
  change Builtins.run (fuel+1) {checked base
    (referenceThis base ⟨.environment input.target name,base.context.strict⟩) (fun thisValue=>
      {base with
        control:=.getValue ⟨.environment input.target name,base.context.strict⟩
        continuation:=.callResolved thisValue arguments false::base.continuation}) with elapsed:=base.elapsed}=_
  rw [receiver]
  change Builtins.run fuel {getReference {base with
    control:=.getValue ⟨.environment input.target name,base.context.strict⟩
    continuation:=.callResolved .undefined arguments false::base.continuation}
    ⟨.environment input.target name,base.context.strict⟩ with elapsed:=base.elapsed}=_
  rw [IdentifierPath.read_window_data {base with
      control:=.getValue ⟨.environment input.target name,base.context.strict⟩
      continuation:=.callResolved .undefined arguments false::base.continuation} name input.target input.window input.object (.object function)
    input.writable input.enumerable input.configurable base.context.strict
    input.globalRead input.objectRead input.kind input.property]
  rfl

theorem arguments_two (base : Machine) (function : ObjectId) (first second : Expr)
    (left right : Value) (firstTicks secondTicks : Nat)
    (firstRead : Reads base first left firstTicks) (secondRead : Reads base second right secondTicks)
    (fuel : Nat) :
    Builtins.run (firstTicks+secondTicks+3+fuel) (atFunction base function [first,second])=
      Builtins.run fuel {base with
    control:=.invoke (.object function) .undefined [left,right] false} := by
  rw [show firstTicks+secondTicks+3+fuel=1+(firstTicks+(1+(secondTicks+(1+fuel)))) by omega,
    Nat.add_comm 1 (firstTicks+(1+(secondTicks+(1+fuel))))]
  change Builtins.run (firstTicks+(1+(secondTicks+(1+fuel)))) {base with
    control:=.expression first
    continuation:=.callArguments (.object function) .undefined [] [second] false::base.continuation}=_
  rw [firstRead _ (by rfl),Nat.add_comm 1 (secondTicks+(1+fuel))]
  change Builtins.run (secondTicks+(1+fuel)) {base with
    control:=.expression second
    continuation:=.callArguments (.object function) .undefined [left] [] false::base.continuation}=_
  rw [secondRead _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem source_two (base : Machine) (name : String) (function : ObjectId)
    (input : Callee base name function) (first second : Expr) (left right : Value)
    (firstTicks secondTicks : Nat)
    (firstRead : Reads base first left firstTicks) (secondRead : Reads base second right secondTicks)
    (fuel : Nat) :
    Builtins.run (firstTicks+secondTicks+7+fuel)
      {base with
    control:=.expression (.call (.identifier name) [first,second])}=
      Builtins.run fuel {base with
    control:=.invoke (.object function) .undefined [left,right] false} := by
  rw [show firstTicks+secondTicks+7+fuel=4+(firstTicks+secondTicks+3+fuel) by omega,
    callee_prefix base name function input]
  exact arguments_two base function first second left right firstTicks secondTicks firstRead secondRead fuel

theorem argument_one (base : Machine) (function : ObjectId) (argument : Expr)
    (value : Value) (ticks : Nat) (read : Reads base argument value ticks) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) (atFunction base function [argument])=
      Builtins.run fuel {base with control:=.invoke (.object function) .undefined [value] false} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression argument
    continuation:=.callArguments (.object function) .undefined [] [] false::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem source_one (base : Machine) (name : String) (function : ObjectId)
    (input : Callee base name function) (argument : Expr) (value : Value) (ticks : Nat)
    (read : Reads base argument value ticks) (fuel : Nat) :
    Builtins.run (ticks+6+fuel) {base with control:=.expression (.call (.identifier name) [argument])}=
      Builtins.run fuel {base with control:=.invoke (.object function) .undefined [value] false} := by
  rw [show ticks+6+fuel=4+(ticks+2+fuel) by omega,callee_prefix base name function input]
  exact argument_one base function argument value ticks read fuel

end CookieClicker.JavaScript.GlobalCall

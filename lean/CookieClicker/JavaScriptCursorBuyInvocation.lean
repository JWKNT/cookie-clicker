import CookieClicker.JavaScriptCursorBuyClauses

namespace CookieClicker.JavaScript.CursorBuyInvocation
open CursorBuyClauses SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,[],clauses,scope,false,source⟩

def argumentObject (base : Machine) (callee : Option ObjectId := none) : JSObject := {
  kind:=.arguments []
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "length",.data (.number 0) true false true⟩]++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }

def localBindings (base : Machine) : List Binding :=
  [{name:="arguments",value:=.object base.heap.objects.size}]

def allocatedHeap (base : Machine) (scope : EnvId) (callee : Option ObjectId := none) : Heap := {
  objects:=base.heap.objects.push (argumentObject base callee)
  environments:=base.heap.environments.push ⟨.declarative (localBindings base),some scope⟩ }

def prepared (base : Machine) (scope cursor : Nat) (callee : Option ObjectId := none) : Machine := {
  base with
  heap:=allocatedHeap base scope callee
  context:=⟨base.heap.environments.size,base.heap.environments.size,.object cursor,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan (clauses.map (true,·)) [] [] clauses }

theorem actual_prepare (base : Machine) (scope cursor : Nat) (source : Option JSString)
    (callee : Option ObjectId := none) :
    prepareCall base (closure scope source) (.object cursor) [] none callee=.ok (prepared base scope cursor callee) := by
  simp [prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,localBindings,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

def hoisted (base : Machine) (scope cursor : Nat) (callee : Option ObjectId := none) : Machine :=
  {prepared base scope cursor callee with control:=.declarationFunctions [] clauses}

attribute [local cbv_opaque] allocatedHeap

theorem actual_hoist (base : Machine) (scope cursor : Nat) (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (56+fuel) (prepared base scope cursor callee)=
      Builtins.run fuel (hoisted base scope cursor callee) := by
  rw [Nat.add_comm 56 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope cursor : Nat) (callee : Option ObjectId) :
    Builtins.builtinStep (hoisted base scope cursor callee)=
      Builtins.builtinStep {hoisted base scope cursor callee with
        control:=.statement BuildingCallbackSyntax.cursorBuyBody} := rfl

end CookieClicker.JavaScript.CursorBuyInvocation

import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptBuiltins

/-! Complete native modifier invocation and declaration scan. -/
namespace CookieClicker.JavaScript.PriceSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def body : List Stmt := match CursorCycleSyntax.modifyBuildingPriceBody with
  | .block statements=>statements | other=>[other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["building","price"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (building : ObjectId) (price : UInt64) (callee : Option ObjectId) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"building"),
    (JSString.ofString "1",localIndex base,"price")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data (.object building) true true true⟩,
    ⟨JSString.ofString "1",.data (.number price) true true true⟩,
    ⟨JSString.ofString "length",.data (.number 4611686018427387904) true false true⟩]++
      argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }
def locals (base : Machine) (building : ObjectId) (price : UInt64) : List Binding :=
  [{name:="building",value:=.object building},{name:="price",value:=.number price},
    {name:="arguments",value:=.object (argumentIndex base)}]
def allocatedHeap (base : Machine) (scope building : ObjectId) (price : UInt64)
    (bindings : List Binding) (callee : Option ObjectId) : Heap := {
  objects:=base.heap.objects.push (argumentObject base building price callee)
  environments:=base.heap.environments.push ⟨.declarative bindings,some scope⟩ }
def prepared (base : Machine) (scope game building : ObjectId) (price : UInt64) (callee : Option ObjectId) : Machine := {
  base with
  heap:=allocatedHeap base scope building price (locals base building price) callee
  context:=⟨localIndex base,localIndex base,.object game,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan (body.map (true,·)) [] [] body }

theorem actual_prepare (base : Machine) (scope game building : ObjectId) (price : UInt64)
    (source : Option JSString) (callee : Option ObjectId) :
    prepareCall (callee:=callee) base (closure scope source) (.object game) [.object building,.number price] none=
      .ok (prepared base scope game building price callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope building : ObjectId) (price : UInt64) (bindings : List Binding)
    (name : String) (value : Value) (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope building price bindings callee) (localIndex base) name value false=
      .ok (allocatedHeap base scope building price
        (if bindings.any (fun b=>b.name==name) then bindings else bindings++[{name:=name,value:=value}]) callee) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

def hoisted (base : Machine) (scope game building : ObjectId) (price : UInt64) (callee : Option ObjectId) : Machine := {
  prepared base scope game building price callee with
  heap:=allocatedHeap base scope building price (locals base building price++[{name:="godLvl",value:=.undefined}]) callee
  control:=.declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

theorem actual_hoist_prefix (base : Machine) (scope game building : ObjectId) (price : UInt64)
    (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (33+fuel) (prepared base scope game building price callee)=
      Builtins.run fuel (hoisted base scope game building price callee) := by
  rw [Nat.add_comm 33 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope game building : ObjectId) (price : UInt64) (callee : Option ObjectId) :
    Builtins.builtinStep (hoisted base scope game building price callee)=
      Builtins.builtinStep {hoisted base scope game building price callee with
        control:=.statement CursorCycleSyntax.modifyBuildingPriceBody} := rfl

end CookieClicker.JavaScript.PriceSource

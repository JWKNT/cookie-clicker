import CookieClicker.JavaScriptGainHelpersSyntax
import CookieClicker.JavaScriptBuiltins

/-! Actual invocation and declaration scan of runModHookOnValue. -/
namespace CookieClicker.JavaScript.ModHookSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def body : List Stmt := match GainHelpersSyntax.runModHookOnValueBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["hook","val"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (hook val : Value) (callee : Option ObjectId := none) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"hook"),
    (JSString.ofString "1",localIndex base,"val")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data hook true true true⟩,
    ⟨JSString.ofString "1",.data val true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false true⟩] ++
      argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }
def locals (base : Machine) (hook val : Value) : List Binding :=
  [{name:="hook",value:=hook},{name:="val",value:=val},
    {name:="arguments",value:=.object (argumentIndex base)}]
def allocatedHeap (base : Machine) (scope : EnvId) (hook val : Value)
    (bindings : List Binding) (callee : Option ObjectId := none) : Heap := {
  objects:=base.heap.objects.push (argumentObject base hook val callee)
  environments:=base.heap.environments.push ⟨.declarative bindings,some scope⟩ }
def prepared (base : Machine) (scope game : ObjectId) (hook val : Value)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap:=allocatedHeap base scope hook val (locals base hook val) callee
  context:=⟨localIndex base,localIndex base,.object game,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan (body.map (true,·)) [] [] body }
def hoisted (base : Machine) (scope game : ObjectId) (hook val : Value)
    (callee : Option ObjectId := none) : Machine := {
  prepared base scope game hook val callee with
  heap:=allocatedHeap base scope hook val (locals base hook val ++ [{name:="i"}]) callee
  control:=.declarationFunctions [] body }

theorem actual_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (hook val : Value) (callee : Option ObjectId := none) :
    prepareCall (callee:=callee) base (closure scope source) (.object game) [hook,val] none=
      .ok (prepared base scope game hook val callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope : EnvId) (hook val : Value)
    (bindings : List Binding) (name : String) (value : Value) (callee : Option ObjectId := none) :
    defineBinding (allocatedHeap base scope hook val bindings callee) (localIndex base) name value false=
      .ok (allocatedHeap base scope hook val
        (if bindings.any (fun b=>b.name==name) then bindings else bindings++[{name:=name,value:=value}]) callee) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

theorem actual_hoist (base : Machine) (scope game : ObjectId) (hook val : Value)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (7+fuel) (prepared base scope game hook val callee)=
      Builtins.run fuel (hoisted base scope game hook val callee) := by
  rw [Nat.add_comm 7 fuel]
  cbv

end CookieClicker.JavaScript.ModHookSource

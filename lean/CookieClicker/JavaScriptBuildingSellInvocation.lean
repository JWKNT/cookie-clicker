import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptBuiltins

/-! Entry of the complete native building sale. The original two arguments,
mapped argument object, declaration scan, and caller boundary are retained. -/
namespace CookieClicker.JavaScript.BuildingSellInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def body : List Stmt := match CursorCycleSyntax.sellBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["amount","bypass"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def argumentObject (base : Machine) (amount bypass : Value) (callee : Option ObjectId) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"amount"),
    (JSString.ofString "1",localIndex base,"bypass")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data amount true true true⟩,
    ⟨JSString.ofString "1",.data bypass true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false true⟩]++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }

def locals (base : Machine) (amount bypass : Value) : List Binding :=
  [{name:="amount",value:=amount},{name:="bypass",value:=bypass},
   {name:="arguments",value:=.object (argumentIndex base)}]

def allocatedHeap (base : Machine) (scope : EnvId) (amount bypass : Value)
    (bindings : List Binding) (callee : Option ObjectId) : Heap := {
  objects:=base.heap.objects.push (argumentObject base amount bypass callee)
  environments:=base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (base : Machine) (scope : EnvId) (building : ObjectId)
    (amount bypass : Value) (callee : Option ObjectId) : Machine := {
  base with
  heap:=allocatedHeap base scope amount bypass (locals base amount bypass) callee
  context:=⟨localIndex base,localIndex base,.object building,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan (body.map (true,·)) [] [] body }

theorem actual_prepare (base : Machine) (scope : EnvId) (source : Option JSString)
    (building : ObjectId) (amount bypass : Value) (callee : Option ObjectId) :
    prepareCall base (closure scope source) (.object building) [amount,bypass] none callee=
      .ok (prepared base scope building amount bypass callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,Except.pure,bind,pure]
  constructor
  all_goals first | rfl | simp [localIndex,argumentIndex,Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope : EnvId) (amount bypass : Value) (bindings : List Binding)
    (name : String) (value : Value) (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope amount bypass bindings callee) (localIndex base) name value false=
      .ok (allocatedHeap base scope amount bypass
        (if bindings.any (fun b=>b.name==name) then bindings else bindings++[{name:=name,value:=value}]) callee) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

def localNames : List String := ["success","moni","sold","i","price","giveBack","godLvl","old",
  "highestBuilding","buffsN","ii"]

def hoistedBindings (base : Machine) (amount bypass : Value) : List Binding :=
  locals base amount bypass++localNames.map (fun name=>({name,value:=.undefined}:Binding))

def hoisted (base : Machine) (scope : EnvId) (building : ObjectId)
    (amount bypass : Value) (callee : Option ObjectId) : Machine := {
  prepared base scope building amount bypass callee with
  heap:=allocatedHeap base scope amount bypass (hoistedBindings base amount bypass) callee
  control:=.declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

-- Both arms are scanned; the repeated native declaration of i remains.
theorem actual_hoist (base : Machine) (scope : EnvId) (building : ObjectId)
    (amount bypass : Value) (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (82+fuel) (prepared base scope building amount bypass callee)=
      Builtins.run fuel (hoisted base scope building amount bypass callee) := by
  rw [Nat.add_comm 82 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope : EnvId) (building : ObjectId)
    (amount bypass : Value) (callee : Option ObjectId) :
    Builtins.builtinStep (hoisted base scope building amount bypass callee)=
      Builtins.builtinStep {hoisted base scope building amount bypass callee with
        control:=.statement CursorCycleSyntax.sellBody} := rfl

end CookieClicker.JavaScript.BuildingSellInvocation

import CookieClicker.JavaScriptLocalizationSyntax
import CookieClicker.JavaScriptSourceBinding
import CookieClicker.JavaScriptEnvironmentAppend

namespace CookieClicker.JavaScript.ParseLocCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false

def text : JSString := JSString.ofString "Achievement unlocked"
def body : List Stmt := match LocalizationSyntax.parseLocBody with
  | .block statements=>statements | statement=>[statement]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["str","params"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def locals (base : Machine) : List Binding :=
  [{name:="str",value:=.string text},{name:="params",value:=.undefined},
   {name:="arguments",value:=.object (argumentIndex base)}]
def argumentObject (base : Machine) (function : ObjectId) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"str"),(JSString.ofString "1",localIndex base,"params")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data (.string text) true true true⟩,
    ⟨JSString.ofString "1",.data .undefined true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false true⟩]++
      argumentsCalleeProperties base false (some function) }
def heap (base : Machine) (scope function : Nat) (bindings : List Binding) : Heap := {
  objects:=base.heap.objects.push (argumentObject base function)
  environments:=base.heap.environments.push ⟨.declarative bindings,some scope⟩ }
def prepared (base : Machine) (scope function : Nat) : Machine := {
  base with
  heap:=heap base scope function (locals base)
  context:=⟨localIndex base,localIndex base,.object base.globalObject,false⟩
  control:=.declarationScan (body.map (true,·)) [] [] body
  continuation:=.callBoundary base.context none::base.continuation }

theorem actual_prepare (base : Machine) (scope function : Nat) (source : Option JSString) :
    prepareCall (callee:=some function) base (closure scope source) .undefined [.string text,.undefined] none=
      .ok (prepared base scope function) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,heap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

def hoistNames : List String := ["plurIndex","plurIndex","out","len","inPercent","i","it"]
def hoistedLocals (base : Machine) : List Binding := locals base++
  ["plurIndex","out","len","inPercent","i","it"].map fun name=>{name:=name}
def hoisted (base : Machine) (scope function : Nat) : Machine := {
  prepared base scope function with
  heap:=heap base scope function (hoistedLocals base)
  control:=.declarationFunctions [] body }

theorem define_local (base : Machine) (scope function : Nat) (bindings : List Binding)
    (name : String) (value : Value) :
    defineBinding (heap base scope function bindings) (localIndex base) name value false=
      .ok (heap base scope function (if bindings.any (fun b=>b.name==name) then bindings
        else bindings++[{name:=name,value:=value}])) := by
  simp [localIndex,defineBinding,checkedEnvironment,heap,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] heap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

-- The scan traverses every branch, including those skipped by this input.
theorem actual_scan (base : Machine) (scope function : Nat) (fuel : Nat) :
    Builtins.run (38+fuel) (prepared base scope function)=
      Builtins.run fuel {prepared base scope function with control:=.declarationVariables hoistNames [] body} := by
  rw [Nat.add_comm 38 fuel]
  cbv

theorem actual_hoist (base : Machine) (scope function : Nat) (fuel : Nat) :
    Builtins.run (46+fuel) (prepared base scope function)=
      Builtins.run fuel (hoisted base scope function) := by
  rw [Nat.add_comm 46 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope function : Nat) :
    Builtins.builtinStep (hoisted base scope function)=
      Builtins.builtinStep {hoisted base scope function with control:=.statement LocalizationSyntax.parseLocBody} := rfl

def emptyArray (base : Machine) : JSObject := {
  kind:=.array
  prototype:=base.arrayPrototype
  properties:=[⟨JSString.ofString "length",.data (.number 0) true false false⟩] }
def finalLocals (base : Machine) : List Binding :=
  (hoistedLocals base).map fun b=>if b.name=="params" then {b with value:=.object (base.heap.objects.size+1)} else b

def returned (base : Machine) (scope function : Nat) : Machine := {
  base with
  heap:={
    objects:=(base.heap.objects.push (argumentObject base function)).push (emptyArray base)
    environments:=base.heap.environments.push ⟨.declarative (finalLocals base),some scope⟩}
  control:=.expressionResult (.value (.string text)) }


end CookieClicker.JavaScript.ParseLocCall

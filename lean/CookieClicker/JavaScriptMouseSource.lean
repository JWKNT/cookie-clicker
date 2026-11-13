import CookieClicker.JavaScriptGainHelpersSyntax
import CookieClicker.JavaScriptBuiltins

/-! Native mouseCps call setup and declaration hoisting.
Every statement of the pinned callback is scanned. The native arguments object
and six source local bindings remain allocated. -/

namespace CookieClicker.JavaScript.MouseSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def localIndex (base : Machine) : EnvId := base.heap.environments.size

def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def body : List Stmt := match GainHelpersSyntax.mouseCpsBody with
  | .block statements => statements
  | other => [other]

def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,[],body,scope,false,source⟩

def argumentObject (base : Machine) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments []
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "length",.data (.number Number.positiveZero) true false true⟩] ++ argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }

def locals (base : Machine) : List Binding :=
  [{name := "arguments",value := .object (argumentIndex base)}]

def allocatedHeap (base : Machine) (scope : EnvId) (bindings : List Binding) (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject (callee := callee) base)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (base : Machine) (scope game : ObjectId) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap (callee := callee) base scope (locals base)
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true, ·)) [] [] body }

theorem actual_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (closure scope source) (.object game) [] none =
      .ok (prepared (callee := callee) base scope game) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,
    Heap.allocateEnvironment,Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope : EnvId) (bindings : List Binding)
    (name : String) (value : Value) (callee : Option ObjectId := none) :
    defineBinding (allocatedHeap (callee := callee) base scope bindings) (localIndex base) name value false =
      .ok (allocatedHeap (callee := callee) base scope (if bindings.any (fun b => b.name == name) then bindings
        else bindings ++ [{name := name,value := value}])) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

def hoisted (base : Machine) (scope game : ObjectId) (callee : Option ObjectId := none) : Machine := {
  prepared (callee := callee) base scope game with
  heap := allocatedHeap (callee := callee) base scope (locals base ++ [
    {name := "add",value := .undefined},{name := "num",value := .undefined},
    {name := "i",value := .undefined},{name := "mult",value := .undefined},
    {name := "godLvl",value := .undefined},{name := "out",value := .undefined}])
  control := .declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

theorem actual_hoist_prefix (base : Machine) (scope game : ObjectId) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (106+fuel) (prepared (callee := callee) base scope game) =
      Builtins.run fuel (hoisted (callee := callee) base scope game) := by
  rw [Nat.add_comm 106 fuel]
  cbv

theorem actual_hoist (base : Machine) (scope game : ObjectId) (callee : Option ObjectId := none) :
    Builtins.run 106 (prepared (callee := callee) base scope game) = hoisted (callee := callee) base scope game := by
  simpa only [Nat.add_zero,Builtins.run] using actual_hoist_prefix (callee := callee) base scope game 0

theorem hoisted_starts_body (base : Machine) (scope game : ObjectId) (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted (callee := callee) base scope game) =
      Builtins.builtinStep {hoisted (callee := callee) base scope game with control := .statement GainHelpersSyntax.mouseCpsBody} := by
  rfl

end CookieClicker.JavaScript.MouseSource

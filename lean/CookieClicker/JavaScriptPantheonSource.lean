import CookieClicker.JavaScriptLumpSyntax
import CookieClicker.JavaScriptBuiltins

/-! Native Pantheon lookup invocation and declaration scan.
The complete for loop and both branches remain in the source body. -/

namespace CookieClicker.JavaScript.PantheonSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def localIndex (base : Machine) : EnvId := base.heap.environments.size

def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def body : List Stmt := match LumpSyntax.hasGodBody with
  | .block statements => statements
  | other => [other]

def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["what"],body,scope,false,source⟩

def argumentObject (base : Machine) (what : Value) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"what")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data what true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++ argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }

def locals (base : Machine) (what : Value) : List Binding :=
  [{name := "what",value := what},{name := "arguments",value := .object (argumentIndex base)}]

def allocatedHeap (base : Machine) (scope : EnvId) (what : Value) (bindings : List Binding) (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject (callee := callee) base what)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap (callee := callee) base scope what (locals base what)
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true, ·)) [] [] body }

theorem actual_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (what : Value) (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (closure scope source) (.object game) [what] none =
      .ok (prepared (callee := callee) base scope game what) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,
    Heap.allocateEnvironment,Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope : EnvId) (what : Value) (bindings : List Binding)
    (name : String) (value : Value) (callee : Option ObjectId := none) :
    defineBinding (allocatedHeap (callee := callee) base scope what bindings) (localIndex base) name value false =
      .ok (allocatedHeap (callee := callee) base scope what (if bindings.any (fun b => b.name == name) then bindings
        else bindings ++ [{name := name,value := value}])) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

def hoisted (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) : Machine := {
  prepared (callee := callee) base scope game what with
  heap := allocatedHeap (callee := callee) base scope what (locals base what ++ [
    {name := "god",value := .undefined},{name := "i",value := .undefined}])
  control := .declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

theorem actual_hoist_prefix (base : Machine) (scope game : ObjectId) (what : Value) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (13+fuel) (prepared (callee := callee) base scope game what) =
      Builtins.run fuel (hoisted (callee := callee) base scope game what) := by
  rw [Nat.add_comm 13 fuel]
  cbv

theorem actual_hoist (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) :
    Builtins.run 13 (prepared (callee := callee) base scope game what) = hoisted (callee := callee) base scope game what := by
  simpa only [Nat.add_zero,Builtins.run] using actual_hoist_prefix (callee := callee) base scope game what 0

theorem hoisted_starts_body (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted (callee := callee) base scope game what) =
      Builtins.builtinStep {hoisted (callee := callee) base scope game what with control := .statement LumpSyntax.hasGodBody} := by
  rfl

end CookieClicker.JavaScript.PantheonSource

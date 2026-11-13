import CookieClicker.JavaScriptUnlockEnvironment
import CookieClicker.JavaScriptHasInvocation

/-! Exact call allocation and declaration hoisting for intact Game.Unlock. -/
namespace CookieClicker.JavaScript.UnlockInvocation

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def localIndex (base : Machine) : EnvId := base.heap.environments.size

def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def body : List Stmt := match BuildingCallbackSyntax.UnlockBody with | .block statements => statements | other => [other]

def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["what"],body,scope,false,source⟩

def argumentObject (base : Machine) (what : Value) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",(localIndex base),"what")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data what true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++ argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }

def locals (base : Machine) (what : Value) : List Binding :=
  [{ name := "what", value := what }, { name := "arguments", value := .object (argumentIndex base) }]

def allocatedHeap (base : Machine) (scope : EnvId) (what : Value) (bindings : List Binding) (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject (callee := callee) base what)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap (callee := callee) base scope what (locals base what)
  context := ⟨(localIndex base),(localIndex base),.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true, ·)) [] [] body }

theorem actual_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (what : Value) (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (closure scope source) (.object game) [what] none =
      .ok (prepared (callee := callee) base scope game what) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_return (base : Machine) (caller : ExecutionContext)
    (continuation : List Frame) (value : Value) :
    Builtins.builtinStep { base with
      control := .completion (.return value)
      continuation := .callBoundary caller none :: continuation } =
    { base with context := caller, control := .expressionResult (.value value), continuation } := by
  cases value <;> rfl

theorem actual_invoke (base : Machine) (scope game function : ObjectId)
    (source : Option JSString) (what : Value) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (closure scope source)) :
    invoke base (.object function) (.object game) [what] false =
      prepared (callee := some function) base scope game what := by
  simp [invoke,present,kind,checked,actual_prepare]

def withAll (base : Machine) (what : Value) : List Binding := locals base what ++ [{name := "i"}]

def hoisted (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) : Machine := {
  prepared (callee := callee) base scope game what with
  heap := allocatedHeap (callee := callee) base scope what (withAll base what)
  control := .declarationFunctions [] body }

theorem hoist_i (base : Machine) (scope : EnvId) (what : Value) (callee : Option ObjectId := none) :
    defineBinding (allocatedHeap (callee := callee) base scope what (locals base what)) (localIndex base)
      "i" .undefined false =
    .ok (allocatedHeap (callee := callee) base scope what (withAll base what)) := by
  simp [localIndex,argumentIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,locals,withAll,Except.bind,bind,Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] allocatedHeap defineBinding locals localIndex argumentIndex withAll
attribute [local cbv_eval] hoist_i

theorem actual_hoist (base : Machine) (scope game : ObjectId) (what : Value) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (16+fuel) (prepared (callee := callee) base scope game what) =
      Builtins.run fuel (hoisted (callee := callee) base scope game what) := by
  rw [Nat.add_comm 16 fuel]
  cbv


theorem hoisted_starts_body (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted (callee := callee) base scope game what) =
    Builtins.builtinStep {hoisted (callee := callee) base scope game what with control := .statement BuildingCallbackSyntax.UnlockBody} := rfl

end CookieClicker.JavaScript.UnlockInvocation

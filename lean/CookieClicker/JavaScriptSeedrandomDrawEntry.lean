import CookieClicker.JavaScriptSeedrandomDrawLocals

/-! Actual nested generator invocation, mapped arguments and declaration
hoisting. Its scope is the retained seedrandom environment. -/
namespace CookieClicker.JavaScript.SeedrandomDrawEntry
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def body : List Stmt := (SeedrandomRandomClosure.closure 0).body
def closure (scope : EnvId) : FunctionClosure := SeedrandomRandomClosure.closure scope
def localIndex (base : Machine) := base.heap.environments.size
def argumentIndex (base : Machine) := base.heap.objects.size
def initialLocals (base : Machine) : List Binding :=
  [{name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (callee : ObjectId) : JSObject := {
  kind := .arguments []
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "length",.data (.number Number.positiveZero) true false true⟩] ++
    argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeap (base : Machine) (scope : EnvId) (callee : ObjectId) (locals : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObject base callee)
  environments := base.heap.environments.push ⟨.declarative locals,some scope⟩ }
def prepared (base : Machine) (scope : EnvId) (callee receiver : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope callee (initialLocals base)
  context := ⟨localIndex base,localIndex base ,.object receiver,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem actual_prepare (base : Machine) (scope : EnvId) (callee receiver : ObjectId) :
    prepareCall base (closure scope) (.object receiver) [] none (some callee) =
      .ok (prepared base scope callee receiver) := by
  simp [prepareCall,body,closure,SeedrandomRandomClosure.closure,SeedrandomRandomClosure.expression,SeedrandomRandomClosure.assignment,SeedrandomRandomClosure.sequence,SeedrandomRandomClosure.returnExpression,SeedrandomRandomClosure.returnStatement,SeedrandomInvocation.body,SeedrandomSyntax.seedrandomBody,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    localIndex,argumentIndex,initialLocals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_invoke (base : Machine) (scope : EnvId) (callee receiver : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee=.ok object)
    (kind : object.kind=.function (closure scope)) :
    invoke base (.object callee) (.object receiver) [] false=prepared base scope callee receiver := by
  simp only [invoke,present,kind,checked,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  rw [actual_prepare]

def withNames (base : Machine) (names : List String) :=
  initialLocals base ++ names.map (fun name => ({name := name} : Binding))
def names : List String := ["a","b","c"]

def hoisted (base : Machine) (scope : EnvId) (callee receiver : ObjectId) : Machine := {
  prepared base scope callee receiver with
  heap := allocatedHeap base scope callee (withNames base names)
  control := .declarationFunctions [] body }

theorem hoist_a (base : Machine) (scope : EnvId) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope callee (withNames base [])) (localIndex base) "a" .undefined false =
      .ok (allocatedHeap base scope callee (withNames base ["a"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_b (base : Machine) (scope : EnvId) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope callee (withNames base ["a"])) (localIndex base) "b" .undefined false =
      .ok (allocatedHeap base scope callee (withNames base ["a","b"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_c (base : Machine) (scope : EnvId) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope callee (withNames base ["a","b"])) (localIndex base) "c" .undefined false =
      .ok (allocatedHeap base scope callee (withNames base ["a","b","c"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withNames defineBinding
attribute [local cbv_eval] hoist_a hoist_b hoist_c

theorem actual_hoist (base : Machine) (scope : EnvId) (callee receiver : ObjectId) (fuel : Nat) :
    Builtins.run (10+fuel) (prepared base scope callee receiver) =
      Builtins.run fuel (hoisted base scope callee receiver) := by
  change Builtins.run (10+fuel) {prepared base scope callee receiver with
    heap := allocatedHeap base scope callee (withNames base [])} = _
  rw [Nat.add_comm 10 fuel]
  cbv

end CookieClicker.JavaScript.SeedrandomDrawEntry

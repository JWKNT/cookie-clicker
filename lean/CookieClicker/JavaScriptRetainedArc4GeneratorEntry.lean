import CookieClicker.JavaScriptRetainedArc4GeneratorLocals

/-! Actual nested generator invocation, mapped arguments and declaration
hoisting. Its scope is the retained constructor environment. -/
namespace CookieClicker.JavaScript.RetainedArc4GeneratorEntry
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def body : List Stmt := match SeedrandomArc4Syntax.generatorBody with | .block body => body | other => [other]
def closure (scope : EnvId) : FunctionClosure :=
  ⟨none,["a"],body,scope,false,some SeedrandomArc4Syntax.generatorText⟩
def localIndex (base : Machine) := base.heap.environments.size
def argumentIndex (base : Machine) := base.heap.objects.size
def initialLocals (base : Machine) (input : Value) : List Binding :=
  [{name := "a",value := input},{name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (input : Value) (callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data input true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++
    argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeap (base : Machine) (scope : EnvId) (input : Value) (callee : ObjectId) (locals : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObject base input callee)
  environments := base.heap.environments.push ⟨.declarative locals,some scope⟩ }
def prepared (base : Machine) (scope : EnvId) (input : Value) (callee receiver : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope input callee (initialLocals base input)
  context := ⟨localIndex base,localIndex base ,.object receiver,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem actual_prepare (base : Machine) (scope : EnvId) (input : Value) (callee receiver : ObjectId) :
    prepareCall base (closure scope) (.object receiver) [input] none (some callee) =
      .ok (prepared base scope input callee receiver) := by
  simp [prepareCall,body,closure,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    localIndex,argumentIndex,initialLocals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_invoke (base : Machine) (scope : EnvId) (input : Value) (callee receiver : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee=.ok object)
    (kind : object.kind=.function (closure scope)) :
    invoke base (.object callee) (.object receiver) [input] false=prepared base scope input callee receiver := by
  simp only [invoke,present,kind,checked,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  rw [actual_prepare]

def withNames (base : Machine) (input : Value) (names : List String) :=
  initialLocals base input ++ names.map (fun name => ({name := name} : Binding))
def names : List String := ["b","c","f","g","h"]

def hoisted (base : Machine) (scope : EnvId) (input : Value) (callee receiver : ObjectId) : Machine := {
  prepared base scope input callee receiver with
  heap := allocatedHeap base scope input callee (withNames base input names)
  control := .declarationFunctions [] body }

theorem hoist_b (base : Machine) (scope : EnvId) (input : Value) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope input callee (withNames base input [])) (localIndex base) "b" .undefined false =
      .ok (allocatedHeap base scope input callee (withNames base input ["b"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_c (base : Machine) (scope : EnvId) (input : Value) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope input callee (withNames base input ["b"])) (localIndex base) "c" .undefined false =
      .ok (allocatedHeap base scope input callee (withNames base input ["b","c"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_f (base : Machine) (scope : EnvId) (input : Value) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope input callee (withNames base input ["b","c"])) (localIndex base) "f" .undefined false =
      .ok (allocatedHeap base scope input callee (withNames base input ["b","c","f"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_g (base : Machine) (scope : EnvId) (input : Value) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope input callee (withNames base input ["b","c","f"])) (localIndex base) "g" .undefined false =
      .ok (allocatedHeap base scope input callee (withNames base input ["b","c","f","g"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_h (base : Machine) (scope : EnvId) (input : Value) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope input callee (withNames base input ["b","c","f","g"])) (localIndex base) "h" .undefined false =
      .ok (allocatedHeap base scope input callee (withNames base input ["b","c","f","g","h"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withNames defineBinding
attribute [local cbv_eval] hoist_b hoist_c hoist_f hoist_g hoist_h

theorem actual_hoist (base : Machine) (scope : EnvId) (input : Value) (callee receiver : ObjectId) (fuel : Nat) :
    Builtins.run (10+fuel) (prepared base scope input callee receiver) =
      Builtins.run fuel (hoisted base scope input callee receiver) := by
  change Builtins.run (10+fuel) {prepared base scope input callee receiver with
    heap := allocatedHeap base scope input callee (withNames base input [])} = _
  rw [Nat.add_comm 10 fuel]
  cbv

end CookieClicker.JavaScript.RetainedArc4GeneratorEntry

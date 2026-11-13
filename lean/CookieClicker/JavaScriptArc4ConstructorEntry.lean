import CookieClicker.JavaScriptArc4ConstructorLoops

/-! Actual source constructor invocation, fresh instanceId and mapped argument
allocation, followed by native declaration scanning and hoisting. -/
namespace CookieClicker.JavaScript.Arc4ConstructorEntry
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def body : List Stmt := match SeedrandomArc4Syntax.constructorBody with | .block body => body | other => [other]
def closure (scope : EnvId) : FunctionClosure :=
  ⟨some "k",["a"],body,scope,false,some SeedrandomArc4Syntax.constructorText⟩
def localIndex (base : Machine) := base.heap.environments.size
def argumentIndex (base : Machine) := base.heap.objects.size
def initialLocals (base : Machine) (key : ObjectId) : List Binding :=
  [{name := "a",value := .object key},{name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (key callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.object key) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++
    argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeap (base : Machine) (scope : EnvId) (key callee : ObjectId) (locals : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObject base key callee)
  environments := base.heap.environments.push ⟨.declarative locals,some scope⟩ }
def prepared (base : Machine) (scope : EnvId) (key callee instanceId : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope key callee (initialLocals base key)
  context := ⟨localIndex base,localIndex base,.object instanceId,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context (some instanceId) :: base.continuation }

theorem actual_prepare (base : Machine) (scope : EnvId) (key callee instanceId : ObjectId) :
    prepareCall base (closure scope) (.object instanceId) [.object key] (some instanceId) (some callee) =
      .ok (prepared base scope key callee instanceId) := by
  simp [prepareCall,body,closure,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    localIndex,argumentIndex,initialLocals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

def instanceIndex (base : Machine) := base.heap.objects.size
def withInstance (base : Machine) (prototype : ObjectId) : Machine :=
  {base with heap := {base.heap with objects := base.heap.objects.push {prototype := some prototype}}}

theorem actual_construct (base : Machine) (scope : EnvId) (key callee prototype : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee=.ok object)
    (kind : object.kind=.function (closure scope)) (constructable : object.constructable=true)
    (writable enumerable configurable : Bool)
    (lookup : lookupProperty base.heap callee (JSString.ofString "prototype") =
      .ok (some (.data (.object prototype) writable enumerable configurable))) :
    invoke base (.object callee) .undefined [.object key] true =
      prepared (withInstance base prototype) scope key callee (instanceIndex base) := by
  simp only [invoke,present,kind,constructable,checked,requireDescriptor,lookup,Heap.allocateObject,
    Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
  rw [actual_prepare]
  rfl

def withNames (base : Machine) (key : ObjectId) (names : List String) :=
  initialLocals base key ++ names.map (fun name => ({name := name} : Binding))
def names : List String := ["b","c","e","f","g","h"]

def hoisted (base : Machine) (scope : EnvId) (key callee instanceId : ObjectId) : Machine := {
  prepared base scope key callee instanceId with
  heap := allocatedHeap base scope key callee (withNames base key names)
  control := .declarationFunctions [] body }

theorem hoist_b (base : Machine) (scope : EnvId) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope key callee (withNames base key [])) (localIndex base) "b" .undefined false =
      .ok (allocatedHeap base scope key callee (withNames base key ["b"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_c (base : Machine) (scope : EnvId) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope key callee (withNames base key ["b"])) (localIndex base) "c" .undefined false =
      .ok (allocatedHeap base scope key callee (withNames base key ["b","c"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_e (base : Machine) (scope : EnvId) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope key callee (withNames base key ["b","c"])) (localIndex base) "e" .undefined false =
      .ok (allocatedHeap base scope key callee (withNames base key ["b","c","e"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_f (base : Machine) (scope : EnvId) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope key callee (withNames base key ["b","c","e"])) (localIndex base) "f" .undefined false =
      .ok (allocatedHeap base scope key callee (withNames base key ["b","c","e","f"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_g (base : Machine) (scope : EnvId) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope key callee (withNames base key ["b","c","e","f"])) (localIndex base) "g" .undefined false =
      .ok (allocatedHeap base scope key callee (withNames base key ["b","c","e","f","g"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem hoist_h (base : Machine) (scope : EnvId) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope key callee (withNames base key ["b","c","e","f","g"])) (localIndex base) "h" .undefined false =
      .ok (allocatedHeap base scope key callee (withNames base key ["b","c","e","f","g","h"])) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withNames,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withNames defineBinding
attribute [local cbv_eval] hoist_b hoist_c hoist_e hoist_f hoist_g hoist_h

theorem actual_hoist (base : Machine) (scope : EnvId) (key callee instanceId : ObjectId) (fuel : Nat) :
    Builtins.run (14+fuel) (prepared base scope key callee instanceId) =
      Builtins.run fuel (hoisted base scope key callee instanceId) := by
  change Builtins.run (14+fuel) {prepared base scope key callee instanceId with
    heap := allocatedHeap base scope key callee (withNames base key [])} = _
  rw [Nat.add_comm 14 fuel]
  cbv

end CookieClicker.JavaScript.Arc4ConstructorEntry

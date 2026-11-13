import CookieClicker.JavaScriptChoiceSource
import CookieClicker.JavaScriptEnvironmentAppend

/-! Invocation of the pinned global choose declaration. The native call creates
the mapped arguments object and the local scope. The intact source body then
reaches its free-draw request. The entry contract states the current Math
bindings; startup correspondence and generator phase remain separate. -/
namespace CookieClicker.JavaScript.ChoiceInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def body : List Stmt := match ChoiceSyntax.body with
  | .block statements => statements
  | other => [other]

def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨some "choose",["arr"],body,scope,false,source⟩

def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def locals (base : Machine) (array : ObjectId) : List Binding :=
  [{name := "arr",value := .object array},
   {name := "arguments",value := .object (argumentIndex base)}]

def argumentObject (base : Machine) (array function : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"arr")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.object array) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++
    argumentsCalleeProperties base false (some function) }

def allocatedHeap (base : Machine) (scope : EnvId) (array function : ObjectId) : Heap := {
  objects := base.heap.objects.push (argumentObject base array function)
  environments := base.heap.environments.push ⟨.declarative (locals base array),some scope⟩ }

def prepared (base : Machine) (scope : EnvId) (array function : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope array function
  context := ⟨localIndex base,localIndex base,.object base.globalObject,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true,·)) [] [] body }

theorem actual_prepare (base : Machine) (scope : EnvId) (source : Option JSString)
    (array function : ObjectId) :
    prepareCall (callee := some function) base (closure scope source) .undefined [.object array] none =
      .ok (prepared base scope array function) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_invoke (base : Machine) (scope : EnvId) (source : Option JSString)
    (array function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (closure scope source)) :
    invoke base (.object function) .undefined [.object array] false =
      prepared base scope array function := by
  simp [invoke,present,kind,checked,actual_prepare]

def hoisted (base : Machine) (scope : EnvId) (array function : ObjectId) : Machine :=
  {prepared base scope array function with control := .declarationFunctions [] body}

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist (base : Machine) (scope : EnvId) (array function : ObjectId) (fuel : Nat) :
    Builtins.run (3+fuel) (prepared base scope array function) =
      Builtins.run fuel (hoisted base scope array function) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope : EnvId) (array function : ObjectId) :
    Builtins.builtinStep (hoisted base scope array function) =
      Builtins.builtinStep {hoisted base scope array function with control := .statement ChoiceSyntax.body} := rfl

theorem extends_objects (base : Machine) (scope : EnvId) (array function : ObjectId) :
    HeapExtension.Extends base.heap (allocatedHeap base scope array function) :=
  HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base array function))
    (HeapExtension.same_objects rfl)

structure Inputs (base : Machine) where
  scope : EnvId
  globalScope : EnvId
  depth : Nat
  math : ObjectId
  random : ObjectId
  floor : ObjectId
  array : ObjectId
  windowObject : JSObject
  mathObject : JSObject
  randomObject : JSObject
  floorObject : JSObject
  arrayObject : JSObject
  mathPath : HasEnvironment.DeclarativePath base.heap.environments "Math" scope globalScope depth
  depthBound : depth ≤ base.heap.environments.size
  globalRead : checkedEnvironment base.heap globalScope = .ok ⟨.object base.globalObject false,none⟩
  windowRead : checkedObject base.heap base.globalObject = .ok windowObject
  windowKind : windowObject.kind = .host "Window" 0
  mathRead : checkedObject base.heap math = .ok mathObject
  mathKind : mathObject.kind = .ordinary
  randomRead : checkedObject base.heap random = .ok randomObject
  randomKind : randomObject.kind = .builtin ⟨"Math","random"⟩
  floorRead : checkedObject base.heap floor = .ok floorObject
  floorKind : floorObject.kind = .builtin ⟨"Math","floor"⟩
  arrayRead : checkedObject base.heap array = .ok arrayObject
  arrayKind : arrayObject.kind = .array
  windowMath : lookupProperty base.heap base.globalObject (JSString.ofString "Math") =
    .ok (some (.data (.object math) true false true))
  mathRandom : lookupProperty base.heap math (JSString.ofString "random") =
    .ok (some (.data (.object random) true false true))
  mathFloor : lookupProperty base.heap math (JSString.ofString "floor") =
    .ok (some (.data (.object floor) true false true))
  arrayLength : lookupProperty base.heap array (JSString.ofString "length") =
    .ok (some (.data (.number (Number.ofNat 2)) true false false))
  arrayZero : lookupProperty base.heap array (JSString.ofString "0") =
    .ok (some (.data (.number 0) true true true))
  arrayOne : lookupProperty base.heap array (JSString.ofString "1") =
    .ok (some (.data (.number Number.one) true true true))
  exclusions : base.objectEnvironmentExclusions = []

def bodyInputs (base : Machine) (i : Inputs base) (function : ObjectId) : ChoiceSource.Inputs where
  heap := allocatedHeap base i.scope i.array function
  localScope := localIndex base
  globalScope := i.globalScope
  depth := i.depth+1
  window := base.globalObject
  math := i.math
  random := i.random
  floor := i.floor
  array := i.array
  windowObject := i.windowObject
  mathObject := i.mathObject
  randomObject := i.randomObject
  floorObject := i.floorObject
  arrayObject := i.arrayObject
  bindings := locals base i.array
  outer := some i.scope
  localRead := by simp [checkedEnvironment,allocatedHeap,localIndex,Heap.environment?]
  arrDeclared := by simp [locals]
  arrRead := by simp [readBinding,checkedEnvironment,allocatedHeap,localIndex,Heap.environment?,locals,Except.bind,Except.pure,bind,pure]
  mathPath := .next (localIndex base) i.scope i.globalScope i.depth (locals base i.array)
    (by simp [allocatedHeap,localIndex])
    (by simp [locals])
    (HasEnvironment.append_path _ _ "Math" i.scope i.globalScope i.depth i.mathPath)
  depthBound := by simpa [allocatedHeap] using Nat.add_le_add_right i.depthBound 1
  globalRead := EnvironmentAppend.checked_old base.heap _ _ _ i.globalScope i.globalRead
  windowRead := HeapExtension.checked_object (extends_objects base i.scope i.array function) _ _ i.windowRead
  windowKind := i.windowKind
  mathRead := HeapExtension.checked_object (extends_objects base i.scope i.array function) _ _ i.mathRead
  mathKind := i.mathKind
  randomRead := HeapExtension.checked_object (extends_objects base i.scope i.array function) _ _ i.randomRead
  randomKind := i.randomKind
  floorRead := HeapExtension.checked_object (extends_objects base i.scope i.array function) _ _ i.floorRead
  floorKind := i.floorKind
  arrayRead := HeapExtension.checked_object (extends_objects base i.scope i.array function) _ _ i.arrayRead
  arrayKind := i.arrayKind
  windowMath := HeapExtension.lookup_property (extends_objects base i.scope i.array function) _ _ _ i.windowMath
  mathRandom := HeapExtension.lookup_property (extends_objects base i.scope i.array function) _ _ _ i.mathRandom
  mathFloor := HeapExtension.lookup_property (extends_objects base i.scope i.array function) _ _ _ i.mathFloor
  arrayLength := HeapExtension.lookup_property (extends_objects base i.scope i.array function) _ _ _ i.arrayLength
  arrayZero := HeapExtension.lookup_property (extends_objects base i.scope i.array function) _ _ _ i.arrayZero
  arrayOne := HeapExtension.lookup_property (extends_objects base i.scope i.array function) _ _ _ i.arrayOne

theorem body_state (base : Machine) (i : Inputs base) (function : ObjectId) :
    ChoiceSource.state (hoisted base i.scope i.array function) (bodyInputs base i function) =
      {hoisted base i.scope i.array function with control := .statement ChoiceSyntax.body} := by
  simp [ChoiceSource.state,ChoiceSource.ambient,ChoiceSource.heap,ChoiceSource.localScope,
    ChoiceSource.window,bodyInputs,hoisted,prepared,i.exclusions]

def request (base : Machine) (i : Inputs base) (function : ObjectId) : Machine :=
  ChoiceSource.request (hoisted base i.scope i.array function) (bodyInputs base i function)

theorem prepared_request (base : Machine) (i : Inputs base) (function : ObjectId) :
    Builtins.run 31 (prepared base i.scope i.array function) = request base i function := by
  rw [show 31=3+28 from rfl,actual_hoist]
  have same := hoisted_starts_body base i.scope i.array function
  change Builtins.run 27 (Builtins.builtinStep (hoisted base i.scope i.array function)) = _
  rw [same]
  change Builtins.run 28 {hoisted base i.scope i.array function with control := .statement ChoiceSyntax.body} = _
  rw [←body_state,ChoiceSource.request_prefix]
  rfl

theorem invoked_request (base : Machine) (i : Inputs base) (function : ObjectId)
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (closure i.scope source)) :
    Builtins.run 31 (invoke base (.object function) .undefined [.object i.array] false) =
      request base i function := by
  rw [actual_invoke base i.scope source i.array function object present kind,prepared_request]

def returned (base : Machine) (i : Inputs base) (function : ObjectId) (value : UInt64) : Machine := {
  base with
  heap := allocatedHeap base i.scope i.array function
  control := .expressionResult (.value (.number value))
  freeDrawCount := base.freeDrawCount+1 }

theorem resumed_return (browser : Browser.State) (base : Machine) (i : Inputs base)
    (function : ObjectId) (draw : CookieClicker.FullGame.UniformRandom.Draw 53) :
    Builtins.run 18 (Execution.afterDraw {browser with machine := request base i function} draw).machine =
      returned base i function (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw)) := by
  rw [request,ChoiceSource.actual_draw_response]
  rw [show 18=17+1 from rfl,ChoiceSource.resumed_draw]
  change Builtins.builtinStep (ChoiceSource.returned (hoisted base i.scope i.array function)
    (bodyInputs base i function) (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw))) = _
  simp [ChoiceSource.returned,ChoiceSource.ambient,ChoiceSource.heap,ChoiceSource.localScope,
    ChoiceSource.window,bodyInputs,hoisted,prepared,returned,i.exclusions]
  rfl

end CookieClicker.JavaScript.ChoiceInvocation

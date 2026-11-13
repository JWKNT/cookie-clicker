import CookieClicker.JavaScriptChoiceInvocation

/-! Evaluation of the actual choose([0,1]) expression. Array construction keeps
the native allocation and property order. Identifier resolution reads the
current Window binding through the caller's lexical chain. -/
namespace CookieClicker.JavaScript.ChoicePrelude
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def elements : List (Option Expr) :=
  [some (.literal (.number 0)),some (.literal (.number Number.one))]
def call : Expr := .call (.identifier "choose") [.array elements]
def start (base : Machine) : Machine := {base with control := .expression call}
def atIdentifier (base : Machine) : Machine := {
  base with
  control := .expression (.identifier "choose")
  continuation := .callCallee [.array elements] false :: base.continuation }
def atReference (base : Machine) (target : EnvId) : Machine :=
  {atIdentifier base with control := .expressionResult (.reference ⟨.environment target "choose",base.context.strict⟩)}
def atGet (base : Machine) (target : EnvId) : Machine := {
  base with
  control := .getValue ⟨.environment target "choose",base.context.strict⟩
  continuation := .callResolved .undefined [.array elements] false :: base.continuation }
def atFunction (base : Machine) (target : EnvId) (function : ObjectId) : Machine :=
  {atGet base target with control := .expressionResult (.value (.object function))}

attribute [local cbv_opaque] Environment.identifier

theorem enter_identifier (base : Machine) (fuel : Nat) :
    Builtins.run (1+fuel) (start base) = Builtins.run fuel (atIdentifier base) := by
  rw [Nat.add_comm 1 fuel]
  cbv

theorem resolve_identifier (base : Machine) (target depth : Nat) (window function : ObjectId)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "choose" base.context.lexicalEnvironment target depth)
    (room : depth ≤ base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (property : lookupProperty base.heap window (JSString.ofString "choose") =
      .ok (some (.data (.object function) true true false)))
    (exclusions : base.objectEnvironmentExclusions = []) (fuel : Nat) :
    Builtins.run (1+fuel) (atIdentifier base) = Builtins.run fuel (atReference base target) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Environment.identifier (atIdentifier base) "choose") = _
  rw [IdentifierPath.identifier (atIdentifier base) "choose" target depth window _ chain room globalRead property exclusions]
  rfl

theorem read_reference (base : Machine) (target : EnvId) (window function : ObjectId) (object : JSObject)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (objectRead : checkedObject base.heap window = .ok object)
    (kind : object.kind = .host "Window" 0)
    (property : lookupProperty base.heap window (JSString.ofString "choose") =
      .ok (some (.data (.object function) true true false))) (fuel : Nat) :
    Builtins.run (2+fuel) (atReference base target) = Builtins.run fuel (atFunction base target function) := by
  have receiver : referenceThis {atReference base target with continuation := base.continuation} ⟨.environment target "choose",base.context.strict⟩ =
      .ok .undefined := by
    simp [referenceThis,show checkedEnvironment (atReference base target).heap target = .ok ⟨.object window false,none⟩ from globalRead,
      Except.bind,Except.pure,bind,pure]
  have first : Builtins.builtinStep (atReference base target) = atGet base target := by
    change {checked {atReference base target with continuation := base.continuation}
      (referenceThis {atReference base target with continuation := base.continuation}
      ⟨.environment target "choose",base.context.strict⟩) (fun thisValue =>
        {base with
          control := .getValue ⟨.environment target "choose",base.context.strict⟩
          continuation := .callResolved thisValue [.array elements] false :: base.continuation})
      with elapsed := base.elapsed} = _
    rw [receiver]
    rfl
  rw [show 2+fuel = (fuel+1)+1 by omega]
  change Builtins.run (fuel+1) (Builtins.builtinStep (atReference base target)) = _
  rw [first]
  change Builtins.run fuel {getReference (atGet base target)
    ⟨.environment target "choose",base.context.strict⟩ with elapsed := base.elapsed} = _
  rw [IdentifierPath.read_window_data (atGet base target) "choose" target window object (.object function)
    true true false base.context.strict globalRead objectRead kind property]
  rfl

def arrayIndex (base : Machine) : ObjectId := base.heap.objects.size
def initialArray (base : Machine) : JSObject := {
  kind := .array
  prototype := base.arrayPrototype
  properties := [⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false false⟩] }
def zeroArray (base : Machine) : JSObject :=
  setOwnProperty (initialArray base) (JSString.ofString "0") (.data (.number 0) true true true)
def nativeArray (base : Machine) : JSObject :=
  setOwnProperty (zeroArray base) (JSString.ofString "1") (.data (.number Number.one) true true true)
def withArray (base : Machine) (object : JSObject) : Machine :=
  {base with heap := {base.heap with objects := base.heap.objects.push object}}
def afterArray (base : Machine) : Machine := withArray base (nativeArray base)
def atInvoke (base : Machine) (function : ObjectId) : Machine := {
  afterArray base with control := .invoke (.object function) .undefined [.object (arrayIndex base)] false }

theorem checked_added (base : Machine) (object : JSObject) :
    checkedObject (withArray base object).heap (arrayIndex base) = .ok object := by
  simp [checkedObject,withArray,arrayIndex,Heap.object?]

theorem replace_added (base : Machine) (before after : JSObject) :
    replaceObject (withArray base before).heap (arrayIndex base) after = .ok (withArray base after).heap := by
  simp [replaceObject,withArray,arrayIndex,Heap.writeObject,Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] checkedObject replaceObject arrayIndex
attribute [local cbv_eval] checked_added replace_added

theorem evaluate_array (base : Machine) (target : EnvId) (function : ObjectId) (fuel : Nat) :
    Builtins.run (7+fuel) (atFunction base target function) = Builtins.run fuel (atInvoke base function) := by
  rw [Nat.add_comm 7 fuel]
  simp [Builtins.run,status,Builtins.builtinStep,step,internalStep,consumeValue,callArguments,
    evaluateExpression,arrayElements,pushExpression,result,checked,Heap.allocateObject,
    checkedObject,Heap.object?,replaceObject,Heap.writeObject,Array.setIfInBounds,Array.set_push,
    atFunction,atGet,atInvoke,afterArray,withArray,arrayIndex,elements,initialArray,zeroArray,
    nativeArray,setOwnProperty,JSString.ofString]
  rfl

theorem array_extends (base : Machine) : HeapExtension.Extends base.heap (afterArray base).heap :=
  HeapExtension.append_object base.heap (nativeArray base)

theorem call_prefix (base : Machine) (target depth : Nat) (window function : ObjectId) (object : JSObject)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "choose" base.context.lexicalEnvironment target depth)
    (room : depth ≤ base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (objectRead : checkedObject base.heap window = .ok object)
    (kind : object.kind = .host "Window" 0)
    (property : lookupProperty base.heap window (JSString.ofString "choose") =
      .ok (some (.data (.object function) true true false)))
    (exclusions : base.objectEnvironmentExclusions = []) (fuel : Nat) :
    Builtins.run (11+fuel) (start base) = Builtins.run fuel (atInvoke base function) := by
  rw [show 11+fuel = 1+(1+(2+(7+fuel))) by omega]
  rw [enter_identifier,resolve_identifier _ target depth window function chain room globalRead property exclusions,
    read_reference _ target window function object globalRead objectRead kind property,evaluate_array]

/-- Math's closure path before the source creates its two-element array. -/
structure Context (base : Machine) where
  scope : EnvId
  globalScope : EnvId
  depth : Nat
  math : ObjectId
  random : ObjectId
  floor : ObjectId
  windowObject : JSObject
  mathObject : JSObject
  randomObject : JSObject
  floorObject : JSObject
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
  windowMath : lookupProperty base.heap base.globalObject (JSString.ofString "Math") =
    .ok (some (.data (.object math) true false true))
  mathRandom : lookupProperty base.heap math (JSString.ofString "random") =
    .ok (some (.data (.object random) true false true))
  mathFloor : lookupProperty base.heap math (JSString.ofString "floor") =
    .ok (some (.data (.object floor) true false true))
  exclusions : base.objectEnvironmentExclusions = []

theorem array_length (base : Machine) :
    lookupProperty (afterArray base).heap (arrayIndex base) (JSString.ofString "length") =
      .ok (some (.data (.number (Number.ofNat 2)) true false false)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,afterArray,withArray,arrayIndex,
    nativeArray,zeroArray,initialArray,setOwnProperty,ownProperty,JSString.ofString,Except.bind,Except.pure,bind,pure]

theorem array_zero (base : Machine) :
    lookupProperty (afterArray base).heap (arrayIndex base) (JSString.ofString "0") =
      .ok (some (.data (.number 0) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,afterArray,withArray,arrayIndex,
    nativeArray,zeroArray,initialArray,setOwnProperty,ownProperty,JSString.ofString,Except.bind,Except.pure,bind,pure]

theorem array_one (base : Machine) :
    lookupProperty (afterArray base).heap (arrayIndex base) (JSString.ofString "1") =
      .ok (some (.data (.number Number.one) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,afterArray,withArray,arrayIndex,
    nativeArray,zeroArray,initialArray,setOwnProperty,ownProperty,JSString.ofString,Except.bind,Except.pure,bind,pure]

def invocationInputs (base : Machine) (c : Context base) : ChoiceInvocation.Inputs (afterArray base) where
  scope := c.scope
  globalScope := c.globalScope
  depth := c.depth
  math := c.math
  random := c.random
  floor := c.floor
  array := arrayIndex base
  windowObject := c.windowObject
  mathObject := c.mathObject
  randomObject := c.randomObject
  floorObject := c.floorObject
  arrayObject := nativeArray base
  mathPath := c.mathPath
  depthBound := c.depthBound
  globalRead := c.globalRead
  windowRead := HeapExtension.checked_object (array_extends base) _ _ c.windowRead
  windowKind := c.windowKind
  mathRead := HeapExtension.checked_object (array_extends base) _ _ c.mathRead
  mathKind := c.mathKind
  randomRead := HeapExtension.checked_object (array_extends base) _ _ c.randomRead
  randomKind := c.randomKind
  floorRead := HeapExtension.checked_object (array_extends base) _ _ c.floorRead
  floorKind := c.floorKind
  arrayRead := checked_added base (nativeArray base)
  arrayKind := by simp [nativeArray,zeroArray,initialArray,setOwnProperty,JSString.ofString]
  windowMath := HeapExtension.lookup_property (array_extends base) _ _ _ c.windowMath
  mathRandom := HeapExtension.lookup_property (array_extends base) _ _ _ c.mathRandom
  mathFloor := HeapExtension.lookup_property (array_extends base) _ _ _ c.mathFloor
  arrayLength := array_length base
  arrayZero := array_zero base
  arrayOne := array_one base
  exclusions := c.exclusions

def request (base : Machine) (c : Context base) (function : ObjectId) : Machine :=
  ChoiceInvocation.request (afterArray base) (invocationInputs base c) function

theorem call_to_free_draw (base : Machine) (c : Context base) (target depth : Nat) (function : ObjectId)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "choose" base.context.lexicalEnvironment target depth)
    (room : depth ≤ base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object base.globalObject false,none⟩)
    (property : lookupProperty base.heap base.globalObject (JSString.ofString "choose") =
      .ok (some (.data (.object function) true true false)))
    (source : Option JSString) (object : JSObject)
    (functionRead : checkedObject base.heap function = .ok object)
    (functionKind : object.kind = .function (ChoiceInvocation.closure c.scope source)) :
    Builtins.run 43 (start base) = request base c function := by
  rw [show 43=11+32 from rfl,call_prefix base target depth base.globalObject function c.windowObject
    chain room globalRead c.windowRead c.windowKind property c.exclusions]
  have callRead := HeapExtension.checked_object (array_extends base) function object functionRead
  change Builtins.run 31 {invoke (atInvoke base function) (.object function) .undefined
    [.object (arrayIndex base)] false with elapsed := base.elapsed} = _
  rw [ChoiceInvocation.actual_invoke (atInvoke base function) c.scope source (arrayIndex base) function
    object callRead functionKind]
  change Builtins.run 31 (ChoiceInvocation.prepared (afterArray base) c.scope (arrayIndex base) function) = _
  exact ChoiceInvocation.prepared_request (afterArray base) (invocationInputs base c) function

theorem draw_returns_to_caller (browser : Browser.State) (base : Machine) (c : Context base)
    (function : ObjectId) (draw : CookieClicker.FullGame.UniformRandom.Draw 53) :
    Builtins.run 18 (Execution.afterDraw {browser with machine := request base c function} draw).machine =
      ChoiceInvocation.returned (afterArray base) (invocationInputs base c) function
        (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw)) :=
  ChoiceInvocation.resumed_return browser (afterArray base) (invocationInputs base c) function draw

end CookieClicker.JavaScript.ChoicePrelude

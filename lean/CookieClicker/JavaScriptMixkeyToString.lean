import CookieClicker.JavaScriptMixkeyApply
import CookieClicker.JavaScriptDataPropertyPath
import CookieClicker.JavaScriptSeedrandomMixkeySyntax
import CookieClicker.JavaScriptEnvironmentAppend

/-! The complete retained o(a) source helper. Its real global String lookup,
inherited apply method, call allocation and caller continuation are explicit. -/
namespace CookieClicker.JavaScript.MixkeyToString
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def body : List Stmt := match SeedrandomMixkeySyntax.toStringBody with | .block body => body | other => [other]
def closure (scope : EnvId) : FunctionClosure :=
  ⟨some "o",["a"],body,scope,false,some SeedrandomMixkeySyntax.toStringText⟩
def localIndex (base : Machine) := base.heap.environments.size
def argumentIndex (base : Machine) := base.heap.objects.size

def locals (base : Machine) (array : ObjectId) : List Binding :=
  [{name := "a",value := .object array},{name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (array callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.object array) true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 1)) true false true⟩] ++
    argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }

def allocatedHeap (base : Machine) (scope : EnvId) (array callee : ObjectId) : Heap := {
  objects := base.heap.objects.push (argumentObject base array callee)
  environments := base.heap.environments.push ⟨.declarative (locals base array),some scope⟩ }

def prepared (base : Machine) (scope : EnvId) (array callee : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope array callee
  context := ⟨localIndex base,localIndex base,.object base.globalObject,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem actual_prepare (base : Machine) (scope : EnvId) (array callee : ObjectId) :
    prepareCall (callee := some callee) base (closure scope) .undefined [.object array] none =
      .ok (prepared base scope array callee) := by
  simp [prepareCall,closure,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    localIndex,argumentIndex,locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

structure Inputs where
  base : Machine
  scope : EnvId
  callee : ObjectId
  array : ObjectId
  globalScope : EnvId
  globalOuter : Option EnvId
  provideThis : Bool
  depth : Nat
  chain : HasEnvironment.DeclarativePath base.heap.environments "String" scope globalScope depth
  depthBound : depth ≤ base.heap.environments.size
  globalRead : checkedEnvironment base.heap globalScope = .ok ⟨.object base.globalObject provideThis,globalOuter⟩
  exclusions : base.objectEnvironmentExclusions = []
  constructorId : ObjectId
  codes : ObjectId
  applyId : ObjectId
  windowObject : JSObject
  constructorObject : JSObject
  codesObject : JSObject
  applyObject : JSObject
  windowRead : checkedObject base.heap base.globalObject = .ok windowObject
  constructorRead : checkedObject base.heap constructorId = .ok constructorObject
  codesRead : checkedObject base.heap codes = .ok codesObject
  applyRead : checkedObject base.heap applyId = .ok applyObject
  windowNotArguments : ∀ mappings, windowObject.kind ≠ .arguments mappings
  constructorKind : constructorObject.kind = .builtin ⟨"global","String"⟩
  codesKind : codesObject.kind = .builtin ⟨"String","fromCharCode"⟩
  applyKind : applyObject.kind = .builtin ⟨"Function.prototype","apply"⟩
  stringDepth : Nat
  constructorDepth : Nat
  applyDepth : Nat
  stringPath : DataPropertyPath.Path base.heap (JSString.ofString "String") (.object constructorId) base.globalObject stringDepth
  constructorPath : DataPropertyPath.Path base.heap (JSString.ofString "fromCharCode") (.object codes) constructorId constructorDepth
  applyPath : DataPropertyPath.Path base.heap (JSString.ofString "apply") (.object applyId) codes applyDepth
  stringBound : stringDepth ≤ base.heap.objects.size
  constructorBound : constructorDepth ≤ base.heap.objects.size
  applyBound : applyDepth ≤ base.heap.objects.size

def base (i : Inputs) := i.base
def scope (i : Inputs) := i.scope
def callee (i : Inputs) := i.callee
def array (i : Inputs) := i.array
def globalScope (i : Inputs) := i.globalScope
def constructorId (i : Inputs) := i.constructorId
def codes (i : Inputs) := i.codes
def applyId (i : Inputs) := i.applyId

def heap (i : Inputs) := allocatedHeap (base i) (scope i) (array i) (callee i)
def start (i : Inputs) := prepared (base i) (scope i) (array i) (callee i)

theorem allocation_extends (i : Inputs) : HeapExtension.Extends (base i).heap (heap i) :=
  HeapExtension.trans (HeapExtension.append_object _ (argumentObject (base i) (array i) (callee i)))
    (HeapExtension.same_objects (before := ((base i).heap.allocateObject (argumentObject (base i) (array i) (callee i))).2)
      (after := heap i) rfl)

theorem local_read (i : Inputs) : checkedEnvironment (heap i) (localIndex (base i)) =
    .ok ⟨.declarative (locals (base i) (array i)),some (scope i)⟩ := by
  simp [heap,allocatedHeap,localIndex,checkedEnvironment,Heap.environment?]

theorem global_read (i : Inputs) : checkedEnvironment (heap i) (globalScope i) =
    .ok ⟨.object (base i).globalObject i.provideThis,i.globalOuter⟩ :=
  EnvironmentAppend.checked_old (base i).heap _ _ _ _ i.globalRead

theorem environment_size (i : Inputs) : (heap i).environments.size = (base i).heap.environments.size+1 := by
  simp [heap,allocatedHeap]

theorem read_a (i : Inputs) : readBinding (heap i) (localIndex (base i)) "a" = .ok (.object (array i)) := by
  simp [readBinding,local_read,locals,Except.bind,bind,Except.pure,pure]

theorem window_read (i : Inputs) : checkedObject (heap i) (base i).globalObject = .ok i.windowObject :=
  HeapExtension.checked_object (allocation_extends i) _ _ i.windowRead

theorem constructor_read (i : Inputs) : checkedObject (heap i) (constructorId i) = .ok i.constructorObject :=
  HeapExtension.checked_object (allocation_extends i) _ _ i.constructorRead

theorem codes_read (i : Inputs) : checkedObject (heap i) (codes i) = .ok i.codesObject :=
  HeapExtension.checked_object (allocation_extends i) _ _ i.codesRead

theorem apply_read (i : Inputs) : checkedObject (heap i) (applyId i) = .ok i.applyObject :=
  HeapExtension.checked_object (allocation_extends i) _ _ i.applyRead


theorem object_size (i : Inputs) : (heap i).objects.size = (base i).heap.objects.size+1 := by
  simp [heap,allocatedHeap]

theorem string_lookup (i : Inputs) : ∃ writable enumerable configurable,
    lookupProperty (heap i) (base i).globalObject (JSString.ofString "String") =
      .ok (some (.data (.object (constructorId i)) writable enumerable configurable)) :=
  DataPropertyPath.lookup (DataPropertyPath.extend (allocation_extends i) i.stringPath)
    (by rw [object_size]; have h := i.stringBound; change i.stringDepth ≤ (base i).heap.objects.size at h; omega)

def ambient (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) : Machine := {
  start i with heap := heap i, control := control, continuation := continuation }

theorem identifier_string (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
    Environment.identifier (ambient i control continuation) "String" =
      { ambient i control continuation with control := .expressionResult (.reference ⟨.environment (globalScope i) "String",false⟩) } := by
  let machine := ambient i control continuation
  have localRead : checkedEnvironment machine.heap (localIndex (base i)) =
      .ok ⟨.declarative (locals (base i) (array i)),some (scope i)⟩ := local_read i
  have globalRead : checkedEnvironment machine.heap (globalScope i) =
      .ok ⟨.object (base i).globalObject i.provideThis,i.globalOuter⟩ := global_read i
  have chain : HasEnvironment.DeclarativePath machine.heap.environments "String"
      (scope i) (globalScope i) i.depth := HasEnvironment.append_path _ _ _ _ _ _ i.chain
  have count : (base i).heap.environments.size+1 = i.depth+((base i).heap.environments.size-i.depth+1) := by
    have h := i.depthBound; change i.depth ≤ (base i).heap.environments.size at h; omega
  obtain ⟨w,e,c,found⟩ := string_lookup i
  change Environment.resolve ((heap i).environments.size+1) machine (localIndex (base i)) "String" false = _
  rw [environment_size,Environment.resolve,localRead]
  simp only [checked,show (locals (base i) (array i)).any (fun b => b.name == "String") = false from rfl,Bool.false_eq_true,↓reduceIte]
  rw [count,HasEnvironment.resolve_path machine "String" false _ _ _ _ chain]
  rw [Environment.resolve,globalRead]
  simp only [checked,machine,ambient,start,prepared,base,i.exclusions]
  simp only [base] at found
  rw [found]
  rfl

theorem read_string (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
    readProperty (ambient i control continuation) (.object (base i).globalObject) (JSString.ofString "String") =
      result (ambient i control continuation) (.object (constructorId i)) :=
  DataPropertyPath.native_read _ _ _ _ _ i.stringDepth
    (DataPropertyPath.extend (allocation_extends i) i.stringPath)
    (by change i.stringDepth ≤ (heap i).objects.size; rw [object_size]; have h := i.stringBound; change i.stringDepth ≤ (base i).heap.objects.size at h; omega)
    (window_read i) i.windowNotArguments

theorem read_codes (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
    readProperty (ambient i control continuation) (.object (constructorId i)) (JSString.ofString "fromCharCode") =
      result (ambient i control continuation) (.object (codes i)) :=
  DataPropertyPath.native_read _ _ _ _ _ i.constructorDepth
    (DataPropertyPath.extend (allocation_extends i) i.constructorPath)
    (by change i.constructorDepth ≤ (heap i).objects.size; rw [object_size]; have h := i.constructorBound; change i.constructorDepth ≤ (base i).heap.objects.size at h; omega)
    (constructor_read i) (by intro mappings; rw [i.constructorKind]; intro h; cases h)

theorem read_apply (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
    readProperty (ambient i control continuation) (.object (codes i)) (JSString.ofString "apply") =
      result (ambient i control continuation) (.object (applyId i)) :=
  DataPropertyPath.native_read _ _ _ _ _ i.applyDepth
    (DataPropertyPath.extend (allocation_extends i) i.applyPath)
    (by change i.applyDepth ≤ (heap i).objects.size; rw [object_size]; have h := i.applyBound; change i.applyDepth ≤ (base i).heap.objects.size at h; omega)
    (codes_read i) (by intro mappings; rw [i.codesKind]; intro h; cases h)

theorem identifier_string_explicit (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
  Environment.identifier {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } "String" =
    ambient i (.expressionResult (.reference ⟨.environment (globalScope i) "String",false⟩)) continuation := identifier_string i control continuation

theorem read_string_explicit (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
  readProperty {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } (.object (base i).globalObject) (JSString.ofString "String") =
    result {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } (.object (constructorId i)) := read_string i control continuation

theorem read_codes_explicit (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
  readProperty {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } (.object (constructorId i)) (JSString.ofString "fromCharCode") =
    result {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } (.object (codes i)) := read_codes i control continuation

theorem read_apply_explicit (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
  readProperty {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } (.object (codes i)) (JSString.ofString "apply") =
    result {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } (.object (applyId i)) := read_apply i control continuation

theorem identifier_a_explicit (i : Inputs) (control : Control) (continuation : List JavaScript.Frame) :
  Environment.identifier {
  heap := heap i
  context := ⟨localIndex (base i),localIndex (base i),.object (base i).globalObject,false⟩
  control := control
  continuation := continuation
  globalObject := (base i).globalObject
  objectPrototype := (base i).objectPrototype
  functionPrototype := (base i).functionPrototype
  arrayPrototype := (base i).arrayPrototype
  stringPrototype := (base i).stringPrototype
  numberPrototype := (base i).numberPrototype
  booleanPrototype := (base i).booleanPrototype
  regexpPrototype := (base i).regexpPrototype
  datePrototype := (base i).datePrototype
  throwTypeErrorIntrinsic := (base i).throwTypeErrorIntrinsic
  objectEnvironmentExclusions := (base i).objectEnvironmentExclusions
  events := (base i).events
  nextEventId := (base i).nextEventId
  elapsed := (base i).elapsed
  epochMilliseconds := (base i).epochMilliseconds
  freeDrawCount := (base i).freeDrawCount } "a" =
    ambient i (.expressionResult (.reference ⟨.environment (localIndex (base i)) "a",false⟩)) continuation  := by
  change Environment.resolve ((heap i).environments.size+1) (ambient i control continuation)
    (localIndex (base i)) "a" false = _
  exact Environment.resolve_declared _ _ _ _ _ _ _ (local_read i) rfl


def returnTail (i : Inputs) : List JavaScript.Frame :=
  .returnValue :: .statementList [] none :: .callBoundary (base i).context none :: (base i).continuation

def beforeString (i : Inputs) : Machine := ambient i (.expression (.identifier "String"))
  (.memberObject (.identifier "fromCharCode") false :: .memberObject (.identifier "apply") false ::
    .callCallee [.literal (.number Number.positiveZero),.identifier "a"] false :: returnTail i)

attribute [local cbv_opaque] base scope callee array globalScope constructorId codes applyId heap localIndex argumentIndex List.length Array.size allocatedHeap JSString.ofString Environment.identifier readProperty checkedEnvironment readBinding
attribute [local cbv_eval] local_read global_read environment_size read_a identifier_string_explicit read_string_explicit read_codes_explicit read_apply_explicit

theorem actual_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (8+fuel) (start i) = Builtins.run fuel (beforeString i) := by
  change Builtins.run (8+fuel) {start i with heap := heap i} = _
  rw [Nat.add_comm 8 fuel]
  cbv


def beforeApply (i : Inputs) : Machine := ambient i
  (.invoke (.object (applyId i)) (.object (codes i)) [.number Number.positiveZero,.object (array i)] false)
  (returnTail i)

def applyRequest (i : Inputs) : Machine := ambient i
  (.unresolved (.builtin ⟨"Function.prototype","apply"⟩ (.object (codes i))
    [.number Number.positiveZero,.object (array i)] false)) (returnTail i)

theorem actual_call_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (16+fuel) (beforeString i) = Builtins.run fuel (beforeApply i) := by
  rw [Nat.add_comm 16 fuel]
  cbv
  simp only [identifier_string_explicit]
  cbv
  simp only [read_string_explicit,read_codes_explicit,read_apply_explicit,environment_size]
  cbv
  simp only [read_string_explicit,read_codes_explicit,read_apply_explicit,environment_size]
  cbv
  simp only [read_string_explicit,read_codes_explicit,read_apply_explicit,identifier_a_explicit,environment_size]
  cbv
  simp only [identifier_a_explicit,environment_size]
  cbv

theorem actual_apply_invoke (i : Inputs) :
    Builtins.builtinStep (beforeApply i) = applyRequest i := by
  change {invoke (beforeApply i) (.object (applyId i)) (.object (codes i))
    [.number Number.positiveZero,.object (array i)] false with elapsed := (base i).elapsed} = _
  have present : checkedObject (beforeApply i).heap (applyId i) = .ok i.applyObject := apply_read i
  simp only [invoke,present,i.applyKind,checked,fail]
  rfl


structure ArrayData (i : Inputs) where
  object : JSObject
  length : Nat
  bytes : Nat → UInt8
  shape : MixkeyArray.Shape object length bytes
  present : checkedObject (base i).heap (array i) = .ok object
  prototype : MixkeyArray.PrototypeFrame (base i).heap object
  room : 2 ≤ (base i).heap.objects.size

def applyInput (i : Inputs) (data : ArrayData i) : MixkeyApply.Inputs := {
  base := applyRequest i, array := array i, object := data.object, length := data.length, bytes := data.bytes
  shape := data.shape
  present := HeapExtension.checked_object (allocation_extends i) _ _ data.present
  prototype := data.prototype.transport rfl
    (HeapExtension.checked_object (allocation_extends i) _ _ data.prototype.arrayRead)
    (HeapExtension.checked_object (allocation_extends i) _ _ data.prototype.rootRead)
  room := by change 2 ≤ (heap i).objects.size; rw [object_size]; have := data.room; omega
  function := codes i, functionObject := i.codesObject, functionPresent := codes_read i, functionKind := i.codesKind }

def text (i : Inputs) (data : ArrayData i) := MixkeyApply.text (applyInput i data)

def afterApply (i : Inputs) (data : ArrayData i) :=
  result (applyRequest i) (.string (text i data))

def returned (i : Inputs) (data : ArrayData i) : Machine :=
  result {(base i) with heap := heap i} (.string (text i data))

theorem actual_native_apply (i : Inputs) (data : ArrayData i) (fuel : Nat) :
    Builtins.run (5+2*data.length+fuel) (applyRequest i) = Builtins.run fuel (afterApply i data) :=
  MixkeyApply.actual_apply_request (applyInput i data) rfl fuel

attribute [local cbv_opaque] text

theorem actual_source_return (i : Inputs) (data : ArrayData i) (fuel : Nat) :
    Builtins.run (3+fuel) (afterApply i data) = Builtins.run fuel (returned i data) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_source_helper (i : Inputs) (data : ArrayData i) (fuel : Nat) :
    Builtins.run (33+2*data.length+fuel) (start i) = Builtins.run fuel (returned i data) := by
  rw [show 33+2*data.length+fuel=8+(16+((5+2*data.length+(3+fuel))+1)) by omega,actual_prefix,actual_call_prefix]
  change Builtins.run (5+2*data.length+(3+fuel)) (Builtins.builtinStep (beforeApply i)) = _
  rw [actual_apply_invoke,actual_native_apply,actual_source_return]

end CookieClicker.JavaScript.MixkeyToString

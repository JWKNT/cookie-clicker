import CookieClicker.JavaScriptComputeCps
import CookieClicker.JavaScriptHasInvocation

/-! Source invocation of ComputeCps, retaining argument/environment allocation
and the caller's continuation. No callback is replaced by an arithmetic oracle.
The closure/object correspondence hypotheses must hold at the call site. -/
namespace CookieClicker.JavaScript.ComputeCpsCall
open ComputeCps
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def body : List Stmt := match ProductionSyntax.ComputeCpsBody with
  | .block statements => statements | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["base","mult","bonus"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def argumentObject (base : Machine) (value : UInt64) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"base"),
    (JSString.ofString "1",localIndex base,"mult"),(JSString.ofString "2",localIndex base,"bonus")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.number value) true true true⟩,
    ⟨JSString.ofString "1",.data (.number 0) true true true⟩,
    ⟨JSString.ofString "2",.data (.number 0) true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 3)) true false true⟩] ++ argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }

def locals (base : Machine) : Locals := {
  extra := [{name := "arguments",value := .object (argumentIndex base)}]
  clean := by simp }

def allocatedHeap (base : Machine) (scope : EnvId) (value : UInt64) (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject (callee := callee) base value)
  environments := base.heap.environments.push
    ⟨.declarative (bindings (locals base) value),some scope⟩ }

def prepared (base : Machine) (scope : EnvId) (game : ObjectId) (value : UInt64) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap (callee := callee) base scope value
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true,·)) [] [] body }

theorem actual_prepare (base : Machine) (scope : EnvId) (game : ObjectId)
    (source : Option JSString) (value : UInt64) (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (closure scope source) (.object game) [.number value,.number 0,.number 0] none =
      .ok (prepared (callee := callee) base scope game value) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,locals,bindings,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

def hoisted (base : Machine) (scope : EnvId) (game : ObjectId) (value : UInt64) (callee : Option ObjectId := none) : Machine :=
  {prepared (callee := callee) base scope game value with control := .declarationFunctions [] body}

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist_prefix (base : Machine) (scope : EnvId) (game : ObjectId)
    (value : UInt64) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (5+fuel) (prepared (callee := callee) base scope game value) =
      Builtins.run fuel (hoisted (callee := callee) base scope game value) := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope : EnvId) (game : ObjectId) (value : UInt64) (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted (callee := callee) base scope game value) =
      Builtins.builtinStep {hoisted (callee := callee) base scope game value with control := .statement ProductionSyntax.ComputeCpsBody} := rfl

def appendObjects (objects : Objects) (added : JSObject) : Objects := {
  objects with
  objects := objects.objects.push added
  windowRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp objects.windowRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using objects.windowRead
  mathRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp objects.mathRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using objects.mathRead
  powRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp objects.powRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using objects.powRead }

def caller (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects)) : Machine := {
  base with
  heap := ⟨objects.objects,scopes.environments⟩
  globalObject := windowIndex objects
  objectEnvironmentExclusions := [] }

def afterBody (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (game : ObjectId) (value : UInt64) (callee : Option ObjectId := none) : Machine :=
  {hoisted (callee := callee) (caller base objects scopes) scopes.closureScope game value with
   control := .completion (.return (.number (Number.add (Number.mul value Number.one) 0)))}

theorem body_state (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (game : ObjectId) (value : UInt64) (callee : Option ObjectId := none) :
    let original := caller base objects scopes
    let before := hoisted (callee := callee) original scopes.closureScope game value
    ComputeCps.state before (appendObjects objects (argumentObject (callee := callee) original value)) scopes (locals original) value =
      {before with control := .statement ProductionSyntax.ComputeCpsBody} := rfl

theorem actual_body_prefix (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (game : ObjectId) (value : UInt64) (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base objects scopes
    Builtins.run (49+fuel) (hoisted (callee := callee) original scopes.closureScope game value) =
      Builtins.run fuel (afterBody (callee := callee) base objects scopes game value) := by
  let original := caller base objects scopes
  let before := hoisted (callee := callee) original scopes.closureScope game value
  have bodyProof := native_body_prefix before
    (appendObjects objects (argumentObject (callee := callee) original value)) scopes (locals original) value fuel
  rw [body_state (callee := callee)] at bodyProof
  change Builtins.run (49+fuel) before = _
  have same : Builtins.run (49+fuel) before =
      Builtins.run (49+fuel) {before with control := .statement ProductionSyntax.ComputeCpsBody} := by
    rw [Nat.add_comm 49 fuel]
    change Builtins.run (fuel+48) (Builtins.builtinStep before) =
      Builtins.run (fuel+48) (Builtins.builtinStep {before with control := .statement ProductionSyntax.ComputeCpsBody})
    rw [hoisted_starts_body (callee := callee)]
  rw [same,bodyProof]
  rfl

def returned (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (value : UInt64) (callee : Option ObjectId := none) : Machine := {
  caller base objects scopes with
  heap := allocatedHeap (callee := callee) (caller base objects scopes) scopes.closureScope value
  control := .expressionResult (.value (.number (Number.add (Number.mul value Number.one) 0))) }

theorem actual_return_prefix (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (game : ObjectId) (value : UInt64) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (1+fuel) (afterBody (callee := callee) base objects scopes game value) =
      Builtins.run fuel (returned (callee := callee) base objects scopes value) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (afterBody (callee := callee) base objects scopes game value)) = _
  exact congrArg (Builtins.run fuel) (HasInvocation.actual_return (afterBody (callee := callee) base objects scopes game value)
    (caller base objects scopes).context (caller base objects scopes).continuation
    (.number (Number.add (Number.mul value Number.one) 0)))

theorem actual_prepared_prefix (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (game : ObjectId) (value : UInt64) (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base objects scopes
    Builtins.run (55+fuel) (prepared (callee := callee) original scopes.closureScope game value) =
      Builtins.run fuel (returned (callee := callee) base objects scopes value) := by
  change Builtins.run (55+fuel) (prepared (callee := callee) (caller base objects scopes) scopes.closureScope game value) = _
  rw [show 55+fuel = 5+(49+(1+fuel)) by omega]
  rw [actual_hoist_prefix (callee := callee),actual_body_prefix (callee := callee),actual_return_prefix (callee := callee)]

theorem caller_eq (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (oldObjects : base.heap.objects = objects.objects)
    (oldEnvironments : base.heap.environments = scopes.environments)
    (global : base.globalObject = windowIndex objects)
    (exclusions : base.objectEnvironmentExclusions = []) : caller base objects scopes = base := by
  unfold caller
  rw [←oldObjects,←oldEnvironments,←global,←exclusions]

theorem actual_invoke_existing_prefix (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (oldObjects : base.heap.objects = objects.objects)
    (oldEnvironments : base.heap.environments = scopes.environments)
    (global : base.globalObject = windowIndex objects)
    (exclusions : base.objectEnvironmentExclusions = [])
    (game function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (closure scopes.closureScope source)) (value : UInt64) (fuel : Nat) :
    Builtins.run (55+fuel) (invoke base (.object function) (.object game) [.number value,.number 0,.number 0] false) =
      Builtins.run fuel {base with
        heap := allocatedHeap (callee := some function) base scopes.closureScope value
        control := .expressionResult (.value (.number (Number.add (Number.mul value Number.one) 0)))} := by
  have same := caller_eq base objects scopes oldObjects oldEnvironments global exclusions
  simp only [invoke,present,JavaScript.checked,kind,Bool.false_and,Bool.false_eq_true,↓reduceIte,actual_prepare]
  have applied := actual_prepared_prefix (callee := some function) base objects scopes game value fuel
  simpa only [same,returned] using applied

end CookieClicker.JavaScript.ComputeCpsCall

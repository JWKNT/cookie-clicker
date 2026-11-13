import CookieClicker.JavaScriptLumpAge
/-! The intact canLumps source callback on its existing-lump branch.
The first source comparison is evaluated; the unused later disjunct remains
in the syntax. Call allocation and the original lexical path are retained. -/
namespace CookieClicker.JavaScript.CanLumpsCall
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
structure Inputs where
  heap : Heap
  localScope : EnvId
  globalScope : EnvId
  depth : Nat
  window : ObjectId
  game : ObjectId
  windowObject : JSObject
  gameObject : JSObject
  total : UInt64
  path : HasEnvironment.DeclarativePath heap.environments "Game" localScope globalScope depth
  room : depth ≤ heap.environments.size
  globalRead : checkedEnvironment heap globalScope = .ok ⟨.object window false,none⟩
  windowRead : checkedObject heap window = .ok windowObject
  gameRead : checkedObject heap game = .ok gameObject
  windowKind : windowObject.kind = .host "Window" 0
  gameKind : gameObject.kind = .ordinary
  windowGame : lookupProperty heap window (JSString.ofString "Game") = .ok (some (.data (.object game) true true false))
  gameTotal : lookupProperty heap game (JSString.ofString "lumpsTotal") = .ok (some (.data (.number total) true true true))
  existing : Number.lessThan 13830554455654793216 total = true
def heap (i : Inputs) : Heap := i.heap
def localScope (i : Inputs) : EnvId := i.localScope
def globalScope (i : Inputs) : EnvId := i.globalScope
def window (i : Inputs) : ObjectId := i.window
def game (i : Inputs) : ObjectId := i.game
def windowObject (i : Inputs) : JSObject := i.windowObject
def gameObject (i : Inputs) : JSObject := i.gameObject
def total (i : Inputs) : UInt64 := i.total

def ambient (base : Machine) (i : Inputs) : Machine := {base with
  heap := heap i
  context := ⟨localScope i,localScope i,base.context.thisValue,false⟩
  globalObject := window i
  objectEnvironmentExclusions := []}

theorem checked_global (i : Inputs) : checkedEnvironment (heap i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := i.globalRead
theorem checked_window (i : Inputs) : checkedObject (heap i) (window i) = .ok (windowObject i) := i.windowRead
theorem checked_game (i : Inputs) : checkedObject (heap i) (game i) = .ok (gameObject i) := i.gameRead
theorem window_kind (i : Inputs) : (windowObject i).kind = .host "Window" 0 := i.windowKind
theorem game_kind (i : Inputs) : (gameObject i).kind = .ordinary := i.gameKind
theorem windowGame_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Game") = .ok (some (.data (.object (game i)) true true false)) := i.windowGame
theorem total_read (i : Inputs) : lookupProperty (heap i) (game i) (JSString.ofString "lumpsTotal") = .ok (some (.data (.number (total i)) true true true)) := i.gameTotal
theorem existing_total (i : Inputs) : Number.lessThan 13830554455654793216 (total i) = true := i.existing

theorem identifier_game (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Game" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Game",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Game" (globalScope i) i.depth (window i)
    (.data (.object (game i)) true true false) i.path i.room i.globalRead i.windowGame rfl
theorem identifier_game_explicit (i : Inputs)
    (thisValue : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat)
    : Environment.identifier {
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } "Game" =
      {({
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } : Machine) with control := .expressionResult (.reference ⟨.environment (globalScope i) "Game",false⟩)} := by
  exact identifier_game {
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount
    } i


theorem negative_one : Number.neg (4607182418800017408 : UInt64) = 13830554455654793216 := by decide +kernel
attribute [local cbv_opaque] heap localScope globalScope window game windowObject gameObject total
attribute [local cbv_opaque] checkedEnvironment checkedObject lookupProperty Environment.identifier Number.lessThan Number.neg JSString.ofString
attribute [local cbv_eval] checked_global checked_window checked_game window_kind game_kind windowGame_read total_read existing_total identifier_game_explicit negative_one

def state (base : Machine) (i : Inputs) : Machine := {ambient base i with control := .statement LumpSyntax.canLumpsBody}
def afterBody (base : Machine) (i : Inputs) : Machine := {ambient base i with control := .completion (.return (.boolean true))}

theorem native_existing_body (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (22+fuel) (state base i) = Builtins.run fuel (afterBody base i) := by
  rw [Nat.add_comm 22 fuel]
  cbv

def body : List Stmt := match LumpSyntax.canLumpsBody with | .block statements => statements | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,[],body,scope,false,source⟩
def argumentObject (base : Machine) (callee : ObjectId) : JSObject := {
  kind := .arguments []
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "length",.data (.number Number.positiveZero) true false true⟩] ++ argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def locals (base : Machine) : List Binding := [{name := "arguments", value := .object base.heap.objects.size}]
def added (base : Machine) (scope : EnvId) : LexicalEnvironment := ⟨.declarative (locals base),some scope⟩
def allocatedHeap (base : Machine) (scope : EnvId) (callee : ObjectId) : Heap := {
  objects := base.heap.objects.push (argumentObject base callee)
  environments := base.heap.environments.push (added base scope) }
def prepared (base : Machine) (scope game callee : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope callee
  context := ⟨base.heap.environments.size,base.heap.environments.size,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true, ·)) [] [] body }

theorem actual_prepare (base : Machine) (scope game callee : ObjectId) (source : Option JSString) :
    prepareCall (callee := some callee) base (closure scope source) (.object game) [] none =
      .ok (prepared base scope game callee) := by
  simp [prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,locals,added,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_invoke (base : Machine) (scope game function : ObjectId)
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (closure scope source)) :
    invoke base (.object function) (.object game) [] false =
      prepared base scope game function := by
  simp [invoke,present,kind,checked,actual_prepare]

def hoisted (base : Machine) (scope game callee : ObjectId) : Machine := {
  prepared base scope game callee with control := .declarationFunctions [] body }
attribute [local cbv_opaque] allocatedHeap

theorem actual_hoist (base : Machine) (scope game callee : ObjectId) (fuel : Nat) :
    Builtins.run (5+fuel) (prepared base scope game callee) =
      Builtins.run fuel (hoisted base scope game callee) := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope game callee : ObjectId) :
    Builtins.builtinStep (hoisted base scope game callee) =
      Builtins.builtinStep {hoisted base scope game callee with control := .statement LumpSyntax.canLumpsBody} := rfl

def caller (base : Machine) (i : Inputs) : Machine := {base with heap := heap i,globalObject := window i,objectEnvironmentExclusions := []}

theorem allocated_extends (base : Machine) (scope callee : ObjectId) :
    HeapExtension.Extends base.heap (allocatedHeap base scope callee) :=
  HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base callee))
    (HeapExtension.same_objects rfl)

def calledInputs (base : Machine) (i : Inputs) (callee : ObjectId) : Inputs := {
  i with
  heap := allocatedHeap (caller base i) (localScope i) callee
  localScope := (heap i).environments.size
  depth := i.depth+1
  path := by
    apply HasEnvironment.DeclarativePath.next _ (localScope i) _ _ (locals (caller base i))
    · simp [allocatedHeap,caller,added]
    · rfl
    · exact HasEnvironment.append_path _ _ _ _ _ _ i.path
  room := by simpa [allocatedHeap,caller,heap] using Nat.add_le_add_right i.room 1
  globalRead := EnvironmentAppend.checked_old _ _ _ _ _ i.globalRead
  windowRead := HeapExtension.checked_object (allocated_extends _ _ _) _ _ i.windowRead
  gameRead := HeapExtension.checked_object (allocated_extends _ _ _) _ _ i.gameRead
  windowGame := HeapExtension.lookup_property (allocated_extends _ _ _) _ _ _ i.windowGame
  gameTotal := HeapExtension.lookup_property (allocated_extends _ _ _) _ _ _ i.gameTotal }

def returned (base : Machine) (i : Inputs) (callee : ObjectId) : Machine := {
  caller base i with
  heap := allocatedHeap (caller base i) (localScope i) callee
  control := .expressionResult (.value (.boolean true)) }

theorem called_body (base : Machine) (i : Inputs) (callee : ObjectId) (fuel : Nat) :
    let before := hoisted (caller base i) (localScope i) (game i) callee
    Builtins.run (22+fuel) before = Builtins.run fuel (afterBody before (calledInputs base i callee)) := by
  let before := hoisted (caller base i) (localScope i) (game i) callee
  have applied := native_existing_body before (calledInputs base i callee) fuel
  have state_eq : state before (calledInputs base i callee) =
      {before with control := .statement LumpSyntax.canLumpsBody} := rfl
  rw [state_eq] at applied
  change Builtins.run (22+fuel) before = _
  have same : Builtins.run (22+fuel) before =
      Builtins.run (22+fuel) {before with control := .statement LumpSyntax.canLumpsBody} := by
    rw [Nat.add_comm 22 fuel]
    change Builtins.run (fuel+21) (Builtins.builtinStep before) =
      Builtins.run (fuel+21) (Builtins.builtinStep {before with control := .statement LumpSyntax.canLumpsBody})
    rw [hoisted_starts_body]
  rw [same,applied]

theorem called_return (base : Machine) (i : Inputs) (callee : ObjectId) :
    Builtins.builtinStep (afterBody (hoisted (caller base i) (localScope i) (game i) callee)
      (calledInputs base i callee)) = returned base i callee := rfl

theorem native_prepared_returns (base : Machine) (i : Inputs) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (28+fuel) (prepared (caller base i) (localScope i) (game i) callee) =
      Builtins.run fuel (returned base i callee) := by
  rw [show 28+fuel = 5+(22+(1+fuel)) by omega,actual_hoist,called_body]
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep _) = _
  rw [called_return]

theorem native_invoke_returns (base : Machine) (i : Inputs) (function : ObjectId)
    (source : Option JSString) (object : JSObject)
    (present : checkedObject (heap i) function = .ok object)
    (kind : object.kind = .function (closure (localScope i) source)) (fuel : Nat) :
    Builtins.run (28+fuel) (invoke (caller base i) (.object function) (.object (game i)) [] false) =
      Builtins.run fuel (returned base i function) := by
  rw [actual_invoke _ _ _ _ _ _ present kind,native_prepared_returns]

theorem returned_elapsed (base : Machine) (i : Inputs) (callee : ObjectId) :
    (returned base i callee).elapsed = base.elapsed := rfl

theorem returned_caller_context (base : Machine) (i : Inputs) (callee : ObjectId) :
    (returned base i callee).context = base.context := rfl

theorem returned_caller_continuation (base : Machine) (i : Inputs) (callee : ObjectId) :
    (returned base i callee).continuation = base.continuation := rfl

end CookieClicker.JavaScript.CanLumpsCall

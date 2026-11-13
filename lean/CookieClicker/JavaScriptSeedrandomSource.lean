import CookieClicker.JavaScriptSeedrandomReset
import CookieClicker.JavaScriptIdentifierPath
/-! Exact evaluation of computeLumpType's final Math.seedrandom() statement.
The captured identity is used by the actual BrowserRuntime reset rule. -/
namespace CookieClicker.JavaScript.SeedrandomSource
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
structure Inputs where
  heap : Heap
  localScope : EnvId
  globalScope : EnvId
  depth : Nat
  window : ObjectId
  math : ObjectId
  seedrandom : ObjectId
  random : ObjectId
  windowObject : JSObject
  mathObject : JSObject
  path : HasEnvironment.DeclarativePath heap.environments "Math" localScope globalScope depth
  room : depth ≤ heap.environments.size
  globalRead : checkedEnvironment heap globalScope = .ok ⟨.object window false,none⟩
  windowRead : checkedObject heap window = .ok windowObject
  mathRead : checkedObject heap math = .ok mathObject
  windowKind : windowObject.kind = .host "Window" 0
  mathKind : mathObject.kind = .ordinary
  windowMath : lookupProperty heap window (JSString.ofString "Math") = .ok (some (.data (.object math) true false true))
  mathSeedrandom : lookupProperty heap math (JSString.ofString "seedrandom") = .ok (some (.data (.object seedrandom) true true true))
def heap (i : Inputs) : Heap := i.heap
def localScope (i : Inputs) : EnvId := i.localScope
def globalScope (i : Inputs) : EnvId := i.globalScope
def window (i : Inputs) : ObjectId := i.window
def math (i : Inputs) : ObjectId := i.math
def seedrandom (i : Inputs) : ObjectId := i.seedrandom
def random (i : Inputs) : ObjectId := i.random
def windowObject (i : Inputs) : JSObject := i.windowObject
def mathObject (i : Inputs) : JSObject := i.mathObject

def ambient (base : Machine) (i : Inputs) : Machine := {base with
  heap := heap i
  context := ⟨localScope i,localScope i,base.context.thisValue,false⟩
  globalObject := window i
  objectEnvironmentExclusions := []}

theorem checked_global (i : Inputs) : checkedEnvironment (heap i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := i.globalRead
theorem checked_window (i : Inputs) : checkedObject (heap i) (window i) = .ok (windowObject i) := i.windowRead
theorem checked_math (i : Inputs) : checkedObject (heap i) (math i) = .ok (mathObject i) := i.mathRead
theorem window_kind (i : Inputs) : (windowObject i).kind = .host "Window" 0 := i.windowKind
theorem math_kind (i : Inputs) : (mathObject i).kind = .ordinary := i.mathKind
theorem windowMath_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Math") = .ok (some (.data (.object (math i)) true false true)) := i.windowMath
theorem seedrandom_read (i : Inputs) : lookupProperty (heap i) (math i) (JSString.ofString "seedrandom") = .ok (some (.data (.object (seedrandom i)) true true true)) := i.mathSeedrandom

theorem identifier_math (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Math" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Math",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Math" (globalScope i) i.depth (window i)
    (.data (.object (math i)) true false true) i.path i.room i.globalRead i.windowMath rfl
theorem identifier_math_explicit (i : Inputs)
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
    } "Math" =
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
    } : Machine) with control := .expressionResult (.reference ⟨.environment (globalScope i) "Math",false⟩)} := by
  exact identifier_math {
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


def call : Expr := .call (.member (.identifier "Math") (.identifier "seedrandom") false) []
def sourceStatement : Stmt := match LumpSyntax.computeLumpTypeBody with
  | .block statements => statements.getLast?.getD .empty
  | _ => .empty

def browserAmbient (base : Browser.State) (i : Inputs) : Browser.State := {
  base with
  machine := ambient base.machine i
  mathObject := some (math i)
  freeRandom := some (random i)
  nativeSeedrandom := some (seedrandom i) }

def start (base : Browser.State) (i : Inputs) : Browser.State := {
  browserAmbient base i with
  machine := {ambient base.machine i with control := .statement sourceStatement} }

attribute [local cbv_opaque] heap localScope globalScope window math seedrandom random windowObject mathObject
attribute [local cbv_opaque] checkedEnvironment checkedObject lookupProperty Environment.identifier JSString.ofString
attribute [local cbv_opaque] Browser.restoreFreeRandom
attribute [local cbv_eval] checked_global checked_window checked_math window_kind math_kind windowMath_read seedrandom_read identifier_math_explicit

theorem source_statement_eq : sourceStatement = .expression call := rfl

theorem actual_source_prefix (base : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (10+fuel) (start base i) =
      BrowserRuntime.run fuel (SeedrandomReset.before (browserAmbient base i) (seedrandom i) (math i) (random i)) := by
  rw [Nat.add_comm 10 fuel]
  cbv

theorem actual_source_prelude (base : Browser.State) (i : Inputs) :
    BrowserRuntime.run 10 (start base i) =
      SeedrandomReset.before (browserAmbient base i) (seedrandom i) (math i) (random i) := by
  cbv

theorem source_step_count (base : Browser.State) (i : Inputs) :
    BrowserRuntime.run 11 (start base i) =
      BrowserRuntime.step (BrowserRuntime.run 10 (start base i)) := by
  cbv

theorem actual_source_reset (base : Browser.State) (i : Inputs) :
    BrowserRuntime.run 11 (start base i) =
      SeedrandomReset.after (browserAmbient base i) (seedrandom i) (math i) (random i) (mathObject i) := by
  rw [source_step_count,actual_source_prelude]
  exact SeedrandomReset.actual_runtime_step _ _ _ _ _ i.mathRead

theorem source_random_property (base : Browser.State) (i : Inputs) (previous : PropertyDescriptor)
    (present : ownProperty (mathObject i) (JSString.ofString "random") = some previous) :
    ((BrowserRuntime.run 11 (start base i)).machine.heap.object? (math i)).map
      (fun object => ownProperty object (JSString.ofString "random")) =
      some (some (.data (.object (random i)) true false true)) := by
  rw [source_step_count,actual_source_prelude]
  exact SeedrandomReset.reset_random_property _ _ _ _ _ i.mathRead i.mathKind previous present

theorem source_preserves_other_objects (base : Browser.State) (i : Inputs)
    (other : ObjectId) (different : other ≠ math i) :
    (BrowserRuntime.run 11 (start base i)).machine.heap.object? other = (heap i).object? other := by
  rw [source_step_count,actual_source_prelude]
  exact SeedrandomReset.reset_preserves_other_objects _ _ _ _ _ i.mathRead other different

theorem source_preserves_environments (base : Browser.State) (i : Inputs) :
    (BrowserRuntime.run 11 (start base i)).machine.heap.environments = (heap i).environments := by
  rw [actual_source_reset]
  rfl

theorem source_no_free_draw (base : Browser.State) (i : Inputs) :
    (BrowserRuntime.run 11 (start base i)).machine.freeDrawCount = base.machine.freeDrawCount := by
  rw [actual_source_reset]
  rfl

theorem source_elapsed (base : Browser.State) (i : Inputs) :
    (BrowserRuntime.run 11 (start base i)).machine.elapsed = base.machine.elapsed := by
  rw [actual_source_reset]
  rfl

theorem actual_reset_tail (base : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (11+fuel) (start base i) =
      BrowserRuntime.run fuel
        (SeedrandomReset.after (browserAmbient base i) (seedrandom i) (math i) (random i) (mathObject i)) := by
  rw [show 11+fuel = 10+(fuel+1) by omega,actual_source_prefix]
  change BrowserRuntime.run fuel (BrowserRuntime.step _) = _
  rw [SeedrandomReset.actual_runtime_step _ _ _ _ _ i.mathRead]
  rfl

def returnBase (base : Browser.State) (caller : ExecutionContext) (continuation : List Frame) : Browser.State := {
  base with machine := {base.machine with
    continuation := .statementList [] none :: .callBoundary caller none :: continuation} }

def returned (base : Browser.State) (i : Inputs) (caller : ExecutionContext)
    (continuation : List Frame) : Browser.State := {
  SeedrandomReset.after (browserAmbient base i) (seedrandom i) (math i) (random i) (mathObject i) with
  machine := {ambient base.machine i with
    heap := SeedrandomReset.updatedHeap (heap i) (math i) (mathObject i) (random i)
    context := caller
    control := .expressionResult (.value .undefined)
    continuation := continuation} }

attribute [local cbv_opaque] SeedrandomReset.updatedHeap

theorem callback_return_tail (base : Browser.State) (i : Inputs)
    (caller : ExecutionContext) (continuation : List Frame) :
    BrowserRuntime.run 3 (SeedrandomReset.after
      (browserAmbient (returnBase base caller continuation) i) (seedrandom i) (math i) (random i) (mathObject i)) =
      returned base i caller continuation := by
  cbv

theorem source_callback_return (base : Browser.State) (i : Inputs)
    (caller : ExecutionContext) (continuation : List Frame) :
    BrowserRuntime.run 14 (start (returnBase base caller continuation) i) =
      returned base i caller continuation := by
  rw [show (14 : Nat) = 11+3 from rfl,actual_reset_tail,callback_return_tail]

theorem callback_restores_generator (base : Browser.State) (i : Inputs)
    (caller : ExecutionContext) (continuation : List Frame) (previous : PropertyDescriptor)
    (present : ownProperty (mathObject i) (JSString.ofString "random") = some previous) :
    ((BrowserRuntime.run 14 (start (returnBase base caller continuation) i)).machine.heap.object? (math i)).map
      (fun object => ownProperty object (JSString.ofString "random")) =
      some (some (.data (.object (random i)) true false true)) := by
  rw [source_callback_return]
  have saved := source_random_property base i previous present
  rw [actual_source_reset] at saved
  exact saved

theorem callback_preserves_free_intrinsic (base : Browser.State) (i : Inputs)
    (caller : ExecutionContext) (continuation : List Frame) (randomObject : JSObject)
    (randomRead : checkedObject (heap i) (random i) = .ok randomObject)
    (randomKind : randomObject.kind = .builtin ⟨"Math","random"⟩) :
    checkedObject (BrowserRuntime.run 14 (start (returnBase base caller continuation) i)).machine.heap
      (random i) = .ok randomObject := by
  have saved := SeedrandomReset.reset_preserves_free_intrinsic (browserAmbient base i)
    (seedrandom i) (math i) (random i) (mathObject i) randomObject i.mathRead randomRead i.mathKind randomKind
  rw [SeedrandomReset.actual_runtime_step _ _ _ _ _ i.mathRead] at saved
  rw [source_callback_return]
  exact saved

end CookieClicker.JavaScript.SeedrandomSource

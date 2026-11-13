import CookieClicker.JavaScriptSeedrandomSource
/-! Native computeLumpType constructs the exact source seed argument before
invoking the captured seeded-generator closure. Its body is not replaced by a
value contract. Timestamp rendering is the selected clock codec. -/
namespace CookieClicker.JavaScript.SeedrandomEntry
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
structure Inputs where
  host : SeedrandomSource.Inputs
  game : ObjectId
  gameObject : JSObject
  gameDepth : Nat
  seed : JSString
  birth : ClockValue.Timestamp
  birthText : JSString
  rendered : ClockValue.Codec.render birth = some birthText
  gamePath : HasEnvironment.DeclarativePath host.heap.environments "Game" host.localScope host.globalScope gameDepth
  gameRoom : gameDepth ≤ host.heap.environments.size
  gameRead : checkedObject host.heap game = .ok gameObject
  gameKind : gameObject.kind = .ordinary
  windowGame : lookupProperty host.heap host.window (JSString.ofString "Game") = .ok (some (.data (.object game) true true false))
  gameSeed : lookupProperty host.heap game (JSString.ofString "seed") = .ok (some (.data (.string seed) true true true))
  gameBirth : lookupProperty host.heap game (JSString.ofString "lumpT") = .ok (some (.data (.timestamp birth) true true true))
def heap (i : Inputs) := i.host.heap
def localScope (i : Inputs) := i.host.localScope
def globalScope (i : Inputs) := i.host.globalScope
def window (i : Inputs) := i.host.window
def math (i : Inputs) := i.host.math
def seedrandom (i : Inputs) := i.host.seedrandom
def random (i : Inputs) := i.host.random
def windowObject (i : Inputs) := i.host.windowObject
def mathObject (i : Inputs) := i.host.mathObject
def game (i : Inputs) := i.game
def gameObject (i : Inputs) := i.gameObject
def seed (i : Inputs) := i.seed
def birth (i : Inputs) := i.birth
def birthText (i : Inputs) := i.birthText
def ambient (base : Machine) (i : Inputs) : Machine := {base with
  heap := heap i
  context := ⟨localScope i,localScope i,base.context.thisValue,false⟩
  globalObject := window i
  objectEnvironmentExclusions := []}
def browserAmbient (base : Browser.State) (i : Inputs) : Browser.State := {base with
  machine := ambient base.machine i
  mathObject := some (math i)
  freeRandom := some (random i)
  nativeSeedrandom := some (seedrandom i)}

theorem checked_global (i : Inputs) : checkedEnvironment (heap i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := i.host.globalRead
theorem checked_window (i : Inputs) : checkedObject (heap i) (window i) = .ok (windowObject i) := i.host.windowRead
theorem checked_math (i : Inputs) : checkedObject (heap i) (math i) = .ok (mathObject i) := i.host.mathRead
theorem window_kind (i : Inputs) : (windowObject i).kind = .host "Window" 0 := i.host.windowKind
theorem math_kind (i : Inputs) : (mathObject i).kind = .ordinary := i.host.mathKind
theorem windowMath_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Math") = .ok (some (.data (.object (math i)) true false true)) := i.host.windowMath
theorem seedrandom_read (i : Inputs) : lookupProperty (heap i) (math i) (JSString.ofString "seedrandom") = .ok (some (.data (.object (seedrandom i)) true true true)) := i.host.mathSeedrandom

theorem identifier_math (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Math" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Math",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Math" (globalScope i) i.host.depth (window i)
    (.data (.object (math i)) true false true) i.host.path i.host.room i.host.globalRead i.host.windowMath rfl
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


theorem checked_game (i : Inputs) : checkedObject (heap i) (game i) = .ok (gameObject i) := i.gameRead
theorem game_kind (i : Inputs) : (gameObject i).kind = .ordinary := i.gameKind
theorem windowGame_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Game") = .ok (some (.data (.object (game i)) true true false)) := i.windowGame
theorem seed_read (i : Inputs) : lookupProperty (heap i) (game i) (JSString.ofString "seed") = .ok (some (.data (.string (seed i)) true true true)) := i.gameSeed
theorem birth_read (i : Inputs) : lookupProperty (heap i) (game i) (JSString.ofString "lumpT") = .ok (some (.data (.timestamp (birth i)) true true true)) := i.gameBirth

theorem identifier_game (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Game" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Game",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Game" i.host.globalScope i.gameDepth i.host.window
    (.data (.object (game i)) true true false) i.gamePath i.gameRoom i.host.globalRead i.windowGame rfl
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


def argument (i : Inputs) : JSString := (seed i ++ [47]) ++ birthText i

theorem string_append (a b : JSString) : binary .add (.string a) (.string b) = .ok (.string (a++b)) := rfl

theorem timestamp_append (i : Inputs) (a : JSString) :
    binary .add (.string a) (.timestamp (birth i)) = .ok (.timestampText (a++birthText i).toArray) := by
  simp [binary,textResult,timestampTextSource,toJSString,birth,birthText,i.rendered,bind,Except.bind,pure,Except.pure]

def sourceStatement : Stmt := match LumpSyntax.computeLumpTypeBody with
  | .block statements => statements.headD .empty
  | _ => .empty

def start (base : Browser.State) (i : Inputs) : Browser.State := {
  browserAmbient base i with
  machine := {ambient base.machine i with control := .statement sourceStatement} }

def atInvoke (base : Browser.State) (i : Inputs) : Browser.State := {
  browserAmbient base i with
  machine := {ambient base.machine i with
    control := .invoke (.object (seedrandom i)) (.object (math i)) [.timestampText (argument i).toArray] false
    continuation := .expressionStatement :: base.machine.continuation} }

attribute [local cbv_opaque] heap localScope globalScope window math seedrandom random windowObject mathObject
attribute [local cbv_opaque] game gameObject seed birth birthText
attribute [local cbv_opaque] checkedEnvironment checkedObject lookupProperty Environment.identifier JSString.ofString binary
attribute [local cbv_opaque] Browser.restoreFreeRandom
attribute [local cbv_eval] checked_global checked_window checked_math window_kind math_kind windowMath_read seedrandom_read identifier_math_explicit
attribute [local cbv_eval] checked_game game_kind windowGame_read seed_read birth_read identifier_game_explicit string_append timestamp_append

theorem actual_seed_argument (base : Browser.State) (i : Inputs) :
    BrowserRuntime.run 32 (start base i) = atInvoke base i := by
  cbv

theorem invoke_step_count (base : Browser.State) (i : Inputs) :
    BrowserRuntime.run 33 (start base i) = BrowserRuntime.step (BrowserRuntime.run 32 (start base i)) := by
  cbv

end CookieClicker.JavaScript.SeedrandomEntry

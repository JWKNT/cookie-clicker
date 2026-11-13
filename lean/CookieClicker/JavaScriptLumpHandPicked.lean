import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptLumpSyntax
/-! The pinned clickLump age branch, choice initializer and award gate.
These prefixes preserve the actual source continuation and native local write.
They start after the animation, eligibility and age-computation effects; the
entry frame and the complete Win callback remain separate source obligations.
-/
namespace CookieClicker.JavaScript.LumpHandPicked
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
structure Inputs where
  heap : Heap
  localScope : Nat
  globalScope : Nat
  depth : Nat
  window : ObjectId
  game : ObjectId
  windowObject : JSObject
  gameObject : JSObject
  bindings : List Binding
  outer : Option EnvId
  age : UInt64
  mature : UInt64
  ripe : UInt64
  localRead : checkedEnvironment heap localScope = .ok ⟨.declarative bindings,outer⟩
  amountDeclared : bindings.any (fun b => b.name == "amount") = true
  ageDeclared : bindings.any (fun b => b.name == "age") = true
  ageRead : readBinding heap localScope "age" = .ok (.number age)
  gamePath : HasEnvironment.DeclarativePath heap.environments "Game" localScope globalScope depth
  depthBound : depth ≤ heap.environments.size
  globalRead : checkedEnvironment heap globalScope = .ok ⟨.object window false,none⟩
  windowRead : checkedObject heap window = .ok windowObject
  windowKind : windowObject.kind = .host "Window" 0
  gameRead : checkedObject heap game = .ok gameObject
  gameKind : gameObject.kind = .ordinary
  windowGame : lookupProperty heap window (JSString.ofString "Game") = .ok (some (.data (.object game) true true false))
  gameMature : lookupProperty heap game (JSString.ofString "lumpMatureAge") = .ok (some (.data (.number mature) true true true))
  gameRipe : lookupProperty heap game (JSString.ofString "lumpRipeAge") = .ok (some (.data (.number ripe) true true true))
  isMature : Number.lessThan age mature = false
  isUnripe : Number.lessThan age ripe = true
def heap (i : Inputs) : Heap := i.heap
def localScope (i : Inputs) : Nat := i.localScope
def globalScope (i : Inputs) : Nat := i.globalScope
def window (i : Inputs) : ObjectId := i.window
def game (i : Inputs) : ObjectId := i.game
def windowObject (i : Inputs) : JSObject := i.windowObject
def gameObject (i : Inputs) : JSObject := i.gameObject
def age (i : Inputs) : UInt64 := i.age
def mature (i : Inputs) : UInt64 := i.mature
def ripe (i : Inputs) : UInt64 := i.ripe

def ambient (base : Machine) (i : Inputs) : Machine := {base with
  heap := heap i
  context := ⟨localScope i,localScope i,base.context.thisValue,false⟩
  globalObject := window i
  objectEnvironmentExclusions := []}
theorem checked_local (i : Inputs) : checkedEnvironment (heap i) (localScope i) = .ok ⟨.declarative i.bindings,i.outer⟩ := i.localRead
theorem checked_global (i : Inputs) : checkedEnvironment (heap i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := i.globalRead
theorem read_age (i : Inputs) : readBinding (heap i) (localScope i) "age" = .ok (.number (age i)) := i.ageRead
theorem checked_window (i : Inputs) : checkedObject (heap i) (window i) = .ok (windowObject i) := i.windowRead
theorem window_kind (i : Inputs) : (windowObject i).kind = .host "Window" 0 := i.windowKind
theorem checked_game (i : Inputs) : checkedObject (heap i) (game i) = .ok (gameObject i) := i.gameRead
theorem game_kind (i : Inputs) : (gameObject i).kind = .ordinary := i.gameKind
theorem windowGame_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Game") = .ok (some (.data (.object (game i)) true true false)) := i.windowGame
theorem gameMature_read (i : Inputs) : lookupProperty (heap i) (game i) (JSString.ofString "lumpMatureAge") = .ok (some (.data (.number (mature i)) true true true)) := i.gameMature
theorem gameRipe_read (i : Inputs) : lookupProperty (heap i) (game i) (JSString.ofString "lumpRipeAge") = .ok (some (.data (.number (ripe i)) true true true)) := i.gameRipe
theorem mature_test (i : Inputs) : Number.lessThan (age i) (mature i) = false := i.isMature
theorem ripe_test (i : Inputs) : Number.lessThan (age i) (ripe i) = true := i.isUnripe
theorem identifier_game (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Game" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Game",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Game" (globalScope i) i.depth (window i)
    (.data (.object (game i)) true true false) i.gamePath i.depthBound i.globalRead i.windowGame rfl

theorem identifier_age (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "age" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (localScope i) "age",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _ i.localRead i.ageDeclared

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
      freeDrawCount := freeDrawCount} "Game" =
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
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (globalScope i) "Game",false⟩)} := by
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
      freeDrawCount := freeDrawCount} i

theorem identifier_age_explicit (i : Inputs)
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
      freeDrawCount := freeDrawCount} "age" =
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
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (localScope i) "age",false⟩)} := by
  exact identifier_age {
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
      freeDrawCount := freeDrawCount} i


def guard : Stmt := match LumpSyntax.clickLumpBody with
  | .block body => (body[4]?).getD .empty
  | _ => .empty

def unripe : Stmt := match guard with
  | .ifThenElse _ _ (some (.ifThenElse _ body _)) => body
  | _ => .empty

def start (base : Machine) (i : Inputs) : Machine := {ambient base i with control := .statement guard}
def atUnripe (base : Machine) (i : Inputs) : Machine := {ambient base i with control := .statement unripe}
attribute [local cbv_opaque] heap localScope globalScope window game windowObject gameObject age mature ripe
attribute [local cbv_opaque] JSString.ofString checkedObject lookupProperty Environment.identifier
attribute [local cbv_opaque] checkedEnvironment readBinding Number.lessThan
attribute [local cbv_eval] checked_local checked_global read_age checked_window window_kind checked_game game_kind
attribute [local cbv_eval] windowGame_read gameMature_read gameRipe_read mature_test ripe_test
set_option pp.deepTerms false in
set_option pp.proofs false in
theorem unripe_branch (base : Machine) (i : Inputs) (fuel : Nat) :
  Builtins.run (30+fuel) (start base i) = Builtins.run fuel (atUnripe base i) := by
  rw [Nat.add_comm 30 fuel]
  cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv
  try simp only [identifier_game_explicit,identifier_age_explicit,checked_local,checked_global,read_age,checked_window,window_kind,checked_game,game_kind,windowGame_read,gameMature_read,gameRipe_read,mature_test,ripe_test]
  try cbv

def unripeStatements : List Stmt := match unripe with
  | .block statements => statements
  | _ => []
def chooseCall : Expr := .call (.identifier "choose")
  [.array [some (.literal (.number 0)),some (.literal (.number Number.one))]]
def afterChoice : List Stmt := unripeStatements.drop 1

def atChoice (base : Machine) (i : Inputs) : Machine := {ambient base i with
  control := .expression chooseCall
  continuation :=
    .assignmentRight .assign ⟨.environment (localScope i) "amount",false⟩ none ::
    .variableWrite [] :: .statementList afterChoice none :: base.continuation}

attribute [local cbv_opaque] List.any

theorem choose_entry (base : Machine) (i : Inputs) (fuel : Nat) :
  Builtins.run (2+fuel) (atUnripe base i) = Builtins.run fuel (atChoice base i) := by
  rw [Nat.add_comm 2 fuel]
  cbv
  try simp only [checked_local,i.amountDeclared]
  try cbv


theorem unripe_choice_prefix (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (32+fuel) (start base i) = Builtins.run fuel (atChoice base i) := by
  rw [show 32+fuel=30+(2+fuel) by omega,unripe_branch,choose_entry]

theorem native_body_guard :
  (match LumpSyntax.clickLumpBody with | .block body => body[4]? | _ => none) = some guard := rfl

theorem native_unripe_choice :
  unripeStatements =
    .variable [("amount",some chooseCall)] :: afterChoice := rfl

theorem identifier_amount (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "amount" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (localScope i) "amount",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _ i.localRead i.amountDeclared

theorem identifier_amount_explicit (i : Inputs)
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
      freeDrawCount := freeDrawCount} "amount" =
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
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (localScope i) "amount",false⟩)} := by
  exact identifier_amount {
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
      freeDrawCount := freeDrawCount} i



def awardGuard : Stmt := afterChoice.headD .empty
def atAwardGuard (base : Machine) (i : Inputs) : Machine :=
  {ambient base i with control := .statement awardGuard}
def awardCall : Expr := .call (.member (.identifier "Game") (.identifier "Win") false)
  [.literal (.string (JSString.ofString "Hand-picked"))]
def atAwardCall (base : Machine) (i : Inputs) : Machine :=
  {ambient base i with control := .statement (.expression awardCall)}

theorem native_award_guard : awardGuard =
    .ifThenElse (.binary .notEqual (.identifier "amount") (.literal (.number 0)))
      (.expression awardCall) none := rfl

theorem one_not_zero : Number.equal Number.one (0 : UInt64) = false := by decide +kernel
theorem zero_eq_zero : Number.equal (0 : UInt64) 0 = true := by decide +kernel
attribute [local cbv_opaque] Number.equal
attribute [local cbv_eval] one_not_zero zero_eq_zero

set_option pp.deepTerms false in
set_option pp.proofs false in
theorem award_one (base : Machine) (i : Inputs)
    (read : readBinding (heap i) (localScope i) "amount" = .ok (.number Number.one))
    (fuel : Nat) :
    Builtins.run (9+fuel) (atAwardGuard base i) = Builtins.run fuel (atAwardCall base i) := by
  rw [Nat.add_comm 9 fuel]
  cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv

set_option pp.deepTerms false in
set_option pp.proofs false in
theorem award_zero (base : Machine) (i : Inputs)
    (read : readBinding (heap i) (localScope i) "amount" = .ok (.number 0))
    (fuel : Nat) :
    Builtins.run (9+fuel) (atAwardGuard base i) = Builtins.run fuel
      {ambient base i with control := .completion (.normal none)} := by
  rw [Nat.add_comm 9 fuel]
  cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv
  try simp only [identifier_amount_explicit,checked_local,read,one_not_zero,zero_eq_zero]
  try cbv

def choiceReturned (base : Machine) (i : Inputs) (value : Value) : Machine :=
  {atChoice base i with control := .expressionResult (.value value)}
def atStoredAward (base : Machine) (i : Inputs) (nextHeap : Heap) : Machine :=
  {ambient base i with
    heap := nextHeap
    control := .statement awardGuard
    continuation := .statementList (afterChoice.drop 1) none :: base.continuation}

attribute [local cbv_opaque] setBinding
set_option pp.deepTerms false in
set_option pp.proofs false in
theorem store_choice_prefix (base : Machine) (i : Inputs) (value : Value)
    (nextHeap : Heap)
    (written : setBinding (heap i) (localScope i) "amount" value false = .ok nextHeap)
    (fuel : Nat) :
    Builtins.run (4+fuel) (choiceReturned base i value) =
      Builtins.run fuel (atStoredAward base i nextHeap) := by
  rw [Nat.add_comm 4 fuel]
  cbv
  try simp only [checked_local,written]
  try cbv
  try simp only [written]
  try cbv

end CookieClicker.JavaScript.LumpHandPicked

import CookieClicker.JavaScriptLumpHandPicked
import CookieClicker.JavaScriptBindingWrite
import CookieClicker.JavaScriptClockSemantics
/-! The intact clickLump age initializer invokes the original Date.now builtin,
subtracts the source lump timestamp and writes the actual local age binding.
The preceding animations/eligibility call and initialized entry invariant are
separate source obligations. No timestamp-selected outcome is assumed. -/
namespace CookieClicker.JavaScript.LumpAge
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
structure Inputs where
  heap : Heap
  localScope : EnvId
  globalScope : EnvId
  gameDepth : Nat
  dateDepth : Nat
  window : ObjectId
  game : ObjectId
  date : ObjectId
  nowFunction : ObjectId
  windowObject : JSObject
  gameObject : JSObject
  dateObject : JSObject
  nowObject : JSObject
  birth : ClockValue.Timestamp
  bindings : List Binding
  outer : Option EnvId
  ageBinding : Binding
  localRead : checkedEnvironment heap localScope = .ok ⟨.declarative bindings,outer⟩
  ageFound : bindings.find? (fun b => b.name == "age") = some ageBinding
  ageMutable : ageBinding.mutable = true
  amountDeclared : bindings.any (fun b => b.name == "amount") = true
  gamePath : HasEnvironment.DeclarativePath heap.environments "Game" localScope globalScope gameDepth
  datePath : HasEnvironment.DeclarativePath heap.environments "Date" localScope globalScope dateDepth
  gameRoom : gameDepth ≤ heap.environments.size
  dateRoom : dateDepth ≤ heap.environments.size
  globalRead : checkedEnvironment heap globalScope = .ok ⟨.object window false,none⟩
  windowRead : checkedObject heap window = .ok windowObject
  gameRead : checkedObject heap game = .ok gameObject
  dateRead : checkedObject heap date = .ok dateObject
  nowRead : checkedObject heap nowFunction = .ok nowObject
  windowKind : windowObject.kind = .host "Window" 0
  gameKind : gameObject.kind = .ordinary
  dateKind : dateObject.kind = .builtin ⟨"global","Date"⟩
  nowKind : nowObject.kind = .builtin ⟨"Date","now"⟩
  windowGame : lookupProperty heap window (JSString.ofString "Game") = .ok (some (.data (.object game) true true false))
  windowDate : lookupProperty heap window (JSString.ofString "Date") = .ok (some (.data (.object date) true false true))
  dateNow : lookupProperty heap date (JSString.ofString "now") = .ok (some (.data (.object nowFunction) true false true))
  gameBirth : lookupProperty heap game (JSString.ofString "lumpT") = .ok (some (.data (.timestamp birth) true true true))
def heap (i : Inputs) : Heap := i.heap
def localScope (i : Inputs) : EnvId := i.localScope
def globalScope (i : Inputs) : EnvId := i.globalScope
def window (i : Inputs) : ObjectId := i.window
def game (i : Inputs) : ObjectId := i.game
def date (i : Inputs) : ObjectId := i.date
def nowFunction (i : Inputs) : ObjectId := i.nowFunction
def windowObject (i : Inputs) : JSObject := i.windowObject
def gameObject (i : Inputs) : JSObject := i.gameObject
def dateObject (i : Inputs) : JSObject := i.dateObject
def nowObject (i : Inputs) : JSObject := i.nowObject
def birth (i : Inputs) : ClockValue.Timestamp := i.birth

def ambient (base : Machine) (i : Inputs) : Machine := {base with
  heap := heap i
  context := ⟨localScope i,localScope i,base.context.thisValue,false⟩
  globalObject := window i
  objectEnvironmentExclusions := []}

def ageStatement : Stmt := match LumpSyntax.clickLumpBody with
  | .block statements => statements[3]?.getD .empty
  | _ => .empty

def ageValue (base : Machine) (i : Inputs) : UInt64 :=
  (ClockValue.Timestamp.now base.epochMilliseconds base.elapsed).difference (birth i)

def changed (base : Machine) (i : Inputs) : Heap :=
  BindingWrite.changedHeap (heap i) (localScope i) i.bindings i.outer "age" (.number (ageValue base i))

def state (base : Machine) (i : Inputs) : Machine := {ambient base i with control := .statement ageStatement}

def returned (base : Machine) (i : Inputs) : Machine := {ambient base i with
  heap := changed base i
  control := .completion (.normal none)}

theorem checked_local (i : Inputs) : checkedEnvironment (heap i) (localScope i) = .ok ⟨.declarative i.bindings,i.outer⟩ := i.localRead
theorem checked_global (i : Inputs) : checkedEnvironment (heap i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := i.globalRead
theorem checked_window (i : Inputs) : checkedObject (heap i) (window i) = .ok (windowObject i) := i.windowRead
theorem window_kind (i : Inputs) : (windowObject i).kind = .host "Window" 0 := i.windowKind
theorem checked_game (i : Inputs) : checkedObject (heap i) (game i) = .ok (gameObject i) := i.gameRead
theorem game_kind (i : Inputs) : (gameObject i).kind = .ordinary := i.gameKind
theorem checked_date (i : Inputs) : checkedObject (heap i) (date i) = .ok (dateObject i) := i.dateRead
theorem date_kind (i : Inputs) : (dateObject i).kind = .builtin ⟨"global","Date"⟩ := i.dateKind
theorem checked_now (i : Inputs) : checkedObject (heap i) (nowFunction i) = .ok (nowObject i) := i.nowRead
theorem now_kind (i : Inputs) : (nowObject i).kind = .builtin ⟨"Date","now"⟩ := i.nowKind
theorem windowGame_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Game") = .ok (some (.data (.object (game i)) true true false)) := i.windowGame
theorem windowDate_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Date") = .ok (some (.data (.object (date i)) true false true)) := i.windowDate
theorem dateNow_read (i : Inputs) : lookupProperty (heap i) (date i) (JSString.ofString "now") = .ok (some (.data (.object (nowFunction i)) true false true)) := i.dateNow
theorem gameBirth_read (i : Inputs) : lookupProperty (heap i) (game i) (JSString.ofString "lumpT") = .ok (some (.data (.timestamp (birth i)) true true true)) := i.gameBirth

theorem identifier_game (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Game" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Game",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Game" (globalScope i) i.gameDepth (window i)
    (.data (.object (game i)) true true false) i.gamePath i.gameRoom i.globalRead i.windowGame rfl

theorem identifier_date (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Date" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Date",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Date" (globalScope i) i.dateDepth (window i)
    (.data (.object (date i)) true false true) i.datePath i.dateRoom i.globalRead i.windowDate rfl

theorem age_declared (i : Inputs) : i.bindings.any (fun b => b.name == "age") = true :=
  List.any_eq_true.mpr ⟨i.ageBinding,List.mem_of_find?_eq_some i.ageFound,(List.find?_eq_some_iff_append.mp i.ageFound).1⟩

theorem age_reference (base : Machine) (i : Inputs) :
    identifierReference (ambient base i) "age" = .ok ⟨.environment (localScope i) "age",false⟩ := by
  simp only [identifierReference,ambient]
  change resolveName (heap i) false ((heap i).environments.size+1) (localScope i) "age" = _
  rw [resolveName,checked_local]
  simp [bind,Except.bind,pure,Except.pure,age_declared]

theorem age_write (i : Inputs) (value : Value) :
    setBinding (heap i) (localScope i) "age" value false =
      .ok (BindingWrite.changedHeap (heap i) (localScope i) i.bindings i.outer "age" value) :=
  BindingWrite.native_set (heap i) (localScope i) i.bindings i.outer "age" value i.ageBinding false
    i.localRead i.ageFound i.ageMutable

theorem date_dispatch (machine : Machine) (receiver : Value) :
    Date.dispatch machine ⟨"Date","now"⟩ receiver [] false =
      result machine (.timestamp (ClockValue.Timestamp.now machine.epochMilliseconds machine.elapsed)) := rfl

theorem timestamp_difference (left right : ClockValue.Timestamp) :
    binary .subtract (.timestamp left) (.timestamp right) = .ok (.number (left.difference right)) := rfl

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

theorem identifier_date_explicit (i : Inputs)
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
    } "Date" =
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
    } : Machine) with control := .expressionResult (.reference ⟨.environment (globalScope i) "Date",false⟩)} := by
  exact identifier_date {
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

theorem age_reference_explicit (i : Inputs)
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
    : identifierReference {
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
    } "age" =
      .ok ⟨.environment (localScope i) "age",false⟩ := by
  exact age_reference {
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

attribute [local cbv_opaque] heap localScope globalScope window game date nowFunction windowObject gameObject dateObject nowObject birth
attribute [local cbv_opaque] checkedEnvironment checkedObject lookupProperty setBinding Environment.identifier identifierReference
attribute [local cbv_opaque] BindingWrite.changedHeap
attribute [local cbv_opaque] Date.dispatch ClockValue.Timestamp.now ClockValue.Timestamp.difference binary JSString.ofString
attribute [local cbv_eval] checked_local checked_global checked_window checked_game checked_date checked_now
attribute [local cbv_eval] window_kind game_kind date_kind now_kind windowGame_read windowDate_read dateNow_read gameBirth_read
attribute [local cbv_eval] identifier_game_explicit identifier_date_explicit age_reference_explicit age_write date_dispatch timestamp_difference

theorem native_age_initializer (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (25+fuel) (state base i) = Builtins.run fuel (returned base i) := by
  rw [Nat.add_comm 25 fuel]
  cbv


theorem changed_extends (base : Machine) (i : Inputs) : HeapExtension.Extends (heap i) (changed base i) :=
  HeapExtension.same_objects rfl

theorem changed_global (base : Machine) (i : Inputs) :
    checkedEnvironment (changed base i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := by
  have different : localScope i ≠ globalScope i := by
    intro same
    have found := checked_global i
    rw [←same,checked_local] at found
    cases found
  rw [changed,BindingWrite.changed_checked_other _ _ _ _ _ _ _ different]
  exact checked_global i

def branchInputs (base : Machine) (i : Inputs) (mature ripe : UInt64)
    (gameMature : lookupProperty (heap i) (game i) (JSString.ofString "lumpMatureAge") =
      .ok (some (.data (.number mature) true true true)))
    (gameRipe : lookupProperty (heap i) (game i) (JSString.ofString "lumpRipeAge") =
      .ok (some (.data (.number ripe) true true true)))
    (isMature : Number.lessThan (ageValue base i) mature = false)
    (isUnripe : Number.lessThan (ageValue base i) ripe = true) : LumpHandPicked.Inputs := {
  heap := changed base i
  localScope := localScope i
  globalScope := globalScope i
  depth := i.gameDepth
  window := window i
  game := game i
  windowObject := windowObject i
  gameObject := gameObject i
  bindings := BindingWrite.changedBindings "age" (.number (ageValue base i)) i.bindings
  outer := i.outer
  age := ageValue base i
  mature := mature
  ripe := ripe
  localRead := BindingWrite.changed_checked (heap i) (localScope i) i.bindings i.outer "age"
    (.number (ageValue base i)) i.localRead
  amountDeclared := by simpa [BindingWrite.same_names] using i.amountDeclared
  ageDeclared := by simpa [BindingWrite.same_names] using age_declared i
  ageRead := BindingWrite.changed_read (heap i) (localScope i) i.bindings i.outer "age"
    (.number (ageValue base i)) i.ageBinding i.localRead i.ageFound
  gamePath := BindingWrite.changed_path (heap i) (localScope i) i.bindings i.outer "age" "Game"
    (.number (ageValue base i)) i.localRead _ _ _ i.gamePath
  depthBound := by simpa [changed,BindingWrite.changedHeap,heap] using i.gameRoom
  globalRead := changed_global base i
  windowRead := HeapExtension.checked_object (changed_extends base i) _ _ i.windowRead
  windowKind := i.windowKind
  gameRead := HeapExtension.checked_object (changed_extends base i) _ _ i.gameRead
  gameKind := i.gameKind
  windowGame := HeapExtension.lookup_property (changed_extends base i) _ _ _ i.windowGame
  gameMature := HeapExtension.lookup_property (changed_extends base i) _ _ _ gameMature
  gameRipe := HeapExtension.lookup_property (changed_extends base i) _ _ _ gameRipe
  isMature := isMature
  isUnripe := isUnripe }

def atAge (base : Machine) (i : Inputs) : Machine :=
  state {base with continuation := .statementList [LumpHandPicked.guard] none :: base.continuation} i

def guardBase (base : Machine) : Machine :=
  {base with continuation := .statementList [] none :: base.continuation}

theorem native_age_to_guard (base : Machine) (i : Inputs) (mature ripe : UInt64)
    (gameMature : lookupProperty (heap i) (game i) (JSString.ofString "lumpMatureAge") =
      .ok (some (.data (.number mature) true true true)))
    (gameRipe : lookupProperty (heap i) (game i) (JSString.ofString "lumpRipeAge") =
      .ok (some (.data (.number ripe) true true true)))
    (isMature : Number.lessThan (ageValue base i) mature = false)
    (isUnripe : Number.lessThan (ageValue base i) ripe = true) (fuel : Nat) :
    Builtins.run (26+fuel) (atAge base i) =
      Builtins.run fuel (LumpHandPicked.start (guardBase base)
        (branchInputs base i mature ripe gameMature gameRipe isMature isUnripe)) := by
  rw [show 26+fuel = 25+(1+fuel) by omega,atAge,native_age_initializer,Nat.add_comm 1 fuel]
  rfl

theorem native_age_source_suffix :
    (match LumpSyntax.clickLumpBody with | .block statements => statements.drop 3 | _ => []) =
      [ageStatement,LumpHandPicked.guard] := rfl

theorem initialized_age_read (base : Machine) (i : Inputs) :
    readBinding (Builtins.run 25 (state base i)).heap (localScope i) "age" = .ok (.number (ageValue base i)) := by
  rw [show (25 : Nat) = 25+0 from rfl,native_age_initializer]
  exact BindingWrite.changed_read (heap i) (localScope i) i.bindings i.outer "age"
    (.number (ageValue base i)) i.ageBinding i.localRead i.ageFound

theorem initializer_elapsed (base : Machine) (i : Inputs) :
    (Builtins.run 25 (state base i)).elapsed = base.elapsed := by
  rw [show (25 : Nat) = 25+0 from rfl,native_age_initializer]
  rfl

end CookieClicker.JavaScript.LumpAge

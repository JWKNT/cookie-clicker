import CookieClicker.JavaScriptWinFrame
import CookieClicker.JavaScriptIdentifierPath
/-! The intact Game.Win write prefix through a native closure environment.
The current local environment is appended to an arbitrary declarative path to
Window. All unrelated scopes, objects and caller continuations are retained. -/
namespace CookieClicker.JavaScript.WinEnvironment
open HasEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def localIndex {window : ObjectId} (scopes : Scopes window) : EnvId := scopes.environments.size

def heap {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) : Heap := {
  objects := frame.objects
  environments := scopes.environments.push
    ⟨.declarative (WinFrame.locals what arguments it name),some scopes.closureScope⟩ }

def ambient {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) : Machine := {
  base with
  heap := heap frame scopes arguments it name
  context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

theorem checked_local {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    checkedEnvironment (heap frame scopes arguments it name) (localIndex scopes) =
      .ok ⟨.declarative (WinFrame.locals what arguments it name),some scopes.closureScope⟩ := by
  simp [checkedEnvironment,heap,localIndex,Heap.environment?]

theorem checked_global {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    checkedEnvironment (heap frame scopes arguments it name) scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := by
  have read := append_old_read scopes.environments
    ⟨.declarative (WinFrame.locals what arguments it name),some scopes.closureScope⟩
    ⟨.object frame.window false,none⟩ scopes.globalScope scopes.globalRead
  simp [checkedEnvironment,heap,Heap.environment?,read]

theorem write_local {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name nextIt nextName : Value) :
    replaceEnvironment (heap frame scopes arguments it name) (localIndex scopes)
      ⟨.declarative (WinFrame.locals what arguments nextIt nextName),some scopes.closureScope⟩ =
      .ok (heap frame scopes arguments nextIt nextName) := by
  simp [replaceEnvironment,Heap.writeEnvironment,heap,localIndex,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_push]
theorem checked_game {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    checkedObject (heap frame scopes arguments it name) frame.game = .ok frame.gameObject := by
  simp [checkedObject,heap,Heap.object?,frame.gameRead]
theorem game_kind {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won) :
    frame.gameObject.kind = .ordinary := frame.gameKind

theorem checked_window {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    checkedObject (heap frame scopes arguments it name) frame.window = .ok frame.windowObject := by
  simp [checkedObject,heap,Heap.object?,frame.windowRead]
theorem window_kind {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won) :
    frame.windowObject.kind = .host "Window" 0 := frame.windowKind

theorem checked_table {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    checkedObject (heap frame scopes arguments it name) frame.table = .ok frame.tableObject := by
  simp [checkedObject,heap,Heap.object?,frame.tableRead]
theorem table_kind {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won) :
    frame.tableObject.kind = .ordinary := frame.tableKind

theorem checked_achievement {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    checkedObject (heap frame scopes arguments it name) frame.achievement = .ok frame.achievementObject := by
  simp [checkedObject,heap,Heap.object?,frame.achievementRead]
theorem achievement_kind {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won) :
    frame.achievementObject.kind = .ordinary := frame.achievementKind

theorem window_binding {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    lookupProperty (heap frame scopes arguments it name) frame.window (JSString.ofString "Game") =
      .ok (some (.data (.object frame.game) true true false)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.windowRead,frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem game_table {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    lookupProperty (heap frame scopes arguments it name) frame.game (JSString.ofString "Achievements") =
      .ok (some (.data (.object frame.table) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.gameRead,frame.gameKnown,frame.gameTable,Except.bind,Except.pure,bind,pure]

theorem selected_achievement {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    lookupProperty (heap frame scopes arguments it name) frame.table (what) =
      .ok (some (.data (.object frame.achievement) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.tableRead,frame.tableKnown,frame.selectedAchievement,Except.bind,Except.pure,bind,pure]

theorem won_value {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    lookupProperty (heap frame scopes arguments it name) frame.achievement (JSString.ofString "won") =
      .ok (some (.data (.number won) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.achievementRead,frame.achievementKnown,frame.wonValue,Except.bind,Except.pure,bind,pure]

theorem display_value {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    lookupProperty (heap frame scopes arguments it name) frame.achievement (JSString.ofString "dname") =
      .ok (some (.data (.string display) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.achievementRead,frame.achievementKnown,frame.displayValue,Except.bind,Except.pure,bind,pure]

theorem short_absent {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    lookupProperty (heap frame scopes arguments it name) frame.achievement (JSString.ofString "shortName") = .ok none :=
  HeapExtension.lookup_property (HeapExtension.same_objects (by rfl)) _ _ _ frame.shortAbsent


theorem no_game (what : JSString) (arguments it name : Value) :
    (WinFrame.locals what arguments it name).any (fun b => b.name == "Game") = false := by simp [WinFrame.locals]

theorem identifier_game {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    Environment.identifier (ambient base frame scopes arguments it name) "Game" =
      {ambient base frame scopes arguments it name with
        control := .expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  let machine := ambient base frame scopes arguments it name
  have localRead : checkedEnvironment machine.heap (localIndex scopes) =
      .ok ⟨.declarative (WinFrame.locals what arguments it name),some scopes.closureScope⟩ := checked_local frame scopes arguments it name
  have globalRead : checkedEnvironment machine.heap scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := checked_global frame scopes arguments it name
  have chain : DeclarativePath machine.heap.environments "Game" scopes.closureScope scopes.globalScope scopes.depth :=
    append_path scopes.environments _ "Game" _ _ _ scopes.chain
  have count : scopes.environments.size+1 = scopes.depth+(scopes.environments.size-scopes.depth+1) := by
    have bound := scopes.depthBound; omega
  change Environment.resolve ((heap frame scopes arguments it name).environments.size+1)
    machine (localIndex scopes) "Game" false = _
  simp only [heap,Array.size_push]
  rw [Environment.resolve,localRead]
  simp only [JavaScript.checked,no_game,Bool.false_eq_true,↓reduceIte]
  rw [count,resolve_path machine "Game" false _ _ _ _ chain]
  rw [Environment.resolve,globalRead]
  simp only [JavaScript.checked,machine,ambient,window_binding]
  rfl

theorem read_what {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    readBinding (heap frame scopes arguments it name) (localIndex scopes) "what" = .ok (.string what) := by
  simp [readBinding,checked_local,WinFrame.locals,bind,Except.bind,pure,Except.pure]
theorem identifier_what {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    Environment.identifier (ambient base frame scopes arguments it name) "what" =
      {ambient base frame scopes arguments it name with
        control := .expressionResult (.reference ⟨.environment (localIndex scopes) "what",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes arguments it name) (by simp [WinFrame.locals])

theorem read_it {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    readBinding (heap frame scopes arguments it name) (localIndex scopes) "it" = .ok (it) := by
  simp [readBinding,checked_local,WinFrame.locals,bind,Except.bind,pure,Except.pure]
theorem identifier_it {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    Environment.identifier (ambient base frame scopes arguments it name) "it" =
      {ambient base frame scopes arguments it name with
        control := .expressionResult (.reference ⟨.environment (localIndex scopes) "it",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes arguments it name) (by simp [WinFrame.locals])

theorem read_name {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    readBinding (heap frame scopes arguments it name) (localIndex scopes) "name" = .ok (name) := by
  simp [readBinding,checked_local,WinFrame.locals,bind,Except.bind,pure,Except.pure]
theorem identifier_name {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    Environment.identifier (ambient base frame scopes arguments it name) "name" =
      {ambient base frame scopes arguments it name with
        control := .expressionResult (.reference ⟨.environment (localIndex scopes) "name",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes arguments it name) (by simp [WinFrame.locals])

theorem it_reference {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    identifierReference (ambient base frame scopes arguments it name) "it" =
      .ok ⟨.environment (localIndex scopes) "it",false⟩ := by
  simp only [identifierReference,ambient,heap,Array.size_push]
  change resolveName (heap frame scopes arguments it name) false (scopes.environments.size+1+1)
    (localIndex scopes) "it" = _
  rw [resolveName,checked_local]
  simp [WinFrame.locals,bind,Except.bind,pure,Except.pure]
theorem set_it {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name next : Value) :
    setBinding (heap frame scopes arguments it name) (localIndex scopes) "it" next false =
      .ok (heap frame scopes arguments next name) := by
  have write := write_local frame scopes arguments it name next name
  unfold WinFrame.locals at write
  simp [setBinding,checked_local,WinFrame.locals,write,bind,Except.bind]

theorem name_reference {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    identifierReference (ambient base frame scopes arguments it name) "name" =
      .ok ⟨.environment (localIndex scopes) "name",false⟩ := by
  simp only [identifierReference,ambient,heap,Array.size_push]
  change resolveName (heap frame scopes arguments it name) false (scopes.environments.size+1+1)
    (localIndex scopes) "name" = _
  rw [resolveName,checked_local]
  simp [WinFrame.locals,bind,Except.bind,pure,Except.pure]
theorem set_name {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name next : Value) :
    setBinding (heap frame scopes arguments it name) (localIndex scopes) "name" next false =
      .ok (heap frame scopes arguments it next) := by
  have write := write_local frame scopes arguments it name it next
  unfold WinFrame.locals at write
  simp [setBinding,checked_local,WinFrame.locals,write,bind,Except.bind]

theorem identifier_game_explicit {what display : JSString} {won : UInt64}
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
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
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } : Machine) with control := .expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  exact identifier_game {
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } frame scopes arguments it name

theorem identifier_what_explicit {what display : JSString} {won : UInt64}
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
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
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } "what" =
      {({
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "what",false⟩)} := by
  exact identifier_what {
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } frame scopes arguments it name

theorem identifier_it_explicit {what display : JSString} {won : UInt64}
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
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
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } "it" =
      {({
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "it",false⟩)} := by
  exact identifier_it {
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } frame scopes arguments it name

theorem it_reference_explicit {what display : JSString} {won : UInt64}
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
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
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } "it" =
      .ok ⟨.environment (localIndex scopes) "it",false⟩ := by
  exact it_reference {
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } frame scopes arguments it name

theorem name_reference_explicit {what display : JSString} {won : UInt64}
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value)
    (control : Control)
    (continuation : List JavaScript.Frame)
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
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } "name" =
      .ok ⟨.environment (localIndex scopes) "name",false⟩ := by
  exact name_reference {
      heap := heap frame scopes arguments it name
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
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
    } frame scopes arguments it name

attribute [local cbv_opaque] heap lookupProperty checkedObject checkedEnvironment replaceEnvironment readBinding setBinding
attribute [local cbv_opaque] Environment.identifier identifierReference localIndex WinFrame.locals JSString.ofString
attribute [local cbv_eval] checked_local checked_global read_what read_it read_name set_it set_name
attribute [local cbv_eval] window_binding game_table selected_achievement won_value display_value short_absent
attribute [local cbv_eval] checked_game checked_window checked_table checked_achievement game_kind window_kind table_kind achievement_kind
attribute [local cbv_eval] identifier_game_explicit identifier_what_explicit identifier_it_explicit it_reference_explicit name_reference_explicit
attribute [local cbv_eval] WinFrame.string_key

def state {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments : Value) : Machine :=
  {ambient base frame scopes arguments .undefined .undefined with control := .statement WinSyntax.WinBody}

def beforeWrite {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : Scopes frame.window) (arguments : Value) : Machine := {
  state base frame scopes arguments with
  heap := heap frame scopes arguments (.object frame.achievement) (.string display)
  control := .putValue ⟨.property (.object frame.achievement) (JSString.ofString "won"),false⟩ (.number Number.one)
  continuation := WinFrame.pendingContinuation base.continuation }

theorem native_before_write_tail {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : Scopes frame.window) (arguments : Value) (fuel : Nat) :
    Builtins.run (97+fuel) (state base frame scopes arguments) =
      Builtins.run fuel (beforeWrite base frame scopes arguments) := by
  rw [Nat.add_comm 97 fuel]
  cbv
  rw [identifier_what_explicit]
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, it_reference_explicit, name_reference_explicit, checked_local, checked_global, read_what, read_it, set_it, set_name, window_binding, game_table, selected_achievement, won_value, display_value, short_absent, checked_game, checked_window, checked_table, checked_achievement, game_kind, window_kind, table_kind, achievement_kind, WinFrame.string_key]
  try cbv
  rw [identifier_it_explicit]
  cbv
  try simp only [checked_local,read_it]
  try cbv


def awardedHeap {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) : Heap := {
  heap frame scopes arguments it name with
  objects := frame.objects.set! frame.achievement (WinFrame.awardedObject frame) }

theorem replace_awarded {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (scopes : Scopes frame.window) (arguments it name : Value) :
    replaceObject (heap frame scopes arguments it name) frame.achievement (WinFrame.awardedObject frame) =
      .ok (awardedHeap frame scopes arguments it name) := by
  have bound : frame.achievement < frame.objects.size := (Array.getElem?_eq_some_iff.mp frame.achievementRead).1
  simp [replaceObject,Heap.writeObject,heap,bound,awardedHeap]

theorem native_won_assignment {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : Scopes frame.window) (arguments it name : Value) :
    writeProperty {base with heap := heap frame scopes arguments it name}
      (.object frame.achievement) (JSString.ofString "won") (.number Number.one) false =
    result {base with heap := awardedHeap frame scopes arguments it name} (.number Number.one) := by
  have replacement := replace_awarded frame scopes arguments it name
  unfold WinFrame.awardedObject WinFrame.achievementObject at replacement
  simp [writeProperty,checked,checked_achievement,achievement_kind,won_value,requireDescriptor,
    frame.wonValue,writeDataProperty,Except.bind,Except.pure,bind,pure,WinFrame.set_property_kind,replacement,result]

def afterWrite {what display : JSString} (base : Machine) (frame : WinFrame.Frame what display 0)
    (scopes : Scopes frame.window) (arguments : Value) : Machine := {
  beforeWrite base frame scopes arguments with
  heap := awardedHeap frame scopes arguments (.object frame.achievement) (.string display)
  control := .expressionResult (.value (.number Number.one)) }

theorem write_step {what display : JSString} (base : Machine) (frame : WinFrame.Frame what display 0)
    (scopes : Scopes frame.window) (arguments : Value) :
    Builtins.builtinStep (beforeWrite base frame scopes arguments) = afterWrite base frame scopes arguments := by
  change {writeProperty (beforeWrite base frame scopes arguments) (.object frame.achievement)
    (JSString.ofString "won") (.number Number.one) false with elapsed := base.elapsed} = _
  rw [show beforeWrite base frame scopes arguments =
    {beforeWrite base frame scopes arguments with heap := heap frame scopes arguments (.object frame.achievement) (.string display)} from rfl]
  rw [native_won_assignment]
  rfl

theorem native_award_write_tail {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : Scopes frame.window) (arguments : Value) (fuel : Nat) :
    Builtins.run (98+fuel) (state base frame scopes arguments) =
      Builtins.run fuel (afterWrite base frame scopes arguments) := by
  rw [show 98+fuel = 97+(1+fuel) by omega,native_before_write_tail,Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (beforeWrite base frame scopes arguments)) = _
  rw [write_step]

end CookieClicker.JavaScript.WinEnvironment

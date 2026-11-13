import CookieClicker.JavaScriptUnlockFrame
import CookieClicker.JavaScriptIdentifierPath
/-! The native Game.Unlock string branch through its closure environment. An already unlocked upgrade leaves all objects unchanged. The actual local scope and caller continuation are retained. -/
namespace CookieClicker.JavaScript.UnlockEnvironment
open HasEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def localIndex {window : ObjectId} (scopes : Scopes window) : EnvId := scopes.environments.size

def heap {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) : Heap := {
  objects := frame.objects
  environments := scopes.environments.push
    ⟨.declarative (UnlockFrame.locals what arguments),some scopes.closureScope⟩ }

def ambient {what : JSString} {unlocked : UInt64} (base : Machine)
    (frame : UnlockFrame.Frame what unlocked) (scopes : Scopes frame.window) (arguments : Value) : Machine := {
  base with
  heap := heap frame scopes arguments
  context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

theorem checked_local {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    checkedEnvironment (heap frame scopes arguments) (localIndex scopes) =
      .ok ⟨.declarative (UnlockFrame.locals what arguments),some scopes.closureScope⟩ := by
  simp [checkedEnvironment,heap,localIndex,Heap.environment?]

theorem checked_global {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    checkedEnvironment (heap frame scopes arguments) scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := by
  have read := append_old_read scopes.environments
    ⟨.declarative (UnlockFrame.locals what arguments),some scopes.closureScope⟩
    ⟨.object frame.window false,none⟩ scopes.globalScope scopes.globalRead
  simp [checkedEnvironment,heap,Heap.environment?,read]

theorem checked_game {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    checkedObject (heap frame scopes arguments) frame.game = .ok frame.gameObject := by
  simp [checkedObject,heap,Heap.object?,frame.gameRead]
theorem game_kind {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked) :
    frame.gameObject.kind = .ordinary := frame.gameKind

theorem checked_window {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    checkedObject (heap frame scopes arguments) frame.window = .ok frame.windowObject := by
  simp [checkedObject,heap,Heap.object?,frame.windowRead]
theorem window_kind {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked) :
    frame.windowObject.kind = .host "Window" 0 := frame.windowKind

theorem checked_table {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    checkedObject (heap frame scopes arguments) frame.table = .ok frame.tableObject := by
  simp [checkedObject,heap,Heap.object?,frame.tableRead]
theorem table_kind {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked) :
    frame.tableObject.kind = .ordinary := frame.tableKind

theorem checked_upgrade {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    checkedObject (heap frame scopes arguments) frame.upgrade = .ok frame.upgradeObject := by
  simp [checkedObject,heap,Heap.object?,frame.upgradeRead]
theorem upgrade_kind {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked) :
    frame.upgradeObject.kind = .ordinary := frame.upgradeKind

theorem window_binding {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    lookupProperty (heap frame scopes arguments) frame.window (JSString.ofString "Game") =
      .ok (some (.data (.object frame.game) true true false)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.windowRead,frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem game_table {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    lookupProperty (heap frame scopes arguments) frame.game (JSString.ofString "Upgrades") =
      .ok (some (.data (.object frame.table) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.gameRead,frame.gameKnown,frame.gameTable,Except.bind,Except.pure,bind,pure]

theorem selected_upgrade {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    lookupProperty (heap frame scopes arguments) frame.table (what) =
      .ok (some (.data (.object frame.upgrade) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.tableRead,frame.tableKnown,frame.selectedUpgrade,Except.bind,Except.pure,bind,pure]

theorem unlocked_value {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    lookupProperty (heap frame scopes arguments) frame.upgrade (JSString.ofString "unlocked") =
      .ok (some (.data (.number unlocked) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.upgradeRead,frame.upgradeKnown,frame.unlockedValue,Except.bind,Except.pure,bind,pure]

theorem no_game (what : JSString) (arguments : Value) :
    (UnlockFrame.locals what arguments).any (fun b => b.name == "Game") = false := by simp [UnlockFrame.locals]

theorem identifier_game {what : JSString} {unlocked : UInt64} (base : Machine)
    (frame : UnlockFrame.Frame what unlocked) (scopes : Scopes frame.window) (arguments : Value) :
    Environment.identifier (ambient base frame scopes arguments) "Game" =
      {ambient base frame scopes arguments with
        control := .expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  let machine := ambient base frame scopes arguments
  have localRead : checkedEnvironment machine.heap (localIndex scopes) =
      .ok ⟨.declarative (UnlockFrame.locals what arguments),some scopes.closureScope⟩ := checked_local frame scopes arguments
  have globalRead : checkedEnvironment machine.heap scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := checked_global frame scopes arguments
  have chain : DeclarativePath machine.heap.environments "Game" scopes.closureScope scopes.globalScope scopes.depth :=
    append_path scopes.environments _ "Game" _ _ _ scopes.chain
  have count : scopes.environments.size+1 = scopes.depth+(scopes.environments.size-scopes.depth+1) := by
    have bound := scopes.depthBound; omega
  change Environment.resolve ((heap frame scopes arguments).environments.size+1)
    machine (localIndex scopes) "Game" false = _
  simp only [heap,Array.size_push]
  rw [Environment.resolve,localRead]
  simp only [JavaScript.checked,no_game,Bool.false_eq_true,↓reduceIte]
  rw [count,resolve_path machine "Game" false _ _ _ _ chain]
  rw [Environment.resolve,globalRead]
  simp only [JavaScript.checked,machine,ambient,window_binding]
  rfl

theorem read_what {what : JSString} {unlocked : UInt64} (frame : UnlockFrame.Frame what unlocked)
    (scopes : Scopes frame.window) (arguments : Value) :
    readBinding (heap frame scopes arguments) (localIndex scopes) "what" = .ok (.string what) := by
  simp [readBinding,checked_local,UnlockFrame.locals,bind,Except.bind,pure,Except.pure]
theorem identifier_what {what : JSString} {unlocked : UInt64} (base : Machine)
    (frame : UnlockFrame.Frame what unlocked) (scopes : Scopes frame.window) (arguments : Value) :
    Environment.identifier (ambient base frame scopes arguments) "what" =
      {ambient base frame scopes arguments with
        control := .expressionResult (.reference ⟨.environment (localIndex scopes) "what",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes arguments) (by simp [UnlockFrame.locals])

theorem identifier_game_explicit {what : JSString} {unlocked : UInt64}
    (frame : UnlockFrame.Frame what unlocked) (scopes : Scopes frame.window) (arguments : Value)
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
      heap := heap frame scopes arguments
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
      heap := heap frame scopes arguments
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
      heap := heap frame scopes arguments
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
    } frame scopes arguments

theorem identifier_what_explicit {what : JSString} {unlocked : UInt64}
    (frame : UnlockFrame.Frame what unlocked) (scopes : Scopes frame.window) (arguments : Value)
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
      heap := heap frame scopes arguments
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
      heap := heap frame scopes arguments
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
      heap := heap frame scopes arguments
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
    } frame scopes arguments


attribute [local cbv_opaque] heap lookupProperty checkedObject checkedEnvironment replaceEnvironment readBinding setBinding
attribute [local cbv_opaque] Environment.identifier identifierReference localIndex UnlockFrame.locals JSString.ofString
attribute [local cbv_eval] checked_local checked_global read_what
attribute [local cbv_eval] window_binding game_table selected_upgrade unlocked_value
attribute [local cbv_eval] checked_game checked_window checked_table checked_upgrade game_kind window_kind table_kind upgrade_kind
attribute [local cbv_eval] identifier_game_explicit identifier_what_explicit

def state {what : JSString} {unlocked : UInt64} (base : Machine)
    (frame : UnlockFrame.Frame what unlocked) (scopes : Scopes frame.window) (arguments : Value) : Machine :=
  {ambient base frame scopes arguments with control := .statement BuildingCallbackSyntax.UnlockBody}

private theorem one_ne_zero : Number.equal 4607182418800017408 0=false := by decide +kernel
private theorem string_key : JSString.ofString "string" = [115,116,114,105,110,103] := rfl
attribute [local cbv_eval] string_key
attribute [local cbv_opaque] Number.equal
attribute [local cbv_eval] one_ne_zero

def completed {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : Scopes frame.window) (arguments : Value) : Machine := {
  ambient base frame scopes arguments with control := .completion (.normal none) }

theorem native_body {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : Scopes frame.window) (arguments : Value) (fuel : Nat) :
    Builtins.run (59+fuel) (state base frame scopes arguments) =
      Builtins.run fuel (completed base frame scopes arguments) := by
  rw [Nat.add_comm 59 fuel]
  cbv
  rw [identifier_what_explicit]
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv
  try simp only [identifier_game_explicit, identifier_what_explicit, checked_local, checked_global, read_what, window_binding, game_table, selected_upgrade, unlocked_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind]
  try cbv

end CookieClicker.JavaScript.UnlockEnvironment

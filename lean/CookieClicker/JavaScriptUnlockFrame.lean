import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptHeapExtension
import CookieClicker.JavaScriptBuildingCallbackSyntax

/-! Data descriptors and local variables for the native Game.Unlock string branch. Unrelated objects and fields remain arbitrary. -/
namespace CookieClicker.JavaScript.UnlockFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Frame (what : JSString) (unlocked : UInt64) where
  objects : Array JSObject
  game : ObjectId
  window : ObjectId
  table : ObjectId
  upgrade : ObjectId
  gameObject : JSObject
  windowObject : JSObject
  tableObject : JSObject
  upgradeObject : JSObject
  gameRead : objects[game]? = some gameObject
  windowRead : objects[window]? = some windowObject
  tableRead : objects[table]? = some tableObject
  upgradeRead : objects[upgrade]? = some upgradeObject
  gameKnown : gameObject.unresolvedOwnNames = []
  windowKnown : windowObject.unresolvedOwnNames = []
  tableKnown : tableObject.unresolvedOwnNames = []
  upgradeKnown : upgradeObject.unresolvedOwnNames = []
  gameKind : gameObject.kind = .ordinary
  windowKind : windowObject.kind = .host "Window" 0
  tableKind : tableObject.kind = .ordinary
  upgradeKind : upgradeObject.kind = .ordinary
  windowGame : ownProperty windowObject (JSString.ofString "Game") =
    some (.data (.object game) true true false)
  gameTable : ownProperty gameObject (JSString.ofString "Upgrades") =
    some (.data (.object table) true true true)
  selectedUpgrade : ownProperty tableObject what =
    some (.data (.object upgrade) true true true)
  unlockedValue : ownProperty upgradeObject (JSString.ofString "unlocked") =
    some (.data (.number unlocked) true true true)

def gameIndex {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : ObjectId := frame.game
def gameObject {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : JSObject := frame.gameObject
def windowIndex {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : ObjectId := frame.window
def windowObject {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : JSObject := frame.windowObject
def tableIndex {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : ObjectId := frame.table
def tableObject {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : JSObject := frame.tableObject
def upgradeIndex {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : ObjectId := frame.upgrade
def upgradeObject {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) : JSObject := frame.upgradeObject

def locals (what : JSString) (arguments : Value) : List Binding :=
  [{name := "what",value := .string what}, {name := "arguments",value := arguments}, {name := "i"}]

def heap {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) : Heap := {
  objects := frame.objects
  environments := ⟨⟨.declarative (locals what arguments),some 1⟩ ::
    ⟨.object (windowIndex frame) false,none⟩ :: extra.toList⟩ }

theorem checked_game {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments extra) (gameIndex frame) = .ok (gameObject frame) := by
  simp [checkedObject,heap,Heap.object?,gameIndex,gameObject,frame.gameRead]
theorem game_kind {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) :
    (gameObject frame).kind = .ordinary := frame.gameKind

theorem checked_window {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments extra) (windowIndex frame) = .ok (windowObject frame) := by
  simp [checkedObject,heap,Heap.object?,windowIndex,windowObject,frame.windowRead]
theorem window_kind {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) :
    (windowObject frame).kind = .host "Window" 0 := frame.windowKind

theorem checked_table {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments extra) (tableIndex frame) = .ok (tableObject frame) := by
  simp [checkedObject,heap,Heap.object?,tableIndex,tableObject,frame.tableRead]
theorem table_kind {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) :
    (tableObject frame).kind = .ordinary := frame.tableKind

theorem checked_upgrade {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments extra) (upgradeIndex frame) = .ok (upgradeObject frame) := by
  simp [checkedObject,heap,Heap.object?,upgradeIndex,upgradeObject,frame.upgradeRead]
theorem upgrade_kind {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked) :
    (upgradeObject frame).kind = .ordinary := frame.upgradeKind

theorem window_binding {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments extra) (windowIndex frame) (JSString.ofString "Game") =
      .ok (some (.data (.object (gameIndex frame)) true true false)) := by
  simp [windowIndex,gameIndex,tableIndex,upgradeIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.windowRead,frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem game_table {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments extra) (gameIndex frame) (JSString.ofString "Upgrades") =
      .ok (some (.data (.object (tableIndex frame)) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,upgradeIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.gameRead,frame.gameKnown,frame.gameTable,Except.bind,Except.pure,bind,pure]

theorem selected_upgrade {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments extra) (tableIndex frame) (what) =
      .ok (some (.data (.object (upgradeIndex frame)) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,upgradeIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.tableRead,frame.tableKnown,frame.selectedUpgrade,Except.bind,Except.pure,bind,pure]

theorem unlocked_value {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments extra) (upgradeIndex frame) (JSString.ofString "unlocked") =
      .ok (some (.data (.number unlocked) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,upgradeIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.upgradeRead,frame.upgradeKnown,frame.unlockedValue,Except.bind,Except.pure,bind,pure]

theorem heap_environments {what : JSString} {unlocked : UInt64} (frame : Frame what unlocked)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    (heap frame arguments extra).environments =
      ⟨⟨.declarative (locals what arguments),some 1⟩ ::
        ⟨.object (windowIndex frame) false,none⟩ :: extra.toList⟩ := rfl


end CookieClicker.JavaScript.UnlockFrame

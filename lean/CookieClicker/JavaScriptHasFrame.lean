import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptLumpSyntax

/-! The intact native Game.Has body in a normal ascension.
Its objects may have arbitrary heap positions and other fields. Only the own
data descriptors it reads are constrained. The local/outer environment layout
is explicit; mapping every initialized call to that layout is separate.
-/
namespace CookieClicker.JavaScript.HasFrame

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Frame (what : JSString) (bought : Value) where
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
  normalMode : ownProperty gameObject (JSString.ofString "ascensionMode") =
    some (.data (.number 0) true true true)
  selectedUpgrade : ownProperty tableObject what =
    some (.data (.object upgrade) true true true)
  boughtValue : ownProperty upgradeObject (JSString.ofString "bought") =
    some (.data bought true true true)

def gameIndex {what : JSString} {bought : Value} (frame : Frame what bought) : ObjectId := frame.game
def windowIndex {what : JSString} {bought : Value} (frame : Frame what bought) : ObjectId := frame.window
def tableIndex {what : JSString} {bought : Value} (frame : Frame what bought) : ObjectId := frame.table
def upgradeIndex {what : JSString} {bought : Value} (frame : Frame what bought) : ObjectId := frame.upgrade

def gameObject {what : JSString} {bought : Value} (frame : Frame what bought) : JSObject := frame.gameObject
def windowObject {what : JSString} {bought : Value} (frame : Frame what bought) : JSObject := frame.windowObject
def tableObject {what : JSString} {bought : Value} (frame : Frame what bought) : JSObject := frame.tableObject
def upgradeObject {what : JSString} {bought : Value} (frame : Frame what bought) : JSObject := frame.upgradeObject

def locals (what : JSString) (it : Value) : List Binding :=
  [{ name := "what", value := .string what }, { name := "it", value := it }]

def heap {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) : Heap := {
  objects := frame.objects
  environments := ⟨⟨.declarative (locals what it), some 1⟩ ::
    ⟨.object (windowIndex frame) false, none⟩ :: extra.toList⟩ }

theorem window_binding {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame it extra) (windowIndex frame) (JSString.ofString "Game") =
      .ok (some (.data (.object (gameIndex frame)) true true false)) := by
  simp [windowIndex,gameIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.windowRead,
    frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem game_table {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame it extra) (gameIndex frame) (JSString.ofString "Upgrades") =
      .ok (some (.data (.object (tableIndex frame)) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.gameRead,
    frame.gameKnown,frame.gameTable,Except.bind,Except.pure,bind,pure]

theorem normal_mode {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame it extra) (gameIndex frame) (JSString.ofString "ascensionMode") =
      .ok (some (.data (.number 0) true true true)) := by
  simp [windowIndex,gameIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.gameRead,
    frame.gameKnown,frame.normalMode,Except.bind,Except.pure,bind,pure]

theorem selected_upgrade {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame it extra) (tableIndex frame) what =
      .ok (some (.data (.object (upgradeIndex frame)) true true true)) := by
  simp [windowIndex,tableIndex,upgradeIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.tableRead,
    frame.tableKnown,frame.selectedUpgrade,Except.bind,Except.pure,bind,pure]

theorem bought_value {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame it extra) (upgradeIndex frame) (JSString.ofString "bought") =
      .ok (some (.data bought true true true)) := by
  simp [windowIndex,upgradeIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.upgradeRead,
    frame.upgradeKnown,frame.boughtValue,Except.bind,Except.pure,bind,pure]

theorem heap_environments {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    (heap frame it extra).environments =
      ⟨⟨.declarative (locals what it), some 1⟩ :: ⟨.object (windowIndex frame) false, none⟩ :: extra.toList⟩ := rfl

theorem write_locals {what : JSString} {bought : Value} (frame : Frame what bought)
    (it next : Value) (extra : Array LexicalEnvironment) :
    replaceEnvironment (heap frame it extra) 0 ⟨.declarative (locals what next),some 1⟩ =
      .ok (heap frame next extra) := by rfl

theorem write_locals_explicit {what : JSString} {bought : Value} (frame : Frame what bought)
    (it next : Value) (extra : Array LexicalEnvironment) :
    replaceEnvironment (heap frame it extra) 0
      ⟨.declarative [{ name := "what", value := .string what }, { name := "it", value := next }],some 1⟩ =
      .ok (heap frame next extra) := write_locals frame it next extra

theorem checked_game {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame it extra) (gameIndex frame) = .ok (gameObject frame) := by
  simp [checkedObject,heap,Heap.object?,gameIndex,gameObject,frame.gameRead]

theorem game_kind {what : JSString} {bought : Value} (frame : Frame what bought) :
    (gameObject frame).kind = .ordinary := frame.gameKind

theorem checked_window {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame it extra) (windowIndex frame) = .ok (windowObject frame) := by
  simp [checkedObject,heap,Heap.object?,windowIndex,windowObject,frame.windowRead]

theorem window_kind {what : JSString} {bought : Value} (frame : Frame what bought) :
    (windowObject frame).kind = .host "Window" 0 := frame.windowKind

theorem checked_table {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame it extra) (tableIndex frame) = .ok (tableObject frame) := by
  simp [checkedObject,heap,Heap.object?,tableIndex,tableObject,frame.tableRead]

theorem table_kind {what : JSString} {bought : Value} (frame : Frame what bought) :
    (tableObject frame).kind = .ordinary := frame.tableKind

theorem checked_upgrade {what : JSString} {bought : Value} (frame : Frame what bought)
    (it : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame it extra) (upgradeIndex frame) = .ok (upgradeObject frame) := by
  simp [checkedObject,heap,Heap.object?,upgradeIndex,upgradeObject,frame.upgradeRead]

theorem upgrade_kind {what : JSString} {bought : Value} (frame : Frame what bought) :
    (upgradeObject frame).kind = .ordinary := frame.upgradeKind

theorem zero_not_one : Number.equal (0 : UInt64) (4607182418800017408 : UInt64) = false := by decide +kernel

attribute [local cbv_opaque] heap lookupProperty checkedObject replaceEnvironment JSString.ofString List.length gameObject windowObject tableObject upgradeObject Number.equal
attribute [local cbv_opaque] windowIndex gameIndex tableIndex upgradeIndex
attribute [local cbv_eval] window_binding game_table normal_mode selected_upgrade bought_value heap_environments write_locals_explicit
attribute [local cbv_eval] List.length_cons List.length_nil
attribute [local cbv_eval] checked_game checked_window checked_table checked_upgrade game_kind window_kind table_kind upgrade_kind
attribute [local cbv_eval] zero_not_one

def state {what : JSString} {bought : Value} (base : Machine) (frame : Frame what bought)
    (extra : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap frame .undefined extra
  context := ⟨0,0,.object (gameIndex frame),false⟩
  globalObject := (windowIndex frame)
  objectEnvironmentExclusions := []
  control := .statement LumpSyntax.HasBody }

theorem native_has_body {what : JSString} {bought : Value} (base : Machine) (frame : Frame what bought)
    (extra : Array LexicalEnvironment) :
    let before := state base frame extra
    Builtins.run 59 before = { before with
      heap := heap frame (.object (upgradeIndex frame)) extra
      control := .completion (.return bought) } := by
  cbv

end CookieClicker.JavaScript.HasFrame

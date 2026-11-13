import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptHeapExtension
import CookieClicker.JavaScriptWinSyntax

/-! The intact Game.Win body up to its native achievement write.
Objects and unrelated fields are arbitrary. Native local variables are present;
call allocation/hoisting and initialized-state invariants are separate bridges.
Notification, ownership-count and Steam effects remain in the continuation.
-/
namespace CookieClicker.JavaScript.WinFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Frame (what display : JSString) (won : UInt64) where
  objects : Array JSObject
  game : ObjectId
  window : ObjectId
  table : ObjectId
  achievement : ObjectId
  gameObject : JSObject
  windowObject : JSObject
  tableObject : JSObject
  achievementObject : JSObject
  gameRead : objects[game]? = some gameObject
  windowRead : objects[window]? = some windowObject
  tableRead : objects[table]? = some tableObject
  achievementRead : objects[achievement]? = some achievementObject
  gameKnown : gameObject.unresolvedOwnNames = []
  windowKnown : windowObject.unresolvedOwnNames = []
  tableKnown : tableObject.unresolvedOwnNames = []
  achievementKnown : achievementObject.unresolvedOwnNames = []
  gameKind : gameObject.kind = .ordinary
  windowKind : windowObject.kind = .host "Window" 0
  tableKind : tableObject.kind = .ordinary
  achievementKind : achievementObject.kind = .ordinary
  windowGame : ownProperty windowObject (JSString.ofString "Game") =
    some (.data (.object game) true true false)
  gameTable : ownProperty gameObject (JSString.ofString "Achievements") =
    some (.data (.object table) true true true)
  selectedAchievement : ownProperty tableObject what =
    some (.data (.object achievement) true true true)
  wonValue : ownProperty achievementObject (JSString.ofString "won") =
    some (.data (.number won) true true true)
  displayValue : ownProperty achievementObject (JSString.ofString "dname") =
    some (.data (.string display) true true true)
  shortAbsent : lookupProperty {objects := objects} achievement (JSString.ofString "shortName") = .ok none

def gameIndex {what display : JSString} {won : UInt64} (frame : Frame what display won) : ObjectId := frame.game
def gameObject {what display : JSString} {won : UInt64} (frame : Frame what display won) : JSObject := frame.gameObject
def windowIndex {what display : JSString} {won : UInt64} (frame : Frame what display won) : ObjectId := frame.window
def windowObject {what display : JSString} {won : UInt64} (frame : Frame what display won) : JSObject := frame.windowObject
def tableIndex {what display : JSString} {won : UInt64} (frame : Frame what display won) : ObjectId := frame.table
def tableObject {what display : JSString} {won : UInt64} (frame : Frame what display won) : JSObject := frame.tableObject
def achievementIndex {what display : JSString} {won : UInt64} (frame : Frame what display won) : ObjectId := frame.achievement
def achievementObject {what display : JSString} {won : UInt64} (frame : Frame what display won) : JSObject := frame.achievementObject

def locals (what : JSString) (arguments it name : Value) : List Binding :=
  [{name := "what",value := .string what}, {name := "arguments",value := arguments},
   {name := "it",value := it}, {name := "name",value := name}, {name := "i"}]

def heap {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) : Heap := {
  objects := frame.objects
  environments := ⟨⟨.declarative (locals what arguments it name),some 1⟩ ::
    ⟨.object (windowIndex frame) false,none⟩ :: extra.toList⟩ }

theorem checked_game {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments it name extra) (gameIndex frame) = .ok (gameObject frame) := by
  simp [checkedObject,heap,Heap.object?,gameIndex,gameObject,frame.gameRead]
theorem game_kind {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    (gameObject frame).kind = .ordinary := frame.gameKind

theorem checked_window {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments it name extra) (windowIndex frame) = .ok (windowObject frame) := by
  simp [checkedObject,heap,Heap.object?,windowIndex,windowObject,frame.windowRead]
theorem window_kind {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    (windowObject frame).kind = .host "Window" 0 := frame.windowKind

theorem checked_table {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments it name extra) (tableIndex frame) = .ok (tableObject frame) := by
  simp [checkedObject,heap,Heap.object?,tableIndex,tableObject,frame.tableRead]
theorem table_kind {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    (tableObject frame).kind = .ordinary := frame.tableKind

theorem checked_achievement {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    checkedObject (heap frame arguments it name extra) (achievementIndex frame) = .ok (achievementObject frame) := by
  simp [checkedObject,heap,Heap.object?,achievementIndex,achievementObject,frame.achievementRead]
theorem achievement_kind {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    (achievementObject frame).kind = .ordinary := frame.achievementKind

theorem window_binding {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments it name extra) (windowIndex frame) (JSString.ofString "Game") =
      .ok (some (.data (.object (gameIndex frame)) true true false)) := by
  simp [windowIndex,gameIndex,tableIndex,achievementIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.windowRead,frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem game_table {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments it name extra) (gameIndex frame) (JSString.ofString "Achievements") =
      .ok (some (.data (.object (tableIndex frame)) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,achievementIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.gameRead,frame.gameKnown,frame.gameTable,Except.bind,Except.pure,bind,pure]

theorem selected_achievement {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments it name extra) (tableIndex frame) (what) =
      .ok (some (.data (.object (achievementIndex frame)) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,achievementIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.tableRead,frame.tableKnown,frame.selectedAchievement,Except.bind,Except.pure,bind,pure]

theorem won_value {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments it name extra) (achievementIndex frame) (JSString.ofString "won") =
      .ok (some (.data (.number won) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,achievementIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.achievementRead,frame.achievementKnown,frame.wonValue,Except.bind,Except.pure,bind,pure]

theorem display_value {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments it name extra) (achievementIndex frame) (JSString.ofString "dname") =
      .ok (some (.data (.string display) true true true)) := by
  simp [windowIndex,gameIndex,tableIndex,achievementIndex,lookupProperty,findProperty,checkedObject,
    Heap.object?,heap,frame.achievementRead,frame.achievementKnown,frame.displayValue,Except.bind,Except.pure,bind,pure]

theorem short_absent {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame arguments it name extra) (achievementIndex frame) (JSString.ofString "shortName") = .ok none :=
  HeapExtension.lookup_property (HeapExtension.same_objects (by rfl)) _ _ _ frame.shortAbsent

theorem heap_environments {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    (heap frame arguments it name extra).environments =
      ⟨⟨.declarative (locals what arguments it name),some 1⟩ ::
        ⟨.object (windowIndex frame) false,none⟩ :: extra.toList⟩ := rfl

theorem write_locals {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name nextIt nextName : Value) (extra : Array LexicalEnvironment) :
    replaceEnvironment (heap frame arguments it name extra) 0
      ⟨.declarative (locals what arguments nextIt nextName),some 1⟩ =
      .ok (heap frame arguments nextIt nextName extra) := by rfl

theorem write_locals_explicit {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name nextIt nextName : Value) (extra : Array LexicalEnvironment) :
    replaceEnvironment (heap frame arguments it name extra) 0
      ⟨.declarative [{name := "what",value := .string what}, {name := "arguments",value := arguments},
        {name := "it",value := nextIt}, {name := "name",value := nextName}, {name := "i"}],some 1⟩ =
      .ok (heap frame arguments nextIt nextName extra) := write_locals frame arguments it name nextIt nextName extra

def awardStatements : List Stmt := match WinSyntax.WinBody with
  | .block [.ifThenElse _ (.block [.ifThenElse _ (.block [_,.ifThenElse _ (.block statements) _]) _]) _] => statements
  | _ => []

def pendingEffects : List Stmt := awardStatements.drop 2

def pendingContinuation (tail : List JavaScript.Frame) : List JavaScript.Frame :=
  .expressionStatement :: .statementList pendingEffects none ::
  .statementList [] none :: .statementList [] none :: .statementList [] none :: tail

def state {what display : JSString} {won : UInt64} (base : Machine) (frame : Frame what display won)
    (arguments : Value) (extra : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap frame arguments .undefined .undefined extra
  context := ⟨0,0,.object (gameIndex frame),false⟩
  globalObject := windowIndex frame
  objectEnvironmentExclusions := []
  control := .statement WinSyntax.WinBody }

def beforeWrite {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) : Machine := {
  state base frame arguments extra with
  heap := heap frame arguments (.object (achievementIndex frame)) (.string display) extra
  control := .putValue ⟨.property (.object (achievementIndex frame)) (JSString.ofString "won"),false⟩ (.number Number.one)
  continuation := pendingContinuation base.continuation }

theorem own_won {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    ownProperty (achievementObject frame) (JSString.ofString "won") =
      some (.data (.number won) true true true) := frame.wonValue

theorem updated_find (properties : List OwnProperty) (key : JSString)
    (descriptor : PropertyDescriptor) (property : OwnProperty)
    (found : properties.find? (fun p => p.name == key) = some property) :
    (properties.map fun p => if p.name == key then {p with descriptor} else p).find?
      (fun p => p.name == key) = some {property with descriptor} := by
  induction properties with
  | nil => simp at found
  | cons first rest ih =>
    by_cases hit : first.name = key
    · simp only [List.map_cons,List.find?_cons,hit,beq_self_eq_true,↓reduceIte] at found ⊢
      cases Option.some.inj found
      simp only [hit]
    · have miss : (first.name == key) = false := beq_eq_false_iff_ne.mpr hit
      simp only [List.map_cons,List.find?_cons,miss,Bool.false_eq_true,↓reduceIte] at found ⊢
      exact ih found

theorem own_set_existing (object : JSObject) (kind : object.kind = .ordinary)
    (key : JSString) (old next : PropertyDescriptor)
    (found : ownProperty object key = some old) :
    ownProperty (setOwnProperty object key next) key = some next := by
  obtain ⟨property,h⟩ : ∃ property, object.properties.find? (fun p => p.name == key) = some property := by
    cases h : object.properties.find? (fun p => p.name == key) with
    | none => simp [ownProperty,h,kind] at found
    | some property => exact ⟨property,rfl⟩
  have any : object.properties.any (fun p => p.name == key) = true := by
    exact List.any_eq_true.mpr ⟨property,List.mem_of_find?_eq_some h,(List.find?_eq_some_iff_append.mp h).1⟩
  simp only [setOwnProperty,any,↓reduceIte,ownProperty,updated_find _ _ next property h,Option.map_some]


theorem set_property_kind (object : JSObject) (key : JSString) (value : PropertyDescriptor) :
    (setOwnProperty object key value).kind = object.kind := by
  unfold setOwnProperty
  split <;> rfl

def awardedObject {what display : JSString} {won : UInt64} (frame : Frame what display won) : JSObject :=
  setOwnProperty (achievementObject frame) (JSString.ofString "won") (.data (.number Number.one) true true true)

def awardedHeap {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) : Heap := {
  heap frame arguments it name extra with
  objects := frame.objects.set! (achievementIndex frame) (awardedObject frame) }

theorem achievement_bound {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    achievementIndex frame < frame.objects.size :=
  (Array.getElem?_eq_some_iff.mp frame.achievementRead).1

theorem replace_awarded {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    replaceObject (heap frame arguments it name extra) (achievementIndex frame) (awardedObject frame) =
      .ok (awardedHeap frame arguments it name extra) := by
  simp [replaceObject,Heap.writeObject,heap,achievement_bound,awardedHeap]


theorem awarded_object_won {what display : JSString} {won : UInt64} (frame : Frame what display won) :
    ownProperty (awardedObject frame) (JSString.ofString "won") =
      some (.data (.number Number.one) true true true) :=
  own_set_existing (achievementObject frame) (achievement_kind frame) _ _ _ (own_won frame)

theorem awarded_heap_object {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    (awardedHeap frame arguments it name extra).object? (achievementIndex frame) = some (awardedObject frame) := by
  simp [awardedHeap,Heap.object?,Array.set!,Array.getElem?_setIfInBounds,achievement_bound]

theorem awarded_heap_other {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) (id : ObjectId)
    (different : achievementIndex frame ≠ id) :
    (awardedHeap frame arguments it name extra).object? id = frame.objects[id]? := by
  simp [awardedHeap,Heap.object?,Array.set!,Array.getElem?_setIfInBounds,different]

theorem awarded_heap_environments {what display : JSString} {won : UInt64} (frame : Frame what display won)
    (arguments it name : Value) (extra : Array LexicalEnvironment) :
    (awardedHeap frame arguments it name extra).environments = (heap frame arguments it name extra).environments := rfl

theorem native_won_assignment {what display : JSString} {won : UInt64} (base : Machine)
    (frame : Frame what display won) (arguments it name : Value) (extra : Array LexicalEnvironment) :
    writeProperty {base with heap := heap frame arguments it name extra}
      (.object (achievementIndex frame)) (JSString.ofString "won") (.number Number.one) false =
    result {base with heap := awardedHeap frame arguments it name extra} (.number Number.one) := by
  have replacement := replace_awarded frame arguments it name extra
  unfold awardedObject at replacement
  simp [writeProperty,checked,checked_achievement,achievement_kind,won_value,requireDescriptor,
    own_won,writeDataProperty,Except.bind,Except.pure,bind,pure,set_property_kind,
    replacement,result]

theorem string_key : JSString.ofString "string" = [115,116,114,105,110,103] := rfl
attribute [local cbv_eval] string_key

attribute [local cbv_opaque] heap lookupProperty checkedObject replaceEnvironment JSString.ofString List.length
attribute [local cbv_opaque] gameIndex windowIndex tableIndex achievementIndex gameObject windowObject tableObject achievementObject
attribute [local cbv_eval] checked_game checked_window checked_table checked_achievement game_kind window_kind table_kind achievement_kind
attribute [local cbv_eval] window_binding game_table selected_achievement won_value display_value short_absent heap_environments write_locals_explicit
attribute [local cbv_eval] List.length_cons List.length_nil

theorem native_before_write_tail {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (97 + fuel) (state base frame arguments extra) =
      Builtins.run fuel (beforeWrite base frame arguments extra) := by
  rw [Nat.add_comm 97 fuel]
  cbv

theorem native_before_write {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    Builtins.run 97 (state base frame arguments extra) = beforeWrite base frame arguments extra :=
  native_before_write_tail base frame arguments extra 0


def afterWrite {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) : Machine := {
  beforeWrite base frame arguments extra with
  heap := awardedHeap frame arguments (.object (achievementIndex frame)) (.string display) extra
  control := .expressionResult (.value (.number Number.one)) }

theorem write_step {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    Builtins.builtinStep (beforeWrite base frame arguments extra) = afterWrite base frame arguments extra := by
  change {writeProperty (beforeWrite base frame arguments extra) (.object (achievementIndex frame))
    (JSString.ofString "won") (.number Number.one) false with elapsed := base.elapsed} = _
  rw [show beforeWrite base frame arguments extra =
    {beforeWrite base frame arguments extra with heap := heap frame arguments (.object (achievementIndex frame)) (.string display) extra} from rfl]
  rw [native_won_assignment]
  rfl

theorem native_award_write {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    Builtins.run 98 (state base frame arguments extra) = afterWrite base frame arguments extra := by
  rw [show (98 : Nat) = 97 + 1 from rfl,native_before_write_tail]
  change Builtins.builtinStep (beforeWrite base frame arguments extra) = _
  exact write_step base frame arguments extra


theorem native_award_sets_won {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) :
    ((Builtins.run 98 (state base frame arguments extra)).heap.object? (achievementIndex frame)).map
      (fun object => ownProperty object (JSString.ofString "won")) =
      some (some (.data (.number Number.one) true true true)) := by
  rw [native_award_write]
  change ((awardedHeap frame arguments (.object (achievementIndex frame)) (.string display) extra).object? _).map _ = _
  rw [awarded_heap_object]
  exact congrArg some (awarded_object_won frame)

theorem native_award_preserves_other {what display : JSString} (base : Machine) (frame : Frame what display 0)
    (arguments : Value) (extra : Array LexicalEnvironment) (id : ObjectId)
    (different : achievementIndex frame ≠ id) :
    (Builtins.run 98 (state base frame arguments extra)).heap.object? id = frame.objects[id]? := by
  rw [native_award_write]
  exact awarded_heap_other frame _ _ _ extra id different

theorem pending_effects_count : pendingEffects.length = 5 := by decide +kernel

theorem one_not_zero : Number.equal (4607182418800017408 : UInt64) (0 : UInt64) = false := by decide +kernel
attribute [local cbv_opaque] Number.equal
attribute [local cbv_eval] one_not_zero

theorem native_already_won {what display : JSString} (base : Machine) (frame : Frame what display Number.one)
    (arguments : Value) (extra : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (67 + fuel) (state base frame arguments extra) =
      Builtins.run fuel {state base frame arguments extra with
        heap := heap frame arguments (.object (achievementIndex frame)) .undefined extra
        control := .completion (.normal none)} := by
  rw [Nat.add_comm 67 fuel]
  cbv

end CookieClicker.JavaScript.WinFrame

import CookieClicker.JavaScriptCounterLens
import CookieClicker.JavaScriptBuiltins
/-! Counter-body execution through the builtin/environment driver.
The outer-environment result uses a local parameter and an outer Window object
binding for Game. Game may occur at any heap index and its counter fields may
occur in either order. Extra heap objects, global fields and environments are
preserved. The entry environment indices and global data descriptor remain
explicit; this does not prove that every initialized call has that layout.
-/
namespace CookieClicker.JavaScript.CounterEnvironment
open CounterLens
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem own_cookie_text (frame : Fields) (cookies earned : UInt64) :
    ownProperty (object frame cookies earned) (JSString.ofString "cookies") =
      some (.data (.number cookies) true true true) := own_cookie frame cookies earned

theorem own_earned_text (frame : Fields) (cookies earned : UInt64) :
    ownProperty (object frame cookies earned) (JSString.ofString "cookiesEarned") =
      some (.data (.number earned) true true true) := own_earned frame cookies earned

theorem set_cookie_text (frame : Fields) (cookies earned value : UInt64) :
    setOwnProperty (object frame cookies earned) (JSString.ofString "cookies")
      (.data (.number value) true true true) = object frame value earned := set_cookie frame cookies earned value

theorem set_earned_text (frame : Fields) (cookies earned value : UInt64) :
    setOwnProperty (object frame cookies earned) (JSString.ofString "cookiesEarned")
      (.data (.number value) true true true) = object frame cookies value := set_earned frame cookies earned value

attribute [local cbv_opaque] Number.add Number.sub Number.ofNat JSString.ofString object ownProperty setOwnProperty
attribute [local cbv_eval] own_cookie_text own_earned_text set_cookie_text set_earned_text
attribute [local cbv_eval] own_cookie own_earned set_cookie set_earned kind_object no_unresolved_fields
attribute [local cbv_opaque] slotHeap Heap.object? replaceObject List.length
attribute [local cbv_eval] slot_size slot_read slot_environments slot_write List.length_cons List.length_nil

theorem actual_builtin_earn_relocated (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (environments : Array LexicalEnvironment) :
    let before := relocatedState base CounterSyntax.earnBody frame cookies earned amount leading trailing environments
    Builtins.run 37 before = { before with
      heap := slotHeap leading (object frame (Number.add cookies amount) (Number.add earned amount)) trailing
        before.heap.environments
      control := .completion (.normal (some (.number (Number.add earned amount)))) } := by
  cbv

theorem actual_builtin_spend_relocated (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (environments : Array LexicalEnvironment) :
    let before := relocatedState base CounterSyntax.spendBody frame cookies earned amount leading trailing environments
    Builtins.run 20 before = { before with
      heap := slotHeap leading (object frame (Number.sub cookies amount) earned) trailing
        before.heap.environments
      control := .completion (.normal (some (.number (Number.sub cookies amount)))) } := by
  cbv

private def window (game : ObjectId) (extra : List OwnProperty) : JSObject := {
  kind := .host "Window" 0
  propertiesComplete := false
  properties := ⟨JSString.ofString "Game",.data (.object game) true true false⟩ :: extra }

theorem own_window (game : ObjectId) (extra : List OwnProperty) :
    ownProperty (window game extra) (JSString.ofString "Game") =
      some (.data (.object game) true true false) := by
  simp [ownProperty,window]
theorem window_kind (game : ObjectId) (extra : List OwnProperty) :
    (window game extra).kind = .host "Window" 0 := rfl
theorem window_known (game : ObjectId) (extra : List OwnProperty) :
    (window game extra).unresolvedOwnNames = [] := rfl
attribute [local cbv_opaque] window
attribute [local cbv_eval] own_window window_kind window_known

theorem slot_next (leading : List JSObject) (game global : JSObject) (trailing : List JSObject)
    (environments : Array LexicalEnvironment) :
    (slotHeap leading game (global :: trailing) environments).object? (leading.length + 1) = some global := by
  simp [slotHeap, Heap.object?]

attribute [local cbv_eval] slot_next

def outerState (base : Machine) (body : Stmt) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (globals : List OwnProperty) (environments : Array LexicalEnvironment) : Machine := {
  base with
  heap := slotHeap leading (object frame cookies earned) (window leading.length globals :: trailing)
    ⟨⟨.declarative [{ name := "howmuch", value := .number amount }],some 1⟩ ::
     ⟨.object (leading.length + 1) false,none⟩ :: environments.toList⟩
  context := ⟨0,0,.object leading.length,false⟩
  globalObject := leading.length + 1
  objectEnvironmentExclusions := []
  control := .statement body }

theorem actual_earn_outer (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (globals : List OwnProperty) (environments : Array LexicalEnvironment) :
    let before := outerState base CounterSyntax.earnBody frame cookies earned amount leading trailing globals environments
    Builtins.run 37 before = { before with
      heap := slotHeap leading (object frame (Number.add cookies amount) (Number.add earned amount))
        (window leading.length globals :: trailing) before.heap.environments
      control := .completion (.normal (some (.number (Number.add earned amount)))) } := by
  cbv
theorem actual_spend_outer (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (globals : List OwnProperty) (environments : Array LexicalEnvironment) :
    let before := outerState base CounterSyntax.spendBody frame cookies earned amount leading trailing globals environments
    Builtins.run 19 before = { before with
      heap := slotHeap leading (object frame (Number.sub cookies amount) earned)
        (window leading.length globals :: trailing) before.heap.environments
      control := .completion (.normal (some (.number (Number.sub cookies amount)))) } := by
  cbv

end CookieClicker.JavaScript.CounterEnvironment

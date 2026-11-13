import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptWinPrelude
/-! Full native Game.Win string call when the achievement is already won. It retains the mapped arguments object and the native it local write. Existing objects, elapsed time and free-draw count remain unchanged. -/
namespace CookieClicker.JavaScript.WinAlreadyWon
open WinEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local cbv_opaque] heap lookupProperty checkedObject checkedEnvironment replaceEnvironment readBinding setBinding
attribute [local cbv_opaque] Environment.identifier identifierReference localIndex WinFrame.locals JSString.ofString
attribute [local cbv_eval] checked_local checked_global read_what read_it read_name set_it set_name
attribute [local cbv_eval] window_binding game_table selected_achievement won_value display_value short_absent
attribute [local cbv_eval] checked_game checked_window checked_table checked_achievement game_kind window_kind table_kind achievement_kind
attribute [local cbv_eval] identifier_game_explicit identifier_what_explicit identifier_it_explicit it_reference_explicit name_reference_explicit
attribute [local cbv_eval] WinFrame.string_key

private theorem one_ne_zero : Number.equal 4607182418800017408 0=false := by decide +kernel
attribute [local cbv_opaque] Number.equal
attribute [local cbv_eval] one_ne_zero

def completed {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window) (arguments : Value) : Machine := {
  ambient base frame scopes arguments (.object frame.achievement) .undefined with
  control := .completion (.normal none) }

theorem native_body {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window) (arguments : Value) (fuel : Nat) :
    Builtins.run (67+fuel) (state base frame scopes arguments) =
      Builtins.run fuel (completed base frame scopes arguments) := by
  rw [Nat.add_comm 67 fuel]
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
  try rw [identifier_it_explicit]
  try cbv
  try simp only [checked_local,read_it]
  try cbv

def afterBody {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) : Machine :=
  let original := WinCall.caller base frame scopes
  let before := WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  completed before
    (WinCall.appendFrame frame (WinInvocation.argumentObject (callee := callee) original (.string what))) scopes
    (.object (WinInvocation.argumentIndex original))

def returned {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) : Machine := {
  afterBody (callee := callee) base frame scopes with
  context := base.context
  control := .expressionResult (.value .undefined)
  continuation := base.continuation }

theorem body_state {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    let original := WinCall.caller base frame scopes
    let before := WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
    state before
      (WinCall.appendFrame frame (WinInvocation.argumentObject (callee := callee) original (.string what))) scopes
      (.object (WinInvocation.argumentIndex original)) =
        {before with control := .statement WinSyntax.WinBody} := rfl

theorem actual_hoisted_body {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (fuel : Nat) (callee : Option ObjectId := none) :
    let original := WinCall.caller base frame scopes
    Builtins.run (67+fuel) (WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (afterBody (callee := callee) base frame scopes) := by
  let original := WinCall.caller base frame scopes
  let before := WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  have body := native_body before
    (WinCall.appendFrame frame (WinInvocation.argumentObject (callee := callee) original (.string what))) scopes
    (.object (WinInvocation.argumentIndex original)) fuel
  rw [body_state (callee := callee)] at body
  change Builtins.run (67+fuel) before = _
  have same : Builtins.run (67+fuel) before =
      Builtins.run (67+fuel) {before with control := .statement WinSyntax.WinBody} := by
    rw [Nat.add_comm 67 fuel]
    change Builtins.run (fuel+66) (Builtins.builtinStep before) =
      Builtins.run (fuel+66) (Builtins.builtinStep {before with control := .statement WinSyntax.WinBody})
    rw [WinInvocation.hoisted_starts_body (callee := callee)]
  rw [same,body]
  rfl

theorem actual_return {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    Builtins.builtinStep (afterBody (callee := callee) base frame scopes) =
      returned (callee := callee) base frame scopes := rfl

theorem actual_prepared {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (fuel : Nat) (callee : Option ObjectId := none) :
    let original := WinCall.caller base frame scopes
    Builtins.run (93+fuel) (WinInvocation.prepared (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (returned (callee := callee) base frame scopes) := by
  change Builtins.run (93+fuel) (WinInvocation.prepared (callee := callee) (WinCall.caller base frame scopes)
    scopes.closureScope frame.game (.string what)) = _
  rw [show 93+fuel = 25+(67+(1+fuel)) by omega,WinInvocation.actual_hoist (callee := callee),
    actual_hoisted_body (callee := callee),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (afterBody (callee := callee) base frame scopes)) = _
  rw [actual_return (callee := callee)]

theorem actual_invoke_existing {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (WinInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (93+fuel) (invoke base (.object function) (.object frame.game) [.string what] false) =
      Builtins.run fuel (returned (callee := some function) base frame scopes) := by
  rw [WinInvocation.actual_invoke _ _ _ _ _ _ _ present kind]
  have same := WinCall.caller_eq base frame scopes objects environments global exclusions
  have applied := actual_prepared (callee := some function) base frame scopes fuel
  simpa only [same] using applied


theorem actual_source_call {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (WinInvocation.closure scopes.closureScope source))
    (property : lookupProperty base.heap frame.game (JSString.ofString "Win") =
      .ok (some (.data (.object function) true true true)))
    (gameRead : SourceRead.Reads base (.identifier "Game") (.object frame.game) 3)
    (argument : Expr) (ticks : Nat)
    (argumentRead : SourceRead.Reads base argument (.string what) ticks) (fuel : Nat) :
    Builtins.run (ticks+104+fuel) {base with control:=.expression (MemberCall.expression "Win" argument)} =
      Builtins.run fuel (returned (callee:=some function) base frame scopes) := by
  have gamePresent : checkedObject base.heap frame.game=.ok frame.gameObject := by
    simp [checkedObject,Heap.object?,objects,frame.gameRead]
  rw [show ticks+104+fuel=ticks+10+(1+(93+fuel)) by omega,
    MemberCall.source_invoke base "Win" argument (.string what) frame.game function frame.gameObject ticks
      gamePresent frame.gameKind property gameRead argumentRead,Nat.add_comm 1 (93+fuel)]
  change Builtins.run (93+fuel) {invoke {base with
    control:=.invoke (.object function) (.object frame.game) [.string what] false}
    (.object function) (.object frame.game) [.string what] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object frame.game) [.string what] false}
      (.object function) (.object frame.game) [.string what] false =
      WinInvocation.prepared (callee:=some function) base scopes.closureScope frame.game (.string what) := by
    simp only [invoke,present,kind,checked,WinInvocation.actual_prepare]
    rfl
  rw [invoked]
  change Builtins.run (93+fuel) (WinInvocation.prepared (callee:=some function)
    base scopes.closureScope frame.game (.string what))=_
  have same := WinCall.caller_eq base frame scopes objects environments global exclusions
  simpa only [same] using actual_prepared (callee:=some function) base frame scopes fuel

theorem returned_objects {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (returned (callee := callee) base frame scopes).heap.objects =
      frame.objects.push (WinInvocation.argumentObject (callee := callee) (WinCall.caller base frame scopes) (.string what)) := rfl

theorem returned_old_object {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) (id : ObjectId) (bound : id<frame.objects.size) :
    (returned (callee := callee) base frame scopes).heap.objects[id]? = frame.objects[id]? := by
  rw [returned_objects (callee := callee)]
  simp only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)]

theorem returned_elapsed {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (returned (callee := callee) base frame scopes).elapsed=base.elapsed := rfl

theorem returned_draws {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (returned (callee := callee) base frame scopes).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.WinAlreadyWon

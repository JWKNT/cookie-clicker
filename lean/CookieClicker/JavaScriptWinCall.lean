import CookieClicker.JavaScriptWinInvocation
/-! Game.Win invocation through the actual mapped arguments allocation, native
hoisting and intact source body to the won write. The remaining native effects
are retained, including caller return and every pending callback. -/
namespace CookieClicker.JavaScript.WinCall
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def appendFrame {what display : JSString} {won : UInt64}
    (frame : WinFrame.Frame what display won) (added : JSObject) : WinFrame.Frame what display won := {
  frame with
  objects := frame.objects.push added
  gameRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp frame.gameRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using frame.gameRead
  windowRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp frame.windowRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using frame.windowRead
  tableRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp frame.tableRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using frame.tableRead
  achievementRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp frame.achievementRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using frame.achievementRead
  shortAbsent := HeapExtension.allocated_lookup {objects := frame.objects} added _ _ _ frame.shortAbsent }

def caller {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : HasEnvironment.Scopes frame.window) : Machine := {
  base with
  heap := ⟨frame.objects,scopes.environments⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

def afterWrite {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) : Machine :=
  let original := caller base frame scopes
  let before := WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  WinEnvironment.afterWrite before
    (appendFrame frame (WinInvocation.argumentObject (callee := callee) original (.string what))) scopes
    (.object (WinInvocation.argumentIndex original))

theorem body_state {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    let before := WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
    WinEnvironment.state before
      (appendFrame frame (WinInvocation.argumentObject (callee := callee) original (.string what))) scopes
      (.object (WinInvocation.argumentIndex original)) =
        {before with control := .statement WinSyntax.WinBody} := rfl

theorem actual_body_prefix {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run (98+fuel) (WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (afterWrite (callee := callee) base frame scopes) := by
  let original := caller base frame scopes
  let before := WinInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  have body := WinEnvironment.native_award_write_tail before
    (appendFrame frame (WinInvocation.argumentObject (callee := callee) original (.string what))) scopes
    (.object (WinInvocation.argumentIndex original)) fuel
  rw [body_state (callee := callee)] at body
  change Builtins.run (98+fuel) before = _
  have same : Builtins.run (98+fuel) before =
      Builtins.run (98+fuel) {before with control := .statement WinSyntax.WinBody} := by
    rw [Nat.add_comm 98 fuel]
    change Builtins.run (fuel+97) (Builtins.builtinStep before) =
      Builtins.run (fuel+97) (Builtins.builtinStep {before with control := .statement WinSyntax.WinBody})
    rw [WinInvocation.hoisted_starts_body (callee := callee)]
  rw [same,body]
  rfl

theorem actual_prepared_prefix {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run (123+fuel) (WinInvocation.prepared (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (afterWrite (callee := callee) base frame scopes) := by
  change Builtins.run (123+fuel) (WinInvocation.prepared (callee := callee) (caller base frame scopes)
    scopes.closureScope frame.game (.string what)) = _
  rw [show 123+fuel = 25+(98+fuel) by omega,WinInvocation.actual_hoist (callee := callee),actual_body_prefix (callee := callee)]

theorem caller_eq {what display : JSString} {won : UInt64} (base : Machine)
    (frame : WinFrame.Frame what display won) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = []) : caller base frame scopes = base := by
  unfold caller
  rw [←objects,←environments,←global,←exclusions]

theorem actual_invoke_existing_prefix {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (WinInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (123+fuel) (invoke base (.object function) (.object frame.game) [.string what] false) =
      Builtins.run fuel (afterWrite (callee := some function) base frame scopes) := by
  rw [WinInvocation.actual_invoke _ _ _ _ _ _ _ present kind]
  have same := caller_eq base frame scopes objects environments global exclusions
  have applied := actual_prepared_prefix (callee := some function) base frame scopes fuel
  simpa only [same] using applied


theorem after_write_object {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (afterWrite (callee := callee) base frame scopes).heap.object? frame.achievement =
      some (WinFrame.awardedObject frame) := by
  have bound : frame.achievement < frame.objects.size := (Array.getElem?_eq_some_iff.mp frame.achievementRead).1
  have more : frame.achievement < frame.objects.size+1 := Nat.lt_trans bound (Nat.lt_succ_self _)
  simp [afterWrite,WinEnvironment.afterWrite,WinEnvironment.awardedHeap,Heap.object?,Array.set!,
    Array.getElem?_setIfInBounds,appendFrame,WinFrame.awardedObject,WinFrame.achievementObject,
    more]

theorem after_write_won {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    ((afterWrite (callee := callee) base frame scopes).heap.object? frame.achievement).map
      (fun object => ownProperty object (JSString.ofString "won")) =
      some (some (.data (.number Number.one) true true true)) := by
  rw [after_write_object (callee := callee)]
  exact congrArg some (WinFrame.awarded_object_won frame)

theorem after_write_continuation {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (afterWrite (callee := callee) base frame scopes).continuation =
      WinFrame.pendingContinuation (.callBoundary base.context none :: base.continuation) := rfl

theorem after_write_elapsed {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (afterWrite (callee := callee) base frame scopes).elapsed = base.elapsed := rfl

end CookieClicker.JavaScript.WinCall

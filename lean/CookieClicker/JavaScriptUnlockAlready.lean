import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptUnlockInvocation
/-! Full native Game.Unlock string call when the upgrade is already unlocked. The source member lookup, argument evaluation, arguments object, local scope and caller return remain in the transition. Array recursion and the whole Cursor callback are separate obligations. -/
namespace CookieClicker.JavaScript.UnlockAlready
open UnlockEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
def appendFrame {what : JSString} {unlocked : UInt64}
    (frame : UnlockFrame.Frame what unlocked) (added : JSObject) : UnlockFrame.Frame what unlocked := {
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
  upgradeRead := by
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp frame.upgradeRead
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using frame.upgradeRead
 }

def caller {what : JSString} {unlocked : UInt64} (base : Machine)
    (frame : UnlockFrame.Frame what unlocked) (scopes : HasEnvironment.Scopes frame.window) : Machine := {
  base with
  heap := ⟨frame.objects,scopes.environments⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

theorem caller_eq {what : JSString} {unlocked : UInt64} (base : Machine)
    (frame : UnlockFrame.Frame what unlocked) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = []) : caller base frame scopes = base := by
  unfold caller
  rw [←objects,←environments,←global,←exclusions]

def afterBody {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) : Machine :=
  let original := caller base frame scopes
  let before := UnlockInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  UnlockEnvironment.completed before
    (appendFrame frame (UnlockInvocation.argumentObject (callee := callee) original (.string what))) scopes
    (.object (UnlockInvocation.argumentIndex original))

def returned {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) : Machine := {
  afterBody (callee := callee) base frame scopes with
  context := base.context
  control := .expressionResult (.value .undefined)
  continuation := base.continuation }

theorem body_state {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    let before := UnlockInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
    state before
      (appendFrame frame (UnlockInvocation.argumentObject (callee := callee) original (.string what))) scopes
      (.object (UnlockInvocation.argumentIndex original)) =
        {before with control := .statement BuildingCallbackSyntax.UnlockBody} := rfl

theorem actual_hoisted_body {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run (59+fuel) (UnlockInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (afterBody (callee := callee) base frame scopes) := by
  let original := caller base frame scopes
  let before := UnlockInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  have body := UnlockEnvironment.native_body before
    (appendFrame frame (UnlockInvocation.argumentObject (callee := callee) original (.string what))) scopes
    (.object (UnlockInvocation.argumentIndex original)) fuel
  rw [body_state (callee := callee)] at body
  change Builtins.run (59+fuel) before = _
  have same : Builtins.run (59+fuel) before =
      Builtins.run (59+fuel) {before with control := .statement BuildingCallbackSyntax.UnlockBody} := by
    rw [Nat.add_comm 59 fuel]
    change Builtins.run (fuel+58) (Builtins.builtinStep before) =
      Builtins.run (fuel+58) (Builtins.builtinStep {before with control := .statement BuildingCallbackSyntax.UnlockBody})
    rw [UnlockInvocation.hoisted_starts_body (callee := callee)]
  rw [same,body]
  rfl

theorem actual_return {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    Builtins.builtinStep (afterBody (callee := callee) base frame scopes) =
      returned (callee := callee) base frame scopes := rfl

theorem actual_prepared {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run (76+fuel) (UnlockInvocation.prepared (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (returned (callee := callee) base frame scopes) := by
  change Builtins.run (76+fuel) (UnlockInvocation.prepared (callee := callee) (caller base frame scopes)
    scopes.closureScope frame.game (.string what)) = _
  rw [show 76+fuel = 16+(59+(1+fuel)) by omega,UnlockInvocation.actual_hoist (callee := callee),
    actual_hoisted_body (callee := callee),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (afterBody (callee := callee) base frame scopes)) = _
  rw [actual_return (callee := callee)]

theorem actual_invoke_existing {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (UnlockInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (76+fuel) (invoke base (.object function) (.object frame.game) [.string what] false) =
      Builtins.run fuel (returned (callee := some function) base frame scopes) := by
  rw [UnlockInvocation.actual_invoke _ _ _ _ _ _ _ present kind]
  have same := caller_eq base frame scopes objects environments global exclusions
  have applied := actual_prepared (callee := some function) base frame scopes fuel
  simpa only [same] using applied


theorem actual_source_call {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (UnlockInvocation.closure scopes.closureScope source))
    (property : lookupProperty base.heap frame.game (JSString.ofString "Unlock") =
      .ok (some (.data (.object function) true true true)))
    (gameRead : SourceRead.Reads base (.identifier "Game") (.object frame.game) 3)
    (argument : Expr) (ticks : Nat)
    (argumentRead : SourceRead.Reads base argument (.string what) ticks) (fuel : Nat) :
    Builtins.run (ticks+87+fuel) {base with control:=.expression (MemberCall.expression "Unlock" argument)} =
      Builtins.run fuel (returned (callee:=some function) base frame scopes) := by
  have gamePresent : checkedObject base.heap frame.game=.ok frame.gameObject := by
    simp [checkedObject,Heap.object?,objects,frame.gameRead]
  rw [show ticks+87+fuel=ticks+10+(1+(76+fuel)) by omega,
    MemberCall.source_invoke base "Unlock" argument (.string what) frame.game function frame.gameObject ticks
      gamePresent frame.gameKind property gameRead argumentRead,Nat.add_comm 1 (76+fuel)]
  change Builtins.run (76+fuel) {invoke {base with
    control:=.invoke (.object function) (.object frame.game) [.string what] false}
    (.object function) (.object frame.game) [.string what] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object frame.game) [.string what] false}
      (.object function) (.object frame.game) [.string what] false =
      UnlockInvocation.prepared (callee:=some function) base scopes.closureScope frame.game (.string what) := by
    simp only [invoke,present,kind,checked,UnlockInvocation.actual_prepare]
    rfl
  rw [invoked]
  change Builtins.run (76+fuel) (UnlockInvocation.prepared (callee:=some function)
    base scopes.closureScope frame.game (.string what))=_
  have same := caller_eq base frame scopes objects environments global exclusions
  simpa only [same] using actual_prepared (callee:=some function) base frame scopes fuel

theorem returned_objects {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (returned (callee := callee) base frame scopes).heap.objects =
      frame.objects.push (UnlockInvocation.argumentObject (callee := callee) (caller base frame scopes) (.string what)) := rfl

theorem returned_old_object {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) (id : ObjectId) (bound : id<frame.objects.size) :
    (returned (callee := callee) base frame scopes).heap.objects[id]? = frame.objects[id]? := by
  rw [returned_objects (callee := callee)]
  simp only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)]

theorem returned_elapsed {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (returned (callee := callee) base frame scopes).elapsed=base.elapsed := rfl

theorem returned_draws {what : JSString} (base : Machine)
    (frame : UnlockFrame.Frame what Number.one) (scopes : HasEnvironment.Scopes frame.window)
    (callee : Option ObjectId := none) :
    (returned (callee := callee) base frame scopes).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.UnlockAlready

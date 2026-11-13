import CookieClicker.JavaScriptHasEnvironment
import CookieClicker.JavaScriptHasInvocation

/-! Native Game.Has invocation, including arguments allocation, declaration
hoisting, the complete source body, and caller return. This extends the object
frame and follows the original declarative closure path. The final theorem
applies directly to any existing machine satisfying the explicit frame.
Initialized source closure correspondence remains a separate obligation. -/

namespace CookieClicker.JavaScript.HasCall
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Re-express the old Has object frame after the native arguments allocation. -/
def appendFrame {what : JSString} {bought : Value}
    (frame : HasFrame.Frame what bought) (added : JSObject) : HasFrame.Frame what bought := {
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
    simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using frame.upgradeRead }

def caller {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) : Machine := {
  base with
  heap := ⟨frame.objects,scopes.environments⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

def locals (base : Machine) : HasEnvironment.Locals := {
  between := [{name := "arguments",value := .object (HasInvocation.argumentIndex base)}]
  clean := by simp }

def afterBody {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (callee : Option ObjectId := none) : Machine :=
  let original := caller base frame scopes
  { HasInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what) with
    heap := HasInvocation.allocatedHeap (callee := callee) original scopes.closureScope (.string what)
      (HasInvocation.locals original (.string what) ++ [{name := "it",value := .object frame.upgrade}])
    control := .completion (.return bought) }

theorem body_state {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    let before := HasInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
    HasEnvironment.state before (appendFrame frame (HasInvocation.argumentObject (callee := callee) original (.string what)))
      scopes (locals original) = {before with control := .statement LumpSyntax.HasBody} := by
  rfl

theorem actual_body {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run 59 (HasInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)) =
      afterBody (callee := callee) base frame scopes := by
  let original := caller base frame scopes
  let before := HasInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  have body := HasEnvironment.native_has_body before
    (appendFrame frame (HasInvocation.argumentObject (callee := callee) original (.string what))) scopes (locals original)
  rw [body_state (callee := callee)] at body
  change Builtins.run 59 before = _
  have same : Builtins.run 59 before = Builtins.run 59 {before with control := .statement LumpSyntax.HasBody} := by
    change Builtins.run 58 (Builtins.builtinStep before) =
      Builtins.run 58 (Builtins.builtinStep {before with control := .statement LumpSyntax.HasBody})
    rw [HasInvocation.hoisted_starts_body (callee := callee)]
  rw [same,body]
  rfl

attribute [local cbv_opaque] HasInvocation.allocatedHeap defineBinding HasInvocation.locals HasInvocation.localIndex HasInvocation.argumentIndex
attribute [local cbv_eval] HasInvocation.hoist_it

theorem actual_hoist_prefix (base : Machine) (scope game : ObjectId) (what : Value) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (7+fuel) (HasInvocation.prepared (callee := callee) base scope game what) =
      Builtins.run fuel (HasInvocation.hoisted (callee := callee) base scope game what) := by
  rw [Nat.add_comm 7 fuel]
  cbv


theorem actual_body_prefix {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run (59+fuel) (HasInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (afterBody (callee := callee) base frame scopes) := by
  let original := caller base frame scopes
  let before := HasInvocation.hoisted (callee := callee) original scopes.closureScope frame.game (.string what)
  have body := HasEnvironment.native_has_body_prefix before
    (appendFrame frame (HasInvocation.argumentObject (callee := callee) original (.string what))) scopes (locals original) fuel
  rw [body_state (callee := callee)] at body
  change Builtins.run (59+fuel) before = _
  have same : Builtins.run (59+fuel) before =
      Builtins.run (59+fuel) {before with control := .statement LumpSyntax.HasBody} := by
    rw [Nat.add_comm 59 fuel]
    change Builtins.run (fuel+58) (Builtins.builtinStep before) =
      Builtins.run (fuel+58) (Builtins.builtinStep {before with control := .statement LumpSyntax.HasBody})
    rw [HasInvocation.hoisted_starts_body (callee := callee)]
  rw [same,body]
  rfl

def returned {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (callee : Option ObjectId := none) : Machine := {
  caller base frame scopes with
  heap := (afterBody (callee := callee) base frame scopes).heap
  control := .expressionResult (.value bought) }

theorem actual_return {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (callee : Option ObjectId := none) :
    Builtins.run 1 (afterBody (callee := callee) base frame scopes) = returned (callee := callee) base frame scopes := by
  change Builtins.builtinStep (afterBody (callee := callee) base frame scopes) = _
  exact HasInvocation.actual_return (afterBody (callee := callee) base frame scopes)
    (caller base frame scopes).context (caller base frame scopes).continuation bought

theorem actual_prepared {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run 67 (HasInvocation.prepared (callee := callee) original scopes.closureScope frame.game (.string what)) =
      returned (callee := callee) base frame scopes := by
  change Builtins.run (7+(59+1)) _ = _
  rw [actual_hoist_prefix (callee := callee),actual_body_prefix (callee := callee),actual_return (callee := callee)]

theorem actual_invoke {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject (caller base frame scopes).heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source)) :
    Builtins.run 67 (invoke (caller base frame scopes) (.object function) (.object frame.game) [.string what] false) =
      returned (callee := some function) base frame scopes := by
  rw [HasInvocation.actual_invoke _ _ _ _ _ _ _ present kind]
  exact actual_prepared (callee := some function) base frame scopes


theorem caller_eq {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = []) :
    caller base frame scopes = base := by
  unfold caller
  rw [←objects,←environments,←global,←exclusions]

theorem actual_invoke_existing {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source)) :
    Builtins.run 67 (invoke base (.object function) (.object frame.game) [.string what] false) =
      { base with
        heap := HasInvocation.allocatedHeap (callee := some function) base scopes.closureScope (.string what)
          (HasInvocation.locals base (.string what) ++ [{name := "it",value := .object frame.upgrade}])
        control := .expressionResult (.value bought) } := by
  have same := caller_eq base frame scopes objects environments global exclusions
  have applied := actual_invoke base frame scopes function source object (by simpa [same] using present) kind
  simpa only [same,returned,afterBody,HasInvocation.hoisted,HasInvocation.prepared] using applied


theorem actual_return_prefix {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (1+fuel) (afterBody (callee := callee) base frame scopes) = Builtins.run fuel (returned (callee := callee) base frame scopes) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (afterBody (callee := callee) base frame scopes)) = _
  exact congrArg (Builtins.run fuel) (HasInvocation.actual_return (afterBody (callee := callee) base frame scopes)
    (caller base frame scopes).context (caller base frame scopes).continuation bought)

theorem actual_prepared_prefix {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window) (fuel : Nat) (callee : Option ObjectId := none) :
    let original := caller base frame scopes
    Builtins.run (67+fuel) (HasInvocation.prepared (callee := callee) original scopes.closureScope frame.game (.string what)) =
      Builtins.run fuel (returned (callee := callee) base frame scopes) := by
  change Builtins.run (67+fuel) (HasInvocation.prepared (callee := callee) (caller base frame scopes)
    scopes.closureScope frame.game (.string what)) = _
  rw [show 67+fuel = 7+(59+(1+fuel)) by omega]
  rw [actual_hoist_prefix (callee := callee),actual_body_prefix (callee := callee),actual_return_prefix (callee := callee)]

theorem actual_invoke_existing_prefix {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (67+fuel) (invoke base (.object function) (.object frame.game) [.string what] false) =
      Builtins.run fuel { base with
        heap := HasInvocation.allocatedHeap (callee := some function) base scopes.closureScope (.string what)
          (HasInvocation.locals base (.string what) ++ [{name := "it",value := .object frame.upgrade}])
        control := .expressionResult (.value bought) } := by
  rw [HasInvocation.actual_invoke _ _ _ _ _ _ _ present kind]
  have same := caller_eq base frame scopes objects environments global exclusions
  have applied := actual_prepared_prefix (callee := some function) base frame scopes fuel
  simpa only [same,returned,afterBody,HasInvocation.hoisted,HasInvocation.prepared] using applied


end CookieClicker.JavaScript.HasCall

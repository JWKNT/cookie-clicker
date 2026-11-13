import CookieClicker.JavaScriptHasCall

/-! Actual native Has calls compose with the caller conditional.
A zero ownership result skips the source branch, retaining the allocated
arguments/local scope and restoring the original caller context. The extra
value-boundary case is the native right operand of &&. -/

namespace CookieClicker.JavaScript.HasGuard
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def guarded (base : Machine) (consequent : Stmt) (logicalRight : Bool) : Machine := {
  base with continuation :=
    (if logicalRight then [.valueBoundary] else []) ++ .ifTest consequent none :: base.continuation }

def skipped (base : Machine) (scope upgrade : ObjectId) (what : JSString) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := HasInvocation.allocatedHeap (callee := callee) base scope (.string what)
    (HasInvocation.locals base (.string what) ++ [{name := "it",value := .object upgrade}])
  control := .completion (.normal none) }

theorem zero_guard_prefix (base : Machine) (consequent : Stmt) (logicalRight : Bool)
    (fuel : Nat) :
    Builtins.run ((if logicalRight then 2 else 1)+fuel)
      {guarded base consequent logicalRight with control := .expressionResult (.value (.number Number.positiveZero))} =
      Builtins.run fuel {base with control := .completion (.normal none)} := by
  cases logicalRight <;> simp only [Bool.false_eq_true,↓reduceIte]
  · rw [Nat.add_comm 1 fuel]; cbv
  · rw [Nat.add_comm 2 fuel]; cbv

theorem actual_has_zero_guard {what : JSString} (base : Machine)
    (frame : HasFrame.Frame what (.number Number.positiveZero))
    (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source))
    (consequent : Stmt) (logicalRight : Bool) (fuel : Nat) :
    Builtins.run ((if logicalRight then 69 else 68)+fuel)
      (invoke (guarded base consequent logicalRight) (.object function) (.object frame.game) [.string what] false) =
      Builtins.run fuel (skipped (callee := some function) base scopes.closureScope frame.upgrade what) := by
  have count : (if logicalRight then 69 else 68)+fuel =
      67+((if logicalRight then 2 else 1)+fuel) := by cases logicalRight <;> simp <;> omega
  rw [count,HasCall.actual_invoke_existing_prefix (guarded base consequent logicalRight) frame scopes
    objects environments global exclusions function source object present kind]
  have result := zero_guard_prefix
    {base with
      heap := HasInvocation.allocatedHeap (callee := some function) base scopes.closureScope (.string what)
        (HasInvocation.locals base (.string what) ++ [{name := "it",value := .object frame.upgrade}])}
    consequent logicalRight fuel
  simpa only [guarded,skipped,HasInvocation.allocatedHeap,HasInvocation.locals,
    HasInvocation.argumentObject,HasInvocation.argumentIndex,HasInvocation.localIndex,
    argumentsCalleeProperties,argumentsCalleeUnknown] using result

end CookieClicker.JavaScript.HasGuard

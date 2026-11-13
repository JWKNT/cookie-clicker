import CookieClicker.JavaScriptGrandmaComplete
import CookieClicker.JavaScriptCommonCpsComplete

namespace CookieClicker.JavaScript.GrandmaCall
open GrandmaGuards GrandmaComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def state (base : Machine) (me function : ObjectId) : LocalState := {
  objects:=base.heap.objects.push (GrandmaSource.argumentObject (callee:=some function) base (.object me))
  values:={me:=.object me,arguments:=.object (GrandmaSource.argumentIndex base)}
  suffix:=#[] }

def bodyBase (base : Machine) (scope receiver me function : ObjectId) : Machine :=
  GrandmaSource.hoisted (callee:=some function) base scope receiver (.object me)

theorem body_state (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    (state base me function).machine world=
      {bodyBase base scope receiver me function with control:=.statement ProductionSyntax.GrandmaCpsBody} := by
  simp [LocalState.machine,bodyBase,state,GrandmaSource.hoisted,GrandmaSource.prepared,
    GrandmaSource.allocatedHeap,GrandmaSource.locals,GrandmaSource.localIndex,
    GrandmaLocals.start,GrandmaLocals.heap,GrandmaLocals.bindings,GrandmaLocals.slotIndex,
    environments,closure,global,exclusions]

def returned (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function)) : Machine := {
  base with
  heap:=(input.after.machine world).heap
  control:=.expressionResult (.value (.number Number.one)) }

/-- Actual invocation through the44-step declaration scan, all18 source
statements and caller return, retaining every nested source allocation. -/
theorem prepared_returns (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) (fuel : Nat) :
    Builtins.run (input.ticks+45+fuel)
      (GrandmaSource.prepared (callee:=some function) base scope receiver (.object me))=
      Builtins.run fuel (returned base scope receiver me function world input) := by
  rw [show input.ticks+45+fuel=44+(input.ticks+(1+fuel)) by omega,
    GrandmaSource.actual_hoist_prefix (callee:=some function) base scope receiver (.object me)]
  have entry : Builtins.run (input.ticks+(1+fuel)) (bodyBase base scope receiver me function)=
      Builtins.run (input.ticks+(1+fuel)) ((state base me function).machine world) := by
    rw [body_state base scope receiver me function world environments closure global exclusions]
    rw [show input.ticks+(1+fuel)=(input.ticks+fuel)+1 by omega]
    change Builtins.run (input.ticks+fuel)
      (Builtins.builtinStep (GrandmaSource.hoisted (callee:=some function) base scope receiver (.object me)))=_
    rw [GrandmaSource.hoisted_starts_body (callee:=some function)]
    rfl
  refine entry.trans ?_
  refine (input.native_body (1+fuel)).trans ?_
  have caller:=TieredCall.return_to_caller base (input.after.machine world) (.number Number.one) fuel
  refine caller.trans ?_
  congr 1
  simp only [returned,LocalState.machine,GrandmaLocals.start,bodyBase,GrandmaSource.hoisted,
    GrandmaSource.prepared,global,exclusions]

theorem native_invoke (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function)) (source : Option JSString) (object : JSObject)
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (GrandmaSource.closure scope source)) (fuel : Nat) :
    Builtins.run (input.ticks+45+fuel) (invoke base (.object function) (.object receiver) [.object me] false)=
      Builtins.run fuel (returned base scope receiver me function world input) := by
  simp only [invoke,present,kind,checked,GrandmaSource.actual_prepare]
  exact prepared_returns base scope receiver me function world input environments closure global exclusions fuel

theorem returned_extends (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function)) :
    HeapExtension.Extends base.heap (returned base scope receiver me function world input).heap := by
  have allocated : HeapExtension.Extends
      (base.heap.allocateObject (GrandmaSource.argumentObject (callee:=some function) base (.object me))).2
      (bodyBase base scope receiver me function).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans
    (HeapExtension.trans (HeapExtension.append_object base.heap
      (GrandmaSource.argumentObject (callee:=some function) base (.object me))) allocated) input.after_extends

/-- The original CalculateGains me.cps(me) expression executes the complete
Grandma source callback and returns native1 to its original caller. -/
theorem source_call (base : Machine) (scope me function : ObjectId)
    (world : World (bodyBase base scope me me function))
    (input : Inputs world (state base me function)) (source : Option JSString)
    (object functionObject : JSObject)
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (present : checkedObject base.heap me=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap me (JSString.ofString "cps")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (GrandmaSource.closure scope source))
    (read : SourceRead.Reads base (.identifier "me") (.object me) 3) (fuel : Nat) :
    Builtins.run (input.ticks+59+fuel) {base with control:=.expression CommonCpsCall.expression}=
      Builtins.run fuel (returned base scope me me function world input) := by
  rw [show input.ticks+59+fuel=13+(1+(input.ticks+45+fuel)) by omega,
    CommonCpsCall.source_invoke base me function object present kind property read,
    Nat.add_comm 1 (input.ticks+45+fuel)]
  change Builtins.run (input.ticks+45+fuel) {invoke {base with
    control:=.invoke (.object function) (.object me) [.object me] false}
    (.object function) (.object me) [.object me] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object me) [.object me] false}
      (.object function) (.object me) [.object me] false=
      GrandmaSource.prepared (callee:=some function) base scope me (.object me) := by
    simp only [invoke,functionPresent,functionKind,checked,GrandmaSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope me me function world input environments closure global exclusions fuel

end CookieClicker.JavaScript.GrandmaCall

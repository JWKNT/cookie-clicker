import CookieClicker.JavaScriptHeavenlyComplete
import CookieClicker.JavaScriptCommonCpsComplete
import CookieClicker.JavaScriptMemberCallEmpty

namespace CookieClicker.JavaScript.HeavenlyCall
open HeavenlyGuards HeavenlyComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def state (base : Machine) (function : ObjectId) : LocalState := {
  objects:=base.heap.objects.push (HeavenlySource.argumentObject (callee:=some function) base )
  values:={arguments:=.object (HeavenlySource.argumentIndex base)}
  suffix:=#[] }

def bodyBase (base : Machine) (scope receiver function : ObjectId) : Machine :=
  HeavenlySource.hoisted (callee:=some function) base scope receiver

theorem body_state (base : Machine) (scope receiver function : ObjectId)
    (world : World (bodyBase base scope receiver function))
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    (state base function).machine world=
      {bodyBase base scope receiver function with control:=.statement GainHelpersSyntax.GetHeavenlyMultiplierBody} := by
  simp [LocalState.machine,bodyBase,state,HeavenlySource.hoisted,HeavenlySource.prepared,
    HeavenlySource.allocatedHeap,HeavenlySource.locals,HeavenlySource.localIndex,
    HeavenlyLocals.start,HeavenlyLocals.heap,HeavenlyLocals.bindings,HeavenlyLocals.slotIndex,
    environments,closure,global,exclusions]

def returned (base : Machine) (scope receiver function : ObjectId)
    (world : World (bodyBase base scope receiver function))
    (input : Inputs world (state base function)) : Machine := {
  base with
  heap:=(input.after.machine world).heap
  control:=.expressionResult (.value (.number 0)) }

/-- Actual invocation through the32-step declaration scan, all12 source
statements and caller return, retaining every nested source allocation. -/
theorem prepared_returns (base : Machine) (scope receiver function : ObjectId)
    (world : World (bodyBase base scope receiver function))
    (input : Inputs world (state base function))
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) (fuel : Nat) :
    Builtins.run (input.ticks+33+fuel)
      (HeavenlySource.prepared (callee:=some function) base scope receiver )=
      Builtins.run fuel (returned base scope receiver function world input) := by
  rw [show input.ticks+33+fuel=32+(input.ticks+(1+fuel)) by omega,
    HeavenlySource.actual_hoist_prefix (callee:=some function) base scope receiver ]
  have entry : Builtins.run (input.ticks+(1+fuel)) (bodyBase base scope receiver function)=
      Builtins.run (input.ticks+(1+fuel)) ((state base function).machine world) := by
    rw [body_state base scope receiver function world environments closure global exclusions]
    rw [show input.ticks+(1+fuel)=(input.ticks+fuel)+1 by omega]
    change Builtins.run (input.ticks+fuel)
      (Builtins.builtinStep (HeavenlySource.hoisted (callee:=some function) base scope receiver ))=_
    rw [HeavenlySource.hoisted_starts_body (callee:=some function)]
    rfl
  refine entry.trans ?_
  refine (input.native_body (1+fuel)).trans ?_
  have caller:=TieredCall.return_to_caller base (input.after.machine world) (.number 0) fuel
  refine caller.trans ?_
  congr 1
  simp only [returned,LocalState.machine,HeavenlyLocals.start,bodyBase,HeavenlySource.hoisted,
    HeavenlySource.prepared,global,exclusions]

theorem native_invoke (base : Machine) (scope receiver function : ObjectId)
    (world : World (bodyBase base scope receiver function))
    (input : Inputs world (state base function)) (source : Option JSString) (object : JSObject)
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (HeavenlySource.closure scope source)) (fuel : Nat) :
    Builtins.run (input.ticks+33+fuel) (invoke base (.object function) (.object receiver) [] false)=
      Builtins.run fuel (returned base scope receiver function world input) := by
  simp only [invoke,present,kind,checked,HeavenlySource.actual_prepare]
  exact prepared_returns base scope receiver function world input environments closure global exclusions fuel

theorem returned_extends (base : Machine) (scope receiver function : ObjectId)
    (world : World (bodyBase base scope receiver function))
    (input : Inputs world (state base function)) :
    HeapExtension.Extends base.heap (returned base scope receiver function world input).heap := by
  have allocated : HeapExtension.Extends
      (base.heap.allocateObject (HeavenlySource.argumentObject (callee:=some function) base)).2
      (bodyBase base scope receiver function).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans
    (HeapExtension.trans (HeapExtension.append_object base.heap
      (HeavenlySource.argumentObject (callee:=some function) base)) allocated) input.after_extends

/-- The original Game.GetHeavenlyMultiplier() expression executes every
source statement and returns native zero to its original caller. -/
theorem source_call (base : Machine) (scope game function : ObjectId)
    (world : World (bodyBase base scope game function))
    (input : Inputs world (state base function)) (source : Option JSString)
    (object functionObject : JSObject)
    (environments : world.scopes.environments=base.heap.environments)
    (closure : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "GetHeavenlyMultiplier")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (HeavenlySource.closure scope source))
    (read : SourceRead.Reads base (.identifier "Game") (.object game) 3) (fuel : Nat) :
    Builtins.run (input.ticks+43+fuel)
      {base with control:=.expression (MemberCallEmpty.expression "GetHeavenlyMultiplier")}=
      Builtins.run fuel (returned base scope game function world input) := by
  rw [show input.ticks+43+fuel=9+(1+(input.ticks+33+fuel)) by omega,
    MemberCallEmpty.source_invoke base "GetHeavenlyMultiplier" game function object present kind property read,
    Nat.add_comm 1 (input.ticks+33+fuel)]
  change Builtins.run (input.ticks+33+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [] false}
    (.object function) (.object game) [] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [] false}
      (.object function) (.object game) [] false=
      HeavenlySource.prepared (callee:=some function) base scope game := by
    simp only [invoke,functionPresent,functionKind,checked,HeavenlySource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope game function world input environments closure global exclusions fuel

end CookieClicker.JavaScript.HeavenlyCall

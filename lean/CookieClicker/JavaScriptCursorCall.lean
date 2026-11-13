import CookieClicker.JavaScriptCursorComplete

/-! Actual CalculateGains `me.cps(me)` invocation of the Cursor closure.
The source argument object, declaration scan, full body and caller return
are included; all nested heap allocations are retained. -/
namespace CookieClicker.JavaScript.CursorCall
open CursorGuards CursorComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def state (base : Machine) (me function : ObjectId) : LocalState := {
  objects:=base.heap.objects.push (CursorSource.argumentObject (callee:=some function) base (.object me))
  values:={me:=.object me,arguments:=.object (CursorSource.argumentIndex base)}
  suffix:=#[] }

def bodyBase (base : Machine) (scope receiver me function : ObjectId) : Machine :=
  CursorSource.hoisted (callee:=some function) base scope receiver (.object me)

theorem body_state (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closureScope : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    (state base me function).machine world=
      {bodyBase base scope receiver me function with control:=.statement ProductionSyntax.CursorCpsBody} := by
  simp [LocalState.machine,bodyBase,state,CursorSource.hoisted,CursorSource.prepared,
    CursorSource.allocatedHeap,CursorSource.locals,CursorSource.localIndex,
    CursorLocals.start,CursorLocals.heap,CursorLocals.bindings,CursorLocals.slotIndex,
    environments,closureScope,global,exclusions]

def returned (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function)) : Machine := {
  base with
  heap:=(input.after.machine world).heap
  control:=.expressionResult (.value (.number CursorComputeCall.baseCps)) }

theorem prepared_returns (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closureScope : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (fuel : Nat) :
    Builtins.run (input.work+45+fuel)
      (CursorSource.prepared (callee:=some function) base scope receiver (.object me))=
      Builtins.run fuel (returned base scope receiver me function world input) := by
  rw [show input.work+45+fuel=44+(input.work+(1+fuel)) by omega,
    CursorSource.actual_hoist_prefix (callee:=some function) base scope receiver (.object me)]
  have entry : Builtins.run (input.work+(1+fuel)) (bodyBase base scope receiver me function)=
      Builtins.run (input.work+(1+fuel)) ((state base me function).machine world) := by
    rw [body_state base scope receiver me function world environments closureScope global exclusions]
    have positive : 0<input.work := by simp only [Inputs.work]; omega
    rw [show input.work+(1+fuel)=(input.work+fuel)+1 by omega]
    change Builtins.run (input.work+fuel)
      (Builtins.builtinStep (CursorSource.hoisted (callee:=some function) base scope receiver (.object me)))=_
    rw [CursorSource.hoisted_starts_body (callee:=some function)]
    rfl
  refine entry.trans ?_
  refine (input.native_body (1+fuel)).trans ?_
  have caller:=TieredCall.return_to_caller base (input.after.machine world)
    (.number CursorComputeCall.baseCps) fuel
  refine caller.trans ?_
  congr 1
  simp only [returned,LocalState.machine,CursorLocals.start,bodyBase,CursorSource.hoisted,
    CursorSource.prepared,global,exclusions]

theorem native_invoke (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closureScope : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (CursorSource.closure scope source)) (fuel : Nat) :
    Builtins.run (input.work+45+fuel) (invoke base (.object function) (.object receiver) [.object me] false)=
      Builtins.run fuel (returned base scope receiver me function world input) := by
  simp only [invoke,present,kind,checked,CursorSource.actual_prepare]
  exact prepared_returns base scope receiver me function world input environments closureScope global exclusions fuel

def expression : Expr := .call (.member (.identifier "me") (.identifier "cps") false) [.identifier "me"]

theorem source_invoke (base : Machine) (me function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap me=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap me (JSString.ofString "cps")=
      .ok (some (.data (.object function) true true true)))
    (read : SourceRead.Reads base (.identifier "me") (.object me) 3) (fuel : Nat) :
    Builtins.run (13+fuel) {base with control:=.expression expression}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object me) [.object me] false} := by
  rw [show 13+fuel=2+(3+(3+(3+2+fuel))) by omega,Nat.add_comm 2 (3+(3+(3+2+fuel)))]
  change Builtins.run (3+(3+(3+2+fuel))) {base with
    control:=.expression (.identifier "me")
    continuation:=.memberObject (.identifier "cps") false::.callCallee [.identifier "me"] false::base.continuation}=_
  rw [read _ (by rfl),MemberCall.callee_data base "cps" (.identifier "me") me function object present kind property,
    MemberCall.argument_value base (.identifier "me") (.object me) me function 3 read]

theorem source_call (base : Machine) (scope me function : ObjectId)
    (world : World (bodyBase base scope me me function))
    (input : Inputs world (state base me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closureScope : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (source : Option JSString) (object functionObject : JSObject)
    (present : checkedObject base.heap me=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap me (JSString.ofString "cps")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CursorSource.closure scope source))
    (read : SourceRead.Reads base (.identifier "me") (.object me) 3) (fuel : Nat) :
    Builtins.run (input.work+59+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (returned base scope me me function world input) := by
  rw [show input.work+59+fuel=13+(1+(input.work+45+fuel)) by omega,
    source_invoke base me function object present kind property read,Nat.add_comm 1 (input.work+45+fuel)]
  change Builtins.run (input.work+45+fuel) {invoke {base with
    control:=.invoke (.object function) (.object me) [.object me] false}
    (.object function) (.object me) [.object me] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object me) [.object me] false}
      (.object function) (.object me) [.object me] false=
      CursorSource.prepared (callee:=some function) base scope me (.object me) := by
    simp only [invoke,functionPresent,functionKind,checked,CursorSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope me me function world input environments closureScope global exclusions fuel

theorem returned_extends (base : Machine) (scope receiver me function : ObjectId)
    (world : World (bodyBase base scope receiver me function))
    (input : Inputs world (state base me function)) :
    HeapExtension.Extends base.heap (returned base scope receiver me function world input).heap := by
  have first : HeapExtension.Extends base.heap ((state base me function).machine world).heap :=
    HeapExtension.trans (HeapExtension.append_object base.heap
      (CursorSource.argumentObject (callee:=some function) base (.object me))) (HeapExtension.same_objects rfl)
  exact HeapExtension.trans first input.after_extends

/-- The finite board count and thirteen literal guards have fixed source work.
The remaining work is the actual complete tier-helper execution. -/
theorem source_call_selected (base : Machine) (scope me function : ObjectId)
    (world : World (bodyBase base scope me me function))
    (input : Inputs world (state base me function))
    (environments : world.scopes.environments=base.heap.environments)
    (closureScope : world.scopes.closureScope=scope)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (source : Option JSString) (object functionObject : JSObject)
    (present : checkedObject base.heap me=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap me (JSString.ofString "cps")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CursorSource.closure scope source))
    (read : SourceRead.Reads base (.identifier "me") (.object me) 3) (fuel : Nat) :
    Builtins.run (input.tier.work+2861+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (returned base scope me me function world input) := by
  have sourceRun:=source_call base scope me function world input environments closureScope global exclusions
    source object functionObject present kind property functionPresent functionKind read fuel
  rw [show input.work+59+fuel=input.tier.work+2861+fuel by rw [input.work_selected]] at sourceRun
  exact sourceRun

end CookieClicker.JavaScript.CursorCall

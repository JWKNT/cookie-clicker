import CookieClicker.JavaScriptBuildingSellPrefix

/-! Complete native sale invocation through its first amount-one loop entry.
The callable identity and closure come from the original machine. -/
namespace CookieClicker.JavaScript.BuildingSellEntry
open BuildingSellInvocation BuildingSellLocals BuildingSellPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def initialValues (base : Machine) (bypass : Value) : Values := {
  amount:=.number Number.one,bypass,arguments:=.object base.heap.objects.size }

def entry (base : Machine) (scope : EnvId) (building : ObjectId)
    (bypass : Value) (callee : Option ObjectId) : Machine :=
  let ready:=hoisted base scope building (.number Number.one) bypass callee
  loopEntry ready ready.heap.objects base.heap.environments scope (initialValues base bypass) #[]

theorem actual_prepared_prefix (base : Machine) (scope : EnvId) (building : ObjectId)
    (bypass : Value) (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (138+fuel) (prepared base scope building (.number Number.one) bypass callee)=
      Builtins.run fuel (entry base scope building bypass callee) := by
  rw [show 138+fuel=82+(56+fuel) by omega,actual_hoist]
  let ready:=hoisted base scope building (.number Number.one) bypass callee
  have same : Builtins.run (56+fuel) ready=
      Builtins.run (56+fuel) {ready with control:=.statement CursorCycleSyntax.sellBody} := by
    rw [Nat.add_comm 56 fuel]
    change Builtins.run (fuel+55) (Builtins.builtinStep ready)=
      Builtins.run (fuel+55) (Builtins.builtinStep {ready with control:=.statement CursorCycleSyntax.sellBody})
    rw [hoisted_starts_body]
  rw [same,←original_hoisted]
  exact amount_one_body_prefix ready ready.heap.objects base.heap.environments scope
    (initialValues base bypass) #[] fuel

theorem actual_invocation_prefix (base : Machine) (scope : EnvId) (building function : ObjectId)
    (bypass : Value) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) (fuel : Nat) :
    Builtins.run (139+fuel) {base with
      control:=.invoke (.object function) (.object building) [.number Number.one,bypass] false}=
      Builtins.run fuel (entry base scope building bypass (some function)) := by
  rw [show 139+fuel=(138+fuel)+1 by omega]
  change Builtins.run (138+fuel) (Builtins.builtinStep {base with
    control:=.invoke (.object function) (.object building) [.number Number.one,bypass] false})=_
  have dispatched : Builtins.builtinStep {base with
      control:=.invoke (.object function) (.object building) [.number Number.one,bypass] false}=
      prepared base scope building (.number Number.one) bypass (some function) := by
    change {invoke {base with
      control:=.invoke (.object function) (.object building) [.number Number.one,bypass] false}
      (.object function) (.object building) [.number Number.one,bypass] false with elapsed:=base.elapsed}=_
    simp only [invoke,present,kind,checked,actual_prepare]
    rfl
  rw [dispatched]
  exact actual_prepared_prefix base scope building bypass (some function) fuel

theorem retained_objects (base : Machine) (scope : EnvId) (building : ObjectId)
    (bypass : Value) (callee : Option ObjectId) :
    (entry base scope building bypass callee).heap.objects=
      base.heap.objects.push (argumentObject base (.number Number.one) bypass callee) := rfl

theorem retained_environments (base : Machine) (scope : EnvId) (building : ObjectId)
    (bypass : Value) (callee : Option ObjectId) :
    (entry base scope building bypass callee).heap.environments=
      base.heap.environments.push ⟨.declarative (bindings (initialized (initialValues base bypass))),some scope⟩ := by
  simp [entry,loopEntry,start,heap]

theorem retained_time (base : Machine) (scope : EnvId) (building : ObjectId)
    (bypass : Value) (callee : Option ObjectId) :
    (entry base scope building bypass callee).elapsed=base.elapsed ∧
    (entry base scope building bypass callee).epochMilliseconds=base.epochMilliseconds ∧
    (entry base scope building bypass callee).freeDrawCount=base.freeDrawCount := ⟨rfl,rfl,rfl⟩

end CookieClicker.JavaScript.BuildingSellEntry

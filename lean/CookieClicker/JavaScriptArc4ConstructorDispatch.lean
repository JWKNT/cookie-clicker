import CookieClicker.JavaScriptArc4ConstructorPrefix

/-! The native control.invoke dispatch step preceding the continuous
constructor prefix. The caller frame and elapsed time are retained. -/
namespace CookieClicker.JavaScript.Arc4ConstructorDispatch
open Arc4ConstructorSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def start (i : Inputs) : Machine := {
  Arc4Locals.base i.source with
  control := .invoke (.object i.callee) .undefined [.object i.key] true }

theorem actual_dispatch (i : Inputs) :
    Builtins.builtinStep (start i)=
      invoke (Arc4Locals.base i.source) (.object i.callee) .undefined [.object i.key] true := by
  change {invoke (start i) (.object i.callee) .undefined [.object i.key] true
    with elapsed := (Arc4Locals.base i.source).elapsed} = _
  rw [Arc4ConstructorEntry.actual_construct (start i) (Arc4Locals.scope i.source)
    i.key i.callee i.prototype i.functionObject i.functionRead i.functionKind i.constructable
    i.prototypeWritable i.prototypeEnumerable i.prototypeConfigurable i.prototypeRead,
    Arc4ConstructorSetup.actual_construct]
  rfl

theorem actual_constructor_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (Arc4ConstructorPrefix.steps i+1+fuel) (start i)=
      Builtins.run fuel (Arc4ConstructorPrefix.finish i) := by
  rw [show Arc4ConstructorPrefix.steps i+1+fuel=(Arc4ConstructorPrefix.steps i+fuel)+1 by omega]
  change Builtins.run (Arc4ConstructorPrefix.steps i+fuel) (Builtins.builtinStep (start i)) = _
  rw [actual_dispatch,Arc4ConstructorPrefix.actual_constructor_prefix]

theorem empty_steps (i : Inputs) (empty : i.keyFrame.length=0) : Arc4ConstructorPrefix.steps i+1=37754 := by
  rw [Arc4ConstructorPrefix.empty_steps i empty]

theorem nonempty_steps (i : Inputs) (nonempty : 0<i.keyFrame.length) : Arc4ConstructorPrefix.steps i+1=37739 := by
  rw [Arc4ConstructorPrefix.nonempty_steps i nonempty]

end CookieClicker.JavaScript.Arc4ConstructorDispatch

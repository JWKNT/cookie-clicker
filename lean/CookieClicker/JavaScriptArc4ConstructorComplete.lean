import CookieClicker.JavaScriptArc4ConstructorFinalFrame
import CookieClicker.JavaScriptArc4ConstructorDispatch

/-! The complete native ARC4 constructor invocation, including the empty-key
fallback, both permutation loops, generator installation, 256-output discard
and return of the newly allocated instance to its original caller. -/
namespace CookieClicker.JavaScript.Arc4ConstructorComplete
open Arc4ConstructorSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

def returned (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) : Machine := {
  Arc4ConstructorFinalFrame.finish i missing with
  context := (Arc4Locals.base i.source).context
  control := .expressionResult (.value (.object (receiver i)))
  continuation := (Arc4Locals.base i.source).continuation }

theorem native_return (base : Machine) (value : Value) (previous : Option Value)
    (caller : ExecutionContext) (instanceId : ObjectId) (tail : List Frame) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value value)
      continuation := .expressionStatement :: .statementList [] previous :: .callBoundary caller (some instanceId) :: tail}=
    Builtins.run fuel {base with context := caller,control := .expressionResult (.value (.object instanceId)),continuation := tail} := by
  rw [Nat.add_comm 3 fuel]
  rfl

theorem actual_return (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none)
    (fuel : Nat) :
    Builtins.run (3+fuel) (Arc4ConstructorFinalFrame.finish i missing)=Builtins.run fuel (returned i missing) := by
  exact native_return (Arc4ConstructorFinalFrame.finish i missing)
    (.number (Arc4GeneratorBodyComplete.returnInputs
      (Arc4GeneratorCall.initialized (Arc4GeneratorInstalledFrame.call
        (Arc4ConstructorFinalFrame.frame i missing)))).accumulator)
    ((Arc4ConstructorFinalFrame.completed i).previous.or (Arc4ConstructorFinalFrame.identity i).previous)
    (Arc4Locals.base i.source).context (receiver i) (Arc4Locals.base i.source).continuation fuel

theorem actual_after_dispatch (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none)
    (fuel : Nat) :
    Builtins.run (Arc4ConstructorPrefix.steps i+34930+fuel)
      (invoke (Arc4Locals.base i.source) (.object i.callee) .undefined [.object i.key] true)=
      Builtins.run fuel (returned i missing) := by
  rw [show Arc4ConstructorPrefix.steps i+34930+fuel=Arc4ConstructorPrefix.steps i+(34927+(3+fuel)) by omega,
    Arc4ConstructorPrefix.actual_constructor_prefix,Arc4ConstructorFinalFrame.actual_suffix i missing,actual_return]

theorem actual_constructor (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none)
    (fuel : Nat) :
    Builtins.run (Arc4ConstructorPrefix.steps i+34931+fuel) (Arc4ConstructorDispatch.start i)=
      Builtins.run fuel (returned i missing) := by
  rw [show Arc4ConstructorPrefix.steps i+34931+fuel=(Arc4ConstructorPrefix.steps i+34930+fuel)+1 by omega]
  change Builtins.run (Arc4ConstructorPrefix.steps i+34930+fuel)
    (Builtins.builtinStep (Arc4ConstructorDispatch.start i))=_
  rw [Arc4ConstructorDispatch.actual_dispatch,actual_after_dispatch i missing]

theorem empty_steps (i : Inputs) (empty : i.keyFrame.length=0) : Arc4ConstructorPrefix.steps i+34931=72684 := by
  rw [Arc4ConstructorPrefix.empty_steps i empty]

theorem nonempty_steps (i : Inputs) (nonempty : 0<i.keyFrame.length) : Arc4ConstructorPrefix.steps i+34931=72669 := by
  rw [Arc4ConstructorPrefix.nonempty_steps i nonempty]

theorem returned_control (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    (returned i missing).control=.expressionResult (.value (.object (receiver i))) := rfl

theorem returned_context (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    (returned i missing).context=(Arc4Locals.base i.source).context := rfl

theorem returned_continuation (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    (returned i missing).continuation=(Arc4Locals.base i.source).continuation := rfl

theorem actual_complete_state (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    Builtins.run (Arc4ConstructorPrefix.steps i+34931) (Arc4ConstructorDispatch.start i)=returned i missing := by
  have zero (machine : Machine) : Builtins.run 0 machine=machine := rfl
  simpa only [Nat.add_zero,zero] using actual_constructor i missing 0

end CookieClicker.JavaScript.Arc4ConstructorComplete

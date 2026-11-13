import CookieClicker.JavaScriptTimestampSeedArc4Complete
import CookieClicker.JavaScriptArc4ConstructorMemory
import CookieClicker.JavaScriptSeedrandomRandomClosure

/-! The source q initializer stores the newly constructed ARC4 instance in the
retained seedrandom activation, then enters the actual return sequence. -/
namespace CookieClicker.JavaScript.TimestampSeedEntropyEntry
open TimestampSeedArc4Complete
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

def mixing (i : Inputs) := i.prelude.mixing
def base (i : Inputs) := TimestampSeedArc4Complete.returned i
def localScope (i : Inputs) := TimestampSeedArc4Prelude.localScope i.prelude
def scope (i : Inputs) := TimestampSeedArc4Prelude.scope i.prelude
def originalLocals (i : Inputs) := TimestampSeedArc4Prelude.locals i.prelude
def receiverId (i : Inputs) := Arc4ConstructorSetup.receiver (constructorFrame i)
def heap (i : Inputs) := BindingWrite.changedHeap (base i).heap (localScope i) (originalLocals i)
  (some (scope i)) "q" (.object (receiverId i))
def locals (i : Inputs) := BindingWrite.changedBindings "q" (.object (receiverId i)) (originalLocals i)

theorem local_environment (i : Inputs) : checkedEnvironment (base i).heap (localScope i)=
    .ok ⟨.declarative (originalLocals i),some (scope i)⟩ :=
  Arc4ConstructorMemory.original_environment (constructorFrame i) (missing_g i) _ _
    (TimestampSeedArc4Prelude.checked_local i.prelude)

theorem native_assign_q (i : Inputs) :
    setBinding (base i).heap (localScope i) "q" (.object (receiverId i)) false=.ok (heap i) :=
  BindingWrite.native_set _ _ _ _ _ _ ({name := "q"} : Binding) false (local_environment i) rfl rfl

def afterAssignment (i : Inputs) : Machine := {
  base i with
  heap := heap i
  control := .expressionResult (.value (.object (receiverId i)))
  continuation := .variableWrite [] :: .statementList (SeedrandomInvocation.body.drop 1) none ::
    .callBoundary (mixing i).globals.base.context none :: (mixing i).globals.base.continuation }

theorem actual_assignment (i : Inputs) (fuel : Nat) :
    Builtins.run (2+fuel) (base i)=Builtins.run fuel (afterAssignment i) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {putReference
    {base i with
      control := .putValue ⟨.environment (localScope i) "q",false⟩ (.object (receiverId i))
      continuation := (afterAssignment i).continuation}
    ⟨.environment (localScope i) "q",false⟩ (.object (receiverId i)) with elapsed := (base i).elapsed}=_
  simp only [putReference]
  rw [local_environment]
  simp only [checked]
  rw [native_assign_q]
  rfl

def atReturn (i : Inputs) : Machine := {
  afterAssignment i with
  control := .statement SeedrandomRandomClosure.returnStatement
  continuation := .statementList [] none :: .callBoundary (mixing i).globals.base.context none ::
    (mixing i).globals.base.continuation }

theorem actual_enter_return (i : Inputs) (fuel : Nat) :
    Builtins.run (2+fuel) (afterAssignment i)=Builtins.run fuel (atReturn i) := by
  rw [Nat.add_comm 2 fuel]
  rfl

theorem actual_constructor_to_return (i : Inputs) (fuel : Nat) :
    Builtins.run (4+fuel) (base i)=Builtins.run fuel (atReturn i) := by
  rw [show 4+fuel=2+(2+fuel) by omega,actual_assignment,actual_enter_return]

theorem checked_local (i : Inputs) : checkedEnvironment (heap i) (localScope i)=
    .ok ⟨.declarative (locals i),some (scope i)⟩ :=
  BindingWrite.changed_checked _ _ _ _ _ _ (local_environment i)

end CookieClicker.JavaScript.TimestampSeedEntropyEntry

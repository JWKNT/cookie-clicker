import CookieClicker.JavaScriptTimestampSeedMixing
import CookieClicker.JavaScriptBindingWrite
import CookieClicker.JavaScriptArc4ConstructorComplete

/-! The completed native seed-mixing call retains the caller's actual
seedrandom environment. Its returned text can be assigned to p without
replacing the retained helper allocations or source bindings. -/
namespace CookieClicker.JavaScript.TimestampSeedReturnedEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

open TimestampMixkeyComplete

theorem mixing_environment (i : TimestampMixkeyComplete.Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (present : checkedEnvironment (global i).base.heap id=.ok environment) :
    checkedEnvironment (returned i).heap id=.ok environment := by
  have first : checkedEnvironment (call i).heap id=.ok environment :=
    EnvironmentAppend.checked_old (global i).base.heap _ _ _ _ present
  exact EnvironmentAppend.checked_old (call i).heap _ _ _ _ first

theorem mixing_environment_size (i : TimestampMixkeyComplete.Inputs) :
    (returned i).heap.environments.size=(global i).base.heap.environments.size+2 := by
  change (MixkeyToString.heap (toStringInput i)).environments.size=_
  rw [MixkeyToString.environment_size]
  change (TimestampMixkeyReturn.sourceHeap (returnInput i)).environments.size+1=_
  rw [TimestampMixkeyReturn.size]
  rfl

theorem local_environment (i : TimestampSeedMixing.Inputs) :
    checkedEnvironment (TimestampSeedMixing.returned i).heap (SeedrandomInvocation.localIndex i.globals.base)=
      .ok ⟨.declarative (TimestampSeedSetup.localBindings (TimestampSeedMixing.setup i)
        (.object (TimestampSeedMixing.key i))),some i.globals.scope⟩ :=
  mixing_environment (TimestampSeedMixing.mixing i) _ _
    (TimestampSeedSetup.retained_checked_local (TimestampSeedMixing.setup i))

theorem original_environment (i : TimestampSeedMixing.Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (present : checkedEnvironment i.globals.base.heap id=.ok environment) :
    checkedEnvironment (TimestampSeedMixing.returned i).heap id=.ok environment :=
  mixing_environment (TimestampSeedMixing.mixing i) _ _
    (TimestampSeedMixingFrame.original_environment (TimestampSeedMixing.setup i) _ _ present)

def localIndex (i : TimestampSeedMixing.Inputs) := SeedrandomInvocation.localIndex i.globals.base
def localBindings (i : TimestampSeedMixing.Inputs) :=
  TimestampSeedSetup.localBindings (TimestampSeedMixing.setup i) (.object (TimestampSeedMixing.key i))
def assignedHeap (i : TimestampSeedMixing.Inputs) := BindingWrite.changedHeap (TimestampSeedMixing.returned i).heap
  (localIndex i) (localBindings i) (some i.globals.scope) "p" (.string (TimestampSeedMixing.text i))

theorem native_assign_p (i : TimestampSeedMixing.Inputs) :
    setBinding (TimestampSeedMixing.returned i).heap (localIndex i) "p" (.string (TimestampSeedMixing.text i)) false=
      .ok (assignedHeap i) :=
  BindingWrite.native_set _ _ _ _ _ _ ({name := "p"} : Binding) false (local_environment i) rfl rfl

def afterAssignment (i : TimestampSeedMixing.Inputs) : Machine := {
  TimestampSeedMixing.returned i with
  heap := assignedHeap i
  control := .expressionResult (.value (.string (TimestampSeedMixing.text i)))
  continuation := .variableWrite TimestampSeedSetup.remainingVariables ::
    .statementList (SeedrandomInvocation.body.drop 1) none ::
    .callBoundary i.globals.base.context none :: i.globals.base.continuation }

theorem actual_assignment (i : TimestampSeedMixing.Inputs) (fuel : Nat) :
    Builtins.run (2+fuel) (TimestampSeedMixing.returned i)=Builtins.run fuel (afterAssignment i) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {putReference
    {TimestampSeedMixing.returned i with
      control := .putValue ⟨.environment (localIndex i) "p",false⟩ (.string (TimestampSeedMixing.text i))
      continuation := (afterAssignment i).continuation}
    ⟨.environment (localIndex i) "p",false⟩ (.string (TimestampSeedMixing.text i))
    with elapsed := i.globals.base.elapsed} = _
  simp only [putReference]
  have localRead : checkedEnvironment (TimestampSeedMixing.returned i).heap (localIndex i)=
    .ok ⟨.declarative (localBindings i),some i.globals.scope⟩ := local_environment i
  rw [localRead]
  simp only [checked]
  rw [native_assign_p]
  rfl

end CookieClicker.JavaScript.TimestampSeedReturnedEnvironment

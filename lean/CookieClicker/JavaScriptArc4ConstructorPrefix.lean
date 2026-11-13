import CookieClicker.JavaScriptArc4ConstructorSetup
import CookieClicker.JavaScriptArc4EmptyKeyFrame

/-! A continuous native constructor execution from invocation through
allocation, hoisting, initializers, key normalization and both permutation
loops. The next source statement assigns and invokes the nested generator. -/
namespace CookieClicker.JavaScript.Arc4ConstructorPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4ConstructorSetup

def normalizationSteps (i : Inputs) : Nat := if i.keyFrame.length=0 then 23 else 8

def matching (i : Inputs) : (Arc4Locals.base (setup i).source).arrayPrototype=
    some (setup i).keyFrame.prototype.arrayId := i.arrayPrototype

def loops (i : Inputs) : Arc4ConstructorLoops.Inputs :=
  if empty : i.keyFrame.length=0 then
    Arc4EmptyKeyFrame.normalized (setup i) (matching i)
  else Arc4Normalize.nonemptyInputs (setup i) (matching i) (by
    change 0<i.keyFrame.length
    exact Nat.pos_of_ne_zero empty)

def finish (i : Inputs) := Arc4ConstructorLoops.finish (loops i) (callerTail i)
def steps (i : Inputs) := 69+normalizationSteps i+37661

theorem actual_normalization (i : Inputs) (fuel : Nat) :
    Builtins.run (normalizationSteps i+fuel) (Arc4Normalize.start (setup i) (callerTail i))=
      Builtins.run fuel (Arc4ConstructorLoops.start (loops i) (callerTail i)) := by
  by_cases empty : i.keyFrame.length=0
  · simp only [normalizationSteps,loops,empty,↓reduceIte]
    exact Arc4EmptyKeyFrame.actual_normalized (setup i) (matching i) empty _ _
  · simp only [normalizationSteps,loops,empty,↓reduceIte]
    exact Arc4Normalize.actual_nonempty (setup i) (matching i) (Nat.pos_of_ne_zero empty) _ _

theorem actual_to_loops (i : Inputs) (fuel : Nat) :
    Builtins.run (69+normalizationSteps i+fuel)
      (invoke (Arc4Locals.base i.source) (.object i.callee) .undefined [.object i.key] true)=
      Builtins.run fuel (Arc4ConstructorLoops.start (loops i) (callerTail i)) := by
  rw [show 69+normalizationSteps i+fuel=14+(1+(54+(normalizationSteps i+fuel))) by omega,
    actual_hoist,actual_statement]
  change Builtins.run (54+(normalizationSteps i+fuel))
    (Arc4Initializers.machineAt (setup i).source (setup i).objects (setup i).argument (setup i).receiver
      (Arc4Initializers.firstValues (setup i).key) (.statement Arc4Initializers.statement)
      (.statementList Arc4Normalize.remaining none :: callerTail i)) = _
  rw [Arc4Initializers.actual_initializers]
  change Builtins.run (normalizationSteps i+fuel) (Arc4Normalize.start (setup i) (callerTail i)) = _
  exact actual_normalization i fuel

theorem actual_constructor_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (steps i+fuel)
      (invoke (Arc4Locals.base i.source) (.object i.callee) .undefined [.object i.key] true)=
      Builtins.run fuel (finish i) := by
  rw [show steps i+fuel=69+normalizationSteps i+(37661+fuel) by unfold steps; omega,
    actual_to_loops,Arc4ConstructorLoops.actual_both_loops]
  rfl

theorem empty_steps (i : Inputs) (empty : i.keyFrame.length=0) : steps i=37753 := by
  simp [steps,normalizationSteps,empty]

theorem nonempty_steps (i : Inputs) (nonempty : 0<i.keyFrame.length) : steps i=37738 := by
  have different : i.keyFrame.length≠0 := Nat.ne_of_gt nonempty
  simp [steps,normalizationSteps,different]

end CookieClicker.JavaScript.Arc4ConstructorPrefix

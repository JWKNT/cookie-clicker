import CookieClicker.JavaScriptSeedrandomSetupLocals

/-! The final source p expression exits through the retained call boundary. -/
namespace CookieClicker.JavaScript.SeedrandomReturnP
open SeedrandomSetupLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def start (i : Inputs) (value : Value) := machine i (.expressionResult (.value value))
  (.sequence [.identifier "p"] :: returnTail i)
def finish (i : Inputs) : Machine := {
  i.base with
  heap := heap i
  context := i.caller
  control := .expressionResult (.value (.string i.text))
  continuation := i.tail }

theorem checked_local (i : Inputs) : checkedEnvironment (heap i) (localScope i)=
    .ok ⟨.declarative i.locals,some (scope i)⟩ := i.localRead

theorem read_p (i : Inputs) : readBinding (heap i) (localScope i) "p"=.ok (.string i.text) := i.pRead

attribute [local cbv_opaque] heap localScope scope Environment.identifier checkedEnvironment readBinding
  Array.size List.length JSString.ofString
attribute [local cbv_eval] SeedrandomSetupLocals.identifier_p checked_local read_p

theorem actual_return (i : Inputs) (value : Value) (fuel : Nat) :
    Builtins.run (8+fuel) (start i value)=Builtins.run fuel (finish i) := by
  rw [Nat.add_comm 8 fuel]
  cbv

end CookieClicker.JavaScript.SeedrandomReturnP

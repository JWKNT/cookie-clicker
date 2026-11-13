import CookieClicker.JavaScriptCursorBuyInvocation
import CookieClicker.JavaScriptCursorBuyComplete

namespace CookieClicker.JavaScript.CursorBuyCall
open CursorBuyInvocation SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def returned (base : Machine) (scope cursor function : Nat) (display : JSString)
    (i : CursorBuyComplete.Inputs (hoisted base scope cursor (some function)) display) : Machine := {
  CursorBuyComplete.completed i with
  context:=base.context
  control:=.expressionResult (.value .undefined)
  continuation:=base.continuation }

theorem actual_hoisted (base : Machine) (scope cursor function : Nat) (display : JSString)
    (i : CursorBuyComplete.Inputs (hoisted base scope cursor (some function)) display)
    (edge : DataEdge (hoisted base scope cursor (some function)) cursor
      (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (700+fuel) (hoisted base scope cursor (some function))=
      Builtins.run fuel (CursorBuyComplete.completed i) := by
  have same : Builtins.run (700+fuel) (hoisted base scope cursor (some function))=
      Builtins.run (700+fuel) {hoisted base scope cursor (some function) with
        control:=.statement BuildingCallbackSyntax.cursorBuyBody} := by
    rw [show 700+fuel=(699+fuel)+1 by omega]
    change Builtins.run (699+fuel) (Builtins.builtinStep (hoisted base scope cursor (some function)))=_
    rw [hoisted_starts_body]
    rfl
  rw [same]
  exact CursorBuyComplete.native_body i cursor rfl edge fuel

theorem actual_return (base : Machine) (scope cursor function : Nat) (display : JSString)
    (i : CursorBuyComplete.Inputs (hoisted base scope cursor (some function)) display) :
    Builtins.builtinStep (CursorBuyComplete.completed i)=returned base scope cursor function display i := rfl

theorem actual_prepared (base : Machine) (scope cursor function : Nat) (display : JSString)
    (i : CursorBuyComplete.Inputs (hoisted base scope cursor (some function)) display)
    (edge : DataEdge (hoisted base scope cursor (some function)) cursor
      (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (757+fuel) (prepared base scope cursor (some function))=
      Builtins.run fuel (returned base scope cursor function display i) := by
  rw [show 757+fuel=56+(700+(1+fuel)) by omega,actual_hoist,
    actual_hoisted base scope cursor function display i edge,Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (CursorBuyComplete.completed i))=_
  rw [actual_return]

theorem actual_invoke (base : Machine) (scope cursor function : Nat) (display : JSString)
    (i : CursorBuyComplete.Inputs (hoisted base scope cursor (some function)) display)
    (edge : DataEdge (hoisted base scope cursor (some function)) cursor
      (JSString.ofString "amount") (.number Number.one))
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) (fuel : Nat) :
    Builtins.run (757+fuel) (invoke base (.object function) (.object cursor) [] false)=
      Builtins.run fuel (returned base scope cursor function display i) := by
  simp only [invoke,present,kind,checked,actual_prepare]
  exact actual_prepared base scope cursor function display i edge fuel

end CookieClicker.JavaScript.CursorBuyCall

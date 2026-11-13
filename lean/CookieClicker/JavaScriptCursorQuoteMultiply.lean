import CookieClicker.JavaScriptCursorQuoteStep

/-! Actual compound multiplication around the reverse quote's nested source
getSellMultiplier call. Native local writes and the result value are retained. -/
namespace CookieClicker.JavaScript.CursorQuoteMultiply
open CursorQuoteLocals CursorQuoteStep SourceRead
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding readBinding Number.mul
attribute [local cbv_eval] checked_local set_price read_price

theorem multiplication_prefix (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (expression : Expr) (fuel : Nat) :
    Builtins.run (6+fuel) {start reverse base objects leading outer v suffix with
      control:=.statement (.expression (.assignment .multiply (.identifier "price") expression))}=
      Builtins.run fuel {start reverse base objects leading outer v suffix with
        control:=.expression expression
        continuation:=.assignmentRight .multiply (reference leading) (some v.price)::
          .expressionStatement::base.continuation} := by
  rw [show 6+fuel=2+(1+(3+fuel)) by omega,Nat.add_comm 2 (1+(3+fuel))]
  change Builtins.run (1+(3+fuel)) {start reverse base objects leading outer v suffix with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .multiply expression::.expressionStatement::base.continuation}=_
  rw [Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) (Environment.identifier {start reverse base objects leading outer v suffix with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .multiply expression::.expressionStatement::base.continuation} "price")=_
  rw [price_reference,Nat.add_comm 3 fuel]
  cbv

theorem multiplication_suffix (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (old added : UInt64) (value : v.price=.number old) (fuel : Nat) :
    Builtins.run (4+fuel) {start reverse base objects leading outer v suffix with
      control:=.expressionResult (.value (.number added))
      continuation:=.assignmentRight .multiply (reference leading) (some v.price)::
        .expressionStatement::base.continuation}=
      Builtins.run fuel {start reverse base objects leading outer {v with price:=.number (Number.mul old added)} suffix with
        control:=.completion (.normal (some (.number (Number.mul old added))))} := by
  rw [value,Nat.add_comm 4 fuel]
  cbv

end CookieClicker.JavaScript.CursorQuoteMultiply

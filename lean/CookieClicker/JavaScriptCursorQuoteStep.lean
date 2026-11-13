import CookieClicker.JavaScriptCursorQuoteLoop

/-! The native quote summand and postfix loop update. Every local write is
executed by the interpreter; there is no arithmetic endpoint substitution. -/
namespace CookieClicker.JavaScript.CursorQuoteStep
open CursorQuoteLocals CursorQuoteRead CursorQuoteLoop SourceRead
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "price",false⟩

theorem price_reference (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (control : Control) (continuation : List Frame) :
    Environment.identifier {start reverse base objects leading outer v suffix with control,continuation} "price"=
      {start reverse base objects leading outer v suffix with
        control:=.expressionResult (.reference (reference leading)),continuation} := by
  exact Environment.resolve_declared _ _ _ "price" false (bindings v) (some outer)
    (checked_local objects leading outer v suffix) (has_price v)

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding readBinding Number.add
attribute [local cbv_eval] checked_local set_price set_i read_price read_i has_i

theorem addition_prefix (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (expression : Expr) (fuel : Nat) :
    Builtins.run (6+fuel) {start reverse base objects leading outer v suffix with
      control:=.statement (.expression (.assignment .add (.identifier "price") expression))}=
      Builtins.run fuel {start reverse base objects leading outer v suffix with
        control:=.expression expression
        continuation:=.assignmentRight .add (reference leading) (some v.price)::
          .expressionStatement::base.continuation} := by
  rw [show 6+fuel=2+(1+(3+fuel)) by omega,Nat.add_comm 2 (1+(3+fuel))]
  change Builtins.run (1+(3+fuel)) {start reverse base objects leading outer v suffix with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .add expression::.expressionStatement::base.continuation}=_
  rw [Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) (Environment.identifier {start reverse base objects leading outer v suffix with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .add expression::.expressionStatement::base.continuation} "price")=_
  rw [price_reference,Nat.add_comm 3 fuel]
  cbv

theorem addition_suffix (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (old added : UInt64) (value : v.price=.number old) (fuel : Nat) :
    Builtins.run (4+fuel) {start reverse base objects leading outer v suffix with
      control:=.expressionResult (.value (.number added))
      continuation:=.assignmentRight .add (reference leading) (some v.price)::
        .expressionStatement::base.continuation}=
      Builtins.run fuel {start reverse base objects leading outer {v with price:=.number (Number.add old added)} suffix with
        control:=.completion (.normal (some (.number (Number.add old added))))} := by
  rw [value,Nat.add_comm 4 fuel]
  cbv

theorem native_body (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (old added : UInt64) (value : v.price=.number old)
    (read : Reads (start reverse base objects leading outer v suffix) (raw reverse) (.number added) 53)
    (fuel : Nat) (previous : Option Value := none) :
    Builtins.run (65+fuel) (atBody reverse base objects leading outer v suffix previous)=
      Builtins.run fuel {atBody reverse base objects leading outer {v with price:=.number (Number.add old added)} suffix previous with
        control:=.completion (.normal (some (.number (Number.add old added))))} := by
  rw [show 65+fuel=1+(6+(53+(4+(1+fuel)))) by omega,Nat.add_comm 1 (6+(53+(4+(1+fuel))))]
  change Builtins.run (6+(53+(4+(1+fuel)))) (Builtins.builtinStep (atBody reverse base objects leading outer v suffix previous))=_
  have first : Builtins.builtinStep (atBody reverse base objects leading outer v suffix previous)=
      {start reverse {base with continuation:=.statementList [] none::(atBody reverse base objects leading outer v suffix previous).continuation}
        objects leading outer v suffix with
        control:=.statement (.expression (.assignment .add (.identifier "price") (raw reverse)))} := by
    cases reverse <;> rfl
  rw [first,addition_prefix]
  change Builtins.run (53+(4+(1+fuel))) {start reverse base objects leading outer v suffix with
    control:=.expression (raw reverse)
    continuation:=.assignmentRight .add (reference leading) (some v.price)::
      .expressionStatement::.statementList [] none::(atBody reverse base objects leading outer v suffix previous).continuation}=_
  rw [read _ (by rfl)]
  change Builtins.run (4+(1+fuel)) {start reverse {base with
    continuation:=.statementList [] none::(atBody reverse base objects leading outer v suffix previous).continuation}
    objects leading outer v suffix with
    control:=.expressionResult (.value (.number added))
    continuation:=.assignmentRight .add (reference leading) (some v.price)::
      .expressionStatement::.statementList [] none::(atBody reverse base objects leading outer v suffix previous).continuation}=_
  rw [addition_suffix _ _ _ _ _ _ _ old added value,Nat.add_comm 1 fuel]
  rfl

theorem native_update (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (index : UInt64) (value : v.i=.number index) (completed : Value) (fuel : Nat)
    (previous : Option Value := none) :
    Builtins.run (9+fuel) {atBody reverse base objects leading outer v suffix previous with
      control:=.completion (.normal (some completed))}=
      Builtins.run fuel (atGuard reverse base objects leading outer {v with i:=.number (Number.add index Number.one)} suffix (some completed)) := by
  rcases v with ⟨amount,arguments,price,i⟩
  dsimp at value
  subst i
  rw [Nat.add_comm 9 fuel]
  have same : update reverse=.update .increment (.identifier "i") false := by cases reverse <;> rfl
  unfold atBody atGuard
  rw [same]
  cbv

end CookieClicker.JavaScript.CursorQuoteStep

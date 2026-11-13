import CookieClicker.JavaScriptCursorGuards

/-! Actual compound-assignment boundaries for the three Cursor helper calls.
The caller locals and all retained source allocations remain represented. -/
namespace CookieClicker.JavaScript.CursorHelpersBody
open CursorLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def multiplyStatement (expression : Expr) : Stmt :=
  .expression (.assignment .multiply (.identifier "mult") expression)

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "mult",false⟩

def callContinuation (leading : Array LexicalEnvironment) (old : UInt64)
    (continuation : List Frame) : List Frame :=
  .assignmentRight .multiply (reference leading) (some (.number old))::
    .expressionStatement::continuation

theorem local_me (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "me") values.me 3 := by
  apply local_identifier _ "me" values.me (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · simp [bindings]
  · exact read_me objects leading outer values suffix

theorem local_mult (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "mult") values.mult 3 := by
  apply local_identifier _ "mult" values.mult (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · exact has_mult values
  · exact read_mult objects leading outer values suffix

theorem multiply_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old : UInt64) (value : values.mult=.number old)
    (expression : Expr) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (6+fuel) {before with control:=.statement (multiplyStatement expression)}=
      Builtins.run fuel {before with
        control:=.expression expression
        continuation:=callContinuation leading old base.continuation} := by
  dsimp only
  rw [show 6+fuel=2+(1+(3+fuel)) by omega,Nat.add_comm 2 (1+(3+fuel))]
  let before:=start base objects leading outer values suffix
  let atIdentifier : Machine := {before with
    control:=.expression (.identifier "mult")
    continuation:=.assignmentLeft .multiply expression::.expressionStatement::base.continuation}
  change Builtins.run (1+(3+fuel)) atIdentifier=_
  have identified : Environment.identifier atIdentifier "mult"={atIdentifier with
      control:=.expressionResult (.reference (reference leading))} :=
    Environment.resolve_declared atIdentifier before.heap.environments.size (slotIndex leading)
      "mult" false (bindings values) (some outer)
      (checked_local objects leading outer values suffix) (has_mult values)
  rw [Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) (Environment.identifier atIdentifier "mult")=_
  rw [identified,Nat.add_comm 3 fuel]
  change Builtins.run (fuel+1) {getReference {before with
      control:=.getValue (reference leading)
      continuation:=.assignmentRead .multiply (reference leading) expression::
        .expressionStatement::base.continuation} (reference leading) with elapsed:=base.elapsed}=_
  simp only [getReference,reference,before,start,checked_local,read_mult,value,checked,result]
  rfl

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding Number.mul
attribute [local cbv_eval] checked_local set_mult

theorem multiply_suffix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old value : UInt64) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (4+fuel) {before with
      control:=.expressionResult (.value (.number value))
      continuation:=callContinuation leading old base.continuation}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with mult:=.number (Number.mul old value)} suffix
        control:=.completion (.normal (some (.number (Number.mul old value))))} := by
  dsimp only
  rw [Nat.add_comm 4 fuel]
  cbv

theorem tier_statement_source : (CursorSource.body.drop 18).headD .empty=
    multiplyStatement (MemberCall.expression "GetTieredCpsMult" (.identifier "me")) := rfl

theorem magic_statement_source : (CursorSource.body.drop 19).headD .empty=
    multiplyStatement (MemberCall.expression "magicCpS" (.literal (.string (JSString.ofString "Cursor")))) := rfl

theorem eff_statement_source : (CursorSource.body.drop 20).headD .empty=
    multiplyStatement (MemberCall.expression "eff" (.literal (.string (JSString.ofString "cursorCps")))) := rfl

end CookieClicker.JavaScript.CursorHelpersBody

import CookieClicker.JavaScriptCursorSellLocals
import CookieClicker.JavaScriptSourceRead
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptReadCombinators

/-! Native statement boundaries in the complete sell-multiplier callback.
The nested aura call returns to the source compound assignment. -/
namespace CookieClicker.JavaScript.CursorSellBody
open CursorSellLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def multiplyStatement (expression : Expr) : Stmt :=
  .expression (.assignment .multiply (.identifier "giveBack") expression)

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "giveBack",false⟩

def callContinuation (leading : Array LexicalEnvironment) (old : UInt64)
    (continuation : List Frame) : List Frame :=
  .assignmentRight .multiply (reference leading) (some (.number old))::
    .expressionStatement::continuation

theorem local_giveBack (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "giveBack") values.giveBack 3 := by
  apply local_identifier _ "giveBack" values.giveBack (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · exact has_giveBack values
  · exact read_giveBack objects leading outer values suffix

theorem multiply_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old : UInt64) (value : values.giveBack=.number old)
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
    control:=.expression (.identifier "giveBack")
    continuation:=.assignmentLeft .multiply expression::.expressionStatement::base.continuation}
  change Builtins.run (1+(3+fuel)) atIdentifier=_
  have identified : Environment.identifier atIdentifier "giveBack"={atIdentifier with
      control:=.expressionResult (.reference (reference leading))} :=
    Environment.resolve_declared atIdentifier before.heap.environments.size (slotIndex leading)
      "giveBack" false (bindings values) (some outer)
      (checked_local objects leading outer values suffix) (has_giveBack values)
  rw [Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) (Environment.identifier atIdentifier "giveBack")=_
  rw [identified,Nat.add_comm 3 fuel]
  change Builtins.run (fuel+1) {getReference {before with
      control:=.getValue (reference leading)
      continuation:=.assignmentRead .multiply (reference leading) expression::
        .expressionStatement::base.continuation} (reference leading) with elapsed:=base.elapsed}=_
  simp only [getReference,reference,before,start,checked_local,read_giveBack,value,checked,result]
  rfl

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding Number.mul
attribute [local cbv_eval] checked_local set_giveBack

theorem multiply_suffix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old value : UInt64) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (4+fuel) {before with
      control:=.expressionResult (.value (.number value))
      continuation:=callContinuation leading old base.continuation}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with giveBack:=.number (Number.mul old value)} suffix
        control:=.completion (.normal (some (.number (Number.mul old value))))} := by
  dsimp only
  rw [Nat.add_comm 4 fuel]
  cbv


def quarter : UInt64 := 4598175219545276416
def auraName : JSString := JSString.ofString "Earth Shatterer"
def auraExpression : Expr := MemberCall.expression "auraMult" (.literal (.string auraName))
def assignmentExpression : Expr := .binary .add (.literal (.number Number.one)) auraExpression
def returnStatement : Stmt := .return (some (.identifier "giveBack"))

def auraContinuation (leading : Array LexicalEnvironment) (continuation : List Frame) : List Frame :=
  .binaryRight .add (.number Number.one)::callContinuation leading quarter
    (.statementList [returnStatement] none::continuation)

theorem native_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (16+fuel) (start base objects leading outer values suffix)=
      Builtins.run fuel {start base objects leading outer {values with giveBack:=.number quarter} suffix with
        control:=.expression auraExpression
        continuation:=auraContinuation leading base.continuation} := by
  rw [show 16+fuel=6+(1+(6+(3+fuel))) by omega,actual_initial_prefix,
    Nat.add_comm 1 (6+(3+fuel))]
  change Builtins.run (6+(3+fuel)) {start {base with
    continuation:=.statementList [returnStatement] none::base.continuation}
    objects leading outer {values with giveBack:=.number quarter} suffix with
    control:=.statement (multiplyStatement assignmentExpression)}=_
  rw [multiply_prefix _ objects leading outer {values with giveBack:=.number quarter}
    suffix quarter rfl assignmentExpression,Nat.add_comm 3 fuel]
  rfl

private theorem add_zero : Number.add Number.one 0=Number.one := by decide +kernel
private theorem multiply_one : Number.mul quarter Number.one=quarter := by decide +kernel
attribute [local cbv_opaque] Number.add
attribute [local cbv_eval] add_zero multiply_one

theorem native_suffix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (value : values.giveBack=.number quarter) (fuel : Nat) :
    Builtins.run (12+fuel) {start base objects leading outer values suffix with
      control:=.expressionResult (.value (.number 0))
      continuation:=auraContinuation leading base.continuation}=
      Builtins.run fuel {start base objects leading outer values suffix with
        control:=.completion (.return (.number quarter))} := by
  rw [show 12+fuel=1+(4+(7+fuel)) by omega,Nat.add_comm 1 (4+(7+fuel))]
  change Builtins.run (4+(7+fuel)) {start {base with
    continuation:=.statementList [returnStatement] none::base.continuation}
    objects leading outer values suffix with
    control:=.expressionResult (.value (.number (Number.add Number.one 0)))
    continuation:=callContinuation leading quarter
      (.statementList [returnStatement] none::base.continuation)}=_
  rw [add_zero,multiply_suffix,multiply_one]
  have unchanged : {values with giveBack:=.number quarter}=values := by cases values; simp_all
  rw [unchanged,show 7+fuel=1+(6+fuel) by omega,Nat.add_comm 1 (6+fuel)]
  change Builtins.run (6+fuel) {start base objects leading outer values suffix with
    control:=.statement returnStatement
    continuation:=.statementList [] (some (.number quarter))::base.continuation}=_
  let atReturn : Machine := {start base objects leading outer values suffix with
    continuation:=.statementList [] (some (.number quarter))::base.continuation}
  have read : Reads atReturn (.identifier "giveBack") (.number quarter) 3 := by
    simpa only [value,Reads,start,atReturn] using local_giveBack base objects leading outer values suffix
  rw [show 6+fuel=3+2+(1+fuel) by omega]
  change Builtins.run (3+2+(1+fuel)) {atReturn with
    control:=.statement (.return (some (.identifier "giveBack")))}=_
  rw [return_read atReturn (.identifier "giveBack") (.number quarter) 3 read,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.CursorSellBody

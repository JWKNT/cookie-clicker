import CookieClicker.JavaScriptMouseGuards

/-! The actual Mouse source count loop adds native building amounts, retaining
all twenty enumeration keys and the caller local frame. -/
namespace CookieClicker.JavaScript.MouseCount
open MouseLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def addStatement (expression : Expr) : Stmt :=
  .expression (.assignment .add (.identifier "num") expression)

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "num",false⟩

def callContinuation (leading : Array LexicalEnvironment) (old : UInt64)
    (continuation : List Frame) : List Frame :=
  .assignmentRight .add (reference leading) (some (.number old))::
    .expressionStatement::continuation

theorem local_num (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "num") values.num 3 := by
  apply local_identifier _ "num" values.num (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · exact has_num values
  · exact read_num objects leading outer values suffix

theorem add_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old : UInt64) (value : values.num=.number old)
    (expression : Expr) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (6+fuel) {before with control:=.statement (addStatement expression)}=
      Builtins.run fuel {before with
        control:=.expression expression
        continuation:=callContinuation leading old base.continuation} := by
  dsimp only
  rw [show 6+fuel=2+(1+(3+fuel)) by omega,Nat.add_comm 2 (1+(3+fuel))]
  let before:=start base objects leading outer values suffix
  let atIdentifier : Machine := {before with
    control:=.expression (.identifier "num")
    continuation:=.assignmentLeft .add expression::.expressionStatement::base.continuation}
  change Builtins.run (1+(3+fuel)) atIdentifier=_
  have identified : Environment.identifier atIdentifier "num"={atIdentifier with
      control:=.expressionResult (.reference (reference leading))} :=
    Environment.resolve_declared atIdentifier before.heap.environments.size (slotIndex leading)
      "num" false (bindings values) (some outer)
      (checked_local objects leading outer values suffix) (has_num values)
  rw [Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) (Environment.identifier atIdentifier "num")=_
  rw [identified,Nat.add_comm 3 fuel]
  change Builtins.run (fuel+1) {getReference {before with
      control:=.getValue (reference leading)
      continuation:=.assignmentRead .add (reference leading) expression::
        .expressionStatement::base.continuation} (reference leading) with elapsed:=base.elapsed}=_
  simp only [getReference,reference,before,start,checked_local,read_num,value,checked,result]
  rfl

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding Number.add
attribute [local cbv_eval] checked_local set_num

theorem add_suffix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old value : UInt64) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (4+fuel) {before with
      control:=.expressionResult (.value (.number value))
      continuation:=callContinuation leading old base.continuation}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with num:=.number (Number.add old value)} suffix
        control:=.completion (.normal (some (.number (Number.add old value))))} := by
  dsimp only
  rw [Nat.add_comm 4 fuel]
  cbv


def selected : Expr := .member (.member (.identifier "Game") (.identifier "Objects") false)
  (.identifier "i") true
def amountExpression : Expr := .member selected (.identifier "amount") false
def countBody : Stmt := match (MouseSource.body.drop 15).headD .empty with
  | .forIn _ _ statement => statement | _ => .empty

theorem body_source : countBody=.block [addStatement amountExpression] := rfl

theorem native_body (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old amount : UInt64) (value : values.num=.number old)
    (read : Reads (start base objects leading outer values suffix) amountExpression (.number amount) 19)
    (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (31+fuel) {before with control:=.statement countBody}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with num:=.number (Number.add old amount)} suffix
        control:=.completion (.normal (some (.number (Number.add old amount))))} := by
  dsimp only
  rw [body_source,show 31+fuel=1+(6+(19+(4+(1+fuel)))) by omega,Nat.add_comm 1 (6+(19+(4+(1+fuel))))]
  change Builtins.run (6+(19+(4+(1+fuel))))
    {start {base with continuation:=.statementList [] none::base.continuation}
      objects leading outer values suffix with control:=.statement (addStatement amountExpression)}=_
  rw [add_prefix _ objects leading outer values suffix old value amountExpression]
  change Builtins.run (19+(4+(1+fuel))) {start base objects leading outer values suffix with
    control:=.expression amountExpression
    continuation:=callContinuation leading old (.statementList [] none::base.continuation)}=_
  rw [read (callContinuation leading old (.statementList [] none::base.continuation)) (by rfl) (4+(1+fuel))]
  change Builtins.run (4+(1+fuel)) {start {base with continuation:=.statementList [] none::base.continuation}
    objects leading outer values suffix with
    control:=.expressionResult (.value (.number amount))
    continuation:=callContinuation leading old (.statementList [] none::base.continuation)}=_
  rw [add_suffix {base with continuation:=.statementList [] none::base.continuation} objects leading outer values suffix old amount,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.MouseCount

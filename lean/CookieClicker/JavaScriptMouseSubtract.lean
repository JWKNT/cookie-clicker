import CookieClicker.JavaScriptMouseGuards

/-! The actual mouseCps subtraction removes the Cursor amount from the
native building total. The caller local frame remains allocated. -/
namespace CookieClicker.JavaScript.MouseSubtract
open MouseLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def subtractStatement (expression : Expr) : Stmt :=
  .expression (.assignment .subtract (.identifier "num") expression)

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "num",false⟩

def callContinuation (leading : Array LexicalEnvironment) (old : UInt64)
    (continuation : List Frame) : List Frame :=
  .assignmentRight .subtract (reference leading) (some (.number old))::
    .expressionStatement::continuation

theorem local_num (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "num") values.num 3 := by
  apply local_identifier _ "num" values.num (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · exact has_num values
  · exact read_num objects leading outer values suffix

theorem subtract_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old : UInt64) (value : values.num=.number old)
    (expression : Expr) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (6+fuel) {before with control:=.statement (subtractStatement expression)}=
      Builtins.run fuel {before with
        control:=.expression expression
        continuation:=callContinuation leading old base.continuation} := by
  dsimp only
  rw [show 6+fuel=2+(1+(3+fuel)) by omega,Nat.add_comm 2 (1+(3+fuel))]
  let before:=start base objects leading outer values suffix
  let atIdentifier : Machine := {before with
    control:=.expression (.identifier "num")
    continuation:=.assignmentLeft .subtract expression::.expressionStatement::base.continuation}
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
      continuation:=.assignmentRead .subtract (reference leading) expression::
        .expressionStatement::base.continuation} (reference leading) with elapsed:=base.elapsed}=_
  simp only [getReference,reference,before,start,checked_local,read_num,value,checked,result]
  rfl

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding Number.sub
attribute [local cbv_eval] checked_local set_num

theorem subtract_suffix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old value : UInt64) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (4+fuel) {before with
      control:=.expressionResult (.value (.number value))
      continuation:=callContinuation leading old base.continuation}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with num:=.number (Number.sub old value)} suffix
        control:=.completion (.normal (some (.number (Number.sub old value))))} := by
  dsimp only
  rw [Nat.add_comm 4 fuel]
  cbv


def selected : Expr := .member
  (.member (.member (.identifier "Game") (.identifier "Objects") false)
    (.literal (.string (JSString.ofString "Cursor"))) true) (.identifier "amount") false
def statement : Stmt := (MouseSource.body.drop 16).headD .empty

theorem source_statement : statement=subtractStatement selected := rfl

theorem native_subtract (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (old amount : UInt64) (value : values.num=.number old)
    (read : Reads (start base objects leading outer values suffix) selected (.number amount) 17)
    (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (27+fuel) {before with control:=.statement statement}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with num:=.number (Number.sub old amount)} suffix
        control:=.completion (.normal (some (.number (Number.sub old amount))))} := by
  dsimp only
  rw [source_statement,show 27+fuel=6+(17+(4+fuel)) by omega]
  rw [subtract_prefix base objects leading outer values suffix old value selected]
  rw [read (callContinuation leading old base.continuation) (by rfl)]
  exact subtract_suffix base objects leading outer values suffix old amount fuel

end CookieClicker.JavaScript.MouseSubtract

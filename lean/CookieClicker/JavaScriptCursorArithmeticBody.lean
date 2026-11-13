import CookieClicker.JavaScriptCursorBoards

namespace CookieClicker.JavaScript.CursorArithmeticBody
open CursorLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding Number.mul
attribute [local cbv_eval] checked_local set_mult has_mult set_num has_num set_add has_add read_add read_num

theorem initialize_mult (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (5+fuel) {before with control:=.statement ((CursorSource.body.drop 14).headD .empty)}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with mult:=.number Number.one} suffix
        control:=.completion (.normal none)} := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem initialize_num (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (5+fuel) {before with control:=.statement ((CursorSource.body.drop 15).headD .empty)}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with num:=.number Number.positiveZero} suffix
        control:=.completion (.normal none)} := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem identifier_add (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (control : Control) (continuation : List Frame) :
    Environment.identifier {start base objects leading outer values suffix with control,continuation} "add"=
      {start base objects leading outer values suffix with
        control:=.expressionResult (.reference ⟨.environment (slotIndex leading) "add",false⟩),continuation} :=
  Environment.resolve_declared _ _ _ "add" false (bindings values) (some outer)
    (checked_local objects leading outer values suffix) (has_add values)

theorem identifier_num (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (control : Control) (continuation : List Frame) :
    Environment.identifier {start base objects leading outer values suffix with control,continuation} "num"=
      {start base objects leading outer values suffix with
        control:=.expressionResult (.reference ⟨.environment (slotIndex leading) "num",false⟩),continuation} :=
  Environment.resolve_declared _ _ _ "num" false (bindings values) (some outer)
    (checked_local objects leading outer values suffix) (has_num values)

attribute [local cbv_opaque] Environment.identifier
attribute [local cbv_eval] identifier_add identifier_num

theorem multiply_add_num (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (add num : UInt64)
    (addValue : values.add=.number add) (numValue : values.num=.number num) (fuel : Nat) :
    let before:=start base objects leading outer values suffix
    Builtins.run (16+fuel) {before with control:=.statement ((CursorSource.body.drop 17).headD .empty)}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {values with add:=.number (Number.mul add num)} suffix
        control:=.completion (.normal (some (.number (Number.mul add num))))} := by
  dsimp only
  let before:=start base objects leading outer values suffix
  let product:=Expr.binary .multiply (.identifier "add") (.identifier "num")
  let ref:Reference:=⟨.environment (slotIndex leading) "add",false⟩
  have addRead : SourceRead.Reads before (.identifier "add") (.number add) 3 := by
    rw [←addValue]
    exact SourceRead.local_identifier before "add" values.add (bindings values) (some outer)
      (checked_local objects leading outer values suffix) (has_add values)
      (read_add objects leading outer values suffix)
  have numRead : SourceRead.Reads before (.identifier "num") (.number num) 3 := by
    rw [←numValue]
    exact SourceRead.local_identifier before "num" values.num (bindings values) (some outer)
      (checked_local objects leading outer values suffix) (has_num values)
      (read_num objects leading outer values suffix)
  rw [show 16+fuel=2+(1+(2+(3+(1+(3+(4+fuel)))))) by omega,
    Nat.add_comm 2 (1+(2+(3+(1+(3+(4+fuel))))))]
  change Builtins.run (1+(2+(3+(1+(3+(4+fuel)))))) {before with
    control:=.expression (.identifier "add")
    continuation:=.assignmentLeft .assign product::.expressionStatement::base.continuation}=_
  rw [Nat.add_comm 1 (2+(3+(1+(3+(4+fuel)))))]
  change Builtins.run (2+(3+(1+(3+(4+fuel)))))
    (Environment.identifier {before with
      control:=.expression (.identifier "add")
      continuation:=.assignmentLeft .assign product::.expressionStatement::base.continuation} "add")=_
  rw [identifier_add,Nat.add_comm 2 (3+(1+(3+(4+fuel))))]
  change Builtins.run (3+(1+(3+(4+fuel)))) {before with
    control:=.expression (.identifier "add")
    continuation:=.binaryLeft .multiply (.identifier "num")::
      .assignmentRight .assign ref none::.expressionStatement::base.continuation}=_
  rw [addRead _ (by rfl),Nat.add_comm 1 (3+(4+fuel))]
  change Builtins.run (3+(4+fuel)) {before with
    control:=.expression (.identifier "num")
    continuation:=.binaryRight .multiply (.number add)::
      .assignmentRight .assign ref none::.expressionStatement::base.continuation}=_
  rw [numRead _ (by rfl),Nat.add_comm 4 fuel]
  cbv


end CookieClicker.JavaScript.CursorArithmeticBody

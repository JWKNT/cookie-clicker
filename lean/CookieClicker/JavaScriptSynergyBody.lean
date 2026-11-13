import CookieClicker.JavaScriptTieredSuffix

/-! The intact synergy-loop body of GetTieredCpsMult. The selected entry is
written through the native variable initializer. Its actual Game.Has call runs
with native arguments/environment allocation and retains the caller locals. -/
namespace CookieClicker.JavaScript.SynergyBody
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

 def selected : Expr := .member (.member (.identifier "me") (.identifier "synergies") false) (.identifier "i") true
 def argument : Expr := .member (.identifier "syn") (.identifier "name") false
 def body : Stmt := match (TieredSource.body.drop 2).headD .empty with
  | .forIn _ _ statement => statement
  | _ => .empty
 def consequent : Stmt := match body with
  | .block [_,.ifThenElse _ statement _] => statement
  | _ => .empty
 def guard : Stmt := .ifThenElse (HasReadPrelude.call argument) consequent none
 theorem source_body : body=.block [.variable [("syn",some selected)],guard] := rfl

 def afterAssignment (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId) : Machine := {
  TieredLocals.start base objects leading outer {values with syn:=.object syn} suffix with
  control:=.completion (.normal none) }

 theorem syn_reference (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) :
    identifierReference (TieredLocals.start base objects leading outer values suffix) "syn"=
      .ok ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ := by
  simp [identifierReference,resolveName,TieredLocals.start,TieredLocals.checked_local,
    TieredLocals.bindings,Except.bind,bind,pure,Except.pure]

 theorem variable_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId)
    (read : Reads (TieredLocals.start base objects leading outer values suffix) selected (.object syn) 15)
    (fuel : Nat) :
    let before:=TieredLocals.start base objects leading outer values suffix
    Builtins.run (19+fuel) {before with control:=.statement (.variable [("syn",some selected)])}=
      Builtins.run fuel (afterAssignment base objects leading outer values suffix syn) := by
  let before:=TieredLocals.start base objects leading outer values suffix
  dsimp only
  rw [show 19+fuel=1+(15+(3+fuel)) by omega,Nat.add_comm 1 (15+(3+fuel))]
  change Builtins.run (15+(3+fuel)) {variables {before with
    control:=.statement (.variable [("syn",some selected)])} [("syn",some selected)] with elapsed:=base.elapsed}=_
  have reference : identifierReference {before with
      control:=.statement (.variable [("syn",some selected)])} "syn"=
      .ok ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ := syn_reference base objects leading outer values suffix
  have initial : variables {before with
      control:=.statement (.variable [("syn",some selected)])} [("syn",some selected)] =
      {before with
        control:=.expression selected
        continuation:=.assignmentRight .assign ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ none::
          .variableWrite []::base.continuation} := by
    rw [variables,reference]
    rfl
  rw [initial]
  change Builtins.run (15+(3+fuel)) {before with
    control:=.expression selected
    continuation:=.assignmentRight .assign ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ none::
      .variableWrite []::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {before with
    control:=.putValue ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ (.object syn)
    continuation:=.variableWrite []::base.continuation}=_
  change Builtins.run (fuel+1) {putReference {before with
    control:=.putValue ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ (.object syn)
    continuation:=.variableWrite []::base.continuation}
      ⟨.environment (TieredLocals.slotIndex leading) "syn",false⟩ (.object syn) with elapsed:=base.elapsed}=_
  simp only [putReference,before,TieredLocals.start,TieredLocals.checked_local,TieredLocals.set_syn,checked,result]
  rfl

 theorem assignment_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId)
    (read : Reads (TieredLocals.start base objects leading outer values suffix) selected (.object syn) 15)
    (fuel : Nat) :
    let before:=TieredLocals.start base objects leading outer values suffix
    let after:=afterAssignment base objects leading outer values suffix syn
    Builtins.run (21+fuel) {before with control:=.statement body}=
      Builtins.run fuel {after with
        control:=.statement guard
        continuation:=.statementList [] none::base.continuation} := by
  dsimp only
  rw [source_body,show 21+fuel=1+(19+(1+fuel)) by omega,Nat.add_comm 1 (19+(1+fuel))]
  change Builtins.run (19+(1+fuel)) {TieredLocals.start
    {base with continuation:=.statementList [guard] none::base.continuation}
    objects leading outer values suffix with control:=.statement (.variable [("syn",some selected)])}=_
  rw [variable_prefix {base with continuation:=.statementList [guard] none::base.continuation}
    objects leading outer values suffix syn read,Nat.add_comm 1 fuel]
  rfl

 def guardCaller (base : Machine) : Machine := {base with
  continuation:=.ifTest consequent none::.statementList [] none::base.continuation }

 attribute [local cbv_opaque] HasInvocation.allocatedHeap

 theorem skip_tail (base : Machine) (scope upgrade function : ObjectId)
    (what : JSString) (fuel : Nat) :
    Builtins.run (2+fuel) (HasReadPrelude.returned (guardCaller base) scope upgrade function what (.number 0))=
      Builtins.run fuel (TieredZero.skipped base scope upgrade function what) := by
  rw [Nat.add_comm 2 fuel]
  cbv

 theorem guard_zero {base : Machine} {what : JSString} (has : TieredSuffix.HasZero base what)
    (nameRead : Reads base argument (.string what) 7) (fuel : Nat) :
    Builtins.run (88+fuel) {base with
      control:=.statement guard
      continuation:=.statementList [] none::base.continuation}=
      Builtins.run fuel has.after := by
  rw [show 88+fuel=1+(85+(2+fuel)) by omega,Nat.add_comm 1 (85+(2+fuel))]
  change Builtins.run (7+78+(2+fuel)) {guardCaller base with
    control:=.expression (HasReadPrelude.call argument)}=_
  rw [HasReadPrelude.source_call (guardCaller base) argument has.frame has.scopes has.objects has.environments
    has.global has.exclusions has.function has.source has.functionObject has.functionRead has.functionKind
    has.gameHas has.gameRead 7 nameRead]
  exact skip_tail base has.scopes.closureScope has.frame.upgrade has.function what fuel

 /-- Every branch in the original source body remains present. A zero-owned
 synergy skips multiplication only after executing the actual Has function. -/
 theorem actual_body (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId) (what : JSString)
    (selectedRead : Reads (TieredLocals.start base objects leading outer values suffix) selected (.object syn) 15)
    (has : TieredSuffix.HasZero (afterAssignment base objects leading outer values suffix syn) what)
    (nameRead : Reads (afterAssignment base objects leading outer values suffix syn) argument (.string what) 7)
    (fuel : Nat) :
    Builtins.run (109+fuel) {TieredLocals.start base objects leading outer values suffix with control:=.statement body}=
      Builtins.run fuel has.after := by
  rw [show 109+fuel=21+(88+fuel) by omega,
    assignment_prefix base objects leading outer values suffix syn selectedRead]
  exact guard_zero has nameRead fuel

 theorem local_syn (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId) :
    Reads (afterAssignment base objects leading outer values suffix syn) (.identifier "syn") (.object syn) 3 := by
  apply local_identifier _ _ _ (TieredLocals.bindings {values with syn:=.object syn}) (some outer)
  · exact TieredLocals.checked_local objects leading outer {values with syn:=.object syn} suffix
  · simp [TieredLocals.bindings]
  · exact TieredLocals.read_syn objects leading outer {values with syn:=.object syn} suffix

 theorem actual_body_data (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId) (what : JSString)
    (selectedRead : Reads (TieredLocals.start base objects leading outer values suffix) selected (.object syn) 15)
    (has : TieredSuffix.HasZero (afterAssignment base objects leading outer values suffix syn) what)
    (nameEdge : DataEdge (afterAssignment base objects leading outer values suffix syn)
      syn (JSString.ofString "name") (.string what)) (fuel : Nat) :
    Builtins.run (109+fuel) {TieredLocals.start base objects leading outer values suffix with control:=.statement body}=
      Builtins.run fuel has.after := by
  exact actual_body base objects leading outer values suffix syn what selectedRead has
    (nameEdge.dot _ 3 (local_syn base objects leading outer values suffix syn)) fuel

 theorem final_heap (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (syn : ObjectId) (what : JSString)
    (has : TieredSuffix.HasZero (afterAssignment base objects leading outer values suffix syn) what) :
    has.after.heap =
      TieredLocals.heap (EnvironmentAppend.hasObjects (callee:=some has.function)
        (afterAssignment base objects leading outer values suffix syn) what)
        leading outer {values with syn:=.object syn}
        (suffix.push (EnvironmentAppend.hasAdded (afterAssignment base objects leading outer values suffix syn)
          has.scopes.closureScope what has.frame.upgrade)) := by
  exact TieredAllocation.returned_has_heap _ objects leading outer {values with syn:=.object syn}
    suffix has.scopes.closureScope what has.frame.upgrade (some has.function) rfl

end CookieClicker.JavaScript.SynergyBody

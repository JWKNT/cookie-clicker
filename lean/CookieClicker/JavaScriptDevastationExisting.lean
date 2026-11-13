import CookieClicker.JavaScriptDevastationWrite

/-! The complete existing-buff arm selected from the original sell body.
The diamond, ruby and jade guards retain their original branch order. -/
namespace CookieClicker.JavaScript.DevastationExisting
open SourceRead DevastationWrite
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def test (level : UInt64) : Expr :=
  .binary .equal (.identifier "godLvl") (.literal (.number level))

def diamond : UInt64 := 4576918229304087675
def ruby : UInt64 := 4572414629676717179
def jade : UInt64 := 4567911030049346683

def selection : Stmt :=
  .ifThenElse (test Number.one) (assignment diamond) (some
    (.ifThenElse (test 4611686018427387904) (assignment ruby) (some
      (.ifThenElse (test 4613937818241073152) (assignment jade) none))))

def sourceBody : Stmt := match GodzamokSyntax.sellBody with
  | .block statements => match (statements[6]? : Option Stmt) with
    | some (.ifThenElse _ (.block body) _) => match (body[2]? : Option Stmt) with
      | some (.ifThenElse _ yes _) => yes
      | _ => .empty
    | _ => .empty
  | _ => .empty

theorem source_selection : sourceBody=.block [selection] := rfl

theorem read_test (base : Machine) (level compared : UInt64)
    (entry : Local base "godLvl" (.number level)) :
    Reads base (test compared) (.boolean (Number.equal level compared)) 7 := by
  apply binary_value base .equal (.identifier "godLvl") (.literal (.number compared))
    (.number level) (.number compared) (.boolean (Number.equal level compared))
    3 1 entry.reads (literal base (.number compared)) rfl rfl (by decide)
  rfl

theorem if_true (base : Machine) (condition : Expr) (yes : Stmt) (no : Option Stmt)
    (value : Value) (ticks : Nat) (read : Reads base condition value ticks)
    (truth : truthy value=true) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) {base with control:=.statement (.ifThenElse condition yes no)}=
      Builtins.run fuel {base with control:=.statement yes} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression condition
    continuation:=.ifTest yes no::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep {base with
    control:=.expressionResult (.value value)
    continuation:=.ifTest yes no::base.continuation})=_
  simp [Builtins.builtinStep,step,internalStep,consumeValue,truth]

theorem if_false (base : Machine) (condition : Expr) (yes no : Stmt)
    (value : Value) (ticks : Nat) (read : Reads base condition value ticks)
    (truth : truthy value=false) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) {base with control:=.statement (.ifThenElse condition yes (some no))}=
      Builtins.run fuel {base with control:=.statement no} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression condition
    continuation:=.ifTest yes (some no)::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep {base with
    control:=.expressionResult (.value value)
    continuation:=.ifTest yes (some no)::base.continuation})=_
  simp [Builtins.builtinStep,step,internalStep,consumeValue,truth]

private theorem one_equal : Number.equal Number.one Number.one=true := by decide +kernel
private theorem two_not_one : Number.equal 4611686018427387904 Number.one=false := by decide +kernel
private theorem two_equal : Number.equal 4611686018427387904 4611686018427387904=true := by decide +kernel
private theorem three_not_one : Number.equal 4613937818241073152 Number.one=false := by decide +kernel
private theorem three_not_two : Number.equal 4613937818241073152 4611686018427387904=false := by decide +kernel
private theorem three_equal : Number.equal 4613937818241073152 4613937818241073152=true := by decide +kernel

theorem diamond_selection (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number Number.one)) (fuel : Nat) :
    Builtins.run (30+fuel) {base with control:=.statement selection}=
      Builtins.run fuel (changed base frame diamond) := by
  rw [show 30+fuel=7+2+(21+fuel) by omega]
  change Builtins.run (7+2+(21+fuel)) {base with
    control:=.statement (.ifThenElse (test Number.one) (assignment diamond) _)}=_
  rw [if_true base (test Number.one) (assignment diamond) _ _ 7
    (read_test base Number.one Number.one entry) (by simp [one_equal,truthy])]
  exact actual_assignment base frame diamond fuel

theorem ruby_selection (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number 4611686018427387904)) (fuel : Nat) :
    Builtins.run (39+fuel) {base with control:=.statement selection}=
      Builtins.run fuel (changed base frame ruby) := by
  rw [show 39+fuel=7+2+(7+2+(21+fuel)) by omega]
  change Builtins.run (7+2+(7+2+(21+fuel))) {base with
    control:=.statement (.ifThenElse (test Number.one) (assignment diamond) (some _))}=_
  rw [if_false base (test Number.one) (assignment diamond) _ _ 7
    (read_test base 4611686018427387904 Number.one entry) (by simp [two_not_one,truthy])]
  rw [if_true base (test 4611686018427387904) (assignment ruby) _ _ 7
    (read_test base 4611686018427387904 4611686018427387904 entry) (by simp [two_equal,truthy])]
  exact actual_assignment base frame ruby fuel

theorem jade_selection (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number 4613937818241073152)) (fuel : Nat) :
    Builtins.run (48+fuel) {base with control:=.statement selection}=
      Builtins.run fuel (changed base frame jade) := by
  rw [show 48+fuel=7+2+(7+2+(7+2+(21+fuel))) by omega]
  change Builtins.run (7+2+(7+2+(7+2+(21+fuel)))) {base with
    control:=.statement (.ifThenElse (test Number.one) (assignment diamond) (some _))}=_
  rw [if_false base (test Number.one) (assignment diamond) _ _ 7
    (read_test base 4613937818241073152 Number.one entry) (by simp [three_not_one,truthy])]
  rw [if_false base (test 4611686018427387904) (assignment ruby) _ _ 7
    (read_test base 4613937818241073152 4611686018427387904 entry) (by simp [three_not_two,truthy])]
  rw [if_true base (test 4613937818241073152) (assignment jade) _ _ 7
    (read_test base 4613937818241073152 4613937818241073152 entry) (by simp [three_equal,truthy])]
  exact actual_assignment base frame jade fuel


theorem diamond_body (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number Number.one)) (fuel : Nat) :
    Builtins.run (32+fuel) {base with control:=.statement sourceBody}=
      Builtins.run fuel (changed base frame diamond) := by
  rw [source_selection,show 32+fuel=1+(30+(1+fuel)) by omega,
    Nat.add_comm 1 (30+(1+fuel))]
  let start : Machine := {base with continuation:=.statementList [] none::base.continuation}
  change Builtins.run (30+(1+fuel)) {start with control:=.statement selection}=_
  rw [diamond_selection start {frame with oldLocal:={frame.oldLocal with},soldLocal:={frame.soldLocal with}} {entry with},Nat.add_comm 1 fuel]
  rfl

theorem ruby_body (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number 4611686018427387904)) (fuel : Nat) :
    Builtins.run (41+fuel) {base with control:=.statement sourceBody}=
      Builtins.run fuel (changed base frame ruby) := by
  rw [source_selection,show 41+fuel=1+(39+(1+fuel)) by omega,
    Nat.add_comm 1 (39+(1+fuel))]
  let start : Machine := {base with continuation:=.statementList [] none::base.continuation}
  change Builtins.run (39+(1+fuel)) {start with control:=.statement selection}=_
  rw [ruby_selection start {frame with oldLocal:={frame.oldLocal with},soldLocal:={frame.soldLocal with}} {entry with},Nat.add_comm 1 fuel]
  rfl

theorem jade_body (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number 4613937818241073152)) (fuel : Nat) :
    Builtins.run (50+fuel) {base with control:=.statement sourceBody}=
      Builtins.run fuel (changed base frame jade) := by
  rw [source_selection,show 50+fuel=1+(48+(1+fuel)) by omega,
    Nat.add_comm 1 (48+(1+fuel))]
  let start : Machine := {base with continuation:=.statementList [] none::base.continuation}
  change Builtins.run (48+(1+fuel)) {start with control:=.statement selection}=_
  rw [jade_selection start {frame with oldLocal:={frame.oldLocal with},soldLocal:={frame.soldLocal with}} {entry with},Nat.add_comm 1 fuel]
  rfl


def sourceOldConditional : Stmt := match GodzamokSyntax.sellBody with
  | .block statements => match (statements[6]? : Option Stmt) with
    | some (.ifThenElse _ (.block body) _) => (body[2]?).getD .empty
    | _ => .empty
  | _ => .empty

def sourceNewBody : Stmt := match sourceOldConditional with
  | .ifThenElse _ _ (some no) => no
  | _ => .empty

theorem source_old_test : sourceOldConditional=
    .ifThenElse (.identifier "old") sourceBody (some sourceNewBody) := rfl

theorem diamond_existing (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number Number.one)) (fuel : Nat) :
    Builtins.run (37+fuel) {base with control:=.statement sourceOldConditional}=
      Builtins.run fuel (changed base frame diamond) := by
  rw [source_old_test,show 37+fuel=3+2+(32+fuel) by omega,
    if_true base (.identifier "old") sourceBody (some sourceNewBody)
      (.object frame.id) 3 frame.oldLocal.reads rfl]
  exact diamond_body base frame entry fuel

theorem ruby_existing (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number 4611686018427387904)) (fuel : Nat) :
    Builtins.run (46+fuel) {base with control:=.statement sourceOldConditional}=
      Builtins.run fuel (changed base frame ruby) := by
  rw [source_old_test,show 46+fuel=3+2+(41+fuel) by omega,
    if_true base (.identifier "old") sourceBody (some sourceNewBody)
      (.object frame.id) 3 frame.oldLocal.reads rfl]
  exact ruby_body base frame entry fuel

theorem jade_existing (base : Machine) (frame : DevastationWrite.Frame base)
    (entry : Local base "godLvl" (.number 4613937818241073152)) (fuel : Nat) :
    Builtins.run (55+fuel) {base with control:=.statement sourceOldConditional}=
      Builtins.run fuel (changed base frame jade) := by
  rw [source_old_test,show 55+fuel=3+2+(50+fuel) by omega,
    if_true base (.identifier "old") sourceBody (some sourceNewBody)
      (.object frame.id) 3 frame.oldLocal.reads rfl]
  exact jade_body base frame entry fuel

end CookieClicker.JavaScript.DevastationExisting

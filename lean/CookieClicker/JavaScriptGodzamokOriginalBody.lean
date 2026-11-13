import CookieClicker.JavaScriptGodzamokOriginalEntry

/-! Complete retained Godzamok existing-buff branch. Both allocating helper
calls and both caller-variable writes precede the original diamond update. -/
namespace CookieClicker.JavaScript.GodzamokOriginalBody
open SourceRead GodzamokOriginalEntry GodzamokInitializers
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def guard : Expr := .logical .and (.identifier "success")
  (.member (.identifier "Game") (.identifier "hasGod") false)
def body : Stmt := .block [godStatement,buffStatement,DevastationExisting.sourceOldConditional]
def branch : Stmt := match GodzamokSyntax.sellBody with
  | .block statements => statements[6]?.getD .empty
  | _ => .empty

theorem source_branch : branch=.ifThenElse guard body none := rfl

theorem true_and (base : Machine) (left right : Expr) (a value : Value)
    (leftTicks rightTicks : Nat) (readLeft : Reads base left a leftTicks)
    (readRight : Reads base right value rightTicks) (truth : truthy a=true) :
    Reads base (.logical .and left right) value (leftTicks+rightTicks+3) := by
  intro continuation consumer fuel
  conv => lhs; arg 1; rw [show leftTicks+rightTicks+3+fuel=
    (leftTicks+(1+(rightTicks+(1+fuel))))+1 by omega]
  change Builtins.run (leftTicks+(1+(rightTicks+(1+fuel)))) {base with
    control:=.expression left,continuation:=.logical .and right::continuation}=_
  refine (readLeft _ (by rfl) (1+(rightTicks+(1+fuel)))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (rightTicks+(1+fuel))]
  have nextStep : Builtins.builtinStep {base with
      control:=.expressionResult (.value a),continuation:=.logical .and right::continuation}=
      {base with control:=.expression right,continuation:=.valueBoundary::continuation} := by
    simp [Builtins.builtinStep,step,internalStep,consumeValue,truth,pushExpression]
  change Builtins.run (rightTicks+(1+fuel)) (Builtins.builtinStep _) =_
  conv => lhs; arg 2; rw [nextStep]
  refine (readRight _ (by rfl) (1+fuel)).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

theorem guard_read {base : Machine} (entry : Entry base) :
    Reads base guard (.object entry.godFunction) 13 := by
  apply true_and base (.identifier "success") _ entry.success (.object entry.godFunction)
    3 7 entry.successLocal.reads _ entry.successTruthy
  exact dot base (.identifier "Game") entry.game "hasGod" (.object entry.godFunction)
    entry.pantheon.gameObject 3
    (entry.pantheon.window.read base (HeapExtension.refl base.heap)
      entry.pantheon.callerPath entry.pantheon.exclusions)
    entry.pantheon.gamePresent (Or.inl entry.pantheon.gameKind) entry.pantheon.method

theorem actual_body {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (297+fuel) {base with control:=.statement body}=
      Builtins.run fuel entry.changed := by
  let firstBase:={base with
    continuation:=.statementList [buffStatement,DevastationExisting.sourceOldConditional] none::base.continuation}
  let first:=entry.withContinuation firstBase.continuation
  conv => lhs; arg 1; rw [show 297+fuel=(196+(1+(60+(1+(37+(1+fuel))))))+1 by omega]
  change Builtins.run (196+(1+(60+(1+(37+(1+fuel))))))
    {firstBase with control:=.statement godStatement}=_
  refine (actual_god_initializer first.pantheon first.godLvlSlot (1+(60+(1+(37+(1+fuel)))))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (60+(1+(37+(1+fuel))))]
  let secondBase:={entry.afterGod with
    continuation:=.statementList [DevastationExisting.sourceOldConditional] none::base.continuation}
  let second:=entry.buffAfterGod.withContinuation secondBase.continuation
  let oldSlot:=entry.oldAfterGod.withContinuation secondBase.continuation
  change Builtins.run (60+(1+(37+(1+fuel))))
    {secondBase with control:=.statement buffStatement}=_
  refine (actual_buff_initializer second oldSlot (1+(37+(1+fuel)))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (37+(1+fuel))]
  let finalBase:={entry.afterCalls with continuation:=.statementList [] none::base.continuation}
  let finalFrame : DevastationWrite.Frame finalBase := {
    entry.finalFrame with oldLocal:={entry.finalFrame.oldLocal with},soldLocal:={entry.finalFrame.soldLocal with}}
  let finalLevel : DevastationWrite.Local finalBase "godLvl" (.number Number.one) := {entry.levelAfterCalls with}
  change Builtins.run (37+(1+fuel)) {finalBase with control:=.statement DevastationExisting.sourceOldConditional}=_
  refine (DevastationExisting.diamond_existing finalBase finalFrame finalLevel (1+fuel)).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

theorem actual_branch {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (312+fuel) {base with control:=.statement branch}=
      Builtins.run fuel entry.changed := by
  conv => lhs; arg 2; rw [source_branch]
  conv => lhs; arg 1; rw [show 312+fuel=13+2+(297+fuel) by omega]
  refine (DevastationExisting.if_true base guard body none (.object entry.godFunction)
    13 (guard_read entry) rfl (297+fuel)).trans ?_
  exact actual_body entry fuel

end CookieClicker.JavaScript.GodzamokOriginalBody

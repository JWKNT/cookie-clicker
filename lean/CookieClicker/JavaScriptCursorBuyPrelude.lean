import CookieClicker.JavaScriptCursorBuyClauses

namespace CookieClicker.JavaScript.CursorBuyPrelude
open SourceRead TieredRead CursorBuyRead CursorBuyClauses
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem true_expression (base : Machine) (test expression : Expr)
    (condition : Reads base test (.boolean true) 9) (fuel : Nat) :
    Builtins.run (12+fuel) {base with control:=.statement (.ifThenElse test (.expression expression) none)}=
      Builtins.run fuel {base with
        control:=.expression expression
        continuation:=.expressionStatement::base.continuation} := by
  rw [show 12+fuel=1+(9+(2+fuel)) by omega,Nat.add_comm 1 (9+(2+fuel))]
  change Builtins.run (9+(2+fuel)) {base with
    control:=.expression test
    continuation:=.ifTest (.expression expression) none::base.continuation}=_
  rw [condition _ (by rfl),Nat.add_comm 2 fuel]
  rfl

theorem true_guard (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) :
    Reads base (guard Number.one) (.boolean true) 9 :=
  guard_read base cursor Number.one true receiver edge (by rfl)

def firstContinuation (base : Machine) : List Frame :=
  .expressionStatement::.statementList (middle++winClause::tailClauses) none::base.continuation

def winContinuation (base : Machine) : List Frame :=
  .expressionStatement::.statementList tailClauses (some .undefined)::base.continuation

theorem source_first_call (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (13+fuel) {base with control:=.statement BuildingCallbackSyntax.cursorBuyBody}=
      Builtins.run fuel {base with
        control:=.expression (MemberCall.expression "Unlock" (ArrayPair.expression firstName secondName))
        continuation:=firstContinuation base} := by
  rw [source_split,show 13+fuel=1+(12+fuel) by omega,Nat.add_comm 1 (12+fuel)]
  change Builtins.run (12+fuel) {base with
    control:=.statement firstClause
    continuation:=.statementList (middle++winClause::tailClauses) none::base.continuation}=_
  rw [source_first]
  exact true_expression {base with continuation:=.statementList (middle++winClause::tailClauses) none::base.continuation}
    (guard Number.one) _ (true_guard base cursor receiver edge) fuel

theorem expression_next (base : Machine) (remaining : List Stmt)
    (previous : Option Value) (fuel : Nat) :
    Builtins.run (2+fuel) {base with
      control:=.expressionResult (.value .undefined)
      continuation:=.expressionStatement::.statementList remaining previous::base.continuation}=
      Builtins.run fuel (statements base remaining (some .undefined)) := by
  cases remaining <;> rw [Nat.add_comm 2 fuel] <;> rfl

theorem source_win_call (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (168+fuel) (statements base (middle++winClause::tailClauses) (some .undefined))=
      Builtins.run fuel {base with
        control:=.expression (MemberCall.expression "Win" (.literal (.string clickName)))
        continuation:=winContinuation base} := by
  rw [show 168+fuel=12*middle.length+(12+fuel) by rw [middle_length];omega,
    false_prefix base middle (winClause::tailClauses) (some .undefined)
      (middle_conditions base cursor receiver edge)]
  change Builtins.run (12+fuel) {base with
    control:=.statement winClause
    continuation:=.statementList tailClauses (some .undefined)::base.continuation}=_
  rw [source_win]
  exact true_expression {base with continuation:=.statementList tailClauses (some .undefined)::base.continuation}
    (guard Number.one) _ (true_guard base cursor receiver edge) fuel

theorem source_tail (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (144+fuel) (statements base tailClauses (some .undefined))=
      Builtins.run fuel {base with control:=.completion (.normal (some .undefined))} := by
  simpa only [tail_length,List.append_nil,statements,complete] using
    false_prefix base tailClauses [] (some .undefined) (tail_conditions base cursor receiver edge) fuel

end CookieClicker.JavaScript.CursorBuyPrelude

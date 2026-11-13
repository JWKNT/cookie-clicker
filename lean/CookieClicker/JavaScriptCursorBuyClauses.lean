import CookieClicker.JavaScriptCursorBuyRead
import CookieClicker.JavaScriptArrayPairCall

namespace CookieClicker.JavaScript.CursorBuyClauses
open SourceRead TieredRead CursorBuyRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def firstName : JSString := JSString.ofString "Reinforced index finger"
def secondName : JSString := JSString.ofString "Carpal tunnel prevention cream"
def clickName : JSString := JSString.ofString "Click"
def clauses : List Stmt := match BuildingCallbackSyntax.cursorBuyBody with | .block statements=>statements | _=>[]
def firstClause : Stmt := clauses.headD .empty
def middle : List Stmt := (clauses.drop 1).take 13
def winClause : Stmt := (clauses.drop 14).headD .empty
def tailClauses : List Stmt := clauses.drop 15

theorem source_split : BuildingCallbackSyntax.cursorBuyBody=
    .block (firstClause::(middle++winClause::tailClauses)) := rfl

theorem source_first : firstClause=.ifThenElse (guard Number.one)
    (.expression (MemberCall.expression "Unlock" (ArrayPair.expression firstName secondName))) none := rfl

theorem source_win : winClause=.ifThenElse (guard Number.one)
    (.expression (MemberCall.expression "Win" (.literal (.string clickName)))) none := rfl

def falseValue : Checked Value → Bool
  | .ok (.boolean false) => true
  | _ => false

theorem false_value_sound (result : Checked Value) (checked : falseValue result=true) :
    result=.ok (.boolean false) := by
  unfold falseValue at checked
  split at checked <;> simp_all

def falseClauseCheck : Stmt → Bool
  | .ifThenElse (.binary .greaterEqual (.member .this (.identifier "amount") false) (.literal (.number threshold))) _ none =>
    falseValue (binaryWithHeap ({} : Heap) .greaterEqual (.number Number.one) (.number threshold))
  | _ => false

theorem middle_checked : middle.all falseClauseCheck=true := by decide +kernel
theorem tail_checked : tailClauses.all falseClauseCheck=true := by decide +kernel

theorem checked_read (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one))
    (statement : Stmt) (verified : falseClauseCheck statement=true) :
    ∃ test body,statement=.ifThenElse test body none ∧ Reads base test (.boolean false) 9 := by
  unfold falseClauseCheck at verified
  split at verified
  · rename_i threshold body
    refine ⟨guard threshold,body,rfl,?_⟩
    exact guard_read base cursor threshold false receiver edge (false_value_sound _ verified)
  · contradiction

theorem middle_conditions (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) :
    ∀ statement∈middle,∃ test body,statement=.ifThenElse test body none ∧ Reads base test (.boolean false) 9 := by
  intro statement member
  exact checked_read base cursor receiver edge statement ((List.all_eq_true.mp middle_checked) statement member)

theorem tail_conditions (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) :
    ∀ statement∈tailClauses,∃ test body,statement=.ifThenElse test body none ∧ Reads base test (.boolean false) 9 := by
  intro statement member
  exact checked_read base cursor receiver edge statement ((List.all_eq_true.mp tail_checked) statement member)

theorem middle_length : middle.length=13 := rfl
theorem tail_length : tailClauses.length=12 := rfl

end CookieClicker.JavaScript.CursorBuyClauses

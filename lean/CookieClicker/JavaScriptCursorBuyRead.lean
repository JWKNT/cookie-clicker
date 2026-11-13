import CookieClicker.JavaScriptReadCombinators
import CookieClicker.JavaScriptBuildingCallbackSyntax

namespace CookieClicker.JavaScript.CursorBuyRead
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def guard (threshold : UInt64) : Expr :=
  .binary .greaterEqual (.member .this (.identifier "amount") false) (.literal (.number threshold))

theorem this_read (base : Machine) : Reads base .this base.context.thisValue 1 := by
  intro continuation ordinary fuel
  rw [Nat.add_comm 1 fuel]
  rfl

theorem amount_read (base : Machine) (cursor : ObjectId)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) :
    Reads base (.member .this (.identifier "amount") false) (.number Number.one) 5 := by
  exact edge.dot _ 1 (by simpa only [receiver] using this_read base)

theorem guard_read (base : Machine) (cursor : ObjectId) (threshold : UInt64) (answer : Bool)
    (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one))
    (computed : binaryWithHeap base.heap .greaterEqual (.number Number.one) (.number threshold)=.ok (.boolean answer)) :
    Reads base (guard threshold) (.boolean answer) 9 := by
  exact binary_value base .greaterEqual _ _ _ _ _ 5 1 (amount_read base cursor receiver edge)
    (literal base (.number threshold)) rfl rfl (by decide) computed

/-- An intact false source clause returns its empty normal completion. -/
theorem false_clause (base : Machine) (test : Expr) (body : Stmt)
    (condition : Reads base test (.boolean false) 9) (fuel : Nat) :
    Builtins.run (11+fuel) {base with control:=.statement (.ifThenElse test body none)}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  rw [show 11+fuel=1+(9+(1+fuel)) by omega,Nat.add_comm 1 (9+(1+fuel))]
  change Builtins.run (9+(1+fuel)) {base with
    control:=.expression test
    continuation:=.ifTest body none::base.continuation}=_
  rw [condition _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem statement_next (base : Machine) (remaining : List Stmt) (previous : Option Value) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal none)
      continuation:=.statementList remaining previous::base.continuation}=
      Builtins.run fuel (statements base remaining previous) := by
  cases remaining <;> rw [Nat.add_comm 1 fuel] <;> rfl

/-- A source leading of false clauses preserves the caller's previous statement
value and proceeds to the actual suffix, without constructing another block. -/
theorem false_prefix (base : Machine) (leading suffix : List Stmt) (previous : Option Value)
    (conditions : ∀ statement∈leading,∃ test body,
      statement=.ifThenElse test body none ∧ Reads base test (.boolean false) 9) (fuel : Nat) :
    Builtins.run (12*leading.length+fuel) (statements base (leading++suffix) previous)=
      Builtins.run fuel (statements base suffix previous) := by
  induction leading with
  | nil => simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.nil_append]
  | cons statement leading ih =>
    obtain ⟨test,body,form,condition⟩:=conditions statement (by simp)
    have rest : ∀ statement∈leading,∃ test body,
        statement=.ifThenElse test body none ∧ Reads base test (.boolean false) 9 := by
      intro statement member;exact conditions statement (by simp [member])
    rw [show 12*(statement::leading).length+fuel=11+(1+(12*leading.length+fuel)) by simp only [List.length_cons];omega]
    simp only [List.cons_append,statements,pushStatement]
    rw [form]
    rw [false_clause {base with continuation:=.statementList (leading++suffix) previous::base.continuation}
      test body condition]
    change Builtins.run (1+(12*leading.length+fuel)) {base with
      control:=.completion (.normal none)
      continuation:=.statementList (leading++suffix) previous::base.continuation}=_
    rw [statement_next]
    exact ih rest

end CookieClicker.JavaScript.CursorBuyRead

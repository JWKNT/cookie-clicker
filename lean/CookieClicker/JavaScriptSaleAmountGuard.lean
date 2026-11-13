import CookieClicker.JavaScriptSaleNumericSource

/-! The successful-sale arithmetic starts only after the original native
amount test. Both branches read the actual amount property with native Number
comparison; a nonpositive or unordered amount cannot enter this block. -/
namespace CookieClicker.JavaScript.SaleAmountGuard
open SourceRead SaleNumericFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def test : Expr := .binary .greater (.member .this (.identifier "amount") false) (.literal (.number 0))
def statement : Stmt := (SaleNumericSource.loopBody[3]?).getD .empty

theorem amount_read {base : Machine} (entry : Entry base) :
    Reads base (.member .this (.identifier "amount") false) (.number entry.amount) 5 := by
  let edge : TieredRead.DataEdge base entry.building (JSString.ofString "amount") (.number entry.amount) := {
    object:=entry.buildingObject
    present:=by simp [checkedObject,entry.buildingPresent]
    kind:=Or.inl entry.buildingKind
    property:=entry.amountLookup }
  apply edge.dot _ 1
  simpa only [entry.receiver] using CursorGetPriceRead.this_read base

theorem source_read {base : Machine} (entry : Entry base) :
    Reads base test (.boolean (Number.lessThan 0 entry.amount)) 9 :=
  binary_value base .greater _ _ (.number entry.amount) (.number 0)
    (.boolean (Number.lessThan 0 entry.amount)) 5 1 (amount_read entry) (literal base (.number 0))
    rfl rfl (by decide) rfl

theorem admitted {base : Machine} (entry : Entry base) (positive : Number.lessThan 0 entry.amount=true) (fuel : Nat) :
    Builtins.run (11+fuel) {base with control:=.statement statement}=
      Builtins.run fuel {base with control:=.statement (.block SaleNumericSource.successBody)} := by
  rw [show 11+fuel=1+(9+(1+fuel)) by omega,Nat.add_comm 1 (9+(1+fuel))]
  change Builtins.run (9+(1+fuel)) {base with
    control:=.expression test
    continuation:=.ifTest (.block SaleNumericSource.successBody) none::base.continuation}=_
  rw [source_read entry _ (by rfl),positive,Nat.add_comm 1 fuel]
  rfl

theorem rejected {base : Machine} (entry : Entry base) (notPositive : Number.lessThan 0 entry.amount=false) (fuel : Nat) :
    Builtins.run (11+fuel) {base with control:=.statement statement}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  rw [show 11+fuel=1+(9+(1+fuel)) by omega,Nat.add_comm 1 (9+(1+fuel))]
  change Builtins.run (9+(1+fuel)) {base with
    control:=.expression test
    continuation:=.ifTest (.block SaleNumericSource.successBody) none::base.continuation}=_
  rw [source_read entry _ (by rfl),notPositive,Nat.add_comm 1 fuel]
  rfl

theorem actual_guarded_prefix {base : Machine} (entry : Entry base)
    (positive : Number.lessThan 0 entry.amount=true) (fuel : Nat) :
    Builtins.run (105+fuel) {base with control:=.statement statement}=
      Builtins.run fuel (SaleNumericSource.atNextPrice entry) := by
  rw [show 105+fuel=11+(94+fuel) by omega,admitted entry positive]
  exact SaleNumericSource.actual_block_prefix entry fuel

end CookieClicker.JavaScript.SaleAmountGuard

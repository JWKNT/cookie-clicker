import CookieClicker.JavaScriptSaleCompleteFrame

namespace CookieClicker.JavaScript.SaleCompleteSource
open SaleCompleteFrame
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

variable {base : Machine} {scope : ObjectId} {price free rate : UInt64}

def ticks (entry : Entry base scope price free rate) : Nat := (tail entry).rowTicks+1466

def after (entry : Entry base scope price free rate) : Machine := (tail entry).changed

theorem actual_remainder (entry : Entry base scope price free rate) (fuel : Nat) :
    Builtins.run ((tail entry).rowTicks+61+fuel) (SaleReprice.after entry.reprice)=
      Builtins.run fuel (after entry) := by
  conv => lhs;arg 1;rw [show (tail entry).rowTicks+61+fuel=((tail entry).rowTicks+60+fuel)+1 by omega]
  change Builtins.run ((tail entry).rowTicks+60+fuel)
    (SaleTailSource.atPriceWrite (tail entry) (some (.number (SaleRepriceFields.quoted entry.reprice))))=_
  exact SaleTailSource.actual_suffix (tail entry) (some (.number (SaleRepriceFields.quoted entry.reprice))) fuel

theorem actual_block (entry : Entry base scope price free rate) (fuel : Nat) :
    Builtins.run (ticks entry+fuel) {base with control:=.statement (.block SaleNumericSource.successBody)}=
      Builtins.run fuel (after entry) := by
  conv => lhs;arg 1;rw [show ticks entry+fuel=1405+((tail entry).rowTicks+61+fuel) by simp only [ticks];omega]
  refine (SaleReprice.actual_prefix entry.reprice ((tail entry).rowTicks+61+fuel)).trans ?_
  exact actual_remainder entry fuel

theorem actual_guarded_block (entry : Entry base scope price free rate)
    (positive : Number.lessThan 0 entry.reprice.numeric.amount=true) (fuel : Nat) :
    Builtins.run (ticks entry+11+fuel) {base with control:=.statement SaleAmountGuard.statement}=
      Builtins.run fuel (after entry) := by
  conv => lhs;arg 1;rw [show ticks entry+11+fuel=11+(ticks entry+fuel) by omega]
  refine (SaleAmountGuard.admitted entry.reprice.numeric positive (ticks entry+fuel)).trans ?_
  exact actual_block entry fuel

theorem step_count (entry : Entry base scope price free rate) :
    ticks entry=if Number.equal (Number.sub entry.reprice.numeric.amount Number.one) 0 then 1487 else 1477 := by
  simp only [ticks,SaleTailFrame.Entry.rowTicks,tail]
  split <;> simp_all

end CookieClicker.JavaScript.SaleCompleteSource

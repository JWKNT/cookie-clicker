import CookieClicker.JavaScriptSaleNumericCatalogue
import CookieClicker.JavaScriptSalePriceAssignment
import CookieClicker.JavaScriptSaleAmountGuard

/-! The successful sale's five native numeric writes feed its actual second
getPrice call. The new call's complete catalogue and price slot are derived
from the original entry, rather than assumed after the economic changes. -/
namespace CookieClicker.JavaScript.SaleReprice
open CursorQuoteCatalogue
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

structure Entry (base : Machine) (scope : ObjectId) (price free rate : UInt64) where
  numeric : SaleNumericFrame.Entry base
  catalogue : Catalogue base scope numeric.building price numeric.amount free rate
  names : SaleNumericCatalogue.Names catalogue
  slot : SourceBinding.Slot base "price"
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (CursorGetPriceSource.closure scope source)
  functionNotGame : function≠numeric.counter.game
  functionNotBuilding : function≠numeric.building
  method : lookupProperty base.heap numeric.building (JSString.ofString "getPrice")=
    .ok (some (.data (.object function) true true true))
  stable : Number.mul (CursorGetPriceRead.rawValue price (Number.sub numeric.amount Number.one) free rate) Number.one=
    CursorGetPriceRead.rawValue price (Number.sub numeric.amount Number.one) free rate

variable {base : Machine} {scope : ObjectId} {price free rate : UInt64}

def retainedCatalogue (entry : Entry base scope price free rate) :
    Catalogue entry.numeric.afterAmount scope entry.numeric.building price (Number.sub entry.numeric.amount Number.one) free rate := by
  rw [←SaleNumericWrites.amount_machine entry.numeric]
  exact SaleNumericCatalogue.afterAmount entry.numeric entry.catalogue entry.names

def callBase (entry : Entry base scope price free rate) : Machine := {
  entry.numeric.afterAmount with
  continuation:=.statementList (SaleNumericSource.successBody.drop 6) (some (.number entry.numeric.amount))::base.continuation }

def priceSlot (entry : Entry base scope price free rate) : SourceBinding.Slot (callBase entry) "price" :=
  {entry.numeric.nextMoniSlot.otherSlot
    (entry.numeric.soldSlot.otherSlot entry.slot (by decide) (.number entry.numeric.newSold))
    (by decide) (.number entry.numeric.newMoni) with}

def callEntry (entry : Entry base scope price free rate) :
    SalePriceAssignment.Entry (callBase entry) scope entry.numeric.building price (Number.sub entry.numeric.amount Number.one) free rate := {
  catalogue:=CursorGetPriceCatalogue.recontext (retainedCatalogue entry)
    entry.numeric.afterAmount.context (callBase entry).continuation
  slot:=priceSlot entry,function:=entry.function,stable:=entry.stable,source:=entry.source
  cursorObject:=setOwnProperty entry.numeric.buildingObject (JSString.ofString "amount")
    (.data (.number (Number.sub entry.numeric.amount Number.one)) true true true)
  functionObject:=entry.functionObject
  receiver:=entry.numeric.receiver
  cursorPresent:=by
    have kept:=SaleNumericPreservation.building_object entry.numeric
    change (callBase entry).heap.object? entry.numeric.building=_ at kept
    simp [checkedObject,kept]
  cursorKind:=by simpa only [PropertyFrame.set_kind] using entry.numeric.buildingKind
  method:=SaleNumericPreservation.other_property entry.numeric entry.numeric.building (JSString.ofString "getPrice")
    (by decide) (by decide) (by decide) _ entry.method
  functionPresent:=by
    have kept:=SaleNumericPreservation.other_object entry.numeric entry.function entry.functionNotGame entry.functionNotBuilding
    change (callBase entry).heap.object? entry.function=base.heap.object? entry.function at kept
    simpa only [checkedObject,kept] using entry.functionPresent
  functionKind:=entry.functionKind }

def after (entry : Entry base scope price free rate) : Machine := SalePriceAssignment.after (callEntry entry)

theorem actual_prefix (entry : Entry base scope price free rate) (fuel : Nat) :
    Builtins.run (1405+fuel) {base with control:=.statement (.block SaleNumericSource.successBody)}=
      Builtins.run fuel (after entry) := by
  rw [show 1405+fuel=94+(1311+fuel) by omega,SaleNumericSource.actual_block_prefix entry.numeric]
  exact SalePriceAssignment.source_assignment (callEntry entry) fuel

theorem actual_guarded_prefix (entry : Entry base scope price free rate)
    (positive : Number.lessThan 0 entry.numeric.amount=true) (fuel : Nat) :
    Builtins.run (1416+fuel) {base with control:=.statement SaleAmountGuard.statement}=
      Builtins.run fuel (after entry) := by
  rw [show 1416+fuel=11+(1405+fuel) by omega,SaleAmountGuard.admitted entry.numeric positive]
  exact actual_prefix entry fuel

end CookieClicker.JavaScript.SaleReprice

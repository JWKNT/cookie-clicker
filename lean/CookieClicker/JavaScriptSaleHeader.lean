import CookieClicker.JavaScriptSalePriceRetention
import CookieClicker.JavaScriptSaleMultiplierInitializer
import CookieClicker.JavaScriptSaleFloor

/-! The intact sale-loop header derives its second allocating call from the
original entry and the actual heap and caller binding left by getPrice. -/
namespace CookieClicker.JavaScript.SaleHeader
open SourceBinding PriceRegistryScope
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

structure Entry (base : Machine) (scope cursor : ObjectId) (price owned free rate : UInt64) where
  first : SalePriceInitializer.Entry base scope cursor price owned free rate
  multiplierScope : ClosureScope base
  giveBack : Slot base "giveBack"
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  method : lookupProperty base.heap cursor (JSString.ofString "getSellMultiplier")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (CursorSellSource.closure multiplierScope.path.closureScope source)

variable {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}

def priceEntry (entry : Entry base scope cursor price owned free rate) :=
  SalePriceRetention.withContinuation entry.first
    (.statementList (SaleNumericSource.loopBody.drop 1) none::base.continuation)

def multiplierContinuation (base : Machine) : List Frame :=
  .statementList (SaleNumericSource.loopBody.drop 2) none::base.continuation

def multiplierBase (entry : Entry base scope cursor price owned free rate) : Machine :=
  {SalePriceInitializer.after (priceEntry entry) with continuation:=multiplierContinuation base}

def multiplierEntry (entry : Entry base scope cursor price owned free rate) :
    SaleMultiplierInitializer.Entry (multiplierBase entry) cursor := by
  let original:=priceEntry entry
  let kept:=SalePriceRetention.original_objects original (multiplierContinuation base)
  exact {
    world:=SalePriceRetention.world original (multiplierContinuation base)
    scope:=SalePriceRetention.closure original (multiplierContinuation base) {entry.multiplierScope with}
    slot:=SalePriceRetention.otherSlot original (multiplierContinuation base)
      (entry.giveBack.withContinuation _) (by decide)
    function:=entry.function,source:=entry.source
    cursorObject:=entry.first.cursorObject,functionObject:=entry.functionObject
    receiver:=entry.first.receiver
    cursorPresent:=HeapExtension.checked_object kept _ _ entry.first.cursorPresent
    cursorKind:=entry.first.cursorKind
    method:=HeapExtension.lookup_property kept _ _ _ entry.method
    functionPresent:=HeapExtension.checked_object kept _ _ entry.functionPresent
    functionKind:=by
      simpa only [SalePriceRetention.closure,PriceRegistryAdvance.Advance.scope_id,
        PriceRegistryBinding.scope_id] using entry.functionKind }

def floorBase (entry : Entry base scope cursor price owned free rate) : Machine :=
  {SaleMultiplierInitializer.after (multiplierEntry entry) with
    control:=.statement SaleFloor.statement
    continuation:=.statementList (SaleNumericSource.loopBody.drop 3) none::base.continuation}

theorem actual_header (entry : Entry base scope cursor price owned free rate) (fuel : Nat) :
    Builtins.run (1519+fuel) {base with control:=.statement (.block SaleNumericSource.loopBody)}=
      Builtins.run fuel (floorBase entry) := by
  rw [show 1519+fuel=1+(1308+(1+(208+(1+fuel)))) by omega,Nat.add_comm 1 (1308+(1+(208+(1+fuel))))]
  change Builtins.run (1308+(1+(208+(1+fuel))))
    { {base with continuation:=.statementList (SaleNumericSource.loopBody.drop 1) none::base.continuation} with
      control:=.statement (.variable [("price",some CursorGetPriceCall.expression)])}=_
  rw [SalePriceInitializer.source_initializer (priceEntry entry),Nat.add_comm 1 (208+(1+fuel))]
  change Builtins.run (208+(1+fuel)) {multiplierBase entry with
    control:=.statement (.variable [("giveBack",some CursorSellCall.expression)])}=_
  rw [SaleMultiplierInitializer.source_initializer (multiplierEntry entry),Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.SaleHeader

import CookieClicker.JavaScriptSaleRepriceFields

namespace CookieClicker.JavaScript.SaleCompleteFrame
open SaleRepriceFields
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) (scope : ObjectId) (price free rate : UInt64) where
  reprice : SaleReprice.Entry base scope price free rate
  owned : UInt64
  priceSlot : BuildingStore.Slot base (JSString.ofString "price")
  priceId : priceSlot.id=reprice.numeric.building
  recalculate : BuildingStore.Slot base (JSString.ofString "recalculateGains")
  recalculateId : recalculate.id=reprice.numeric.counter.game
  buildingsOwned : BuildingStore.Slot base (JSString.ofString "BuildingsOwned")
  ownedId : buildingsOwned.id=reprice.numeric.counter.game
  ownedValue : buildingsOwned.oldValue=.number owned
  successSlot : SourceBinding.Slot base "success"
  sellFunctionValue : Value
  sellFunction : TieredRead.DataEdge base reprice.numeric.building (JSString.ofString "sellFunction") sellFunctionValue
  noSellFunction : truthy sellFunctionValue=false
  idEdge : TieredRead.DataEdge base reprice.numeric.building (JSString.ofString "id") (.number Number.positiveZero)

variable {base : Machine} {scope : ObjectId} {price free rate : UInt64}

def propertySlot (entry : Entry base scope price free rate) {key : JSString} (original : BuildingStore.Slot base key)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : BuildingStore.Slot (tailBase entry.reprice) key :=
  retainedSlot _ (call_objects entry.reprice) (numericSlot entry.reprice.numeric original cookies earned amount)

theorem propertySlot_id (entry : Entry base scope price free rate) {key : JSString} (original : BuildingStore.Slot base key)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : (propertySlot entry original cookies earned amount).id=original.id :=
by simp only [propertySlot,retainedSlot_id,numericSlot_id]

theorem propertySlot_value (entry : Entry base scope price free rate) {key : JSString} (original : BuildingStore.Slot base key)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : (propertySlot entry original cookies earned amount).oldValue=original.oldValue :=
by simp only [propertySlot,retainedSlot_value,numericSlot_value]

def originalWindow (entry : Entry base scope price free rate) :
    OriginalNamePath.Window base "Game" (.object entry.reprice.numeric.counter.game) := {
  id:=entry.reprice.numeric.counter.window,object:=entry.reprice.numeric.counter.windowObject
  present:=by rw [entry.reprice.numeric.originalHeap];exact CounterObjects.checked_window _ _
  kind:=entry.reprice.numeric.counter.windowKind
  writable:=true,enumerable:=true,configurable:=false
  property:=by rw [entry.reprice.numeric.originalHeap];exact CounterObjects.game_binding _ _ }

def gameWindow (entry : Entry base scope price free rate) :
    OriginalNamePath.Window (tailBase entry.reprice) "Game" (.object entry.reprice.numeric.counter.game) :=
  retainedWindow _ (call_objects entry.reprice)
    (numericWindow entry.reprice.numeric (originalWindow entry) (by decide) (by decide) (by decide))

theorem window_id (entry : Entry base scope price free rate) :
    (gameWindow entry).id=entry.reprice.numeric.counter.window :=
by simp only [gameWindow,retainedWindow_id,numericWindow_id,originalWindow]

theorem context (entry : Entry base scope price free rate) : (tailBase entry.reprice).context=base.context := by
  simp only [tailBase,SaleReprice.after,SalePriceAssignment.after,AllocatingAssignment.after,
    AllocatingInitializer.Result.machine,SourceBinding.Slot.after,SaleReprice.callBase,
    SaleNumericFrame.Entry.afterAmount,SaleNumericFrame.Entry.afterEarned,SaleNumericFrame.Entry.afterMoni,
    SaleNumericFrame.Entry.afterSold]

theorem exclusions (entry : Entry base scope price free rate) : (tailBase entry.reprice).objectEnvironmentExclusions=[] := by
  simpa only [tailBase,SaleReprice.after,SalePriceAssignment.after,AllocatingAssignment.after,
    AllocatingInitializer.Result.machine,SourceBinding.Slot.after,SaleReprice.callBase,
    SaleNumericFrame.Entry.afterAmount,SaleNumericFrame.Entry.afterEarned,SaleNumericFrame.Entry.afterMoni,
    SaleNumericFrame.Entry.afterSold] using entry.reprice.numeric.exclusions

def gamePath (entry : Entry base scope price free rate) :
    OriginalNamePath.Path "Game" (tailBase entry.reprice).heap.environments
      (tailBase entry.reprice).context.lexicalEnvironment (gameWindow entry).id := by
  rw [context,window_id]
  exact path entry.reprice entry.reprice.numeric.gamePath

def amountEdge (entry : Entry base scope price free rate) :
    TieredRead.DataEdge (tailBase entry.reprice) entry.reprice.numeric.building (JSString.ofString "amount")
      (.number (Number.sub entry.reprice.numeric.amount Number.one)) :=
  retainedEdge _ (call_objects entry.reprice) (SaleReprice.retainedCatalogue entry.reprice).arithmetic.amountRead

def tail (entry : Entry base scope price free rate) : SaleTailFrame.Entry (tailBase entry.reprice) := {
  price:=quoted entry.reprice,amount:=Number.sub entry.reprice.numeric.amount Number.one
  owned:=entry.owned,game:=entry.reprice.numeric.counter.game
  priceLocal:=priceLocal entry.reprice
  priceSlot:=propertySlot entry entry.priceSlot (by decide) (by decide) (by decide)
  receiver:=by rw [context,propertySlot_id,entry.priceId];exact entry.reprice.numeric.receiver
  recalculate:=propertySlot entry entry.recalculate (by decide) (by decide) (by decide)
  recalculateId:=(propertySlot_id _ _ _ _ _).trans entry.recalculateId
  buildingsOwned:=propertySlot entry entry.buildingsOwned (by decide) (by decide) (by decide)
  ownedId:=(propertySlot_id _ _ _ _ _).trans entry.ownedId
  ownedValue:=(propertySlot_value _ _ _ _ _).trans entry.ownedValue
  successSlot:=localSlot entry.reprice entry.successSlot (by decide) (by decide) (by decide)
  gameWindow:=gameWindow entry,gamePath:=gamePath entry,exclusions:=exclusions entry
  sellFunctionValue:=entry.sellFunctionValue
  sellFunction:=by
    rw [propertySlot_id,entry.priceId]
    exact retainedEdge _ (call_objects entry.reprice)
      (numericEdge entry.reprice.numeric entry.sellFunction (by decide) (by decide) (by decide))
  noSellFunction:=entry.noSellFunction
  amountEdge:=by rw [propertySlot_id,entry.priceId];exact amountEdge entry
  idEdge:=by
    rw [propertySlot_id,entry.priceId]
    exact retainedEdge _ (call_objects entry.reprice)
      (numericEdge entry.reprice.numeric entry.idEdge (by decide) (by decide) (by decide)) }

end CookieClicker.JavaScript.SaleCompleteFrame

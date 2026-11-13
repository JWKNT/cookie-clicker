import CookieClicker.JavaScriptSaleCompleteSource
import CookieClicker.JavaScriptSaleTailPreservation

namespace CookieClicker.JavaScript.SaleCompletePreservation
open SaleCompleteFrame SaleCompleteSource SaleRepriceFields
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

variable {base : Machine} {scope : ObjectId} {price free rate : UInt64}

def afterCallLocal (entry : Entry base scope price free rate) {name : String} {value : Value}
    (frame : DevastationWrite.Local entry.reprice.numeric.afterAmount name value) (notPrice : name≠"price") :
    DevastationWrite.Local (tailBase entry.reprice) name value :=
  {InitializerReadRetention.otherLocal (SalePriceAssignment.output (SaleReprice.callEntry entry.reprice))
    (SaleReprice.callEntry entry.reprice).slot (.number (quoted entry.reprice)) {frame with} notPrice with}

def soldLocal (entry : Entry base scope price free rate) :
    DevastationWrite.Local (after entry) "sold" (.number entry.reprice.numeric.newSold) :=
  SaleTailPreservation.local_after (tail entry)
    (afterCallLocal entry {SaleNumericPreservation.soldFinal entry.reprice.numeric with} (by decide)) (by decide)

def moniLocal (entry : Entry base scope price free rate) :
    DevastationWrite.Local (after entry) "moni" (.number entry.reprice.numeric.newMoni) :=
  SaleTailPreservation.local_after (tail entry)
    (afterCallLocal entry {SaleNumericPreservation.moniFinal entry.reprice.numeric with} (by decide)) (by decide)

def priceLocal (entry : Entry base scope price free rate) :
    DevastationWrite.Local (after entry) "price" (.number (quoted entry.reprice)) :=
  SaleTailPreservation.local_after (tail entry) (SaleRepriceFields.priceLocal entry.reprice) (by decide)

def originalLocal (entry : Entry base scope price free rate) {name : String} {value : Value}
    (original : DevastationWrite.Local base name value)
    (notSold : name≠"sold") (notMoni : name≠"moni") (notPrice : name≠"price") (notSuccess : name≠"success") :
    DevastationWrite.Local (after entry) name value :=
  SaleTailPreservation.local_after (tail entry)
    (afterCallLocal entry {SaleNumericPreservation.localFinal entry.reprice.numeric
      (GodzamokLocalTransport.localOther entry.reprice.numeric.nextMoniSlot
        (GodzamokLocalTransport.localOther entry.reprice.numeric.soldSlot original notSold
          (.number entry.reprice.numeric.newSold)) notMoni (.number entry.reprice.numeric.newMoni)) with} notPrice) notSuccess

def originalSlot (entry : Entry base scope price free rate) {name : String}
    (original : SourceBinding.Slot base name)
    (notSold : name≠"sold") (notMoni : name≠"moni") (notPrice : name≠"price") (notSuccess : name≠"success") :
    SourceBinding.Slot (after entry) name :=
  SaleTailPreservation.slot_after (tail entry)
    (localSlot entry.reprice original notSold notMoni notPrice) notSuccess

theorem success_read (entry : Entry base scope price free rate) :
    SourceRead.Reads (after entry) (.identifier "success") (.number Number.one) 3 :=
  SaleTailPreservation.success_read (tail entry)

theorem cookies_lookup (entry : Entry base scope price free rate) :
    lookupProperty (after entry).heap entry.reprice.numeric.counter.game (JSString.ofString "cookies")=
      .ok (some (.data (.number entry.reprice.numeric.newCookies) true true true)) :=
  SaleTailPreservation.other_property (tail entry) _ _ _ (by decide) (by decide) (by decide)
    (HeapExtension.lookup_property (call_objects entry.reprice) _ _ _
      (SaleNumericPreservation.cookies_lookup entry.reprice.numeric))

theorem earned_lookup (entry : Entry base scope price free rate) :
    lookupProperty (after entry).heap entry.reprice.numeric.counter.game (JSString.ofString "cookiesEarned")=
      .ok (some (.data (.number entry.reprice.numeric.newEarned) true true true)) :=
  SaleTailPreservation.other_property (tail entry) _ _ _ (by decide) (by decide) (by decide)
    (HeapExtension.lookup_property (call_objects entry.reprice) _ _ _
      (SaleNumericPreservation.earned_lookup entry.reprice.numeric))

theorem amount_lookup (entry : Entry base scope price free rate) :
    lookupProperty (after entry).heap entry.reprice.numeric.building (JSString.ofString "amount")=
      .ok (some (.data (.number (Number.sub entry.reprice.numeric.amount Number.one)) true true true)) :=
  SaleTailPreservation.other_property (tail entry) _ _ _ (by decide) (by decide) (by decide)
    (HeapExtension.lookup_property (call_objects entry.reprice) _ _ _
      (SaleNumericPreservation.amount_lookup entry.reprice.numeric))

theorem price_lookup (entry : Entry base scope price free rate) :
    lookupProperty (after entry).heap entry.reprice.numeric.building (JSString.ofString "price")=
      .ok (some (.data (.number (quoted entry.reprice)) true
        (tail entry).priceSlot.enumerable (tail entry).priceSlot.configurable)) := by
  have found:=SaleTailPreservation.price_lookup (tail entry)
  have id : (tail entry).priceSlot.id=entry.reprice.numeric.building := by
    simp only [tail,propertySlot_id,entry.priceId]
  rw [id] at found
  exact found

theorem recalculate_lookup (entry : Entry base scope price free rate) :
    lookupProperty (after entry).heap entry.reprice.numeric.counter.game (JSString.ofString "recalculateGains")=
      .ok (some (.data (.number Number.one) true
        (tail entry).recalculate.enumerable (tail entry).recalculate.configurable)) :=
  SaleTailPreservation.recalculate_lookup (tail entry)

theorem owned_lookup (entry : Entry base scope price free rate) :
    lookupProperty (after entry).heap entry.reprice.numeric.counter.game (JSString.ofString "BuildingsOwned")=
      .ok (some (.data (.number (Number.sub entry.owned Number.one)) true
        (tail entry).buildingsOwned.enumerable (tail entry).buildingsOwned.configurable)) :=
  SaleTailPreservation.owned_lookup (tail entry)

theorem other_property (entry : Entry base scope price free rate) (id : ObjectId) (key : JSString)
    (descriptor : Option PropertyDescriptor)
    (notCookies : JSString.ofString "cookies"≠key) (notEarned : JSString.ofString "cookiesEarned"≠key)
    (notAmount : JSString.ofString "amount"≠key) (notPrice : JSString.ofString "price"≠key)
    (notRecalculate : JSString.ofString "recalculateGains"≠key) (notOwned : JSString.ofString "BuildingsOwned"≠key)
    (original : lookupProperty base.heap id key=.ok descriptor) :
    lookupProperty (after entry).heap id key=.ok descriptor :=
  SaleTailPreservation.other_property (tail entry) id key descriptor notPrice notRecalculate notOwned
    (HeapExtension.lookup_property (call_objects entry.reprice) id key descriptor
      (SaleNumericPreservation.other_property entry.reprice.numeric id key notCookies notEarned notAmount descriptor original))

def originalPath (entry : Entry base scope price free rate) {name : String} {start : EnvId} {window : ObjectId}
    (original : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name (after entry).heap.environments start window :=
  afterTailPath (tail entry) (path entry.reprice original)

def originalWindow (entry : Entry base scope price free rate) {name : String} {value : Value}
    (original : OriginalNamePath.Window base name value)
    (notCookies : JSString.ofString "cookies"≠JSString.ofString name)
    (notEarned : JSString.ofString "cookiesEarned"≠JSString.ofString name)
    (notAmount : JSString.ofString "amount"≠JSString.ofString name)
    (notPrice : JSString.ofString "price"≠JSString.ofString name)
    (notRecalculate : JSString.ofString "recalculateGains"≠JSString.ofString name)
    (notOwned : JSString.ofString "BuildingsOwned"≠JSString.ofString name) :
    OriginalNamePath.Window (after entry) name value :=
  afterTailWindow (tail entry)
    (retainedWindow _ (call_objects entry.reprice)
      (numericWindow entry.reprice.numeric original notCookies notEarned notAmount)) notPrice notRecalculate notOwned

theorem originalWindow_id (entry : Entry base scope price free rate) {name : String} {value : Value}
    (original : OriginalNamePath.Window base name value)
    (notCookies : JSString.ofString "cookies"≠JSString.ofString name)
    (notEarned : JSString.ofString "cookiesEarned"≠JSString.ofString name)
    (notAmount : JSString.ofString "amount"≠JSString.ofString name)
    (notPrice : JSString.ofString "price"≠JSString.ofString name)
    (notRecalculate : JSString.ofString "recalculateGains"≠JSString.ofString name)
    (notOwned : JSString.ofString "BuildingsOwned"≠JSString.ofString name) :
    (originalWindow entry original notCookies notEarned notAmount notPrice notRecalculate notOwned).id=original.id := by
  simp only [originalWindow,afterTailWindow_id,retainedWindow_id,numericWindow_id]

theorem completed (entry : Entry base scope price free rate) :
    (after entry).control=.completion (.normal (some (.number Number.one))) ∧
    (after entry).continuation=base.continuation ∧ (after entry).context=base.context := by
  have done:=SaleTailPreservation.completed (tail entry)
  simp only [after]
  refine ⟨done.1,?_,done.2.2.trans (context entry)⟩
  simpa only [tailBase] using done.2.1

theorem call_no_time_or_draw (entry : Entry base scope price free rate) :
    (tailBase entry.reprice).elapsed=base.elapsed ∧
    (tailBase entry.reprice).epochMilliseconds=base.epochMilliseconds ∧
    (tailBase entry.reprice).freeDrawCount=base.freeDrawCount ∧
    (tailBase entry.reprice).events=base.events ∧
    (tailBase entry.reprice).nextEventId=base.nextEventId := by
  simp only [tailBase,SaleReprice.after,SalePriceAssignment.after,AllocatingAssignment.after,
    AllocatingInitializer.Result.machine,SourceBinding.Slot.after,SaleReprice.callBase,
    SaleNumericFrame.Entry.afterAmount,SaleNumericFrame.Entry.afterEarned,SaleNumericFrame.Entry.afterMoni,
    SaleNumericFrame.Entry.afterSold]
  trivial

theorem no_time_or_draw (entry : Entry base scope price free rate) :
    (after entry).elapsed=base.elapsed ∧ (after entry).epochMilliseconds=base.epochMilliseconds ∧
    (after entry).freeDrawCount=base.freeDrawCount ∧ (after entry).events=base.events ∧
    (after entry).nextEventId=base.nextEventId := by
  have first:=SaleTailPreservation.no_time_or_draw (tail entry)
  have second:=call_no_time_or_draw entry
  exact ⟨first.1.trans second.1,first.2.1.trans second.2.1,first.2.2.1.trans second.2.2.1,
    first.2.2.2.1.trans second.2.2.2.1,first.2.2.2.2.trans second.2.2.2.2⟩

end CookieClicker.JavaScript.SaleCompletePreservation

import CookieClicker.JavaScriptSaleReprice
import CookieClicker.JavaScriptSaleTailSource
import CookieClicker.JavaScriptInitializerReadRetention

namespace CookieClicker.JavaScript.SaleRepriceFields
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

variable {base : Machine} {key : JSString}

def retainedSlot (next : Machine) (objects : HeapExtension.Extends base.heap next.heap)
    (slot : BuildingStore.Slot base key) : BuildingStore.Slot next key := {
  id:=slot.id,object:=slot.object,oldValue:=slot.oldValue,enumerable:=slot.enumerable,configurable:=slot.configurable
  present:=HeapExtension.checked_object objects _ _ slot.present
  kind:=slot.kind,own:=slot.own
  lookup:=HeapExtension.lookup_property objects _ _ _ slot.lookup }

theorem retainedSlot_id (next : Machine) (objects : HeapExtension.Extends base.heap next.heap)
    (slot : BuildingStore.Slot base key) : (retainedSlot next objects slot).id=slot.id := rfl

theorem retainedSlot_value (next : Machine) (objects : HeapExtension.Extends base.heap next.heap)
    (slot : BuildingStore.Slot base key) : (retainedSlot next objects slot).oldValue=slot.oldValue := rfl

def retainedEdge (next : Machine) (objects : HeapExtension.Extends base.heap next.heap)
    {id : ObjectId} {value : Value} (edge : TieredRead.DataEdge base id key value) :
    TieredRead.DataEdge next id key value := {
  object:=edge.object,present:=HeapExtension.checked_object objects _ _ edge.present,kind:=edge.kind
  property:=HeapExtension.lookup_property objects _ _ _ edge.property }

def retainedWindow (next : Machine) (objects : HeapExtension.Extends base.heap next.heap)
    {name : String} {value : Value} (window : OriginalNamePath.Window base name value) :
    OriginalNamePath.Window next name value := {
  id:=window.id,object:=window.object,present:=HeapExtension.checked_object objects _ _ window.present,kind:=window.kind
  writable:=window.writable,enumerable:=window.enumerable,configurable:=window.configurable
  property:=HeapExtension.lookup_property objects _ _ _ window.property }

theorem retainedWindow_id (next : Machine) (objects : HeapExtension.Extends base.heap next.heap)
    {name : String} {value : Value} (window : OriginalNamePath.Window base name value) :
    (retainedWindow next objects window).id=window.id := rfl

def writtenSlot (write : PriceRegistryWrite.Write base) (slot : BuildingStore.Slot base key)
    (different : write.key≠key) : BuildingStore.Slot write.after key := {
  id:=slot.id,object:=write.transformed slot.id slot.object
  oldValue:=slot.oldValue,enumerable:=slot.enumerable,configurable:=slot.configurable
  present:=write.checked _ _ slot.present
  kind:=by rw [write.kind];exact slot.kind
  own:=by rw [PriceRegistryWrite.Write.transformed,PropertyFrame.transformed_own _ _ _ _ _ _ different];exact slot.own
  lookup:=(PropertyFrame.lookup_other _ _ _ _ _ _ write.present different _).trans slot.lookup }

def writtenEdge (write : PriceRegistryWrite.Write base) {id : ObjectId} {value : Value}
    (edge : TieredRead.DataEdge base id key value) (different : write.key≠key) :
    TieredRead.DataEdge write.after id key value :=
  PropertyFrame.edge edge write.target write.object write.key write.descriptor write.present different

def writtenWindow (write : PriceRegistryWrite.Write base) {name : String} {value : Value}
    (window : OriginalNamePath.Window base name value) (different : write.key≠JSString.ofString name) :
    OriginalNamePath.Window write.after name value := {
  id:=window.id,object:=write.transformed window.id window.object
  present:=write.checked _ _ window.present
  kind:=by simpa only [write.kind] using window.kind
  writable:=window.writable,enumerable:=window.enumerable,configurable:=window.configurable
  property:=(PropertyFrame.lookup_other _ _ _ _ _ _ write.present different _).trans window.property }

def castSlot {before after : Machine} (same : before=after) (slot : BuildingStore.Slot before key) :
    BuildingStore.Slot after key := same ▸ slot

theorem castSlot_id {before after : Machine} (same : before=after) (slot : BuildingStore.Slot before key) :
    (castSlot same slot).id=slot.id := by cases same; rfl

theorem castSlot_value {before after : Machine} (same : before=after) (slot : BuildingStore.Slot before key) :
    (castSlot same slot).oldValue=slot.oldValue := by cases same;rfl

def castWindow {before after : Machine} (same : before=after) {name : String} {value : Value}
    (window : OriginalNamePath.Window before name value) : OriginalNamePath.Window after name value := same ▸ window

theorem castWindow_id {before after : Machine} (same : before=after) {name : String} {value : Value}
    (window : OriginalNamePath.Window before name value) : (castWindow same window).id=window.id := by cases same;rfl

variable (numeric : SaleNumericFrame.Entry base)

def numericSlot (slot : BuildingStore.Slot base key)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : BuildingStore.Slot numeric.afterAmount key :=
  castSlot (SaleNumericWrites.amount_machine numeric) (writtenSlot (SaleNumericWrites.amount numeric)
    (writtenSlot (SaleNumericWrites.earned numeric)
      (writtenSlot (SaleNumericWrites.cookies numeric) (slot.transport numeric.afterMoni rfl) cookies) earned) amount)

def numericEdge {id : ObjectId} {value : Value} (edge : TieredRead.DataEdge base id key value)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : TieredRead.DataEdge numeric.afterAmount id key value := by
  rw [←SaleNumericWrites.amount_machine numeric]
  exact writtenEdge (SaleNumericWrites.amount numeric)
    (writtenEdge (SaleNumericWrites.earned numeric)
      (writtenEdge (SaleNumericWrites.cookies numeric)
        (retainedEdge numeric.afterMoni (HeapExtension.same_objects (before:=base.heap) (after:=numeric.afterMoni.heap) rfl) edge) cookies) earned) amount

def numericWindow {name : String} {value : Value} (window : OriginalNamePath.Window base name value)
    (cookies : JSString.ofString "cookies"≠JSString.ofString name)
    (earned : JSString.ofString "cookiesEarned"≠JSString.ofString name)
    (amount : JSString.ofString "amount"≠JSString.ofString name) : OriginalNamePath.Window numeric.afterAmount name value :=
  castWindow (SaleNumericWrites.amount_machine numeric) (writtenWindow (SaleNumericWrites.amount numeric)
    (writtenWindow (SaleNumericWrites.earned numeric)
      (writtenWindow (SaleNumericWrites.cookies numeric)
        (retainedWindow numeric.afterMoni (HeapExtension.same_objects (before:=base.heap) (after:=numeric.afterMoni.heap) rfl) window) cookies) earned) amount)

theorem numericSlot_id (slot : BuildingStore.Slot base key)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : (numericSlot numeric slot cookies earned amount).id=slot.id := by
  simp only [numericSlot,castSlot_id,writtenSlot,BuildingStore.Slot.transport]

theorem numericSlot_value (slot : BuildingStore.Slot base key)
    (cookies : JSString.ofString "cookies"≠key) (earned : JSString.ofString "cookiesEarned"≠key)
    (amount : JSString.ofString "amount"≠key) : (numericSlot numeric slot cookies earned amount).oldValue=slot.oldValue := by
  simp only [numericSlot,castSlot_value,writtenSlot,BuildingStore.Slot.transport]

theorem numericWindow_id {name : String} {value : Value} (window : OriginalNamePath.Window base name value)
    (cookies : JSString.ofString "cookies"≠JSString.ofString name)
    (earned : JSString.ofString "cookiesEarned"≠JSString.ofString name)
    (amount : JSString.ofString "amount"≠JSString.ofString name) :
    (numericWindow numeric window cookies earned amount).id=window.id := by
  simp only [numericWindow,castWindow_id,writtenWindow,retainedWindow]

def numericLocalSlot {name : String} (slot : SourceBinding.Slot base name)
    (notSold : name≠"sold") (notMoni : name≠"moni") : SourceBinding.Slot numeric.afterAmount name :=
  {numeric.nextMoniSlot.otherSlot (numeric.soldSlot.otherSlot slot notSold (.number numeric.newSold))
    notMoni (.number numeric.newMoni) with}

def numericPath {name : String} {start : EnvId} {window : ObjectId}
    (path : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name numeric.afterAmount.heap.environments start window :=
  (path.written numeric.soldSlot (.number numeric.newSold)).written numeric.nextMoniSlot (.number numeric.newMoni)

def afterTailPath (entry : SaleTailFrame.Entry base) {name : String} {start : EnvId} {window : ObjectId}
    (original : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name entry.changed.heap.environments start window :=
  OriginalNamePath.Path.written (base:=entry.afterOwned) original entry.successAfterOwned (.number Number.one)

def afterTailWindow (entry : SaleTailFrame.Entry base) {name : String} {value : Value}
    (original : OriginalNamePath.Window base name value)
    (notPrice : JSString.ofString "price"≠JSString.ofString name)
    (notRecalculate : JSString.ofString "recalculateGains"≠JSString.ofString name)
    (notOwned : JSString.ofString "BuildingsOwned"≠JSString.ofString name) :
    OriginalNamePath.Window entry.changed name value :=
  retainedWindow entry.changed (HeapExtension.same_objects (before:=entry.afterOwned.heap) rfl)
    (OriginalPropertyWrite.window entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one))
      (OriginalPropertyWrite.window entry.recalculateAfterPrice (.number Number.one)
        (OriginalPropertyWrite.window entry.priceSlot (.number entry.price) original notPrice) notRecalculate) notOwned)

theorem afterTailWindow_id (entry : SaleTailFrame.Entry base) {name : String} {value : Value}
    (original : OriginalNamePath.Window base name value)
    (notPrice : JSString.ofString "price"≠JSString.ofString name)
    (notRecalculate : JSString.ofString "recalculateGains"≠JSString.ofString name)
    (notOwned : JSString.ofString "BuildingsOwned"≠JSString.ofString name) :
    (afterTailWindow entry original notPrice notRecalculate notOwned).id=original.id := by
  simp only [afterTailWindow,retainedWindow,OriginalPropertyWrite.window]

variable {scope : ObjectId} {price free rate : UInt64}

def tailBase (entry : SaleReprice.Entry base scope price free rate) : Machine :=
  {SaleReprice.after entry with continuation:=base.continuation}

def quoted (entry : SaleReprice.Entry base scope price free rate) : UInt64 :=
  Number.ceil (CursorGetPriceRead.rawValue price (Number.sub entry.numeric.amount Number.one) free rate)

theorem allocation (entry : SaleReprice.Entry base scope price free rate) :
    HeapExtension.Extends (SaleReprice.callBase entry).heap
      (SalePriceAssignment.output (SaleReprice.callEntry entry)).heap :=
  CursorGetPriceOriginal.retained_objects (SalePriceAssignment.callCatalogue (SaleReprice.callEntry entry)) entry.function

theorem call_objects (entry : SaleReprice.Entry base scope price free rate) :
    HeapExtension.Extends entry.numeric.afterAmount.heap (tailBase entry).heap :=
  HeapExtension.trans (allocation entry) (HeapExtension.same_objects rfl)

def priceLocal (entry : SaleReprice.Entry base scope price free rate) :
    DevastationWrite.Local (tailBase entry) "price" (.number (quoted entry)) :=
  {InitializerReadRetention.writtenLocal (SalePriceAssignment.output (SaleReprice.callEntry entry))
    (SaleReprice.callEntry entry).slot (.number (quoted entry)) with}

def localSlot (entry : SaleReprice.Entry base scope price free rate) {name : String}
    (slot : SourceBinding.Slot base name) (notSold : name≠"sold") (notMoni : name≠"moni") (notPrice : name≠"price") :
    SourceBinding.Slot (tailBase entry) name :=
  {InitializerReadRetention.otherSlot (SalePriceAssignment.output (SaleReprice.callEntry entry))
    (SaleReprice.callEntry entry).slot (.number (quoted entry))
    {numericLocalSlot entry.numeric slot notSold notMoni with} notPrice with}

def path (entry : SaleReprice.Entry base scope price free rate) {name : String} {start : EnvId} {window : ObjectId}
    (original : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name (tailBase entry).heap.environments start window :=
  InitializerReadRetention.writtenPath (SalePriceAssignment.output (SaleReprice.callEntry entry))
    (SaleReprice.callEntry entry).slot (.number (quoted entry)) (numericPath entry.numeric original)

end CookieClicker.JavaScript.SaleRepriceFields

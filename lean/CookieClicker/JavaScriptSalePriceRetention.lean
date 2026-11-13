import CookieClicker.JavaScriptSalePriceInitializer
import CookieClicker.JavaScriptPriceRegistryBinding

/-! The original sale catalogue and caller slots survive the actual allocating
price initializer and its price write. Later frames are derived from entry. -/
namespace CookieClicker.JavaScript.SalePriceRetention
open SalePriceInitializer PriceRegistryScope
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

variable {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}

def allocation (entry : Entry base scope cursor price owned free rate) :
    PriceRegistryAdvance.Advance base (output entry).machine := {
  heap:=CursorGetPriceOriginal.retained_objects (callCatalogue entry) entry.function
  suffix:=(output entry).suffix,environments:=(output entry).environments
  global:=rfl,exclusions:=rfl }

def priceSlot (entry : Entry base scope cursor price owned free rate) :
    SourceBinding.Slot (output entry).machine "price" := (output entry).slot entry.slot

def continuationAdvance (entry : Entry base scope cursor price owned free rate) (continuation : List Frame) :
    PriceRegistryAdvance.Advance
      ((priceSlot entry).after (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate))))
      {after entry with continuation} := {
  heap:=HeapExtension.refl _,suffix:=#[],environments:=by simp [after,AllocatingInitializer.Result.after,priceSlot]
  global:=rfl,exclusions:=rfl }

def world (entry : Entry base scope cursor price owned free rate) (continuation : List Frame) :
    PriceRegistry.World {after entry with continuation} :=
  (continuationAdvance entry continuation).world
    (PriceRegistryBinding.world (priceSlot entry)
      (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate)))
      ((allocation entry).world entry.catalogue.pricing))

def closure (entry : Entry base scope cursor price owned free rate) (continuation : List Frame)
    (original : ClosureScope base) : ClosureScope {after entry with continuation} :=
  (continuationAdvance entry continuation).scope
    (PriceRegistryBinding.scope (priceSlot entry)
      (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate)))
      ((allocation entry).scope original))

def otherSlot (entry : Entry base scope cursor price owned free rate) (continuation : List Frame)
    {name : String} (original : SourceBinding.Slot base name) (different : name≠"price") :
    SourceBinding.Slot {after entry with continuation} name :=
  {((priceSlot entry).otherSlot ((output entry).slot original) different
    (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate)))) with}

theorem original_objects (entry : Entry base scope cursor price owned free rate) (continuation : List Frame) :
    HeapExtension.Extends base.heap {after entry with continuation}.heap :=
  HeapExtension.trans (allocation entry).heap
    (HeapExtension.same_objects rfl)

def withContinuation (entry : Entry base scope cursor price owned free rate) (continuation : List Frame) :
    Entry {base with continuation} scope cursor price owned free rate := {
  catalogue:=CursorGetPriceCatalogue.recontext entry.catalogue base.context continuation
  slot:=entry.slot.withContinuation continuation
  function:=entry.function,stable:=entry.stable,source:=entry.source
  cursorObject:=entry.cursorObject,functionObject:=entry.functionObject
  receiver:=entry.receiver,cursorPresent:=entry.cursorPresent,cursorKind:=entry.cursorKind
  method:=entry.method,functionPresent:=entry.functionPresent,functionKind:=entry.functionKind }

end CookieClicker.JavaScript.SalePriceRetention

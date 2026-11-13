import CookieClicker.JavaScriptSaleHeaderFloor

namespace CookieClicker.JavaScript.SaleHeaderPreservation
open SaleHeaderFloor
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

variable {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}

def finalPrice (entry : Entry base scope cursor price owned free rate) :
    DevastationWrite.Local (after entry) "price" (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) :=
  {GodzamokLocalTransport.localWritten (floorSlot entry)
    (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with}

def finalGiveBack (entry : Entry base scope cursor price owned free rate) :
    DevastationWrite.Local (after entry) "giveBack" (.number CursorSellBody.quarter) :=
  {GodzamokLocalTransport.localOther (floorSlot entry) (floorGiveBack entry) (by decide)
    (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with}

def originalLocal (entry : Entry base scope cursor price owned free rate) {name : String} {value : Value}
    (original : DevastationWrite.Local base name value) (notPrice : name≠"price") (notGiveBack : name≠"giveBack") :
    DevastationWrite.Local (after entry) name value := by
  let firstFrame : DevastationWrite.Local
      {base with continuation:=.statementList (SaleNumericSource.loopBody.drop 1) none::base.continuation} name value := {original with}
  let firstWritten:=InitializerReadRetention.otherLocal (SalePriceInitializer.output (SaleHeader.priceEntry entry.header))
    (SaleHeader.priceEntry entry.header).slot (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) firstFrame notPrice
  let multiplierFrame : DevastationWrite.Local (SaleHeader.multiplierBase entry.header) name value := {firstWritten with}
  let secondWritten:=InitializerReadRetention.otherLocal (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter) multiplierFrame notGiveBack
  let floorFrame : DevastationWrite.Local (SaleHeader.floorBase entry.header) name value := {secondWritten with}
  exact {GodzamokLocalTransport.localOther (floorSlot entry) floorFrame notPrice
    (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with}

def originalSlot (entry : Entry base scope cursor price owned free rate) {name : String}
    (original : SourceBinding.Slot base name) (notPrice : name≠"price") (notGiveBack : name≠"giveBack") :
    SourceBinding.Slot (after entry) name := by
  let firstSlot:=original.withContinuation (.statementList (SaleNumericSource.loopBody.drop 1) none::base.continuation)
  let firstWritten:=InitializerReadRetention.otherSlot (SalePriceInitializer.output (SaleHeader.priceEntry entry.header))
    (SaleHeader.priceEntry entry.header).slot (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) firstSlot notPrice
  let multiplierSlot : SourceBinding.Slot (SaleHeader.multiplierBase entry.header) name := {firstWritten with}
  let secondWritten:=InitializerReadRetention.otherSlot (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter) multiplierSlot notGiveBack
  let floorOriginal : SourceBinding.Slot (SaleHeader.floorBase entry.header) name := {secondWritten with}
  exact {(floorSlot entry).otherSlot floorOriginal notPrice
    (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with}

theorem objects_exact (entry : Entry base scope cursor price owned free rate) :
    (after entry).heap.objects=(SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header)).heap.objects := rfl

theorem original_objects (entry : Entry base scope cursor price owned free rate) :
    HeapExtension.Extends base.heap (after entry).heap := by
  have first : HeapExtension.Extends base.heap (SaleHeader.multiplierBase entry.header).heap:=
    SalePriceRetention.original_objects (SaleHeader.priceEntry entry.header) (SaleHeader.multiplierContinuation base)
  exact HeapExtension.trans first (HeapExtension.trans (multiplierObjects (SaleHeader.multiplierEntry entry.header))
    (HeapExtension.same_objects rfl))

theorem original_property (entry : Entry base scope cursor price owned free rate)
    (id : ObjectId) (name : JSString) (descriptor : Option PropertyDescriptor)
    (found : lookupProperty base.heap id name=.ok descriptor) : lookupProperty (after entry).heap id name=.ok descriptor :=
  HeapExtension.lookup_property (original_objects entry) id name descriptor found

theorem caller_retained (entry : Entry base scope cursor price owned free rate) :
    (after entry).context=base.context ∧ (after entry).elapsed=base.elapsed ∧
    (after entry).epochMilliseconds=base.epochMilliseconds ∧ (after entry).freeDrawCount=base.freeDrawCount ∧
    (after entry).events=base.events ∧ (after entry).nextEventId=base.nextEventId := by
  simp only [after,SourceBinding.Slot.after,SaleHeader.floorBase,SaleMultiplierInitializer.after,
    AllocatingInitializer.Result.after,SaleHeader.multiplierBase,SalePriceInitializer.after,
    AllocatingInitializer.Result.machine]
  trivial

def originalPath (entry : Entry base scope cursor price owned free rate)
    {name : String} {start : EnvId} {window : ObjectId}
    (original : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name (after entry).heap.environments start window := by
  let firstWritten:=InitializerReadRetention.writtenPath
    (SalePriceInitializer.output (SaleHeader.priceEntry entry.header))
    (SaleHeader.priceEntry entry.header).slot
    (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) original
  let secondWritten:=InitializerReadRetention.writtenPath
    (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter) firstWritten
  exact OriginalNamePath.Path.written (base:=SaleHeader.floorBase entry.header) secondWritten (floorSlot entry)
    (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate)))

def originalWindow (entry : Entry base scope cursor price owned free rate)
    {name : String} {value : Value} (original : OriginalNamePath.Window base name value) :
    OriginalNamePath.Window (after entry) name value := {
  id:=original.id,object:=original.object
  present:=HeapExtension.checked_object (original_objects entry) _ _ original.present
  kind:=original.kind,writable:=original.writable,enumerable:=original.enumerable,configurable:=original.configurable
  property:=HeapExtension.lookup_property (original_objects entry) _ _ _ original.property }

theorem exclusions_retained (entry : Entry base scope cursor price owned free rate) :
    (after entry).objectEnvironmentExclusions=base.objectEnvironmentExclusions := by
  simp only [after,SourceBinding.Slot.after,SaleHeader.floorBase,SaleMultiplierInitializer.after,
    AllocatingInitializer.Result.after,SaleHeader.multiplierBase,SalePriceInitializer.after,
    AllocatingInitializer.Result.machine]

def originalMath (entry : Entry base scope cursor price owned free rate) {method : String}
    (original : InitializerMathRetention.Frame base method) :
    InitializerMathRetention.Frame (after entry) method :=
  original.retained (after entry) (original_objects entry) (caller_retained entry).1
    ((exclusions_retained entry).trans original.exclusions) (originalPath entry original.path)

theorem originalMath_identifiers (entry : Entry base scope cursor price owned free rate) {method : String}
    (original : InitializerMathRetention.Frame base method) :
    (originalMath entry original).math=original.math ∧
    (originalMath entry original).function=original.function ∧
    (originalMath entry original).window.id=original.window.id :=
  original.retained_identifiers (after entry) (original_objects entry) (caller_retained entry).1
    ((exclusions_retained entry).trans original.exclusions) (originalPath entry original.path)

theorem math_identities (entry : Entry base scope cursor price owned free rate) :
    (floorMath entry).math=entry.math.math ∧ (floorMath entry).function=entry.math.function ∧
    (floorMath entry).window.id=entry.math.window.id := by
  simp only [floorMath,mathAfterPrice,InitializerMathRetention.Frame.reframe,
    InitializerMathRetention.Frame.afterInitializer]
  trivial

theorem price_read (entry : Entry base scope cursor price owned free rate) :
    SourceRead.Reads (after entry) (.identifier "price")
      (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) 3 := (finalPrice entry).reads

theorem giveBack_read (entry : Entry base scope cursor price owned free rate) :
    SourceRead.Reads (after entry) (.identifier "giveBack") (.number CursorSellBody.quarter) 3 := (finalGiveBack entry).reads

theorem source_continuation (entry : Entry base scope cursor price owned free rate) :
    (after entry).control=.completion (.normal (some (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))))) ∧
    (after entry).continuation=.statementList (SaleNumericSource.loopBody.drop 3) none::base.continuation := ⟨rfl,rfl⟩

end CookieClicker.JavaScript.SaleHeaderPreservation

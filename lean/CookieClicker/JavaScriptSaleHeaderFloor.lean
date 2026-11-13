import CookieClicker.JavaScriptSaleHeader
import CookieClicker.JavaScriptInitializerMathRetention

namespace CookieClicker.JavaScript.SaleHeaderFloor
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) (scope cursor : ObjectId) (price owned free rate : UInt64) where
  header : SaleHeader.Entry base scope cursor price owned free rate
  math : InitializerMathRetention.Frame base "floor"

variable {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}

def quoted : UInt64 := Number.ceil (CursorGetPriceRead.rawValue price owned free rate)
def credited : UInt64 := Number.floor (Number.mul (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate)) CursorSellBody.quarter)

def priceLocal (entry : Entry base scope cursor price owned free rate) :
    DevastationWrite.Local (SaleHeader.multiplierBase entry.header) "price" (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) :=
  {InitializerReadRetention.writtenLocal (SalePriceInitializer.output (SaleHeader.priceEntry entry.header))
    (SaleHeader.priceEntry entry.header).slot (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with}

def priceSlot (entry : Entry base scope cursor price owned free rate) :
    SourceBinding.Slot (SaleHeader.multiplierBase entry.header) "price" :=
  {InitializerReadRetention.writtenSlot (SalePriceInitializer.output (SaleHeader.priceEntry entry.header))
    (SaleHeader.priceEntry entry.header).slot (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with}

def mathAfterPrice (entry : Entry base scope cursor price owned free rate) :
    InitializerMathRetention.Frame (SaleHeader.multiplierBase entry.header) "floor" :=
  ((entry.math.reframe base.control (.statementList (SaleNumericSource.loopBody.drop 1) none::base.continuation)).afterInitializer
    (SalePriceInitializer.output (SaleHeader.priceEntry entry.header))
    (SalePriceRetention.allocation (SaleHeader.priceEntry entry.header)).heap
    (SaleHeader.priceEntry entry.header).slot (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate)))).reframe
      (.completion (.normal none)) (SaleHeader.multiplierContinuation base)

theorem multiplierObjects {machine : Machine} {cursor : ObjectId} (entry : SaleMultiplierInitializer.Entry machine cursor) :
    HeapExtension.Extends machine.heap (SaleMultiplierInitializer.output entry).heap :=
  (CursorSellRegistry.returnedAdvance (SaleMultiplierInitializer.caller machine)
    ((SaleMultiplierInitializer.callerAdvance machine).world entry.world)
    ((SaleMultiplierInitializer.callerAdvance machine).scope entry.scope) cursor entry.function).heap

def floorPrice (entry : Entry base scope cursor price owned free rate) :
    DevastationWrite.Local (SaleHeader.floorBase entry.header) "price" (.number (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate))) :=
  {InitializerReadRetention.otherLocal (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter) (priceLocal entry) (by decide) with}

def floorGiveBack (entry : Entry base scope cursor price owned free rate) :
    DevastationWrite.Local (SaleHeader.floorBase entry.header) "giveBack" (.number CursorSellBody.quarter) :=
  {InitializerReadRetention.writtenLocal (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter) with}

def floorSlot (entry : Entry base scope cursor price owned free rate) :
    SourceBinding.Slot (SaleHeader.floorBase entry.header) "price" :=
  {InitializerReadRetention.otherSlot (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter) (priceSlot entry) (by decide) with}

def floorMath (entry : Entry base scope cursor price owned free rate) :
    InitializerMathRetention.Frame (SaleHeader.floorBase entry.header) "floor" :=
  ((mathAfterPrice entry).afterInitializer
    (SaleMultiplierInitializer.output (SaleHeader.multiplierEntry entry.header))
    (multiplierObjects (SaleHeader.multiplierEntry entry.header))
    (SaleHeader.multiplierEntry entry.header).slot (.number CursorSellBody.quarter)).reframe
      (.statement SaleFloor.statement) (.statementList (SaleNumericSource.loopBody.drop 3) none::base.continuation)

def after (entry : Entry base scope cursor price owned free rate) : Machine :=
  {(floorSlot entry).after (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate))) with
    control:=.completion (.normal (some (.number (credited (price:=price) (owned:=owned) (free:=free) (rate:=rate)))))}

theorem actual_floor (entry : Entry base scope cursor price owned free rate) (fuel : Nat) :
    Builtins.run (28+fuel) (SaleHeader.floorBase entry.header)=Builtins.run fuel (after entry) :=
  SaleFloor.source_assignment (SaleHeader.floorBase entry.header) (floorMath entry).binding (floorSlot entry)
    (quoted (price:=price) (owned:=owned) (free:=free) (rate:=rate)) CursorSellBody.quarter
    (floorPrice entry).reads (floorGiveBack entry).reads fuel

theorem actual_header (entry : Entry base scope cursor price owned free rate) (fuel : Nat) :
    Builtins.run (1547+fuel) {base with control:=.statement (.block SaleNumericSource.loopBody)}=
      Builtins.run fuel (after entry) := by
  conv => lhs;arg 1;rw [show 1547+fuel=1519+(28+fuel) by omega]
  refine (SaleHeader.actual_header entry.header (28+fuel)).trans ?_
  exact actual_floor entry fuel

end CookieClicker.JavaScript.SaleHeaderFloor

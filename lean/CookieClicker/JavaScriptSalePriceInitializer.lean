import CookieClicker.JavaScriptCursorGetPriceOriginal
import CookieClicker.JavaScriptAllocatingInitializer

/-! The first native price initializer of a building sale runs the complete
getPrice call and writes its actual return into the original caller slot. -/
namespace CookieClicker.JavaScript.SalePriceInitializer
open CursorGetPriceCatalogue CursorGetPriceOriginal
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

structure Entry (base : Machine) (scope cursor : ObjectId) (price owned free rate : UInt64) where
  catalogue : Catalogue base scope cursor price owned free rate
  slot : SourceBinding.Slot base "price"
  function : ObjectId
  stable : Number.mul (CursorGetPriceRead.rawValue price owned free rate) Number.one=
    CursorGetPriceRead.rawValue price owned free rate
  source : Option JSString
  cursorObject : JSObject
  functionObject : JSObject
  receiver : base.context.thisValue=.object cursor
  cursorPresent : checkedObject base.heap cursor=.ok cursorObject
  cursorKind : cursorObject.kind=.ordinary
  method : lookupProperty base.heap cursor (JSString.ofString "getPrice")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (CursorGetPriceSource.closure scope source)

def callCatalogue {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) :
    Catalogue {base with continuation:=VariableCall.frames base "price"} scope cursor price owned free rate :=
  recontext entry.catalogue base.context (VariableCall.frames base "price")

def output {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) : AllocatingInitializer.Result base := {
  heap:=(CursorGetPriceOriginal.after (callCatalogue entry) entry.function).heap
  suffix:=environmentSuffix (callCatalogue entry) entry.function
  environments:=retained_environments (callCatalogue entry) entry.function }

def after {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) : Machine :=
  (output entry).after entry.slot (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate)))

theorem source_initializer {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) (fuel : Nat) :
    Builtins.run (1308+fuel) {base with
      control:=.statement (.variable [("price",some CursorGetPriceCall.expression)])}=
      Builtins.run fuel (after entry) := by
  apply AllocatingInitializer.compose base "price" entry.slot CursorGetPriceCall.expression rfl
    (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate))) 1304 (output entry)
  intro later
  exact actual_source_call (callCatalogue entry) entry.function entry.stable entry.source
    entry.cursorObject entry.functionObject entry.receiver entry.cursorPresent entry.cursorKind
    entry.method entry.functionPresent entry.functionKind later

end CookieClicker.JavaScript.SalePriceInitializer

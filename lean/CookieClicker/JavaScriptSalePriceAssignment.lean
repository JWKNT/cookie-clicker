import CookieClicker.JavaScriptSalePriceInitializer
import CookieClicker.JavaScriptAllocatingAssignment
import CookieClicker.JavaScriptSaleNumericSource

/-! The successful sale recomputes the stored price with the complete native
getPrice call and assigns its returned value to the original price local. -/
namespace CookieClicker.JavaScript.SalePriceAssignment
open CursorGetPriceCatalogue CursorGetPriceOriginal
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

abbrev Entry := SalePriceInitializer.Entry

def callCatalogue {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) :
    Catalogue {base with continuation:=AllocatingAssignment.frames base "price"} scope cursor price owned free rate :=
  recontext entry.catalogue base.context (AllocatingAssignment.frames base "price")

def output {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) : AllocatingInitializer.Result base := {
  heap:=(CursorGetPriceOriginal.after (callCatalogue entry) entry.function).heap
  suffix:=environmentSuffix (callCatalogue entry) entry.function
  environments:=retained_environments (callCatalogue entry) entry.function }

def after {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) : Machine :=
  AllocatingAssignment.after base "price" entry.slot (output entry)
    (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate)))

theorem source_assignment {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (entry : Entry base scope cursor price owned free rate) (fuel : Nat) :
    Builtins.run (1311+fuel) {base with control:=.statement (SaleNumericSource.sourceStatement 5)}=
      Builtins.run fuel (after entry) := by
  apply AllocatingAssignment.compose base "price" entry.slot CursorGetPriceCall.expression rfl
    (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate))) 1304 (output entry)
  intro later
  exact actual_source_call (callCatalogue entry) entry.function entry.stable entry.source
    entry.cursorObject entry.functionObject entry.receiver entry.cursorPresent entry.cursorKind
    entry.method entry.functionPresent entry.functionKind later

end CookieClicker.JavaScript.SalePriceAssignment

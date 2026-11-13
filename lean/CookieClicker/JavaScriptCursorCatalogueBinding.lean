import CookieClicker.JavaScriptCursorQuoteCatalogue
import CookieClicker.JavaScriptPriceRegistryBinding

/-! A caller binding write preserves the original complete Cursor arithmetic
and modifier catalogue, including source closure paths for Math and Game. -/
namespace CookieClicker.JavaScript.CursorCatalogueBinding
open CursorQuoteRegistry CursorQuoteCatalogue
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

variable {base : Machine} {written : String}

def global (slot : SourceBinding.Slot base written) (value : Value)
    {scope : EnvId} {name : String} {observed : Value} (original : Global base scope name observed) :
    Global (slot.after value) scope name observed := by
  let path : OriginalNamePath.Path name base.heap.environments scope base.globalObject :=
    ⟨original.target,original.depth,original.chain,original.room,original.globalRead⟩
  let kept:=path.written slot value
  exact {
    target:=original.target,depth:=original.depth,chain:=kept.chain,room:=kept.room,globalRead:=kept.globalRead
    object:=original.object,present:=original.present,kind:=original.kind
    writable:=original.writable,enumerable:=original.enumerable,configurable:=original.configurable
    property:=HeapExtension.lookup_property (PriceRegistryBinding.extension slot value) _ _ _ original.property,exclusions:=original.exclusions }

def member (slot : SourceBinding.Slot base written) (value : Value)
    {math : ObjectId} {name : String} (original : MathMember base math name) :
    MathMember (slot.after value) math name := {
  function:=original.function,object:=original.object
  present:=HeapExtension.checked_object (PriceRegistryBinding.extension slot value) _ _ original.present
  kind:=original.kind
  property:=HeapExtension.lookup_property (PriceRegistryBinding.extension slot value) _ _ _ original.property }

def arithmetic (slot : SourceBinding.Slot base written) (value : Value)
    {scope cursor : ObjectId} {price owned free rate : UInt64}
    (original : World base scope cursor price owned free rate) :
    World (slot.after value) scope cursor price owned free rate := {
  game:=original.game,math:=original.math
  gameRead:=global slot value original.gameRead,mathRead:=global slot value original.mathRead
  mathObject:=original.mathObject,mathPresent:=original.mathPresent,mathKind:=original.mathKind
  maximum:=member slot value original.maximum,power:=member slot value original.power,ceiling:=member slot value original.ceiling
  priceRead:=original.priceRead.extend (PriceRegistryBinding.extension slot value)
  amountRead:=original.amountRead.extend (PriceRegistryBinding.extension slot value)
  freeRead:=original.freeRead.extend (PriceRegistryBinding.extension slot value)
  rateRead:=original.rateRead.extend (PriceRegistryBinding.extension slot value) }

def catalogue (slot : SourceBinding.Slot base written) (value : Value) (notM : written≠"M")
    {scope cursor : ObjectId} {price owned free rate : UInt64}
    (original : Catalogue base scope cursor price owned free rate) :
    Catalogue (slot.after value) scope cursor price owned free rate := {
  arithmetic:=arithmetic slot value original.arithmetic
  pricing:=PriceRegistryBinding.world slot value original.pricing
  profile:=PriceRegistryBinding.profile slot value notM original.profile
  sameGame:=original.sameGame,sameBuilding:=original.sameBuilding
  function:=original.function,source:=original.source,functionObject:=original.functionObject
  functionPresent:=HeapExtension.checked_object (PriceRegistryBinding.extension slot value) _ _ original.functionPresent
  functionKind:=by simpa only [PriceRegistryBinding.world,PriceRegistryBinding.scope_id] using original.functionKind
  method:=HeapExtension.lookup_property (PriceRegistryBinding.extension slot value) _ _ _ original.method }

end CookieClicker.JavaScript.CursorCatalogueBinding

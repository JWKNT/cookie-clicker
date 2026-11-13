import CookieClicker.JavaScriptCursorQuoteCatalogue
import CookieClicker.JavaScriptPriceRegistryProfileWrite

/-! Economic property writes preserve the complete source pricing catalogue.
The changed amount edge is supplied by the actual native amount write; every
other arithmetic or helper descriptor is reconstructed from the original heap. -/
namespace CookieClicker.JavaScript.CursorCatalogueWrite
open CursorQuoteRegistry CursorQuoteCatalogue PriceRegistryWrite
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

variable {base : Machine}

def arithmeticNames : List String := ["Math","max","pow","ceil","basePrice","free","priceIncrease","modifyBuildingPrice"]
def Safe (write : Write base) : Prop := ∀ name∈arithmeticNames,write.key≠JSString.ofString name

def global (write : Write base) {scope : EnvId} {name : String} {observed : Value}
    (original : Global base scope name observed) (different : write.key≠JSString.ofString name) :
    Global write.after scope name observed := {
  target:=original.target,depth:=original.depth,chain:=original.chain,room:=original.room,globalRead:=original.globalRead
  object:=write.transformed base.globalObject original.object
  present:=write.checked _ _ original.present
  kind:=by simpa only [write.kind] using original.kind
  writable:=original.writable,enumerable:=original.enumerable,configurable:=original.configurable
  property:=(PropertyFrame.lookup_other base.heap write.target write.object write.key (JSString.ofString name)
    write.descriptor write.present different base.globalObject).trans original.property
  exclusions:=original.exclusions }

def member (write : Write base) {math : ObjectId} {name : String}
    (original : MathMember base math name) (different : write.key≠JSString.ofString name) :
    MathMember write.after math name := {
  function:=original.function,object:=write.transformed original.function original.object
  present:=write.checked _ _ original.present
  kind:=by simpa only [write.kind] using original.kind
  property:=(PropertyFrame.lookup_other base.heap write.target write.object write.key (JSString.ofString name)
    write.descriptor write.present different math).trans original.property }

def arithmetic (write : Write base) (safe : Safe write)
    {scope cursor : ObjectId} {price owned free rate newOwned : UInt64}
    (original : World base scope cursor price owned free rate)
    (amount : TieredRead.DataEdge write.after cursor (JSString.ofString "amount") (.number newOwned)) :
    World write.after scope cursor price newOwned free rate := {
  game:=original.game,math:=original.math
  gameRead:=global write original.gameRead (write.protectedFields _ (by decide))
  mathRead:=global write original.mathRead (safe _ (by decide))
  mathObject:=write.transformed original.math original.mathObject
  mathPresent:=write.checked _ _ original.mathPresent
  mathKind:=by simpa only [write.kind] using original.mathKind
  maximum:=member write original.maximum (safe _ (by decide))
  power:=member write original.power (safe _ (by decide))
  ceiling:=member write original.ceiling (safe _ (by decide))
  priceRead:=PropertyFrame.edge original.priceRead write.target write.object write.key write.descriptor write.present (safe _ (by decide))
  amountRead:=amount
  freeRead:=PropertyFrame.edge original.freeRead write.target write.object write.key write.descriptor write.present (safe _ (by decide))
  rateRead:=PropertyFrame.edge original.rateRead write.target write.object write.key write.descriptor write.present (safe _ (by decide)) }

def catalogue (write : Write base) (safe : Safe write)
    {scope cursor : ObjectId} {price owned free rate newOwned : UInt64}
    (original : Catalogue base scope cursor price owned free rate)
    (ownership : Write.OwnershipSafe write original.profile)
    (amount : TieredRead.DataEdge write.after cursor (JSString.ofString "amount") (.number newOwned)) :
    Catalogue write.after scope cursor price newOwned free rate := {
  arithmetic:=arithmetic write safe original.arithmetic amount
  pricing:=write.world original.pricing,profile:=write.profile original.profile ownership
  sameGame:=original.sameGame,sameBuilding:=original.sameBuilding
  function:=original.function,source:=original.source
  functionObject:=write.transformed original.function original.functionObject
  functionPresent:=write.checked _ _ original.functionPresent
  functionKind:=by simpa only [Write.world,Write.scope,write.kind] using original.functionKind
  method:=(PropertyFrame.lookup_other base.heap write.target write.object write.key (JSString.ofString "modifyBuildingPrice")
    write.descriptor write.present (safe _ (by decide)) original.pricing.window.game).trans original.method }

end CookieClicker.JavaScript.CursorCatalogueWrite

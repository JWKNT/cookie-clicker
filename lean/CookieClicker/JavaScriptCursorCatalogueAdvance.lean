import CookieClicker.JavaScriptCursorQuoteCatalogue

/-! Actual allocation suffixes preserve the whole original Cursor catalogue.
No fresh caller or helper descriptor is introduced as a later premise. -/
namespace CookieClicker.JavaScript.CursorCatalogueAdvance
open CursorQuoteRegistry CursorQuoteCatalogue PriceRegistryAdvance
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

variable {before after : Machine}

def global (advance : Advance before after) {scope : EnvId} {name : String} {value : Value}
    (original : Global before scope name value) : Global after scope name value := {
  target:=original.target,depth:=original.depth
  chain:=by
    rw [advance.environments]
    exact TieredAllocation.append_path before.heap.environments advance.suffix name scope original.target original.depth original.chain
  room:=by rw [advance.environments,Array.size_append];have h:=original.room;omega
  globalRead:=by
    rw [advance.environments,advance.global]
    exact TieredAllocation.append_read before.heap.environments advance.suffix _ _ original.globalRead
  object:=original.object
  present:=by rw [advance.global];exact HeapExtension.checked_object advance.heap _ _ original.present
  kind:=original.kind,writable:=original.writable,enumerable:=original.enumerable,configurable:=original.configurable
  property:=by rw [advance.global];exact HeapExtension.lookup_property advance.heap _ _ _ original.property
  exclusions:=advance.exclusions.trans original.exclusions }

def member (advance : Advance before after) {math : ObjectId} {name : String}
    (original : MathMember before math name) : MathMember after math name := {
  function:=original.function,object:=original.object
  present:=HeapExtension.checked_object advance.heap _ _ original.present,kind:=original.kind
  property:=HeapExtension.lookup_property advance.heap _ _ _ original.property }

def arithmetic (advance : Advance before after) {scope cursor : ObjectId} {price owned free rate : UInt64}
    (original : World before scope cursor price owned free rate) : World after scope cursor price owned free rate := {
  game:=original.game,math:=original.math
  gameRead:=global advance original.gameRead,mathRead:=global advance original.mathRead
  mathObject:=original.mathObject,mathPresent:=HeapExtension.checked_object advance.heap _ _ original.mathPresent,mathKind:=original.mathKind
  maximum:=member advance original.maximum,power:=member advance original.power,ceiling:=member advance original.ceiling
  priceRead:=original.priceRead.extend advance.heap,amountRead:=original.amountRead.extend advance.heap
  freeRead:=original.freeRead.extend advance.heap,rateRead:=original.rateRead.extend advance.heap }

def catalogue (advance : Advance before after) {scope cursor : ObjectId} {price owned free rate : UInt64}
    (original : Catalogue before scope cursor price owned free rate) : Catalogue after scope cursor price owned free rate := {
  arithmetic:=arithmetic advance original.arithmetic
  pricing:=advance.world original.pricing,profile:=advance.profile original.profile
  sameGame:=original.sameGame,sameBuilding:=original.sameBuilding
  function:=original.function,source:=original.source,functionObject:=original.functionObject
  functionPresent:=HeapExtension.checked_object advance.heap _ _ original.functionPresent
  functionKind:=by simpa only [Advance.world,Advance.scope_id] using original.functionKind
  method:=by simpa only [Advance.world,Advance.window] using HeapExtension.lookup_property advance.heap _ _ _ original.method }

end CookieClicker.JavaScript.CursorCatalogueAdvance

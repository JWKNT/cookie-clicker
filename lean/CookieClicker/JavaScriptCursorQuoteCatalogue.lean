import CookieClicker.JavaScriptCursorQuotePrefix
import CookieClicker.JavaScriptCursorQuoteTail
import CookieClicker.JavaScriptPriceRegistryExecution

/-! A quote runs from one original source catalogue. The constructor derives
all later modifier inputs and the final Math.ceil binding after retained
allocations; no independent post-call heap is assumed. -/
namespace CookieClicker.JavaScript.CursorQuoteCatalogue
open SourceRead CursorQuoteRegistry
set_option maxRecDepth 32768
set_option maxHeartbeats 14000000

structure Catalogue (base : Machine) (scope cursor : ObjectId) (price owned free rate : UInt64) where
  arithmetic : World base scope cursor price owned free rate
  pricing : PriceRegistry.World base
  profile : PriceRegistryComplete.Profile pricing
  sameGame : arithmetic.game=pricing.window.game
  sameBuilding : profile.building=cursor
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (PriceSource.closure pricing.priceScope.path.closureScope source)
  method : lookupProperty base.heap pricing.window.game (JSString.ofString "modifyBuildingPrice")=
    .ok (some (.data (.object function) true true true))

def bodyBase (base : Machine) (cursor : ObjectId) : Machine :=
  {base with context:={base.context with thisValue:=.object cursor}}

def current (reverse : Bool) (base : Machine) (scope cursor : ObjectId) (s : CursorQuoteTail.State) : Machine :=
  CursorQuoteTail.machine reverse (bodyBase base cursor) base.heap.environments scope s

def advance (reverse : Bool) (base : Machine) (scope cursor game : ObjectId) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    PriceRegistryAdvance.Advance base
      (PriceCall.bodyBase (CursorQuoteTail.caller reverse (bodyBase base cursor) base.heap.environments scope s) game) := {
  heap:=HeapExtension.trans extension (HeapExtension.same_objects rfl)
  suffix:=#[⟨.declarative (CursorQuoteLocals.bindings s.values),some scope⟩]++s.suffix
  environments:=by simp only [CursorQuoteTail.caller,CursorQuoteTail.machine,CursorQuoteLocals.start,
    CursorQuoteLocals.heap,PriceCall.bodyBase,Array.push_eq_append,Array.append_assoc]
  global:=rfl,exclusions:=rfl }

def Catalogue.inputs {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (reverse : Bool) (s : CursorQuoteTail.State)
    (result : UInt64) (value : s.values.price=.number result)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    CursorQuoteTail.Inputs reverse (bodyBase base cursor) base.heap.environments scope s result := by
  let progress:=advance reverse base scope cursor catalogue.pricing.window.game s extension
  exact {
    game:=catalogue.pricing.window.game,function:=catalogue.function
    world:=progress.world catalogue.pricing,profile:=progress.profile catalogue.profile
    sameGame:=rfl,source:=catalogue.source,functionObject:=catalogue.functionObject
    method:=HeapExtension.lookup_property progress.heap _ _ _ catalogue.method
    functionPresent:=HeapExtension.checked_object progress.heap _ _ catalogue.functionPresent
    functionKind:=by simpa only [PriceRegistryAdvance.Advance.world,PriceRegistryAdvance.Advance.scope_id] using catalogue.functionKind
    gameRead:=by
      have read:=catalogue.arithmetic.gameRead.read reverse cursor s.objects s.values s.suffix
        (by simp [CursorQuoteLocals.bindings])
        (HeapExtension.trans extension (HeapExtension.same_objects rfl))
      simpa only [catalogue.sameGame,SourceRead.Reads,CursorQuoteRegistry.machine,
        CursorQuoteTail.caller,CursorQuoteTail.machine,bodyBase] using read
    receiver:=by simpa only [PriceRegistryAdvance.Advance.profile,bodyBase] using congrArg Value.object catalogue.sameBuilding.symm
    priceValue:=value }

def Catalogue.after {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (reverse : Bool) (s : CursorQuoteTail.State)
    (result : UInt64) (value : s.values.price=.number result)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) : CursorQuoteTail.State :=
  (catalogue.inputs reverse s result value extension).after

theorem Catalogue.retained {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (reverse : Bool) (s : CursorQuoteTail.State)
    (result : UInt64) (value : s.values.price=.number result)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    HeapExtension.Extends base.heap (current reverse base scope cursor (catalogue.after reverse s result value extension)).heap := by
  let input:=catalogue.inputs reverse s result value extension
  have retained:=PriceRegistryCall.retained_objects
    (CursorQuoteTail.caller reverse (bodyBase base cursor) base.heap.environments scope s)
    input.game input.function result input.world input.profile
  rw [input.layout] at retained
  have before : HeapExtension.Extends base.heap
      (CursorQuoteTail.caller reverse (bodyBase base cursor) base.heap.environments scope s).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  exact HeapExtension.trans before retained

def Catalogue.ceiling {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (reverse : Bool) (s : CursorQuoteTail.State)
    (result : UInt64) (value : s.values.price=.number result)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    BuildingMathRead.Binding (current reverse base scope cursor (catalogue.after reverse s result value extension)) "ceil" :=
  catalogue.arithmetic.binding catalogue.arithmetic.ceiling reverse
    (catalogue.after reverse s result value extension).objects
    (catalogue.after reverse s result value extension).values
    (catalogue.after reverse s result value extension).suffix
    (catalogue.retained reverse s result value extension)

def buyState (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (price free rate : UInt64) : CursorQuoteTail.State :=
  ⟨objects,CursorQuotePrefix.afterBuy values price free rate,suffix,some (.number (CursorQuotePrefix.sum price free rate))⟩

theorem Catalogue.native_sum_body {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price Number.one free rate)
    (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (amount : values.amount=.number Number.one)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments})
    (stable : Number.mul (CursorQuotePrefix.sum price free rate) Number.one=CursorQuotePrefix.sum price free rate)
    (fuel : Nat) :
    let s:=buyState objects values suffix price free rate
    Builtins.run (1399+fuel) (CursorQuoteRegistry.machine false base scope cursor objects values suffix)=
      Builtins.run fuel {current false base scope cursor
        (catalogue.after false s (CursorQuotePrefix.sum price free rate) rfl extension) with
        control:=.completion (.return (.number (Number.ceil (CursorQuotePrefix.sum price free rate))))} := by
  dsimp only
  rw [show 1399+fuel=170+(1229+fuel) by omega,
    CursorQuotePrefix.native_buy_prefix base scope cursor price free rate catalogue.arithmetic objects values suffix amount extension]
  exact (catalogue.inputs false (buyState objects values suffix price free rate)
    (CursorQuotePrefix.sum price free rate) rfl extension).native_sum_tail stable
      (catalogue.ceiling false (buyState objects values suffix price free rate)
        (CursorQuotePrefix.sum price free rate) rfl extension) fuel

end CookieClicker.JavaScript.CursorQuoteCatalogue

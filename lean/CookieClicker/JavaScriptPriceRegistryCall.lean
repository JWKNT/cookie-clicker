import CookieClicker.JavaScriptPriceRegistryComplete
import CookieClicker.JavaScriptPriceCallRetention

/-! The complete price-modifier invocation now takes one original catalogue.
It constructs, rather than assumes, every later helper input after allocation. -/
namespace CookieClicker.JavaScript.PriceRegistryCall
open SourceRead PriceRegistryScope PriceRegistry PriceRegistryComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def inputs (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world) :
    PriceComplete.Inputs (PriceCall.bodyBase base game) base.heap.environments
      world.priceScope.path.closureScope (PriceCall.initial base profile.building function price) :=
  construct world profile (PriceCall.initial base profile.building function price)
    (HeapExtension.trans (HeapExtension.append_object base.heap
      (PriceSource.argumentObject base profile.building price (some function))) (HeapExtension.same_objects rfl)) rfl

def returned (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world) : Machine :=
  PriceCall.returned base world.priceScope.path.closureScope game profile.building function price
    (inputs base game function price world profile)

theorem prepared_returns (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1186+fuel)
      (PriceSource.prepared base world.priceScope.path.closureScope game profile.building price (some function))=
      Builtins.run fuel (returned base game function price world profile) :=
  PriceCall.prepared_returns base world.priceScope.path.closureScope game profile.building function price
    (inputs base game function price world profile) stable fuel

theorem source_call (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world)
    (source : Option JSString) (functionObject : JSObject)
    (sameGame : world.window.game=game)
    (method : lookupProperty base.heap game (JSString.ofString "modifyBuildingPrice")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (PriceSource.closure world.priceScope.path.closureScope source))
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (first second : Expr) (firstTicks secondTicks : Nat)
    (firstRead : Reads base first (.object profile.building) firstTicks)
    (secondRead : Reads base second (.number price) secondTicks)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (firstTicks+secondTicks+1198+fuel) {base with control:=.expression (PriceCall.expression first second)}=
      Builtins.run fuel (returned base game function price world profile) := by
  exact PriceCall.source_call base world.priceScope.path.closureScope game profile.building function price
    (inputs base game function price world profile) stable source world.gameObject functionObject first second firstTicks secondTicks
    (by simpa only [PriceCall.bodyBase,sameGame] using world.gamePresent) world.gameKind method
    functionPresent functionKind gameRead firstRead secondRead fuel

theorem retained_objects (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world) :
    HeapExtension.Extends base.heap (returned base game function price world profile).heap :=
  PriceCallRetention.returned_extends base world.priceScope.path.closureScope game profile.building function price
    (inputs base game function price world profile)

end CookieClicker.JavaScript.PriceRegistryCall

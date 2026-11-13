import CookieClicker.JavaScriptPriceRegistryScope

/-! A single source descriptor catalogue constructs the Has contracts at all
price-modifier stages. Original object positions and lexical paths are arbitrary;
actual call allocations extend them, rather than replace later frame premises. -/
namespace CookieClicker.JavaScript.PriceRegistry
open HasEnvironment SourceRead TieredRead PriceStages PriceRegistryScope
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

structure World (base : Machine) where
  window : Window base
  priceScope : ClosureScope base
  gameObject : JSObject
  gamePresent : checkedObject base.heap window.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  has : Method base window.game "Has" HasInvocation.closure
  aura : Method base window.game "auraMult" AuraSource.closure
  buffs : Method base window.game "hasBuff" HasBuffCall.closure
  effect : Method base window.game "eff" EffCall.closure
  auraWorld : AuraRead.World base
  auraGame : auraWorld.game=window.game
  buffTable : ObjectId
  buffObject : JSObject
  buffPresent : checkedObject base.heap buffTable=.ok buffObject
  buffKind : buffObject.kind=.ordinary
  buffProperty : lookupProperty base.heap window.game (JSString.ofString "buffs")=
    .ok (some (.data (.object buffTable) true true true))
  effectTable : ObjectId
  effectObject : JSObject
  effectPresent : checkedObject base.heap effectTable=.ok effectObject
  effectKind : effectObject.kind=.ordinary
  effectProperty : lookupProperty base.heap window.game (JSString.ofString "effs")=
    .ok (some (.data (.object effectTable) true true true))

structure Upgrade {base : Machine} (world : World base) (name : JSString) where
  frame : HasFrame.Frame name (.number 0)
  game : frame.game=world.window.game
  window : frame.window=base.globalObject
  objects : frame.objects=base.heap.objects

def current {base : Machine} (world : World base) (s : State) : Machine :=
  machine base base.heap.environments world.priceScope.path.closureScope s

def Upgrade.scopes {base : Machine} {world : World base} {name : JSString}
    (row : Upgrade world name) (s : State) : Scopes row.frame.window := {
  environments := (world.has.scope.atPrice world.priceScope.path.closureScope s).environments
  closureScope := world.has.scope.path.closureScope
  globalScope := world.has.scope.path.globalScope
  depth := world.has.scope.path.depth
  chain := (world.has.scope.atPrice world.priceScope.path.closureScope s).chain
  globalRead := by
    simpa only [row.window,ClosureScope.atPrice,extendScopes] using (world.has.scope.atPrice world.priceScope.path.closureScope s).globalRead
  depthBound := (world.has.scope.atPrice world.priceScope.path.closureScope s).depthBound }

def upgrade {base : Machine} {world : World base} {name : JSString}
    (row : Upgrade world name) (s : State)
    (extension : HeapExtension.Extends base.heap (current world s).heap) :
    TieredSuffix.HasZero (current world s) name := {
  frame:=extendHasFrame base (current world s) row.frame row.objects.symm extension
  scopes:=row.scopes s
  objects:=rfl
  environments:=by
    simpa only [Upgrade.scopes,current] using
      (world.has.scope.atPrice_environments world.priceScope.path.closureScope s).symm
  global:=row.window.symm
  exclusions:=world.window.exclusions
  function:=world.has.function
  source:=world.has.source
  functionObject:=world.has.object
  functionRead:=HeapExtension.checked_object extension _ _ world.has.present
  functionKind:=world.has.kind
  gameHas:=by
    simpa only [extendHasFrame,row.game] using HeapExtension.lookup_property extension _ _ _ world.has.property
  gameRead:=by
    simpa only [extendHasFrame,row.game,current] using currentGame base world.window world.priceScope s extension }

theorem upgrade_extends {base : Machine} {world : World base} {name : JSString}
    (row : Upgrade world name) (s : State)
    (extension : HeapExtension.Extends base.heap (current world s).heap) :
    HeapExtension.Extends base.heap
      (current world (PriceComplete.upgradeAfter (upgrade row s extension))).heap :=
  HeapExtension.trans extension (PriceRetention.upgrade (upgrade row s extension))

end CookieClicker.JavaScript.PriceRegistry

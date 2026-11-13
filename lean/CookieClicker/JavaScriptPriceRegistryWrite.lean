import CookieClicker.JavaScriptPriceRegistryComplete
import CookieClicker.JavaScriptPropertyFrame

/-! Native economic writes can rebuild the immutable pricing catalogue.
The changed object is retained with its real new descriptor. Existing source
function identities, closure paths and unrelated native fields are preserved. -/
namespace CookieClicker.JavaScript.PriceRegistryWrite
open SourceRead TieredRead PriceRegistryScope PriceRegistry PriceRegistryHelpers PriceRegistryComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def protectedNames : List String := ["Game","Has","auraMult","hasBuff","eff","buffs","effs",
  "dragonAuras","dragonAura","dragonAura2","0","name","Upgrades","ascensionMode","fortune",
  "Season savings","Santa's dominion","Faberge egg","Divine discount","Fortune #100","hasGod",
  "gods","slot","creation","id","1","2","Everything must go","Crafty pixies","Nasty goblins","buildingCost"]

structure Write (base : Machine) where
  target : ObjectId
  object : JSObject
  key : JSString
  descriptor : PropertyDescriptor
  present : base.heap.object? target=some object
  protectedFields : ∀ name∈protectedNames, key≠JSString.ofString name

namespace Write

def after {base : Machine} (write : Write base) : Machine := {base with
  heap:=PropertyFrame.replace base.heap write.target (setOwnProperty write.object write.key write.descriptor) }

def transformed {base : Machine} (write : Write base) (id : ObjectId) (object : JSObject) : JSObject :=
  PropertyFrame.transformed write.target id object write.key write.descriptor

theorem checked {base : Machine} (write : Write base) (id : ObjectId) (object : JSObject)
    (present : checkedObject base.heap id=.ok object) :
    checkedObject write.after.heap id=.ok (write.transformed id object) :=
  PropertyFrame.transformed_checked base.heap write.target write.object write.key write.descriptor write.present id object present

theorem kind {base : Machine} (write : Write base) (id : ObjectId) (object : JSObject) :
    (write.transformed id object).kind=object.kind := PropertyFrame.transformed_kind _ _ _ _ _

theorem lookup {base : Machine} (write : Write base) (id : ObjectId) (name : String)
    (member : name∈protectedNames) :
    lookupProperty write.after.heap id (JSString.ofString name)=lookupProperty base.heap id (JSString.ofString name) :=
  PropertyFrame.lookup_other base.heap write.target write.object write.key (JSString.ofString name)
    write.descriptor write.present (write.protectedFields name member) id

def window {base : Machine} (write : Write base) (old : Window base) : Window write.after := {
  game:=old.game,object:=write.transformed base.globalObject old.object
  present:=write.checked _ _ old.present
  kind:=by simpa only [write.kind] using old.kind
  property:=by
    change lookupProperty write.after.heap base.globalObject (JSString.ofString "Game")=_
    rw [write.lookup _ "Game" (by decide)]
    exact old.property
  exclusions:=old.exclusions }

def scope {base : Machine} (write : Write base) (old : ClosureScope base) : ClosureScope write.after := {
  path:=old.path,environments:=old.environments }

def method {base : Machine} (write : Write base) {game : ObjectId} {name : String}
    {body : EnvId→Option JSString→FunctionClosure} (old : Method base game name body)
    (member : name∈protectedNames) : Method write.after game name body := {
  scope:=write.scope old.scope,function:=old.function,source:=old.source,object:=write.transformed old.function old.object
  present:=write.checked _ _ old.present
  kind:=by simpa only [write.kind,scope] using old.kind
  property:=by simpa only [write.lookup _ name member] using old.property }

def auraWorld {base : Machine} (write : Write base) (old : AuraRead.World base) : AuraRead.World write.after := {
  game:=old.game,auras:=old.auras,emptyAura:=old.emptyAura
  table:=PropertyFrame.edge old.table write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
  first:=PropertyFrame.edge old.first write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
  second:=PropertyFrame.edge old.second write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
  zeroEntry:=PropertyFrame.edge old.zeroEntry write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
  name:=PropertyFrame.edge old.name write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide)) }

def world {base : Machine} (write : Write base) (old : World base) : World write.after := {
  window:=write.window old.window,priceScope:=write.scope old.priceScope
  gameObject:=write.transformed old.window.game old.gameObject
  gamePresent:=write.checked _ _ old.gamePresent
  gameKind:=by simpa only [write.kind] using old.gameKind
  has:=write.method old.has (by decide)
  aura:=write.method old.aura (by decide)
  buffs:=write.method old.buffs (by decide)
  effect:=write.method old.effect (by decide)
  auraWorld:=write.auraWorld old.auraWorld
  auraGame:=old.auraGame
  buffTable:=old.buffTable,buffObject:=write.transformed old.buffTable old.buffObject
  buffPresent:=write.checked _ _ old.buffPresent
  buffKind:=by simpa only [write.kind] using old.buffKind
  buffProperty:=by simpa only [window,write.lookup _ "buffs" (by decide)] using old.buffProperty
  effectTable:=old.effectTable,effectObject:=write.transformed old.effectTable old.effectObject
  effectPresent:=write.checked _ _ old.effectPresent
  effectKind:=by simpa only [write.kind] using old.effectKind
  effectProperty:=by simpa only [window,write.lookup _ "effs" (by decide)] using old.effectProperty }

end Write

end CookieClicker.JavaScript.PriceRegistryWrite

import CookieClicker.JavaScriptPriceRegistry

/-! Price helper inputs are derived from the same original object catalogue.
Every later source frame is built after the previous real allocation. -/
namespace CookieClicker.JavaScript.PriceRegistryHelpers
open HasEnvironment SourceRead TieredRead PriceStages PriceRegistryScope PriceRegistry
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem buff_callee {base : Machine} (world : World base) (s : State) (name : JSString)
    (extension : HeapExtension.Extends base.heap (current world s).heap) :
    Reads (HasBuffCall.started (current world s) world.buffs.scope.path.closureScope
      world.window.game name (some world.buffs.function)) (.identifier "Game") (.object world.window.game) 3 := by
  let before:=current world s
  let scopes:=world.buffs.scope.atPrice world.priceScope.path.closureScope s
  apply AllocatedGameRead.appended before _ scopes (HasBuffCall.locals before name)
    world.window.game world.window.object (world.buffs.scope.atPrice_environments _ _) rfl rfl
    (writable:=true) (enumerable:=true) (configurable:=false)
  · simp [HasBuffCall.locals]
  · exact HeapExtension.trans (HeapExtension.append_object before.heap
      (HasBuffCall.argumentObject before name (some world.buffs.function))) (HeapExtension.same_objects rfl)
  · exact HeapExtension.checked_object extension _ _ world.window.present
  · exact world.window.kind
  · exact HeapExtension.lookup_property extension _ _ _ world.window.property
  · exact world.window.exclusions

def buff {base : Machine} (world : World base) (s : State) (name : JSString)
    (extension : HeapExtension.Extends base.heap (current world s).heap)
    (missing : lookupProperty base.heap world.buffTable name=.ok none) :
    PriceCalls.Buff (current world s) name := {
  scope:=world.buffs.scope.path.closureScope,game:=world.window.game,effects:=world.buffTable
  function:=world.buffs.function,source:=world.buffs.source
  gameObject:=world.gameObject,effectsObject:=world.buffObject,functionObject:=world.buffs.object
  gamePresent:=HeapExtension.checked_object extension _ _ world.gamePresent
  gameKind:=world.gameKind
  method:=HeapExtension.lookup_property extension _ _ _ world.buffs.property
  functionPresent:=HeapExtension.checked_object extension _ _ world.buffs.present
  functionKind:=world.buffs.kind
  effectsProperty:=HeapExtension.lookup_property extension _ _ _ world.buffProperty
  effectsPresent:=HeapExtension.checked_object extension _ _ world.buffPresent
  effectsKind:=world.buffKind
  missing:=HeapExtension.lookup_property extension _ _ _ missing
  callerGame:=currentGame base world.window world.priceScope s extension
  calleeGame:=buff_callee world s name extension }

def effect {base : Machine} (world : World base) (s : State) (name : JSString)
    (extension : HeapExtension.Extends base.heap (current world s).heap)
    (missing : lookupProperty base.heap world.effectTable name=.ok none) :
    PriceCalls.Effect (current world s) name := {
  scope:=world.effect.scope.path.closureScope,game:=world.window.game,effects:=world.effectTable
  function:=world.effect.function,source:=world.effect.source
  gameObject:=world.gameObject,effectsObject:=world.effectObject,functionObject:=world.effect.object
  gamePresent:=HeapExtension.checked_object extension _ _ world.gamePresent
  gameKind:=world.gameKind
  method:=HeapExtension.lookup_property extension _ _ _ world.effect.property
  functionPresent:=HeapExtension.checked_object extension _ _ world.effect.present
  functionKind:=world.effect.kind
  effectsProperty:=HeapExtension.lookup_property extension _ _ _ world.effectProperty
  effectsPresent:=HeapExtension.checked_object extension _ _ world.effectPresent
  effectsKind:=world.effectKind
  missing:=HeapExtension.lookup_property extension _ _ _ missing
  callerGame:=currentGame base world.window world.priceScope s extension
  calleeGame:=AllocatedGameRead.eff_callee (current world s)
    (world.effect.scope.atPrice world.priceScope.path.closureScope s) world.window.game name world.effect.function
    world.window.object (world.effect.scope.atPrice_environments _ _)
    (HeapExtension.checked_object extension _ _ world.window.present) world.window.kind true true false
    (HeapExtension.lookup_property extension _ _ _ world.window.property) world.window.exclusions }

private theorem aura_callee {base : Machine} (world : World base) (s : State) (name : JSString)
    (extension : HeapExtension.Extends base.heap (current world s).heap) :
    Reads (AuraCall.state (current world s) world.aura.scope.path.closureScope
      world.window.game name world.aura.function (.number 0)) (.identifier "Game") (.object world.window.game) 3 := by
  let before:=current world s
  let scopes:=world.aura.scope.atPrice world.priceScope.path.closureScope s
  apply AllocatedGameRead.appended before _ scopes
    (AuraLocals.bindings (AuraCall.values before name (.number 0))) world.window.game world.window.object
    (world.aura.scope.atPrice_environments _ _) (by simp [AuraCall.state,AuraLocals.start,AuraLocals.heap,before,scopes,ClosureScope.atPrice,extendScopes]) rfl
    (writable:=true) (enumerable:=true) (configurable:=false)
  · simp [AuraLocals.bindings]
  · exact AuraCall.state_extends before scopes.closureScope world.window.game name world.aura.function (.number 0)
  · exact HeapExtension.checked_object extension _ _ world.window.present
  · exact world.window.kind
  · exact HeapExtension.lookup_property extension _ _ _ world.window.property
  · exact world.window.exclusions

def aura {base : Machine} (world : World base) (s : State) (name : JSString)
    (extension : HeapExtension.Extends base.heap (current world s).heap)
    (different : AuraRead.noAura≠name) : PriceCalls.Aura (current world s) name := {
  scope:=world.aura.scope.path.closureScope
  world:=AuraCall.extendWorld world.auraWorld extension
  function:=world.aura.function,source:=world.aura.source
  gameObject:=world.gameObject,functionObject:=world.aura.object,other:=different
  gamePresent:=by
    simpa only [AuraCall.extendWorld,world.auraGame,current] using
      HeapExtension.checked_object extension _ _ world.gamePresent
  gameKind:=world.gameKind
  method:=by
    simpa only [AuraCall.extendWorld,world.auraGame,current] using
      HeapExtension.lookup_property extension _ _ _ world.aura.property
  functionPresent:=HeapExtension.checked_object extension _ _ world.aura.present
  functionKind:=world.aura.kind
  callerGame:=by
    simpa only [AuraCall.extendWorld,world.auraGame,current] using
      currentGame base world.window world.priceScope s extension
  calleeGame:=by
    simpa only [AuraCall.extendWorld,world.auraGame,current] using aura_callee world s name extension }

structure God {base : Machine} (world : World base) where
  scope : EnvId
  function : ObjectId
  source : Option JSString
  object : JSObject
  present : checkedObject base.heap function=.ok object
  kind : object.kind=.function (PantheonSource.closure scope source)
  property : lookupProperty base.heap world.window.game (JSString.ofString "hasGod")=
    .ok (some (.data (.object function) true true true))
  pantheon : PantheonRead.World base
  capture : PantheonRead.CapturedM base.heap.environments scope pantheon.m

def god {base : Machine} {world : World base} (entry : God world) (s : State)
    (extension : HeapExtension.Extends base.heap (current world s).heap) : PriceGod.Inputs (current world s) := {
  scope:=entry.scope,game:=world.window.game,function:=entry.function
  world:=entry.pantheon.extend (HeapExtension.trans extension
    (HeapExtension.trans (HeapExtension.append_object (current world s).heap
      (PantheonSource.argumentObject (current world s) (.string PantheonRead.creation) (some entry.function)))
      (HeapExtension.same_objects rfl)))
  capture:=appendCapture (entry.capture.append
    ⟨.declarative (PriceLocals.bindings s.values),some world.priceScope.path.closureScope⟩) s.suffix
  source:=entry.source,gameObject:=world.gameObject,functionObject:=entry.object
  gamePresent:=HeapExtension.checked_object extension _ _ world.gamePresent
  gameKind:=world.gameKind
  method:=HeapExtension.lookup_property extension _ _ _ entry.property
  functionPresent:=HeapExtension.checked_object extension _ _ entry.present
  functionKind:=entry.kind
  gameRead:=currentGame base world.window world.priceScope s extension }

end CookieClicker.JavaScript.PriceRegistryHelpers

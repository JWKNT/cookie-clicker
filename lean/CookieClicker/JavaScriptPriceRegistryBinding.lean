import CookieClicker.JavaScriptCapturedBindingWrite
import CookieClicker.JavaScriptPriceRegistryAdvance

/-! The original pricing catalogue survives a native caller binding write.
Every later closure path and captured M frame is constructed from the entry. -/
namespace CookieClicker.JavaScript.PriceRegistryBinding
open HasEnvironment SourceRead TieredRead PriceRegistryScope PriceRegistry PriceRegistryHelpers PriceRegistryComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {base : Machine} {name : String}

theorem extension (slot : SourceBinding.Slot base name) (value : Value) : HeapExtension.Extends base.heap (slot.after value).heap :=
  HeapExtension.same_objects rfl

def scope (slot : SourceBinding.Slot base name) (value : Value) (old : ClosureScope base) : ClosureScope (slot.after value) := by
  let path : OriginalNamePath.Path "Game" base.heap.environments old.path.closureScope base.globalObject := {
    target:=old.path.globalScope,depth:=old.path.depth
    chain:=by rw [←old.environments];exact old.path.chain
    room:=by rw [←old.environments];exact Nat.le_of_lt old.path.depthBound
    globalRead:=by rw [←old.environments];exact old.path.globalRead }
  let retained:=path.written slot value
  have bound : old.path.depth<(slot.after value).heap.environments.size := by
    simpa [SourceBinding.Slot.after,BindingWrite.changedHeap,old.environments] using old.path.depthBound
  exact {
    path:={
      environments:=(slot.after value).heap.environments,closureScope:=old.path.closureScope
      globalScope:=old.path.globalScope,depth:=old.path.depth
      chain:=retained.chain,globalRead:=retained.globalRead,depthBound:=bound}
    environments:=rfl }

theorem scope_id (slot : SourceBinding.Slot base name) (value : Value) (old : ClosureScope base) :
    (scope slot value old).path.closureScope=old.path.closureScope := rfl

def window (slot : SourceBinding.Slot base name) (value : Value) (old : Window base) : Window (slot.after value) := {
  game:=old.game,object:=old.object
  present:=HeapExtension.checked_object (extension slot value) _ _ old.present
  kind:=old.kind
  property:=HeapExtension.lookup_property (extension slot value) _ _ _ old.property
  exclusions:=old.exclusions }

def method (slot : SourceBinding.Slot base name) (value : Value) {game : ObjectId} {methodName : String}
    {body : EnvId→Option JSString→FunctionClosure} (old : Method base game methodName body) : Method (slot.after value) game methodName body := {
  scope:=scope slot value old.scope,function:=old.function,source:=old.source,object:=old.object
  present:=HeapExtension.checked_object (extension slot value) _ _ old.present
  kind:=old.kind
  property:=HeapExtension.lookup_property (extension slot value) _ _ _ old.property }

def world (slot : SourceBinding.Slot base name) (value : Value) (old : World base) : World (slot.after value) := {
  window:=window slot value old.window,priceScope:=scope slot value old.priceScope
  gameObject:=old.gameObject
  gamePresent:=HeapExtension.checked_object (extension slot value) _ _ old.gamePresent
  gameKind:=old.gameKind
  has:=method slot value old.has,aura:=method slot value old.aura,buffs:=method slot value old.buffs,effect:=method slot value old.effect
  auraWorld:=AuraCall.extendWorld old.auraWorld (extension slot value)
  auraGame:=old.auraGame
  buffTable:=old.buffTable,buffObject:=old.buffObject
  buffPresent:=HeapExtension.checked_object (extension slot value) _ _ old.buffPresent
  buffKind:=old.buffKind
  buffProperty:=HeapExtension.lookup_property (extension slot value) _ _ _ old.buffProperty
  effectTable:=old.effectTable,effectObject:=old.effectObject
  effectPresent:=HeapExtension.checked_object (extension slot value) _ _ old.effectPresent
  effectKind:=old.effectKind
  effectProperty:=HeapExtension.lookup_property (extension slot value) _ _ _ old.effectProperty }

def upgrade (slot : SourceBinding.Slot base name) (value : Value) {old : World base}
    {upgradeName : JSString} (row : Upgrade old upgradeName) : Upgrade (world slot value old) upgradeName := {
  frame:=row.frame,game:=row.game,window:=row.window,objects:=row.objects }

def god (slot : SourceBinding.Slot base name) (value : Value) (different : name≠"M")
    {old : World base} (entry : God old) : God (world slot value old) := {
  scope:=entry.scope,function:=entry.function,source:=entry.source,object:=entry.object
  present:=HeapExtension.checked_object (extension slot value) _ _ entry.present
  kind:=entry.kind
  property:=HeapExtension.lookup_property (extension slot value) _ _ _ entry.property
  pantheon:=entry.pantheon.extend (extension slot value)
  capture:=CapturedBindingWrite.capturedM slot value different entry.capture }

def profile (slot : SourceBinding.Slot base name) (value : Value) (different : name≠"M")
    {old : World base} (entry : Profile old) : Profile (world slot value old) := {
  savings:=upgrade slot value entry.savings,santa:=upgrade slot value entry.santa,egg:=upgrade slot value entry.egg
  divine:=upgrade slot value entry.divine,fortune100:=upgrade slot value entry.fortune100
  fortuneName:=entry.fortuneName,fortune:=upgrade slot value entry.fortune
  building:=entry.building,fortuneUpgrade:=entry.fortuneUpgrade
  fortuneSelected:=entry.fortuneSelected.extend (extension slot value)
  fortuneNameRead:=entry.fortuneNameRead.extend (extension slot value)
  everything:=HeapExtension.lookup_property (extension slot value) _ _ _ entry.everything
  pixies:=HeapExtension.lookup_property (extension slot value) _ _ _ entry.pixies
  goblins:=HeapExtension.lookup_property (extension slot value) _ _ _ entry.goblins
  effect:=HeapExtension.lookup_property (extension slot value) _ _ _ entry.effect
  god:=god slot value different entry.god }

theorem objects_unchanged (slot : SourceBinding.Slot base name) (value : Value) :
    (slot.after value).heap.objects=base.heap.objects := rfl

theorem closure_ids (slot : SourceBinding.Slot base name) (value : Value) (old : World base) :
    (world slot value old).priceScope.path.closureScope=old.priceScope.path.closureScope ∧
    (world slot value old).has.function=old.has.function ∧
    (world slot value old).aura.function=old.aura.function ∧
    (world slot value old).buffs.function=old.buffs.function ∧
    (world slot value old).effect.function=old.effect.function := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem captured_identity (slot : SourceBinding.Slot base name) (value : Value) (different : name≠"M")
    {old : World base} (entry : Profile old) :
    (profile slot value different entry).god.scope=entry.god.scope ∧
    (profile slot value different entry).god.function=entry.god.function ∧
    (profile slot value different entry).god.pantheon.m=entry.god.pantheon.m ∧
    (profile slot value different entry).god.capture.binding=entry.god.capture.binding :=
  ⟨rfl,rfl,rfl,CapturedBindingWrite.binding_preserved slot value different entry.god.capture⟩

end CookieClicker.JavaScript.PriceRegistryBinding

import CookieClicker.JavaScriptPriceRegistryComplete

/-! One pricing catalogue is retained across native argument allocations and
DOM text allocations. The full new heap and environment suffix are retained;
no finite-heap reset or independent later descriptor profile is assumed. -/
namespace CookieClicker.JavaScript.PriceRegistryAdvance
open HasEnvironment SourceRead TieredRead PriceRegistryScope PriceRegistry PriceRegistryHelpers PriceRegistryComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

structure Advance (before after : Machine) where
  heap : HeapExtension.Extends before.heap after.heap
  suffix : Array LexicalEnvironment
  environments : after.heap.environments=before.heap.environments++suffix
  global : after.globalObject=before.globalObject
  exclusions : after.objectEnvironmentExclusions=before.objectEnvironmentExclusions

namespace Advance

def refl (base : Machine) : Advance base base :=
  ⟨HeapExtension.refl _,#[],by simp,rfl,rfl⟩

def trans {a b c : Machine} (left : Advance a b) (right : Advance b c) : Advance a c :=
  ⟨HeapExtension.trans left.heap right.heap,left.suffix++right.suffix,
    by rw [right.environments,left.environments,Array.append_assoc],
    right.global.trans left.global,right.exclusions.trans left.exclusions⟩

def scope {before after : Machine} (advance : Advance before after)
    (old : ClosureScope before) : ClosureScope after := by
  let suffix:=advance.suffix
  have layout:=advance.environments
  exact {
    path:={
      environments:=after.heap.environments,closureScope:=old.path.closureScope
      globalScope:=old.path.globalScope,depth:=old.path.depth
      chain:=by
        rw [layout,←old.environments]
        exact TieredAllocation.append_path old.path.environments suffix "Game" _ _ _ old.path.chain
      globalRead:=by
        rw [layout,advance.global,←old.environments]
        exact TieredAllocation.append_read old.path.environments suffix _ _ old.path.globalRead
      depthBound:=by
        rw [layout,Array.size_append,←old.environments]
        have :=old.path.depthBound;omega }
    environments:=rfl }

theorem scope_id {before after : Machine} (advance : Advance before after) (old : ClosureScope before) :
    (advance.scope old).path.closureScope=old.path.closureScope := by
  rfl

def window {before after : Machine} (advance : Advance before after) (old : Window before) : Window after := {
  game:=old.game,object:=old.object
  present:=by rw [advance.global];exact HeapExtension.checked_object advance.heap _ _ old.present
  kind:=old.kind
  property:=by rw [advance.global];exact HeapExtension.lookup_property advance.heap _ _ _ old.property
  exclusions:=advance.exclusions.trans old.exclusions }

def method {before after : Machine} (advance : Advance before after) {game : ObjectId} {name : String}
    {body : EnvId→Option JSString→FunctionClosure} (old : Method before game name body) : Method after game name body := {
  scope:=advance.scope old.scope,function:=old.function,source:=old.source,object:=old.object
  present:=HeapExtension.checked_object advance.heap _ _ old.present
  kind:=by simpa only [advance.scope_id] using old.kind
  property:=HeapExtension.lookup_property advance.heap _ _ _ old.property }

def world {before after : Machine} (advance : Advance before after) (old : World before) : World after := {
  window:=advance.window old.window,priceScope:=advance.scope old.priceScope
  gameObject:=old.gameObject
  gamePresent:=HeapExtension.checked_object advance.heap _ _ old.gamePresent
  gameKind:=old.gameKind
  has:=advance.method old.has,aura:=advance.method old.aura,buffs:=advance.method old.buffs,effect:=advance.method old.effect
  auraWorld:=AuraCall.extendWorld old.auraWorld advance.heap
  auraGame:=old.auraGame
  buffTable:=old.buffTable,buffObject:=old.buffObject
  buffPresent:=HeapExtension.checked_object advance.heap _ _ old.buffPresent
  buffKind:=old.buffKind
  buffProperty:=HeapExtension.lookup_property advance.heap _ _ _ old.buffProperty
  effectTable:=old.effectTable,effectObject:=old.effectObject
  effectPresent:=HeapExtension.checked_object advance.heap _ _ old.effectPresent
  effectKind:=old.effectKind
  effectProperty:=HeapExtension.lookup_property advance.heap _ _ _ old.effectProperty }

def upgrade {before after : Machine} (advance : Advance before after) {old : World before}
    {name : JSString} (row : Upgrade old name) : Upgrade (advance.world old) name := {
  frame:=extendHasFrame before after row.frame row.objects.symm advance.heap
  game:=row.game,window:=row.window.trans advance.global.symm,objects:=rfl }

def god {before after : Machine} (advance : Advance before after) {old : World before}
    (entry : God old) : God (advance.world old) := by
  let suffix:=advance.suffix
  have layout:=advance.environments
  exact {
    scope:=entry.scope,function:=entry.function,source:=entry.source,object:=entry.object
    present:=HeapExtension.checked_object advance.heap _ _ entry.present
    kind:=entry.kind
    property:=HeapExtension.lookup_property advance.heap _ _ _ entry.property
    pantheon:=entry.pantheon.extend advance.heap
    capture:=by rw [layout];exact appendCapture entry.capture suffix }

def profile {before after : Machine} (advance : Advance before after) {old : World before}
    (entry : Profile old) : Profile (advance.world old) := {
  savings:=advance.upgrade entry.savings,santa:=advance.upgrade entry.santa,egg:=advance.upgrade entry.egg
  divine:=advance.upgrade entry.divine,fortune100:=advance.upgrade entry.fortune100
  fortuneName:=entry.fortuneName,fortune:=advance.upgrade entry.fortune
  building:=entry.building,fortuneUpgrade:=entry.fortuneUpgrade
  fortuneSelected:=entry.fortuneSelected.extend advance.heap
  fortuneNameRead:=entry.fortuneNameRead.extend advance.heap
  everything:=HeapExtension.lookup_property advance.heap _ _ _ entry.everything
  pixies:=HeapExtension.lookup_property advance.heap _ _ _ entry.pixies
  goblins:=HeapExtension.lookup_property advance.heap _ _ _ entry.goblins
  effect:=HeapExtension.lookup_property advance.heap _ _ _ entry.effect
  god:=advance.god entry.god }

end Advance
end CookieClicker.JavaScript.PriceRegistryAdvance

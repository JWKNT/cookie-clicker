import CookieClicker.JavaScriptPriceRegistryUpgradeWrite

/-! A coherent price profile survives the native cycle's economic writes.
Upgrade ownership is preserved by object separation when the Cursor's bought
counter is written. Every reconstructed helper still executes its source body. -/
namespace CookieClicker.JavaScript.PriceRegistryWrite.Write
open SourceRead TieredRead PriceRegistryScope PriceRegistry PriceRegistryHelpers PriceRegistryComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def god {base : Machine} {old : World base} (write : Write base) (entry : God old) : God (write.world old) := {
  scope:=entry.scope,function:=entry.function,source:=entry.source
  object:=write.transformed entry.function entry.object
  present:=write.checked _ _ entry.present
  kind:=by simpa only [write.kind] using entry.kind
  property:=by simpa only [world,window,write.lookup _ "hasGod" (by decide)] using entry.property
  pantheon:={
    m:=entry.pantheon.m,gods:=entry.pantheon.gods,slots:=entry.pantheon.slots,god:=entry.pantheon.god
    godsRead:=PropertyFrame.edge entry.pantheon.godsRead write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
    slotRead:=PropertyFrame.edge entry.pantheon.slotRead write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
    selectedRead:=PropertyFrame.edge entry.pantheon.selectedRead write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
    idRead:=PropertyFrame.edge entry.pantheon.idRead write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
    slotsRead:=fun i=>PropertyFrame.edge (entry.pantheon.slotsRead i) write.target write.object write.key write.descriptor write.present (by
      have finite : ∀ i : Fin 3, toString i.val∈protectedNames := by decide +kernel
      exact write.protectedFields (toString i.val) (finite i)) }
  capture:=entry.capture }

def upgradeIds {base : Machine} {old : World base} (profile : Profile old) : List ObjectId :=
  [profile.savings.frame.upgrade,profile.santa.frame.upgrade,profile.egg.frame.upgrade,
   profile.divine.frame.upgrade,profile.fortune100.frame.upgrade,profile.fortune.frame.upgrade]

structure OwnershipSafe {base : Machine} {old : World base} (write : Write base) (profile : Profile old) : Prop where
  fortuneKey : write.key≠profile.fortuneName
  bought : ∀ id∈upgradeIds profile, write.target≠id ∨ write.key≠JSString.ofString "bought"

def profile {base : Machine} {old : World base} (write : Write base) (entry : Profile old)
    (safe : OwnershipSafe write entry) : Profile (write.world old) := {
  savings:=write.upgrade entry.savings (write.protectedFields _ (by decide)) (safe.bought _ (by simp [upgradeIds]))
  santa:=write.upgrade entry.santa (write.protectedFields _ (by decide)) (safe.bought _ (by simp [upgradeIds]))
  egg:=write.upgrade entry.egg (write.protectedFields _ (by decide)) (safe.bought _ (by simp [upgradeIds]))
  divine:=write.upgrade entry.divine (write.protectedFields _ (by decide)) (safe.bought _ (by simp [upgradeIds]))
  fortune100:=write.upgrade entry.fortune100 (write.protectedFields _ (by decide)) (safe.bought _ (by simp [upgradeIds]))
  fortuneName:=entry.fortuneName
  fortune:=write.upgrade entry.fortune safe.fortuneKey (safe.bought _ (by simp [upgradeIds]))
  building:=entry.building,fortuneUpgrade:=entry.fortuneUpgrade
  fortuneSelected:=PropertyFrame.edge entry.fortuneSelected write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
  fortuneNameRead:=PropertyFrame.edge entry.fortuneNameRead write.target write.object write.key write.descriptor write.present (write.protectedFields _ (by decide))
  everything:=by simpa only [world,write.lookup _ "Everything must go" (by decide)] using entry.everything
  pixies:=by simpa only [world,write.lookup _ "Crafty pixies" (by decide)] using entry.pixies
  goblins:=by simpa only [world,write.lookup _ "Nasty goblins" (by decide)] using entry.goblins
  effect:=by simpa only [world,PriceStatements.effectName,write.lookup _ "buildingCost" (by decide)] using entry.effect
  god:=write.god entry.god }

theorem native_price_after_write {base : Machine} {old : World base} (write : Write base)
    (entry : Profile old) (safe : OwnershipSafe write entry) (s : PriceStages.State)
    (extension : HeapExtension.Extends write.after.heap (current (write.world old) s).heap)
    (building : s.values.building=.object entry.building)
    (price : UInt64) (value : s.values.price=.number price)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1152+fuel) (current (write.world old) s)=
      Builtins.run fuel {current (write.world old)
        (construct (write.world old) (write.profile entry safe) s extension building).final with
        control:=.completion (.return (.number price))} :=
  PriceRegistryComplete.native_body (write.world old) (write.profile entry safe) s extension building price value stable fuel

end CookieClicker.JavaScript.PriceRegistryWrite.Write

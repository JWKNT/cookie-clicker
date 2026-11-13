import CookieClicker.JavaScriptPriceRegistryWrite

/-! Reconstruction of actual Has ownership frames after a native data write.
A Cursor bought-counter write may share its property name with upgrades. The
proof therefore uses object separation for that field, not a false key-only rule. -/
namespace CookieClicker.JavaScript.PriceRegistryWrite.Write
open SourceRead TieredRead PriceRegistryScope PriceRegistry PriceRegistryWrite
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem own {base : Machine} (write : Write base) (id : ObjectId) (object : JSObject)
    (name : JSString) (safe : write.target≠id ∨ write.key≠name) :
    ownProperty (write.transformed id object) name=ownProperty object name := by
  rcases safe with differentObject|differentName
  · simp only [transformed,PropertyFrame.transformed,Ne.symm differentObject,↓reduceIte]
  · exact PropertyFrame.transformed_own _ _ _ _ _ _ differentName

theorem read {base : Machine} (write : Write base) (id : ObjectId) (object : JSObject)
    (present : base.heap.objects[id]?=some object) :
    write.after.heap.objects[id]?=some (write.transformed id object) :=
  PropertyFrame.transformed_read base.heap write.target write.object write.key write.descriptor write.present id object present

def upgrade {base : Machine} {old : World base} {name : JSString} (write : Write base)
    (row : Upgrade old name) (differentName : write.key≠name)
    (differentBought : write.target≠row.frame.upgrade ∨ write.key≠JSString.ofString "bought") :
    Upgrade (write.world old) name := {
  frame:={
    objects:=write.after.heap.objects
    game:=row.frame.game,window:=row.frame.window,table:=row.frame.table,upgrade:=row.frame.upgrade
    gameObject:=write.transformed row.frame.game row.frame.gameObject
    windowObject:=write.transformed row.frame.window row.frame.windowObject
    tableObject:=write.transformed row.frame.table row.frame.tableObject
    upgradeObject:=write.transformed row.frame.upgrade row.frame.upgradeObject
    gameRead:=write.read _ _ (by simpa only [row.objects] using row.frame.gameRead)
    windowRead:=write.read _ _ (by simpa only [row.objects] using row.frame.windowRead)
    tableRead:=write.read _ _ (by simpa only [row.objects] using row.frame.tableRead)
    upgradeRead:=write.read _ _ (by simpa only [row.objects] using row.frame.upgradeRead)
    gameKnown:=by simpa only [transformed,PropertyFrame.transformed_unresolved] using row.frame.gameKnown
    windowKnown:=by simpa only [transformed,PropertyFrame.transformed_unresolved] using row.frame.windowKnown
    tableKnown:=by simpa only [transformed,PropertyFrame.transformed_unresolved] using row.frame.tableKnown
    upgradeKnown:=by simpa only [transformed,PropertyFrame.transformed_unresolved] using row.frame.upgradeKnown
    gameKind:=by simpa only [write.kind] using row.frame.gameKind
    windowKind:=by simpa only [write.kind] using row.frame.windowKind
    tableKind:=by simpa only [write.kind] using row.frame.tableKind
    upgradeKind:=by simpa only [write.kind] using row.frame.upgradeKind
    windowGame:=by
      rw [write.own _ _ _ (Or.inr (write.protectedFields _ (by decide)))]
      exact row.frame.windowGame
    gameTable:=by
      rw [write.own _ _ _ (Or.inr (write.protectedFields _ (by decide)))]
      exact row.frame.gameTable
    normalMode:=by
      rw [write.own _ _ _ (Or.inr (write.protectedFields _ (by decide)))]
      exact row.frame.normalMode
    selectedUpgrade:=by
      rw [write.own _ _ _ (Or.inr differentName)]
      exact row.frame.selectedUpgrade
    boughtValue:=by
      rw [write.own _ _ _ differentBought]
      exact row.frame.boughtValue }
  game:=row.game,window:=row.window,objects:=rfl }

end CookieClicker.JavaScript.PriceRegistryWrite.Write

import CookieClicker.JavaScriptSaleNumericPreservation
import CookieClicker.JavaScriptCursorCatalogueWrite

/-! The three successful-sale property changes are the actual native writes.
These equations connect the generic catalogue transport to the source result. -/
namespace CookieClicker.JavaScript.SaleNumericWrites
open SaleNumericFrame PriceRegistryWrite
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

variable {base : Machine}

def cookies (entry : Entry base) : Write entry.afterMoni := {
  target:=entry.counter.game,object:=entry.counter.gameObject
  key:=JSString.ofString "cookies",descriptor:=.data (.number entry.newCookies) true true true
  present:=by rw [entry.moniHeap];exact entry.counter.gameRead
  protectedFields:=by decide }

theorem cookies_machine (entry : Entry base) : (cookies entry).after=entry.afterCookies := by
  have kept : (cookies entry).after.heap=entry.afterCookies.heap:=entry.cookiesWrite
  change {entry.afterMoni with heap:=(cookies entry).after.heap}=entry.afterCookies
  rw [kept]
  rfl

def earned (entry : Entry base) : Write (cookies entry).after := {
  target:=entry.counter.game,object:=entry.cookiesFrame.gameObject
  key:=JSString.ofString "cookiesEarned",descriptor:=.data (.number entry.newEarned) true true true
  present:=by rw [cookies_machine];exact entry.cookiesFrame.gameRead
  protectedFields:=by decide }

theorem earned_machine (entry : Entry base) : (earned entry).after=entry.afterEarned := by
  change {(cookies entry).after with
    heap:=PropertyFrame.write (cookies entry).after.heap
      entry.counter.game entry.cookiesFrame.gameObject (JSString.ofString "cookiesEarned")
      (.number entry.newEarned) true true}=entry.afterEarned
  rw [cookies_machine]
  rfl

def amount (entry : Entry base) : Write (earned entry).after := {
  target:=entry.building,object:=entry.buildingObject
  key:=JSString.ofString "amount",descriptor:=.data (.number (Number.sub entry.amount Number.one)) true true true
  present:=by rw [earned_machine];exact entry.buildingPresentEarned
  protectedFields:=by decide }

theorem amount_machine (entry : Entry base) : (amount entry).after=entry.afterAmount := by
  change {(earned entry).after with
    heap:=PropertyFrame.write (earned entry).after.heap
      entry.building entry.buildingObject (JSString.ofString "amount")
      (.number (Number.sub entry.amount Number.one)) true true}=entry.afterAmount
  rw [earned_machine]
  rfl

theorem cookies_safe (entry : Entry base) : CursorCatalogueWrite.Safe (cookies entry) := by
  change ∀ name∈CursorCatalogueWrite.arithmeticNames,JSString.ofString "cookies"≠JSString.ofString name
  decide
 theorem earned_safe (entry : Entry base) : CursorCatalogueWrite.Safe (earned entry) := by
  change ∀ name∈CursorCatalogueWrite.arithmeticNames,JSString.ofString "cookiesEarned"≠JSString.ofString name
  decide
 theorem amount_safe (entry : Entry base) : CursorCatalogueWrite.Safe (amount entry) := by
  change ∀ name∈CursorCatalogueWrite.arithmeticNames,JSString.ofString "amount"≠JSString.ofString name
  decide

def changedAmount (entry : Entry base) : TieredRead.DataEdge (amount entry).after entry.building
    (JSString.ofString "amount") (.number (Number.sub entry.amount Number.one)) := {
  object:=setOwnProperty entry.buildingObject (JSString.ofString "amount")
    (.data (.number (Number.sub entry.amount Number.one)) true true true)
  present:=by
    rw [amount_machine]
    have kept:=SaleNumericPreservation.building_object entry
    change entry.afterAmount.heap.object? entry.building=_ at kept
    simp [checkedObject,kept]
  kind:=Or.inl (by simpa [PropertyFrame.set_kind] using entry.buildingKind)
  property:=by
    rw [amount_machine]
    exact SaleNumericPreservation.amount_lookup entry }

end CookieClicker.JavaScript.SaleNumericWrites

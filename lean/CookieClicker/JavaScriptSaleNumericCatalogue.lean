import CookieClicker.JavaScriptSaleNumericWrites
import CookieClicker.JavaScriptCursorCatalogueBinding

/-! The second price computation uses the actual catalogue left by the first
five successful-sale statements. Local and property transports are composed
from one original catalogue and the original successful-sale entry. -/
namespace CookieClicker.JavaScript.SaleNumericCatalogue
open CursorQuoteCatalogue SaleNumericWrites
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

variable {base : Machine} {scope : ObjectId} {price free rate : UInt64}

structure Names {entry : SaleNumericFrame.Entry base}
    (original : Catalogue base scope entry.building price entry.amount free rate) : Prop where
  cookies : JSString.ofString "cookies"≠original.profile.fortuneName
  earned : JSString.ofString "cookiesEarned"≠original.profile.fortuneName
  amount : JSString.ofString "amount"≠original.profile.fortuneName

def afterBindings (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) :
    Catalogue entry.afterMoni scope entry.building price entry.amount free rate :=
  CursorCatalogueBinding.catalogue entry.nextMoniSlot (.number entry.newMoni) (by decide)
    (CursorCatalogueBinding.catalogue entry.soldSlot (.number entry.newSold) (by decide) original)

theorem cookiesOwnership (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    PriceRegistryWrite.Write.OwnershipSafe (cookies entry) (afterBindings entry original).profile := {
  fortuneKey:=names.cookies
  bought:=by intro id member;exact Or.inr (show JSString.ofString "cookies"≠JSString.ofString "bought" by decide) }

def afterCookies (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    Catalogue (cookies entry).after scope entry.building price entry.amount free rate :=
  CursorCatalogueWrite.catalogue (cookies entry) (cookies_safe entry) (afterBindings entry original)
    (cookiesOwnership entry original names)
    (PropertyFrame.edge (afterBindings entry original).arithmetic.amountRead
      (cookies entry).target (cookies entry).object (cookies entry).key (cookies entry).descriptor
      (cookies entry).present (show JSString.ofString "cookies"≠JSString.ofString "amount" by decide))

theorem earnedOwnership (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    PriceRegistryWrite.Write.OwnershipSafe (earned entry) (afterCookies entry original names).profile := {
  fortuneKey:=names.earned
  bought:=by intro id member;exact Or.inr (show JSString.ofString "cookiesEarned"≠JSString.ofString "bought" by decide) }

def afterEarned (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    Catalogue (earned entry).after scope entry.building price entry.amount free rate :=
  CursorCatalogueWrite.catalogue (earned entry) (earned_safe entry) (afterCookies entry original names)
    (earnedOwnership entry original names)
    (PropertyFrame.edge (afterCookies entry original names).arithmetic.amountRead
      (earned entry).target (earned entry).object (earned entry).key (earned entry).descriptor
      (earned entry).present (show JSString.ofString "cookiesEarned"≠JSString.ofString "amount" by decide))

theorem amountOwnership (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    PriceRegistryWrite.Write.OwnershipSafe (amount entry) (afterEarned entry original names).profile := {
  fortuneKey:=names.amount
  bought:=by intro id member;exact Or.inr (show JSString.ofString "amount"≠JSString.ofString "bought" by decide) }

def afterAmount (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    Catalogue (amount entry).after scope entry.building price (Number.sub entry.amount Number.one) free rate :=
  CursorCatalogueWrite.catalogue (amount entry) (amount_safe entry) (afterEarned entry original names)
    (amountOwnership entry original names) (changedAmount entry)

theorem actual_machine (entry : SaleNumericFrame.Entry base) :
    (amount entry).after=entry.afterAmount := amount_machine entry

theorem original_ids (entry : SaleNumericFrame.Entry base)
    (original : Catalogue base scope entry.building price entry.amount free rate) (names : Names original) :
    (afterAmount entry original names).function=original.function ∧
    (afterAmount entry original names).pricing.window.game=original.pricing.window.game ∧
    (afterAmount entry original names).profile.building=original.profile.building := ⟨rfl,rfl,rfl⟩

end CookieClicker.JavaScript.SaleNumericCatalogue

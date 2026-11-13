import CookieClicker.JavaScriptOriginalPropertyWrite
import CookieClicker.JavaScriptLocalAssign
import CookieClicker.JavaScriptSaleNumericSource

namespace CookieClicker.JavaScript.SaleTailFrame
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) where
  price : UInt64
  amount : UInt64
  owned : UInt64
  game : ObjectId
  priceLocal : DevastationWrite.Local base "price" (.number price)
  priceSlot : BuildingStore.Slot base (JSString.ofString "price")
  receiver : base.context.thisValue=.object priceSlot.id
  recalculate : BuildingStore.Slot base (JSString.ofString "recalculateGains")
  recalculateId : recalculate.id=game
  buildingsOwned : BuildingStore.Slot base (JSString.ofString "BuildingsOwned")
  ownedId : buildingsOwned.id=game
  ownedValue : buildingsOwned.oldValue=.number owned
  successSlot : SourceBinding.Slot base "success"
  gameWindow : OriginalNamePath.Window base "Game" (.object game)
  gamePath : OriginalNamePath.Path "Game" base.heap.environments base.context.lexicalEnvironment gameWindow.id
  exclusions : base.objectEnvironmentExclusions=[]
  sellFunctionValue : Value
  sellFunction : TieredRead.DataEdge base priceSlot.id (JSString.ofString "sellFunction") sellFunctionValue
  noSellFunction : truthy sellFunctionValue=false
  amountEdge : TieredRead.DataEdge base priceSlot.id (JSString.ofString "amount") (.number amount)
  idEdge : TieredRead.DataEdge base priceSlot.id (JSString.ofString "id") (.number Number.positiveZero)

namespace Entry
variable {base : Machine}
def afterPrice (entry : Entry base) : Machine := entry.priceSlot.after (.number entry.price)
def recalculateAfterPrice (entry : Entry base) := OriginalPropertyWrite.otherSlot entry.priceSlot
  (.number entry.price) entry.recalculate (by decide)
def afterRecalculate (entry : Entry base) : Machine := entry.recalculateAfterPrice.after (.number Number.one)
def ownedAfterPrice (entry : Entry base) := OriginalPropertyWrite.otherSlot entry.priceSlot
  (.number entry.price) entry.buildingsOwned (by decide)
def ownedAfterRecalculate (entry : Entry base) := OriginalPropertyWrite.otherSlot entry.recalculateAfterPrice
  (.number Number.one) entry.ownedAfterPrice (by decide)
def afterOwned (entry : Entry base) : Machine := entry.ownedAfterRecalculate.after (.number (Number.sub entry.owned Number.one))
def successAfterPrice (entry : Entry base) := OriginalPropertyWrite.localSlot entry.priceSlot
  (.number entry.price) entry.successSlot
def successAfterRecalculate (entry : Entry base) := OriginalPropertyWrite.localSlot entry.recalculateAfterPrice
  (.number Number.one) entry.successAfterPrice
def successAfterOwned (entry : Entry base) := OriginalPropertyWrite.localSlot entry.ownedAfterRecalculate
  (.number (Number.sub entry.owned Number.one)) entry.successAfterRecalculate
def changed (entry : Entry base) : Machine := {entry.successAfterOwned.after (.number Number.one) with
  control:=.completion (.normal (some (.number Number.one)))}

def windowAfterPrice (entry : Entry base) := OriginalPropertyWrite.window entry.priceSlot
  (.number entry.price) entry.gameWindow (by decide)
def windowAfterRecalculate (entry : Entry base) := OriginalPropertyWrite.window entry.recalculateAfterPrice
  (.number Number.one) entry.windowAfterPrice (by decide)
theorem gameReadAfterPrice (entry : Entry base) : Reads entry.afterPrice (.identifier "Game") (.object entry.game) 3 :=
  entry.windowAfterPrice.read _ (HeapExtension.refl _) entry.gamePath entry.exclusions
theorem gameReadAfterRecalculate (entry : Entry base) : Reads entry.afterRecalculate (.identifier "Game") (.object entry.game) 3 :=
  entry.windowAfterRecalculate.read _ (HeapExtension.refl _) entry.gamePath entry.exclusions

def sellAfterPrice (entry : Entry base) := OriginalPropertyWrite.edge entry.priceSlot
  (.number entry.price) entry.sellFunction (by decide)
def amountAfterPrice (entry : Entry base) := OriginalPropertyWrite.edge entry.priceSlot
  (.number entry.price) entry.amountEdge (by decide)
def amountAfterRecalculate (entry : Entry base) := OriginalPropertyWrite.edge entry.recalculateAfterPrice
  (.number Number.one) entry.amountAfterPrice (by decide)
def idAfterPrice (entry : Entry base) := OriginalPropertyWrite.edge entry.priceSlot
  (.number entry.price) entry.idEdge (by decide)
def idAfterRecalculate (entry : Entry base) := OriginalPropertyWrite.edge entry.recalculateAfterPrice
  (.number Number.one) entry.idAfterPrice (by decide)

theorem receiverRead (entry : Entry base) (next : Machine) (receiver : next.context.thisValue=.object entry.priceSlot.id) :
    Reads next .this (.object entry.priceSlot.id) 1 := by
  simpa only [receiver] using CursorGetPriceRead.this_read next

theorem sellRead (entry : Entry base) : Reads entry.afterPrice
    (.member .this (.identifier "sellFunction") false) entry.sellFunctionValue 5 :=
  entry.sellAfterPrice.dot _ 1 (entry.receiverRead _ entry.receiver)

def amountTest : Expr := .binary .equal (.member .this (.identifier "amount") false) (.literal (.number 0))
def idTest : Expr := .binary .notEqual (.member .this (.identifier "id") false) (.literal (.number 0))
def rowTest : Expr := .logical .and amountTest idTest
def rowTicks (entry : Entry base) : Nat := if Number.equal entry.amount 0 then 21 else 11

theorem amountRead (entry : Entry base) : Reads entry.afterRecalculate amountTest (.boolean (Number.equal entry.amount 0)) 9 := by
  apply binary_value _ .equal _ _ (.number entry.amount) (.number 0) (.boolean (Number.equal entry.amount 0))
    5 1 (entry.amountAfterRecalculate.dot _ 1 (entry.receiverRead _ entry.receiver)) (literal _ (.number 0)) rfl rfl (by decide)
  rfl

theorem idRead (entry : Entry base) : Reads entry.afterRecalculate idTest (.boolean false) 9 := by
  apply binary_value _ .notEqual _ _ (.number 0) (.number 0) (.boolean false)
    5 1 (entry.idAfterRecalculate.dot _ 1 (entry.receiverRead _ entry.receiver)) (literal _ (.number 0)) rfl rfl (by decide)
  rfl

theorem rowRead (entry : Entry base) : Reads entry.afterRecalculate rowTest (.boolean false) entry.rowTicks := by
  cases equal:Number.equal entry.amount 0 with
  | false =>
    have firstPart:Reads entry.afterRecalculate amountTest (.boolean false) 9:=by simpa only [equal] using entry.amountRead
    simpa [rowTicks,rowTest,equal] using false_and _ _ _ (.boolean false) 9 firstPart rfl
  | true =>
    have firstPart:Reads entry.afterRecalculate amountTest (.boolean true) 9:=by simpa only [equal] using entry.amountRead
    simpa [rowTicks,rowTest,equal] using LocalAssign.true_and _ _ _ (.boolean true) (.boolean false) 9 9 firstPart entry.idRead rfl

end Entry
end CookieClicker.JavaScript.SaleTailFrame

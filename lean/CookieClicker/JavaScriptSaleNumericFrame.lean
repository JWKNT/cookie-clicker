import CookieClicker.JavaScriptLocalNumeric
import CookieClicker.JavaScriptOriginalNamePath
import CookieClicker.JavaScriptCounterObjects
import CookieClicker.JavaScriptCursorGetPriceRead

namespace CookieClicker.JavaScript.SaleNumericFrame
open SourceRead SourceBinding GodzamokLocalTransport TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) where
  sold : UInt64
  moni : UInt64
  price : UInt64
  cookies : UInt64
  earned : UInt64
  amount : UInt64
  soldSlot : Slot base "sold"
  moniSlot : Slot base "moni"
  soldRead : DevastationWrite.Local base "sold" (.number sold)
  moniRead : DevastationWrite.Local base "moni" (.number moni)
  priceRead : DevastationWrite.Local base "price" (.number price)
  counter : CounterObjects.Frame cookies earned
  objects : base.heap.objects=counter.objects
  gamePath : OriginalNamePath.Path "Game" base.heap.environments base.context.lexicalEnvironment counter.window
  mathPath : OriginalNamePath.Path "Math" base.heap.environments base.context.lexicalEnvironment counter.window
  exclusions : base.objectEnvironmentExclusions=[]
  maximum : BuildingMathRead.Binding base "max"
  mathWritable : Bool
  mathEnumerable : Bool
  mathConfigurable : Bool
  mathProperty : lookupProperty base.heap counter.window (JSString.ofString "Math")=
    .ok (some (.data (.object maximum.math) mathWritable mathEnumerable mathConfigurable))
  mathDistinct : maximum.math≠counter.game
  functionDistinct : maximum.function≠counter.game
  building : ObjectId
  buildingObject : JSObject
  receiver : base.context.thisValue=.object building
  buildingDistinct : building≠counter.game
  buildingPresent : base.heap.object? building=some buildingObject
  buildingKind : buildingObject.kind=.ordinary
  amountOwn : ownProperty buildingObject (JSString.ofString "amount")=some (.data (.number amount) true true true)
  amountLookup : lookupProperty base.heap building (JSString.ofString "amount")=
    .ok (some (.data (.number amount) true true true))

namespace Entry
variable {base : Machine}
def newSold (entry : Entry base) := Number.add entry.sold Number.one
def newMoni (entry : Entry base) := Number.add entry.moni entry.price
def newCookies (entry : Entry base) := Number.add entry.cookies entry.price
def newEarned (entry : Entry base) :=
  Number.maximum (Number.maximum Number.negativeInfinity entry.newCookies) entry.earned

def afterSold (entry : Entry base) : Machine := entry.soldSlot.after (.number entry.newSold)
def nextMoniSlot (entry : Entry base) : Slot entry.afterSold "moni" :=
  entry.soldSlot.otherSlot entry.moniSlot (by decide) (.number entry.newSold)
def afterMoni (entry : Entry base) : Machine := entry.nextMoniSlot.after (.number entry.newMoni)
def cookiesFrame (entry : Entry base) := (CounterObjects.writeCookies entry.counter) entry.newCookies
def afterCookies (entry : Entry base) : Machine := {entry.afterMoni with
  heap:=CounterObjects.heap entry.cookiesFrame entry.afterMoni.heap.environments}
def earnedFrame (entry : Entry base) := (CounterObjects.writeEarned entry.cookiesFrame) entry.newEarned
def afterEarned (entry : Entry base) : Machine := {entry.afterMoni with
  heap:=CounterObjects.heap entry.earnedFrame entry.afterMoni.heap.environments}
def afterAmount (entry : Entry base) : Machine := {entry.afterEarned with
  heap:=PropertyFrame.write entry.afterEarned.heap entry.building entry.buildingObject
    (JSString.ofString "amount") (.number (Number.sub entry.amount Number.one)) true true}

def moniAfterSold (entry : Entry base) : DevastationWrite.Local entry.afterSold "moni" (.number entry.moni) :=
  localOther entry.soldSlot entry.moniRead (by decide) _
def priceAfterSold (entry : Entry base) : DevastationWrite.Local entry.afterSold "price" (.number entry.price) :=
  localOther entry.soldSlot entry.priceRead (by decide) _
def priceAfterMoni (entry : Entry base) : DevastationWrite.Local entry.afterMoni "price" (.number entry.price) :=
  localOther entry.nextMoniSlot entry.priceAfterSold (by decide) _

theorem originalHeap (entry : Entry base) : base.heap=CounterObjects.heap entry.counter base.heap.environments := by
  have same:=entry.objects
  cases h:base.heap
  simp_all [CounterObjects.heap]
theorem moniHeap (entry : Entry base) : entry.afterMoni.heap=CounterObjects.heap entry.counter entry.afterMoni.heap.environments := by
  have same:entry.afterMoni.heap.objects=entry.counter.objects:=entry.objects
  cases h:entry.afterMoni.heap
  simp_all [CounterObjects.heap]

def gamePathAfterMoni (entry : Entry base) :
    OriginalNamePath.Path "Game" entry.afterMoni.heap.environments entry.afterMoni.context.lexicalEnvironment entry.counter.window :=
  (entry.gamePath.written entry.soldSlot (.number entry.newSold)).written entry.nextMoniSlot (.number entry.newMoni)
def mathPathAfterMoni (entry : Entry base) :
    OriginalNamePath.Path "Math" entry.afterMoni.heap.environments entry.afterMoni.context.lexicalEnvironment entry.counter.window :=
  (entry.mathPath.written entry.soldSlot (.number entry.newSold)).written entry.nextMoniSlot (.number entry.newMoni)

def gameWindowMoni (entry : Entry base) : OriginalNamePath.Window entry.afterMoni "Game" (.object entry.counter.game) := {
  id:=entry.counter.window,object:=entry.counter.windowObject
  present:=by rw [entry.moniHeap]; exact (CounterObjects.checked_window entry.counter) _
  kind:=entry.counter.windowKind
  writable:=true,enumerable:=true,configurable:=false
  property:=by rw [entry.moniHeap];exact (CounterObjects.game_binding entry.counter) _ }
def gameWindowCookies (entry : Entry base) : OriginalNamePath.Window entry.afterCookies "Game" (.object entry.counter.game) := {
  id:=entry.counter.window,object:=entry.counter.windowObject
  present:=(CounterObjects.checked_window entry.cookiesFrame) _
  kind:=entry.counter.windowKind
  writable:=true,enumerable:=true,configurable:=false
  property:=(CounterObjects.game_binding entry.cookiesFrame) _ }

theorem gameReadMoni (entry : Entry base) : Reads entry.afterMoni (.identifier "Game") (.object entry.counter.game) 3 :=
  entry.gameWindowMoni.read _ (HeapExtension.refl _) entry.gamePathAfterMoni entry.exclusions
theorem gameReadCookies (entry : Entry base) : Reads entry.afterCookies (.identifier "Game") (.object entry.counter.game) 3 :=
  entry.gameWindowCookies.read _ (HeapExtension.refl _) entry.gamePathAfterMoni entry.exclusions

theorem cookiesWrite (entry : Entry base) :
    PropertyFrame.write entry.afterMoni.heap entry.counter.game entry.counter.gameObject
      (JSString.ofString "cookies") (.number entry.newCookies) true true=entry.afterCookies.heap := by
  rw [entry.moniHeap]
  rfl

theorem mathLookupMoni (entry : Entry base) : lookupProperty entry.afterMoni.heap entry.counter.window (JSString.ofString "Math")=
    .ok (some (.data (.object entry.maximum.math) entry.mathWritable entry.mathEnumerable entry.mathConfigurable)) :=
  HeapExtension.lookup_property (HeapExtension.same_objects (before:=base.heap) (after:=entry.afterMoni.heap) rfl) _ _ _ entry.mathProperty

def mathWindowCookies (entry : Entry base) : OriginalNamePath.Window entry.afterCookies "Math" (.object entry.maximum.math) := {
  id:=entry.counter.window,object:=entry.counter.windowObject
  present:=(CounterObjects.checked_window entry.cookiesFrame) _
  kind:=entry.counter.windowKind
  writable:=entry.mathWritable,enumerable:=entry.mathEnumerable,configurable:=entry.mathConfigurable
  property:=by
    rw [←entry.cookiesWrite]
    exact (PropertyFrame.lookup_other entry.afterMoni.heap entry.counter.game entry.counter.gameObject
      (JSString.ofString "cookies") (JSString.ofString "Math") (.data (.number entry.newCookies) true true true)
      (by rw [entry.moniHeap];exact entry.counter.gameRead) (by decide) _).trans entry.mathLookupMoni }

theorem otherObjectCookies (entry : Entry base) (id : ObjectId) (different : id≠entry.counter.game) :
    entry.afterCookies.heap.object? id=base.heap.object? id := by
  change entry.cookiesFrame.objects[id]?=base.heap.objects[id]?
  unfold cookiesFrame
  rw [CounterObjects.writeCookies_other_object _ _ _ different,entry.objects]

def maximumCookies (entry : Entry base) : BuildingMathRead.Binding entry.afterCookies "max" := {
  math:=entry.maximum.math,function:=entry.maximum.function
  mathObject:=entry.maximum.mathObject,functionObject:=entry.maximum.functionObject
  mathRead:=entry.mathWindowCookies.read _ (HeapExtension.refl _) entry.mathPathAfterMoni entry.exclusions
  mathPresent:=by
    simp only [checkedObject,entry.otherObjectCookies _ entry.mathDistinct]
    exact entry.maximum.mathPresent
  mathKind:=entry.maximum.mathKind
  property:=by
    rw [←entry.cookiesWrite]
    refine (PropertyFrame.lookup_other entry.afterMoni.heap entry.counter.game entry.counter.gameObject
      (JSString.ofString "cookies") (JSString.ofString "max") (.data (.number entry.newCookies) true true true)
      (by rw [entry.moniHeap];exact entry.counter.gameRead) (by decide) _).trans ?_
    exact HeapExtension.lookup_property (HeapExtension.same_objects (before:=base.heap) (after:=entry.afterMoni.heap) rfl) _ _ _ entry.maximum.property
  functionPresent:=by
    simp only [checkedObject,entry.otherObjectCookies _ entry.functionDistinct]
    exact entry.maximum.functionPresent
  functionKind:=entry.maximum.functionKind }

def cookiesEdge (entry : Entry base) : DataEdge entry.afterCookies entry.counter.game (JSString.ofString "cookies") (.number entry.newCookies) := {
  object:=entry.cookiesFrame.gameObject
  present:=(CounterObjects.checked_game entry.cookiesFrame) _
  kind:=Or.inl entry.cookiesFrame.gameKind
  property:=(CounterObjects.cookies_lookup entry.cookiesFrame) _ }
def earnedEdge (entry : Entry base) : DataEdge entry.afterCookies entry.counter.game (JSString.ofString "cookiesEarned") (.number entry.earned) := {
  object:=entry.cookiesFrame.gameObject
  present:=(CounterObjects.checked_game entry.cookiesFrame) _
  kind:=Or.inl entry.cookiesFrame.gameKind
  property:=(CounterObjects.earned_lookup entry.cookiesFrame) _ }

theorem maximumRead (entry : Entry base) :
    Reads entry.afterCookies (BuildingMathRead.call "max"
      [.member (.identifier "Game") (.identifier "cookies") false,
       .member (.identifier "Game") (.identifier "cookiesEarned") false]) (.number entry.newEarned) 27 := by
  apply BuildingMathRead.binary _ "max" entry.maximumCookies _ _
    (.number entry.newCookies) (.number entry.earned) (.number entry.newEarned) 7 7
    (entry.cookiesEdge.dot _ 3 entry.gameReadCookies) (entry.earnedEdge.dot _ 3 entry.gameReadCookies)
  rfl

theorem buildingPresentEarned (entry : Entry base) : entry.afterEarned.heap.object? entry.building=some entry.buildingObject := by
  change entry.earnedFrame.objects[entry.building]?=some entry.buildingObject
  unfold earnedFrame cookiesFrame
  rw [CounterObjects.writeEarned_other_object (CounterObjects.writeCookies entry.counter entry.newCookies) entry.newEarned entry.building entry.buildingDistinct,
    CounterObjects.writeCookies_other_object _ _ _ entry.buildingDistinct,←entry.objects]
  exact entry.buildingPresent

theorem amountLookupEarned (entry : Entry base) : lookupProperty entry.afterEarned.heap entry.building (JSString.ofString "amount")=
    .ok (some (.data (.number entry.amount) true true true)) := by
  change lookupProperty (PropertyFrame.write entry.afterCookies.heap entry.counter.game entry.cookiesFrame.gameObject
    (JSString.ofString "cookiesEarned") (.number entry.newEarned) true true) _ _=_
  refine (PropertyFrame.lookup_other entry.afterCookies.heap entry.counter.game entry.cookiesFrame.gameObject
    (JSString.ofString "cookiesEarned") (JSString.ofString "amount") (.data (.number entry.newEarned) true true true) entry.cookiesFrame.gameRead (by decide) entry.building).trans ?_
  rw [←entry.cookiesWrite]
  refine (PropertyFrame.lookup_other entry.afterMoni.heap entry.counter.game entry.counter.gameObject
    (JSString.ofString "cookies") (JSString.ofString "amount") (.data (.number entry.newCookies) true true true)
    (by rw [entry.moniHeap];exact entry.counter.gameRead) (by decide) entry.building).trans ?_
  exact HeapExtension.lookup_property (HeapExtension.same_objects (before:=base.heap) (after:=entry.afterMoni.heap) rfl) _ _ _ entry.amountLookup

end Entry
end CookieClicker.JavaScript.SaleNumericFrame

import CookieClicker.JavaScriptSaleNumericSource

namespace CookieClicker.JavaScript.SaleNumericPreservation
open SaleNumericFrame SaleNumericSource GodzamokLocalTransport
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem retained_sell_body : GodzamokSyntax.sellBody=CursorCycleSyntax.sellBody := rfl

theorem retained_next_call : sourceStatement 5=
    .expression (.assignment .assign (.identifier "price") (.call (.member .this (.identifier "getPrice") false) [])) := rfl

theorem intact_statement_tail {base : Machine} (entry : Entry base) :
    (atNextPrice entry).control=.statement (sourceStatement 5) ∧
    (atNextPrice entry).continuation=
      .statementList (successBody.drop 6) (some (.number entry.amount))::base.continuation := ⟨rfl,rfl⟩

def localFinal {base : Machine} (entry : Entry base) {name : String} {value : Value}
    (retained : DevastationWrite.Local entry.afterMoni name value) :
    DevastationWrite.Local (atNextPrice entry) name value := {
  bindings:=retained.bindings,outer:=retained.outer
  environment:=retained.environment
  found:=retained.found
  read:=by
    have environment : checkedEnvironment (atNextPrice entry).heap base.context.lexicalEnvironment=
        .ok ⟨.declarative retained.bindings,retained.outer⟩:=retained.environment
    have beforeEnv : checkedEnvironment entry.afterMoni.heap base.context.lexicalEnvironment=
        .ok ⟨.declarative retained.bindings,retained.outer⟩:=retained.environment
    have beforeRead : readBinding entry.afterMoni.heap base.context.lexicalEnvironment name=.ok value:=retained.read
    change readBinding (atNextPrice entry).heap base.context.lexicalEnvironment name=.ok value
    simpa only [readBinding,environment,beforeEnv] using beforeRead }

def soldFinal {base : Machine} (entry : Entry base) :
    DevastationWrite.Local (atNextPrice entry) "sold" (.number entry.newSold) :=
  localFinal entry (localOther entry.nextMoniSlot (localWritten entry.soldSlot (.number entry.newSold)) (by decide) _)
def moniFinal {base : Machine} (entry : Entry base) :
    DevastationWrite.Local (atNextPrice entry) "moni" (.number entry.newMoni) :=
  localFinal entry (localWritten entry.nextMoniSlot (.number entry.newMoni))
def priceFinal {base : Machine} (entry : Entry base) :
    DevastationWrite.Local (atNextPrice entry) "price" (.number entry.price) := localFinal entry entry.priceAfterMoni

theorem cookies_lookup {base : Machine} (entry : Entry base) :
    lookupProperty (atNextPrice entry).heap entry.counter.game (JSString.ofString "cookies")=
      .ok (some (.data (.number entry.newCookies) true true true)) := by
  refine (PropertyFrame.lookup_other entry.afterEarned.heap entry.building entry.buildingObject
    (JSString.ofString "amount") (JSString.ofString "cookies")
    (.data (.number (Number.sub entry.amount Number.one)) true true true)
    entry.buildingPresentEarned (by decide) entry.counter.game).trans ?_
  exact CounterObjects.cookies_lookup entry.earnedFrame _

theorem earned_lookup {base : Machine} (entry : Entry base) :
    lookupProperty (atNextPrice entry).heap entry.counter.game (JSString.ofString "cookiesEarned")=
      .ok (some (.data (.number entry.newEarned) true true true)) := by
  refine (PropertyFrame.lookup_other entry.afterEarned.heap entry.building entry.buildingObject
    (JSString.ofString "amount") (JSString.ofString "cookiesEarned")
    (.data (.number (Number.sub entry.amount Number.one)) true true true)
    entry.buildingPresentEarned (by decide) entry.counter.game).trans ?_
  exact CounterObjects.earned_lookup entry.earnedFrame _

theorem amount_own {base : Machine} (entry : Entry base) :
    ownProperty (setOwnProperty entry.buildingObject (JSString.ofString "amount")
      (.data (.number (Number.sub entry.amount Number.one)) true true true)) (JSString.ofString "amount")=
      some (.data (.number (Number.sub entry.amount Number.one)) true true true) := PropertyFrame.own_set _ _ _

theorem building_object {base : Machine} (entry : Entry base) :
    (atNextPrice entry).heap.object? entry.building=some
      (setOwnProperty entry.buildingObject (JSString.ofString "amount")
        (.data (.number (Number.sub entry.amount Number.one)) true true true)) :=
  PropertyFrame.replaced_read _ _ _ ((Array.getElem?_eq_some_iff.mp entry.buildingPresentEarned).1)

theorem amount_lookup {base : Machine} (entry : Entry base) :
    lookupProperty (atNextPrice entry).heap entry.building (JSString.ofString "amount")=
      .ok (some (.data (.number (Number.sub entry.amount Number.one)) true true true)) := by
  have known : entry.buildingObject.unresolvedOwnNames.contains (JSString.ofString "amount")=false := by
    have original:=entry.amountLookup
    cases status:entry.buildingObject.unresolvedOwnNames.contains (JSString.ofString "amount") with
    | false => rfl
    | true => simp only [lookupProperty,findProperty,checkedObject,entry.buildingPresent,Except.bind,bind,status,ite_true] at original
              cases original
  simp only [lookupProperty,findProperty,checkedObject,building_object entry,PropertyFrame.set_unresolved,
    known,PropertyFrame.own_set,Except.bind,bind,pure,Except.pure,Bool.false_eq_true,ite_false]

theorem other_object {base : Machine} (entry : Entry base) (id : ObjectId)
    (notGame : id≠entry.counter.game) (notBuilding : id≠entry.building) :
    (atNextPrice entry).heap.object? id=base.heap.object? id := by
  refine (PropertyFrame.other_read _ _ _ _ notBuilding).trans ?_
  change entry.earnedFrame.objects[id]?=base.heap.objects[id]?
  unfold Entry.earnedFrame Entry.cookiesFrame
  rw [CounterObjects.writeEarned_other_object (CounterObjects.writeCookies entry.counter entry.newCookies)
    entry.newEarned id notGame,CounterObjects.writeCookies_other_object entry.counter entry.newCookies id notGame,entry.objects]

theorem other_property {base : Machine} (entry : Entry base) (id : ObjectId) (name : JSString)
    (notCookies : JSString.ofString "cookies"≠name)
    (notEarned : JSString.ofString "cookiesEarned"≠name)
    (notAmount : JSString.ofString "amount"≠name) (descriptor : Option PropertyDescriptor)
    (original : lookupProperty base.heap id name=.ok descriptor) :
    lookupProperty (atNextPrice entry).heap id name=.ok descriptor := by
  refine (PropertyFrame.lookup_other entry.afterEarned.heap entry.building entry.buildingObject
    (JSString.ofString "amount") name (.data (.number (Number.sub entry.amount Number.one)) true true true)
    entry.buildingPresentEarned notAmount id).trans ?_
  refine (PropertyFrame.lookup_other entry.afterCookies.heap entry.counter.game entry.cookiesFrame.gameObject
    (JSString.ofString "cookiesEarned") name (.data (.number entry.newEarned) true true true)
    entry.cookiesFrame.gameRead notEarned id).trans ?_
  rw [←entry.cookiesWrite]
  refine (PropertyFrame.lookup_other entry.afterMoni.heap entry.counter.game entry.counter.gameObject
    (JSString.ofString "cookies") name (.data (.number entry.newCookies) true true true)
    (by rw [entry.moniHeap];exact entry.counter.gameRead) notCookies id).trans ?_
  exact HeapExtension.lookup_property (HeapExtension.same_objects (before:=base.heap) (after:=entry.afterMoni.heap) rfl) _ _ _ original

theorem other_environment {base : Machine} (entry : Entry base) (id : EnvId)
    (different : base.context.lexicalEnvironment≠id) :
    checkedEnvironment (atNextPrice entry).heap id=checkedEnvironment base.heap id :=
  (entry.nextMoniSlot.other_environment (.number entry.newMoni) id different).trans
    (entry.soldSlot.other_environment (.number entry.newSold) id different)

theorem other_local {base : Machine} (entry : Entry base) (name : String)
    (notSold : name≠"sold") (notMoni : name≠"moni") :
    readBinding (atNextPrice entry).heap base.context.lexicalEnvironment name=
      readBinding base.heap base.context.lexicalEnvironment name := by
  have written := entry.nextMoniSlot.other_read (.number entry.newMoni) name notMoni
  have environment : checkedEnvironment (atNextPrice entry).heap base.context.lexicalEnvironment=
      .ok ⟨.declarative (BindingWrite.changedBindings "moni" (.number entry.newMoni) entry.nextMoniSlot.bindings),entry.nextMoniSlot.outer⟩:=
    entry.nextMoniSlot.updated_present _
  have finalRead : readBinding (atNextPrice entry).heap base.context.lexicalEnvironment name=
      readBinding entry.afterMoni.heap base.context.lexicalEnvironment name := by
    have beforeEnv : checkedEnvironment entry.afterMoni.heap base.context.lexicalEnvironment=
        .ok ⟨.declarative (BindingWrite.changedBindings "moni" (.number entry.newMoni) entry.nextMoniSlot.bindings),entry.nextMoniSlot.outer⟩:=
      entry.nextMoniSlot.updated_present _
    simp only [readBinding,environment,beforeEnv]
  exact finalRead.trans (written.trans (entry.soldSlot.other_read (.number entry.newSold) name notSold))

theorem retained_context {base : Machine} (entry : Entry base) :
    (atNextPrice entry).context=base.context ∧
    (atNextPrice entry).elapsed=base.elapsed ∧
    (atNextPrice entry).epochMilliseconds=base.epochMilliseconds ∧
    (atNextPrice entry).freeDrawCount=base.freeDrawCount ∧
    (atNextPrice entry).events=base.events ∧
    (atNextPrice entry).nextEventId=base.nextEventId := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem retained_sizes {base : Machine} (entry : Entry base) :
    (atNextPrice entry).heap.objects.size=base.heap.objects.size ∧
    (atNextPrice entry).heap.environments.size=base.heap.environments.size := by
  constructor
  · simp [atNextPrice,Entry.afterAmount,Entry.afterEarned,Entry.earnedFrame,Entry.cookiesFrame,
      CounterObjects.heap,CounterObjects.writeEarned,CounterObjects.writeCookies,PropertyFrame.write,
      PropertyFrame.replace,entry.objects]
  · simp [atNextPrice,Entry.afterAmount,Entry.afterEarned,Entry.afterMoni,Entry.afterSold,
      Entry.nextMoniSlot,SourceBinding.Slot.after,BindingWrite.changedHeap,CounterObjects.heap,
      PropertyFrame.write,PropertyFrame.replace]

end CookieClicker.JavaScript.SaleNumericPreservation

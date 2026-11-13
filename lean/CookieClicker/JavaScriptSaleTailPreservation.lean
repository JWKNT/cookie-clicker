import CookieClicker.JavaScriptSaleTailSource

namespace CookieClicker.JavaScript.SaleTailPreservation
open SaleTailFrame OriginalPropertyWrite
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {base : Machine}

theorem success_read (entry : Entry base) :
    SourceRead.Reads entry.changed (.identifier "success") (.number Number.one) 3 :=
  entry.successAfterOwned.value_read (.number Number.one)

def local_after (entry : Entry base) {name : String} {value : Value}
    (frame : DevastationWrite.Local base name value) (different : name≠"success") :
    DevastationWrite.Local entry.changed name value := by
  let retained:=GodzamokLocalTransport.localOther entry.successAfterOwned
    (localFrame entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one))
      (localFrame entry.recalculateAfterPrice (.number Number.one)
        (localFrame entry.priceSlot (.number entry.price) frame))) different (.number Number.one)
  exact {retained with}

def slot_after (entry : Entry base) {name : String}
    (slot : SourceBinding.Slot base name) (different : name≠"success") : SourceBinding.Slot entry.changed name := by
  let retained:=entry.successAfterOwned.otherSlot
    (localSlot entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one))
      (localSlot entry.recalculateAfterPrice (.number Number.one)
        (localSlot entry.priceSlot (.number entry.price) slot))) different (.number Number.one)
  exact {retained with}

theorem price_local (entry : Entry base) : SourceRead.Reads entry.changed (.identifier "price") (.number entry.price) 3 :=
  (local_after entry entry.priceLocal (by decide)).reads

theorem price_lookup (entry : Entry base) :
    lookupProperty entry.changed.heap entry.priceSlot.id (JSString.ofString "price")=
      .ok (some (.data (.number entry.price) true entry.priceSlot.enumerable entry.priceSlot.configurable)) := by
  apply HeapExtension.lookup_property (HeapExtension.same_objects (before:=entry.afterOwned.heap) (after:=entry.changed.heap) rfl)
  refine (lookup_other entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one)) _ (by decide)).trans ?_
  refine (lookup_other entry.recalculateAfterPrice (.number Number.one) _ (by decide)).trans ?_
  exact lookup_written entry.priceSlot (.number entry.price)

theorem recalculate_lookup (entry : Entry base) :
    lookupProperty entry.changed.heap entry.game (JSString.ofString "recalculateGains")=
      .ok (some (.data (.number Number.one) true entry.recalculate.enumerable entry.recalculate.configurable)) := by
  apply HeapExtension.lookup_property (HeapExtension.same_objects (before:=entry.afterOwned.heap) (after:=entry.changed.heap) rfl)
  refine (lookup_other entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one)) _ (by decide)).trans ?_
  have found:=lookup_written entry.recalculateAfterPrice (.number Number.one)
  have idEq:entry.recalculateAfterPrice.id=entry.game:=entry.recalculateId
  rw [idEq] at found
  exact found

theorem owned_lookup (entry : Entry base) :
    lookupProperty entry.changed.heap entry.game (JSString.ofString "BuildingsOwned")=
      .ok (some (.data (.number (Number.sub entry.owned Number.one)) true entry.buildingsOwned.enumerable entry.buildingsOwned.configurable)) := by
  apply HeapExtension.lookup_property (HeapExtension.same_objects (before:=entry.afterOwned.heap) (after:=entry.changed.heap) rfl)
  have found:=lookup_written entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one))
  have idEq:entry.ownedAfterRecalculate.id=entry.game:=entry.ownedId
  rw [idEq] at found
  exact found

theorem other_property (entry : Entry base) (id : ObjectId) (name : JSString) (descriptor : Option PropertyDescriptor)
    (notPrice : JSString.ofString "price"≠name)
    (notRecalculate : JSString.ofString "recalculateGains"≠name)
    (notOwned : JSString.ofString "BuildingsOwned"≠name)
    (original : lookupProperty base.heap id name=.ok descriptor) :
    lookupProperty entry.changed.heap id name=.ok descriptor := by
  apply HeapExtension.lookup_property (HeapExtension.same_objects (before:=entry.afterOwned.heap) (after:=entry.changed.heap) rfl)
  refine (lookup_other entry.ownedAfterRecalculate (.number (Number.sub entry.owned Number.one)) _ notOwned).trans ?_
  refine (lookup_other entry.recalculateAfterPrice (.number Number.one) _ notRecalculate).trans ?_
  exact (lookup_other entry.priceSlot (.number entry.price) _ notPrice).trans original

theorem other_environment (entry : Entry base) (id : EnvId) (different : base.context.lexicalEnvironment≠id) :
    checkedEnvironment entry.changed.heap id=checkedEnvironment base.heap id :=
  entry.successAfterOwned.other_environment (.number Number.one) id different

theorem other_object (entry : Entry base) (id : ObjectId)
    (notBuilding : id≠entry.priceSlot.id) (notGame : id≠entry.game) :
    entry.changed.heap.object? id=base.heap.object? id := by
  have notOwned : id≠entry.ownedAfterRecalculate.id:=by simpa only [show entry.ownedAfterRecalculate.id=entry.game from entry.ownedId] using notGame
  have notRecalculate : id≠entry.recalculateAfterPrice.id:=by simpa only [show entry.recalculateAfterPrice.id=entry.game from entry.recalculateId] using notGame
  refine (PropertyFrame.other_read entry.afterRecalculate.heap entry.ownedAfterRecalculate.id id _ notOwned).trans ?_
  refine (PropertyFrame.other_read entry.afterPrice.heap entry.recalculateAfterPrice.id id _ notRecalculate).trans ?_
  exact PropertyFrame.other_read base.heap entry.priceSlot.id id _ notBuilding

theorem completed (entry : Entry base) :
    entry.changed.control=.completion (.normal (some (.number Number.one))) ∧
    entry.changed.continuation=base.continuation ∧ entry.changed.context=base.context := ⟨rfl,rfl,rfl⟩

theorem no_time_or_draw (entry : Entry base) :
    entry.changed.elapsed=base.elapsed ∧ entry.changed.epochMilliseconds=base.epochMilliseconds ∧
    entry.changed.freeDrawCount=base.freeDrawCount ∧ entry.changed.events=base.events ∧
    entry.changed.nextEventId=base.nextEventId := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem no_allocation (entry : Entry base) :
    entry.changed.heap.objects.size=base.heap.objects.size ∧ entry.changed.heap.environments.size=base.heap.environments.size := by
  simp [Entry.changed,Entry.afterOwned,Entry.afterRecalculate,Entry.afterPrice,Entry.successAfterOwned,
    Entry.successAfterRecalculate,Entry.successAfterPrice,Entry.ownedAfterRecalculate,Entry.ownedAfterPrice,
    Entry.recalculateAfterPrice,OriginalPropertyWrite.localSlot,OriginalPropertyWrite.otherSlot,
    BuildingStore.Slot.after,SourceBinding.Slot.after,BindingWrite.changedHeap]

end CookieClicker.JavaScript.SaleTailPreservation

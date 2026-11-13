import CookieClicker.JavaScriptGodzamokOriginalBody

/-! The full original branch changes only the existing multiplier property and
its two caller locals, while retaining all three helper-call allocations. -/
namespace CookieClicker.JavaScript.GodzamokOriginalPreservation
open GodzamokOriginalEntry GodzamokInitializers GodzamokLocalTransport SourceBinding
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

theorem changed_multiplier {base : Machine} (entry : Entry base) :
    lookupProperty entry.changed.heap entry.buff (JSString.ofString "multClick")=
      .ok (some (.data (.number (Number.add entry.multiplier
        (Number.mul entry.sold DevastationExisting.diamond))) true true true)) :=
  DevastationWrite.changed_lookup entry.afterCalls entry.finalFrame DevastationExisting.diamond

theorem changed_old_object {base : Machine} (entry : Entry base) (id : ObjectId) (object : JSObject)
    (different : id≠entry.buff) (present : base.heap.object? id=some object) :
    entry.changed.heap.object? id=some object := by
  have unchanged:=DevastationWrite.changed_other_object entry.afterCalls entry.finalFrame
    DevastationExisting.diamond id different
  exact unchanged.trans (entry.calls_extend.read id object present)

theorem changed_other_property {base : Machine} (entry : Entry base) (id : ObjectId) (key : JSString)
    (different : JSString.ofString "multClick"≠key) (value : Option PropertyDescriptor)
    (present : lookupProperty base.heap id key=.ok value) :
    lookupProperty entry.changed.heap id key=.ok value :=
  (DevastationWrite.changed_other_property entry.afterCalls entry.finalFrame
    DevastationExisting.diamond id key different).trans
    (HeapExtension.lookup_property entry.calls_extend id key value present)

theorem changed_deadline {base : Machine} (entry : Entry base) (deadline : UInt64)
    (present : lookupProperty base.heap entry.buff (JSString.ofString "time")=
      .ok (some (.data (.number deadline) true true true))) :
    lookupProperty entry.changed.heap entry.buff (JSString.ofString "time")=
      .ok (some (.data (.number deadline) true true true)) :=
  changed_other_property entry entry.buff _ (by decide) _ present

def successAfterCalls {base : Machine} (entry : Entry base) :
    DevastationWrite.Local entry.afterCalls "success" entry.success :=
  localOther (buffSlot entry.oldAfterGod entry.buffScope entry.buffFunction)
    (buffLocal (localOther (godSlot entry.pantheon entry.godLvlSlot)
      (godLocal entry.pantheon entry.successLocal) (by decide) (.number Number.one))
      entry.buffScope entry.buffFunction) (by decide) (.object entry.buff)

theorem changed_success {base : Machine} (entry : Entry base) :
    SourceRead.Reads entry.changed (.identifier "success") entry.success 3 :=
  ((successAfterCalls entry).retained entry.finalFrame DevastationExisting.diamond).reads

theorem changed_sold {base : Machine} (entry : Entry base) :
    SourceRead.Reads entry.changed (.identifier "sold") (.number entry.sold) 3 :=
  (entry.soldAfterCalls.retained entry.finalFrame DevastationExisting.diamond).reads

theorem changed_level {base : Machine} (entry : Entry base) :
    SourceRead.Reads entry.changed (.identifier "godLvl") (.number Number.one) 3 :=
  (entry.levelAfterCalls.retained entry.finalFrame DevastationExisting.diamond).reads

theorem changed_old {base : Machine} (entry : Entry base) :
    SourceRead.Reads entry.changed (.identifier "old") (.object entry.buff) 3 :=
  (entry.oldAfterCalls.retained entry.finalFrame DevastationExisting.diamond).reads

theorem calls_objects {base : Machine} (entry : Entry base) :
    entry.afterCalls.heap.objects=
      ((base.heap.objects.push (PantheonRuinPreservation.firstArgument base entry.godFunction)).push
        (PantheonRuinPreservation.secondArgument entry.pantheon)).push
        (buffArgument entry.afterGod entry.buffFunction) := rfl

theorem changed_object_count {base : Machine} (entry : Entry base) :
    entry.changed.heap.objects.size=base.heap.objects.size+3 := by
  change (entry.afterCalls.heap.objects.set! entry.buff _).size=_
  simp only [Array.size_setIfInBounds,Array.set!_eq_setIfInBounds,calls_objects,Array.size_push]

theorem changed_environment_count {base : Machine} (entry : Entry base) :
    entry.changed.heap.environments.size=base.heap.environments.size+3 := by
  simp only [Entry.changed,DevastationWrite.changed,PropertyFrame.write,PropertyFrame.replace,
    Entry.afterCalls,buffWritten,Slot.after,BindingWrite.changedHeap,
    Array.set!_eq_setIfInBounds,Array.size_setIfInBounds,buffAllocated,GodzamokBuffEntry.appended,
    Entry.afterGod,godWritten,godAllocated,Array.size_push]

theorem changed_control {base : Machine} (entry : Entry base) :
    entry.changed.control=.completion (.normal (some (.number
      (Number.add entry.multiplier (Number.mul entry.sold DevastationExisting.diamond))))) := rfl

theorem changed_context {base : Machine} (entry : Entry base) : entry.changed.context=base.context := rfl

theorem changed_continuation {base : Machine} (entry : Entry base) : entry.changed.continuation=base.continuation := rfl

theorem changed_elapsed {base : Machine} (entry : Entry base) : entry.changed.elapsed=base.elapsed := rfl

theorem changed_free_draws {base : Machine} (entry : Entry base) : entry.changed.freeDrawCount=base.freeDrawCount := rfl

theorem changed_events {base : Machine} (entry : Entry base) : entry.changed.events=base.events := rfl

theorem changed_epoch {base : Machine} (entry : Entry base) : entry.changed.epochMilliseconds=base.epochMilliseconds := rfl

end CookieClicker.JavaScript.GodzamokOriginalPreservation

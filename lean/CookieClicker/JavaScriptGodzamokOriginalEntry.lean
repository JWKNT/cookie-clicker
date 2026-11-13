import CookieClicker.JavaScriptGodzamokInitializers

/-! One original entry supplies all local and object evidence for the existing
Godzamok branch. Every later binding and property frame is constructed here. -/
namespace CookieClicker.JavaScript.GodzamokOriginalEntry
open SourceBinding GodzamokInitializers GodzamokLocalTransport PantheonRuinPreservation
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) where
  game : ObjectId
  godScope : EnvId
  godFunction : ObjectId
  buffScope : EnvId
  buffFunction : ObjectId
  buff : ObjectId
  pantheon : PantheonRuinOriginal.Entry base godScope game godFunction
  buffHelper : GodzamokBuffEntry.Entry base buffScope game buffFunction buff
  godLvlSlot : Slot base "godLvl"
  oldSlot : Slot base "old"
  success : Value
  successLocal : DevastationWrite.Local base "success" success
  successTruthy : truthy success=true
  sold : UInt64
  soldLocal : DevastationWrite.Local base "sold" (.number sold)
  object : JSObject
  multiplier : UInt64
  present : base.heap.object? buff=some object
  ordinary : object.kind=.ordinary
  own : ownProperty object (JSString.ofString "multClick")=
    some (.data (.number multiplier) true true true)
  lookup : lookupProperty base.heap buff (JSString.ofString "multClick")=
    .ok (some (.data (.number multiplier) true true true))

def Entry.withContinuation {base : Machine} (entry : Entry base) (continuation : List Frame) :
    Entry {base with continuation} := {
  entry with
  pantheon:=pantheonWithContinuation entry.pantheon continuation
  buffHelper:=entry.buffHelper.withContinuation continuation
  godLvlSlot:=entry.godLvlSlot.withContinuation continuation
  oldSlot:=entry.oldSlot.withContinuation continuation
  successLocal:={entry.successLocal with}
  soldLocal:={entry.soldLocal with} }

def Entry.afterGod {base : Machine} (entry : Entry base) : Machine := godWritten entry.pantheon entry.godLvlSlot

def Entry.oldAfterGod {base : Machine} (entry : Entry base) : Slot entry.afterGod "old" :=
  (godSlot entry.pantheon entry.godLvlSlot).otherSlot (godSlot entry.pantheon entry.oldSlot) (by decide) (.number Number.one)

def Entry.buffAfterGod {base : Machine} (entry : Entry base) :
    GodzamokBuffEntry.Entry entry.afterGod entry.buffScope entry.game entry.buffFunction entry.buff :=
  ((entry.buffHelper.appended (firstArgument base entry.godFunction)
    (firstEnvironment base entry.godScope entry.pantheon.world.god)).appended
      (secondArgument entry.pantheon) (secondEnvironment entry.pantheon)).written
        (godSlot entry.pantheon entry.godLvlSlot) (.number Number.one)

def Entry.afterCalls {base : Machine} (entry : Entry base) : Machine :=
  buffWritten entry.oldAfterGod entry.buffScope entry.buffFunction entry.buff

def Entry.oldAfterCalls {base : Machine} (entry : Entry base) :
    DevastationWrite.Local entry.afterCalls "old" (.object entry.buff) :=
  localWritten (buffSlot entry.oldAfterGod entry.buffScope entry.buffFunction) (.object entry.buff)

def Entry.levelAfterCalls {base : Machine} (entry : Entry base) :
    DevastationWrite.Local entry.afterCalls "godLvl" (.number Number.one) :=
  localOther (buffSlot entry.oldAfterGod entry.buffScope entry.buffFunction)
    (buffLocal (localWritten (godSlot entry.pantheon entry.godLvlSlot) (.number Number.one))
      entry.buffScope entry.buffFunction) (by decide) (.object entry.buff)

def Entry.soldAfterCalls {base : Machine} (entry : Entry base) :
    DevastationWrite.Local entry.afterCalls "sold" (.number entry.sold) :=
  localOther (buffSlot entry.oldAfterGod entry.buffScope entry.buffFunction)
    (buffLocal (localOther (godSlot entry.pantheon entry.godLvlSlot)
      (godLocal entry.pantheon entry.soldLocal) (by decide) (.number Number.one))
      entry.buffScope entry.buffFunction) (by decide) (.object entry.buff)

theorem Entry.calls_extend {base : Machine} (entry : Entry base) :
    HeapExtension.Extends base.heap entry.afterCalls.heap :=
  HeapExtension.trans (god_written_extends entry.pantheon entry.godLvlSlot)
    (buff_written_extends entry.oldAfterGod entry.buffScope entry.buffFunction entry.buff)

def Entry.finalFrame {base : Machine} (entry : Entry base) : DevastationWrite.Frame entry.afterCalls := {
  id:=entry.buff,object:=entry.object,multiplier:=entry.multiplier,sold:=entry.sold
  present:=entry.calls_extend.read _ _ entry.present
  ordinary:=entry.ordinary,own:=entry.own
  lookup:=HeapExtension.lookup_property entry.calls_extend _ _ _ entry.lookup
  oldLocal:=entry.oldAfterCalls,soldLocal:=entry.soldAfterCalls }

def Entry.changed {base : Machine} (entry : Entry base) : Machine :=
  DevastationWrite.changed entry.afterCalls entry.finalFrame DevastationExisting.diamond

end CookieClicker.JavaScript.GodzamokOriginalEntry

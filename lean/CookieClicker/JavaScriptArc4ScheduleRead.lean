import CookieClicker.JavaScriptArc4Schedule

/-! Actual native array reads used by the retained ARC4 scheduling expression. -/
namespace CookieClicker.JavaScript.Arc4ScheduleRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Schedule

theorem native_key (i : Inputs) (v : Arc4Locals.Values) (context : ExecutionContext)
    (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (key i)) (MixkeyIndex.key (slot i)) =
      result (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (keyNat i))) := by
  have read := MixkeyArray.native_read (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (key i) i.keyFrame.object
    i.keyFrame.length i.keyFrame.bytes i.keyFrame.shape (localKeyFrame i v).present (localKeyFrame i v).prototype
    (slot i) (slot_small i) (localKeyFrame i v).room
  simpa only [MixkeyArray.readByte,slot,keyNat,keyByte,Nat.mod_lt _ i.nonempty,↓reduceIte,MixkeyArray.byteValue] using read

theorem native_old (i : Inputs) (v : Arc4Locals.Values) (context : ExecutionContext)
    (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (array i)) (MixkeyIndex.key (index i)) =
      result (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (oldNat i))) := by
  have read := MixkeyArray.native_read (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (array i) i.arrayFrame.object
    i.arrayFrame.length i.arrayFrame.bytes i.arrayFrame.shape (localArrayFrame i v).present (localArrayFrame i v).prototype
    (index i) (i.small) (localArrayFrame i v).room
  simpa only [MixkeyArray.readByte,index,oldNat,oldByte,i.full,i.small,↓reduceIte,MixkeyArray.byteValue] using read

theorem native_moved (i : Inputs) (v : Arc4Locals.Values) (context : ExecutionContext)
    (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (array i)) (MixkeyIndex.key (nextIndex i)) =
      result (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (movedNat i))) := by
  have read := MixkeyArray.native_read (Machine.mk (Arc4Locals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (array i) i.arrayFrame.object
    i.arrayFrame.length i.arrayFrame.bytes i.arrayFrame.shape (localArrayFrame i v).present (localArrayFrame i v).prototype
    (nextIndex i) (next_small i) (localArrayFrame i v).room
  simpa only [MixkeyArray.readByte,movedNat,movedByte,i.full,next_small i,↓reduceIte,MixkeyArray.byteValue] using read

end CookieClicker.JavaScript.Arc4ScheduleRead

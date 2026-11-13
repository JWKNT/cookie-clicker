import CookieClicker.JavaScriptRetainedArc4Generate

/-! Native pre-swap array reads of the source generation expression. -/
namespace CookieClicker.JavaScript.RetainedArc4GenerateRead
open RetainedArc4Generate
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

theorem native_picked (i : Inputs) (v : RetainedArc4GeneratorLocals.Values) (context : ExecutionContext) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (RetainedArc4GeneratorLocals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (array i)) (MixkeyIndex.key (fIndex i))=
      result (Machine.mk (RetainedArc4GeneratorLocals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (picked i))) := by
  have read := MixkeyArray.native_read (Machine.mk (RetainedArc4GeneratorLocals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (array i) i.arrayFrame.object
    i.arrayFrame.length i.arrayFrame.bytes i.arrayFrame.shape (localFrame i v).present (localFrame i v).prototype
    (fIndex i) (f_small i) (localFrame i v).room
  simpa only [MixkeyArray.readByte,i.full,f_small i,↓reduceIte,MixkeyArray.byteValue,picked,pickedByte] using read

theorem native_moved (i : Inputs) (v : RetainedArc4GeneratorLocals.Values) (context : ExecutionContext) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (RetainedArc4GeneratorLocals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (array i)) (MixkeyIndex.key (gIndex i))=
      result (Machine.mk (RetainedArc4GeneratorLocals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (moved i))) := by
  have read := MixkeyArray.native_read (Machine.mk (RetainedArc4GeneratorLocals.heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (array i) i.arrayFrame.object
    i.arrayFrame.length i.arrayFrame.bytes i.arrayFrame.shape (localFrame i v).present (localFrame i v).prototype
    (gIndex i) (g_small i) (localFrame i v).room
  simpa only [MixkeyArray.readByte,i.full,g_small i,↓reduceIte,MixkeyArray.byteValue,moved,movedByte] using read

end CookieClicker.JavaScript.RetainedArc4GenerateRead

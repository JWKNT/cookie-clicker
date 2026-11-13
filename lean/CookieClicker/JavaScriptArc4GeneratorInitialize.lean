import CookieClicker.JavaScriptArc4Instance

/-! The nested g function initializes its counter and reads e.i, e.j and e.S
from the actual captured constructor instance before entering its source loop. -/
namespace CookieClicker.JavaScript.Arc4GeneratorInitialize
open Arc4GeneratorLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  source : Arc4GeneratorLocals.Inputs
  objects : Array JSObject
  argument : ObjectId
  receiver : ObjectId
  array : ObjectId
  count : Nat
  small : count≤256
  oldF : UInt8
  oldG : UInt8
  instanceObject : JSObject
  instanceRead : checkedObject (Arc4Generate.objectHeap source objects) receiver=.ok instanceObject
  instanceShape : Arc4Instance.Shape instanceObject oldF oldG array
  receiverRead : source.constructorValues.e=.object receiver
  arrayFrame : Arc4Bytes.Frame (Arc4Generate.objectHeap source objects) array
  full : arrayFrame.length=256

def source (i : Inputs) := i.source
def objects (i : Inputs) := i.objects
def argument (i : Inputs) := i.argument
def receiver (i : Inputs) := i.receiver
def array (i : Inputs) := i.array
def count (i : Inputs) := i.count
def oldF (i : Inputs) := i.oldF.toNat
def oldG (i : Inputs) := i.oldG.toNat

def initialValues (i : Inputs) : Values := {a := .number (Number.ofNat (count i))}
def start (i : Inputs) (tail : List Frame) :=
  machine (source i) (objects i) (argument i) (initialValues i)
    (.declarationFunctions [] Arc4GeneratorEntry.body) tail

def returnStatement : Stmt := match SeedrandomArc4Syntax.generatorBody with
  | .block statements => statements[1]?.getD .empty
  | _ => .empty

def cursor (i : Inputs) : Arc4GenerateCursor.Cursor := {
  source := source i, objects := objects i, argument := argument i, array := array i
  arrayFrame := i.arrayFrame, full := i.full, remaining := count i, small := i.small
  oldB := .undefined, accumulator := 0, oldF := i.oldF, oldG := i.oldG }
def finish (i : Inputs) (tail : List Frame) :=
  Arc4GenerateCursor.start (cursor i) none (.statementList [returnStatement] none :: tail)

theorem outer_e (i : Inputs) (v : Values) :
    readBinding (heap (source i) (objects i) (argument i) v) (constructorIndex (source i)) "e"=
      .ok (.object (receiver i)) := by
  rw [Arc4GeneratorLocals.read_e]
  exact congrArg Except.ok i.receiverRead

theorem checked_instance (i : Inputs) (v : Values) :
    checkedObject (heap (source i) (objects i) (argument i) v) (receiver i)=.ok i.instanceObject :=
  i.instanceRead

theorem native_i (i : Inputs) (v : Values) (context : ExecutionContext) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (receiver i)) (JSString.ofString "i")=
      result (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (oldF i))) :=
  Arc4Instance.read_field (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (receiver i) i.instanceObject
    (JSString.ofString "i") (.number (Number.ofNat (oldF i))) (checked_instance i v)
    i.instanceShape.unresolved i.instanceShape.kind i.instanceShape.indexI

theorem native_j (i : Inputs) (v : Values) (context : ExecutionContext) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (receiver i)) (JSString.ofString "j")=
      result (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (oldG i))) :=
  Arc4Instance.read_field (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (receiver i) i.instanceObject
    (JSString.ofString "j") (.number (Number.ofNat (oldG i))) (checked_instance i v)
    i.instanceShape.unresolved i.instanceShape.kind i.instanceShape.indexJ

theorem native_S (i : Inputs) (v : Values) (context : ExecutionContext) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (receiver i)) (JSString.ofString "S")=
      result (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (array i)) :=
  Arc4Instance.read_field (Machine.mk (heap (source i) (objects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (receiver i) i.instanceObject
    (JSString.ofString "S") (.object (array i)) (checked_instance i v)
    i.instanceShape.unresolved i.instanceShape.kind i.instanceShape.stateS

attribute [local cbv_opaque] base constructorIndex libraryIndex localIndex heap Number.ofNat Number.add Number.mul
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty writeProperty JSString.ofString source objects argument receiver array count oldF oldG
attribute [local cbv_eval] checked_library checked_constructor checked_local environment_size
  identifier_a identifier_b identifier_c identifier_e identifier_f identifier_g identifier_h identifier_d identifier_j
  read_a read_b read_c outer_e read_f read_g read_h read_d read_j write_a write_b write_c write_f write_g write_h
  native_i native_j native_S Arc4Initializers.number_zero

theorem actual_initialization (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (38+fuel) (start i tail)=Builtins.run fuel (finish i tail) := by
  rw [Nat.add_comm 38 fuel]
  cbv

end CookieClicker.JavaScript.Arc4GeneratorInitialize

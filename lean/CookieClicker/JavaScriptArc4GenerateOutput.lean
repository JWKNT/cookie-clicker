import CookieClicker.JavaScriptArc4GenerateWrites

/-! The generator reads its output byte after both in-place swaps and then
performs the actual binary64 accumulator multiply/add. -/
namespace CookieClicker.JavaScript.Arc4GenerateOutput
open Arc4Generate Arc4GeneratorLocals Arc4GenerateBody Arc4GenerateWrites
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def outputBits (i : Arc4Generate.Inputs) := Number.add (Number.ofNat (moved i)) (Number.ofNat (picked i))
def outputSlot (i : Arc4Generate.Inputs) := MixkeyArray.maskedByte (outputBits i)
def outputIndex (i : Arc4Generate.Inputs) := (outputSlot i).toNat
def outputByte (i : Arc4Generate.Inputs) := (secondFrame i).bytes (outputIndex i)
def outputNat (i : Arc4Generate.Inputs) := (outputByte i).toNat
def accumulated (i : Arc4Generate.Inputs) := Number.add (product i) (Number.ofNat (outputNat i))
def outputValues (i : Arc4Generate.Inputs) : Values := {updatedValues i with c := .number (accumulated i)}

def outputFrame (i : Arc4Generate.Inputs) (v : Values) :
    Arc4Bytes.Frame (heap (source i) (secondObjects i) (argument i) v) (array i) :=
  Arc4Bytes.transport (secondFrame i) rfl

theorem output_small (i : Arc4Generate.Inputs) : outputIndex i<256 := (outputSlot i).toNat_lt

theorem output_key (i : Arc4Generate.Inputs) :
    toJSString (.number (Number.ofNat (outputIndex i)))=.ok (MixkeyIndex.key (outputIndex i)) :=
  Arc4Identity.native_key _ (output_small i)

theorem native_output_mask (i : Arc4Generate.Inputs) :
    binary .bitAnd (.number (Number.ofNat 255))
      (.number (Number.add (Number.ofNat (moved i)) (Number.ofNat (picked i))))=
      .ok (.number (Number.ofNat (outputIndex i))) := by
  change (Except.ok (.number (Number.bitAnd (Number.ofNat 255) (outputBits i))) : Checked Value) = _
  rw [MixkeyArray.masked_value]
  rfl

theorem native_output (i : Arc4Generate.Inputs) (v : Values) (context : ExecutionContext) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    readProperty (Machine.mk (heap (source i) (secondObjects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.object (array i)) (MixkeyIndex.key (outputIndex i))=
      result (Machine.mk (heap (source i) (secondObjects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (.number (Number.ofNat (outputNat i))) := by
  have read := MixkeyArray.native_read (Machine.mk (heap (source i) (secondObjects i) (argument i) v) context control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) (array i) (secondFrame i).object
    (secondFrame i).length (secondFrame i).bytes (secondFrame i).shape (outputFrame i v).present (outputFrame i v).prototype
    (outputIndex i) (output_small i) (outputFrame i v).room
  simpa only [MixkeyArray.readByte,second_length,output_small i,↓reduceIte,MixkeyArray.byteValue,outputNat,outputByte] using read

def finish (i : Arc4Generate.Inputs) (tail : List Frame) :=
  machine (source i) (secondObjects i) (argument i) (outputValues i) (.expression test)
    (.forTest (some test) none body [] (some (.number (accumulated i))) :: tail)

attribute [local cbv_opaque] base constructorIndex libraryIndex localIndex heap Number.ofNat Number.add Number.mul
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty writeProperty source objects argument array count oldB accumulator oldF oldG fIndex picked gIndex moved
  firstObjects secondObjects outputIndex outputNat
attribute [local cbv_eval] checked_library checked_constructor checked_local environment_size
  identifier_a identifier_b identifier_c identifier_e identifier_f identifier_g identifier_h identifier_d identifier_j
  read_a read_b read_c read_e read_f read_g read_h read_d read_j write_a write_b write_c write_f write_g write_h
  f_key g_key Arc4Schedule.native_add native_mul native_f_mask_literal native_g_mask
  output_key native_output_mask native_output

theorem actual_finish (i : Arc4Generate.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (11+fuel) (afterSecond i previous tail)=Builtins.run fuel (finish i tail) := by
  rw [Nat.add_comm 11 fuel]
  cbv

theorem actual_body (i : Arc4Generate.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (128+fuel) (Arc4GenerateBody.start i previous tail)=Builtins.run fuel (finish i tail) := by
  rw [show 128+fuel=99+(29+fuel) by omega,actual_first_prefix]
  rw [show 29+fuel=(28+fuel)+1 by omega]
  change Builtins.run (28+fuel) (Builtins.builtinStep (firstWrite i previous tail)) = _
  rw [actual_first_write,show 28+fuel=16+(12+fuel) by omega,actual_second_prefix]
  rw [show 12+fuel=(11+fuel)+1 by omega]
  change Builtins.run (11+fuel) (Builtins.builtinStep (secondWrite i previous tail)) = _
  rw [actual_second_write,actual_finish]

end CookieClicker.JavaScript.Arc4GenerateOutput

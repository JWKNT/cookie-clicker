import CookieClicker.JavaScriptArc4ScheduleBody

/-! Both in-place ARC4 swaps are actual native assignments. The second write
uses the saved source b binding even when both selected slots coincide. -/
namespace CookieClicker.JavaScript.Arc4ScheduleWrites
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Schedule Arc4Locals Arc4ScheduleBody

def finalValues (i : Arc4Schedule.Inputs) :=
  Arc4Schedule.values i (.number (Number.ofNat (oldNat i))) (.number (Number.ofNat (nextIndex i)))
def firstObjects (i : Arc4Schedule.Inputs) :=
  (objects i).set! (array i) (MixkeyArray.written i.arrayFrame.object i.arrayFrame.length (index i) (movedByte i))
def firstFrame (i : Arc4Schedule.Inputs) :
    Arc4Bytes.Frame (heap (source i) (firstObjects i) (argument i) (finalValues i)) (array i) :=
  Arc4Bytes.write (localArrayFrame i (finalValues i)) (index i) (movedByte i) i.small (by simp [localArrayFrame,Arc4Bytes.transport,i.full]; exact Nat.le_of_lt i.small)

def afterFirst (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  result {firstWrite i previous tail with heap := heap (source i) (firstObjects i) (argument i) (finalValues i)}
    (.number (Number.ofNat (movedNat i)))

theorem actual_first_write (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) :
    Builtins.builtinStep (firstWrite i previous tail) = afterFirst i previous tail := by
  change {writeProperty (firstWrite i previous tail) (.object (array i)) (MixkeyIndex.key (index i))
    (MixkeyArray.byteValue (movedByte i)) false with elapsed := (base (source i)).elapsed} = _
  rw [MixkeyArray.native_write _ (array i) i.arrayFrame.object i.arrayFrame.length i.arrayFrame.bytes i.arrayFrame.shape
    (localArrayFrame i (finalValues i)).present (localArrayFrame i (finalValues i)).prototype
    (index i) i.small (movedByte i) (localArrayFrame i (finalValues i)).room (localArrayFrame i (finalValues i)).bound false]
  rfl

def secondWrite (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (firstObjects i) (argument i) (finalValues i)
    (.putValue ⟨.property (.object (array i)) (MixkeyIndex.key (nextIndex i)),false⟩ (.number (Number.ofNat (oldNat i))))
    (.sequence [] :: .expressionStatement :: .forBody (some test) update body [] previous :: tail)

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty source objects argument key array index length oldG oldB receiver slot keyNat oldNat nextIndex movedNat firstObjects
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_b write_c write_e write_f write_g write_h
  native_remainder index_key slot_key next_key native_add native_mask
  Arc4ScheduleRead.native_key Arc4ScheduleRead.native_old Arc4ScheduleRead.native_moved

theorem actual_second_prefix (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (16+fuel) (afterFirst i previous tail) = Builtins.run fuel (secondWrite i previous tail) := by
  rw [Nat.add_comm 16 fuel]
  cbv

def secondObjects (i : Arc4Schedule.Inputs) :=
  (firstObjects i).set! (array i) (MixkeyArray.written (firstFrame i).object (firstFrame i).length (nextIndex i) (oldByte i))

theorem first_length (i : Arc4Schedule.Inputs) : (firstFrame i).length=256 := by
  simp [firstFrame,Arc4Bytes.write,localArrayFrame,Arc4Bytes.transport,MixkeyArray.nextLength,i.full,show ¬ i.index≥256 by exact Nat.not_le.mpr i.small,index]

def secondFrame (i : Arc4Schedule.Inputs) :
    Arc4Bytes.Frame (heap (source i) (secondObjects i) (argument i) (finalValues i)) (array i) :=
  Arc4Bytes.write (firstFrame i) (nextIndex i) (oldByte i) (next_small i) (by rw [first_length]; exact Nat.le_of_lt (next_small i))

def afterSecond (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  result {secondWrite i previous tail with heap := heap (source i) (secondObjects i) (argument i) (finalValues i)}
    (.number (Number.ofNat (oldNat i)))

theorem actual_second_write (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) :
    Builtins.builtinStep (secondWrite i previous tail) = afterSecond i previous tail := by
  change {writeProperty (secondWrite i previous tail) (.object (array i)) (MixkeyIndex.key (nextIndex i))
    (MixkeyArray.byteValue (oldByte i)) false with elapsed := (base (source i)).elapsed} = _
  rw [MixkeyArray.native_write _ (array i) (firstFrame i).object (firstFrame i).length (firstFrame i).bytes (firstFrame i).shape
    (firstFrame i).present (firstFrame i).prototype
    (nextIndex i) (next_small i) (oldByte i) (firstFrame i).room (firstFrame i).bound false]
  rfl

theorem second_length (i : Arc4Schedule.Inputs) : (secondFrame i).length=256 := by
  simp [secondFrame,Arc4Bytes.write,MixkeyArray.nextLength,first_length,show ¬nextIndex i≥256 by exact Nat.not_le.mpr (next_small i)]

end CookieClicker.JavaScript.Arc4ScheduleWrites

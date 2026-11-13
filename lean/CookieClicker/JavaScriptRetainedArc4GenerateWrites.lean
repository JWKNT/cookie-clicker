import CookieClicker.JavaScriptRetainedArc4GenerateBody

/-! Both in-place ARC4 swaps are actual native assignments. The second write
uses the saved source b binding even when both selected slots coincide. -/
namespace CookieClicker.JavaScript.RetainedArc4GenerateWrites
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open RetainedArc4Generate RetainedArc4GeneratorLocals RetainedArc4GenerateBody

def finalValues (i : RetainedArc4Generate.Inputs) := updatedValues i
def firstObjects (i : RetainedArc4Generate.Inputs) :=
  (objects i).set! (array i) (MixkeyArray.written i.arrayFrame.object i.arrayFrame.length (fIndex i) (movedByte i))
def firstFrame (i : RetainedArc4Generate.Inputs) :
    Arc4Bytes.Frame (heap (source i) (firstObjects i) (argument i) (finalValues i)) (array i) :=
  Arc4Bytes.write (localFrame i (finalValues i)) (fIndex i) (movedByte i) (f_small i) (by simp [localFrame,Arc4Bytes.transport,i.full]; exact Nat.le_of_lt (f_small i))

def afterFirst (i : RetainedArc4Generate.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  result {firstWrite i previous tail with heap := heap (source i) (firstObjects i) (argument i) (finalValues i)}
    (.number (Number.ofNat (moved i)))

theorem actual_first_write (i : RetainedArc4Generate.Inputs) (previous : Option Value) (tail : List Frame) :
    Builtins.builtinStep (firstWrite i previous tail) = afterFirst i previous tail := by
  change {writeProperty (firstWrite i previous tail) (.object (array i)) (MixkeyIndex.key (fIndex i))
    (MixkeyArray.byteValue (movedByte i)) false with elapsed := (base (source i)).elapsed} = _
  rw [MixkeyArray.native_write _ (array i) i.arrayFrame.object i.arrayFrame.length i.arrayFrame.bytes i.arrayFrame.shape
    (localFrame i (finalValues i)).present (localFrame i (finalValues i)).prototype
    (fIndex i) (f_small i) (movedByte i) (localFrame i (finalValues i)).room (localFrame i (finalValues i)).bound false]
  rfl

def secondWrite (i : RetainedArc4Generate.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (firstObjects i) (argument i) (finalValues i)
    (.putValue ⟨.property (.object (array i)) (MixkeyIndex.key (gIndex i)),false⟩ (.number (Number.ofNat (picked i))))
    (.binaryRight .add (.number (Number.ofNat (moved i))) ::
      .binaryRight .bitAnd (.number (Number.ofNat 255)) :: .memberProperty (.object (array i)) ::
      .binaryRight .add (.number (product i)) ::
      .assignmentRight .assign ⟨.environment (localIndex (source i)) "c",false⟩ none ::
      .sequence [] :: .expressionStatement :: .forBody (some test) none body [] previous :: tail)

attribute [local cbv_opaque] base constructorIndex libraryIndex localIndex heap Number.ofNat Number.add Number.mul
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty writeProperty source objects argument array count oldB accumulator oldF oldG fIndex picked gIndex moved firstObjects
attribute [local cbv_eval] checked_library checked_constructor checked_local environment_size
  identifier_a identifier_b identifier_c identifier_e identifier_f identifier_g identifier_h identifier_d identifier_j
  read_a read_b read_c read_e read_f read_g read_h read_d read_j write_a write_b write_c write_f write_g write_h
  f_key g_key Arc4Schedule.native_add native_mul native_f_mask_literal native_g_mask

theorem actual_second_prefix (i : RetainedArc4Generate.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (16+fuel) (afterFirst i previous tail) = Builtins.run fuel (secondWrite i previous tail) := by
  rw [Nat.add_comm 16 fuel]
  cbv

def secondObjects (i : RetainedArc4Generate.Inputs) :=
  (firstObjects i).set! (array i) (MixkeyArray.written (firstFrame i).object (firstFrame i).length (gIndex i) (pickedByte i))

theorem first_length (i : RetainedArc4Generate.Inputs) : (firstFrame i).length=256 := by
  simp [firstFrame,Arc4Bytes.write,localFrame,Arc4Bytes.transport,MixkeyArray.nextLength,i.full,show ¬ fIndex i≥256 by exact Nat.not_le.mpr (f_small i)]

def secondFrame (i : RetainedArc4Generate.Inputs) :
    Arc4Bytes.Frame (heap (source i) (secondObjects i) (argument i) (finalValues i)) (array i) :=
  Arc4Bytes.write (firstFrame i) (gIndex i) (pickedByte i) (g_small i) (by rw [first_length]; exact Nat.le_of_lt (g_small i))

def afterSecond (i : RetainedArc4Generate.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  result {secondWrite i previous tail with heap := heap (source i) (secondObjects i) (argument i) (finalValues i)}
    (.number (Number.ofNat (picked i)))

theorem actual_second_write (i : RetainedArc4Generate.Inputs) (previous : Option Value) (tail : List Frame) :
    Builtins.builtinStep (secondWrite i previous tail) = afterSecond i previous tail := by
  change {writeProperty (secondWrite i previous tail) (.object (array i)) (MixkeyIndex.key (gIndex i))
    (MixkeyArray.byteValue (pickedByte i)) false with elapsed := (base (source i)).elapsed} = _
  rw [MixkeyArray.native_write _ (array i) (firstFrame i).object (firstFrame i).length (firstFrame i).bytes (firstFrame i).shape
    (firstFrame i).present (firstFrame i).prototype
    (gIndex i) (g_small i) (pickedByte i) (firstFrame i).room (firstFrame i).bound false]
  rfl

theorem second_length (i : RetainedArc4Generate.Inputs) : (secondFrame i).length=256 := by
  simp [secondFrame,Arc4Bytes.write,MixkeyArray.nextLength,first_length,show ¬gIndex i≥256 by exact Nat.not_le.mpr (g_small i)]

end CookieClicker.JavaScript.RetainedArc4GenerateWrites

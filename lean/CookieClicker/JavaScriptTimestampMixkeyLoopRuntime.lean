import CookieClicker.JavaScriptTimestampMixkeyLoop
import CookieClicker.JavaScriptBrowserCoreStep

/-! Retained source prefixes under the composed browser handlers. -/
namespace CookieClicker.JavaScript.TimestampMixkeyLoopRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkeyLoop
open TimestampMixkey

attribute [local cbv_opaque] base scope seed key libraryBindings libraryOuter heap localIndex bodyHeap
  checkedEnvironment binary toJSString readBinding MixkeyIndex.key Nat.mod Number.ofNat Array.size List.length readProperty

attribute [local cbv_eval] checked_library checked_local environment_size contains_mask read_mask
  MixkeyIndex.source_slot MixkeyIndex.source_key

attribute [local cbv_eval] local_read_a local_read_b local_read_c local_read_d local_read_e slot_ofNat key_mod

theorem actual_before_old_byte (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat)
    (previous : Option Value) (fuel : Nat) :
    BrowserRuntime.run (48+fuel) {state with machine := (start i objects d index previous)} =
      BrowserRuntime.run fuel {state with machine := (atOldByte i objects d index previous)} := by
  change BrowserRuntime.run (48+fuel) {state with machine := {start i objects d index previous with heap := heap i objects d index}} = _
  rw [Nat.add_comm 48 fuel]
  cbv
  all_goals (try simp only [environment_size,slot_ofNat,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat,key_mod]; cbv)


attribute [local cbv_opaque] multiplied nextSmear MixkeyArray.readByte setBinding Number.mul Number.bitXor

attribute [local cbv_eval] native_multiply native_smear write_d multiply_numbers multiply_undefined xor_numbers xor_undefined

theorem actual_smear (state : Browser.State) (i : Inputs) (objects : Array JSObject) (smear : Option UInt64) (index : Nat)
    (previous : Option Value) (length : Nat) (bytes : Nat → UInt8) (fuel : Nat) :
    BrowserRuntime.run (4+fuel) {state with machine := (afterOldByte i objects (smearValue smear) index previous length bytes)} =
      BrowserRuntime.run fuel {state with machine := (afterSmear i objects smear index previous length bytes)} := by
  change BrowserRuntime.run (4+fuel) {state with machine := {afterOldByte i objects (smearValue smear) index previous length bytes with
    heap := heap i objects (smearValue smear) index}} = _
  rw [Nat.add_comm 4 fuel]
  by_cases occupied : Nat.mod index 256 < length
  · have read : MixkeyArray.readByte length bytes (Nat.mod index 256) =
        .number (Number.ofNat (bytes (Nat.mod index 256)).toNat) := by simp [MixkeyArray.readByte,occupied,MixkeyArray.byteValue]
    cases smear <;> cbv
    all_goals (simp only [read]; cbv)
    all_goals simp only [heap,nextSmear,multiplied,oldBits,occupied,↓reduceIte,Option.getD]
    all_goals rfl
  · have read : MixkeyArray.readByte length bytes (Nat.mod index 256) = .undefined := by simp [MixkeyArray.readByte,occupied]
    cases smear <;> cbv
    all_goals (simp only [read]; cbv)
    all_goals simp only [heap,nextSmear,multiplied,oldBits,occupied,↓reduceIte,Option.getD]
    all_goals rfl



theorem actual_read_old_byte (state : Browser.State) (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat)
    (previous : Option Value) (object : JSObject) (length : Nat) (bytes : Nat → UInt8)
    (shape : MixkeyArray.Shape object length bytes)
    (present : checkedObject (heap i objects d index) (key i) = .ok object)
    (prototype : MixkeyArray.PrototypeFrame (heap i objects d index) object)
    (room : 2 ≤ objects.size) :
    BrowserRuntime.step {state with machine := atOldByte i objects d index previous} =
      {state with machine := afterOldByte i objects d index previous length bytes} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,
    TimestampMixkeyLoop.actual_read_old_byte i objects d index previous object length bytes shape present prototype room]
  rfl

end CookieClicker.JavaScript.TimestampMixkeyLoopRuntime

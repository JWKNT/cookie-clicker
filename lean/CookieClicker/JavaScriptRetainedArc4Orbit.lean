import CookieClicker.JavaScriptArc4ByteArithmetic
import CookieClicker.Arc4Orbit
import CookieClicker.JavaScriptRetainedArc4GeneratorCall

/-! Projection of each actual source generator swap and output byte to the
finite invertible byte dynamics. -/
namespace CookieClicker.JavaScript.RetainedArc4SourceOrbit
open RetainedArc4Generate RetainedArc4GenerateCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def project (cursor : Cursor) : CookieClicker.Arc4Orbit.State :=
  ⟨fun byte => cursor.arrayFrame.bytes byte.toNat,cursor.oldF,cursor.oldG⟩

theorem first_index (cursor : Cursor) : nextF (inputs cursor) = cursor.oldF+1 := by
  exact Arc4ByteArithmetic.add_mask cursor.oldF 1

theorem second_index (cursor : Cursor) :
    nextG (inputs cursor) = cursor.oldG + pickedByte (inputs cursor) :=
  Arc4ByteArithmetic.add_mask cursor.oldG (pickedByte (inputs cursor))

theorem writes_swap (bytes : Nat → UInt8) (a b : UInt8) :
    (fun byte : UInt8 => MixkeyArray.nextBytes
      (MixkeyArray.nextBytes bytes a.toNat (bytes b.toNat)) b.toNat (bytes a.toNat) byte.toNat) =
      CookieClicker.Arc4Orbit.swap (fun byte => bytes byte.toNat) a b := by
  funext byte
  simp only [MixkeyArray.nextBytes,UInt8.toNat_inj,CookieClicker.Arc4Orbit.swap]
  by_cases first : byte = a
  · subst byte
    by_cases same : a = b
    · subst b; simp
    · simp [same]
  · simp [first]

theorem project_next (cursor : Cursor) :
    project (next cursor) = CookieClicker.Arc4Orbit.next (project cursor) := by
  change CookieClicker.Arc4Orbit.State.mk
    (fun byte => (next cursor).arrayFrame.bytes byte.toNat)
    (nextF (inputs cursor)) (nextG (inputs cursor)) = _
  rw [RetainedArc4GenerateCursor.next_permutation]
  change CookieClicker.Arc4Orbit.State.mk
    (fun byte => MixkeyArray.nextBytes
      (MixkeyArray.nextBytes cursor.arrayFrame.bytes (nextF (inputs cursor)).toNat
        (cursor.arrayFrame.bytes (nextG (inputs cursor)).toNat))
      (nextG (inputs cursor)).toNat (cursor.arrayFrame.bytes (nextF (inputs cursor)).toNat) byte.toNat)
    (nextF (inputs cursor)) (nextG (inputs cursor)) = _
  rw [writes_swap,second_index,first_index]
  unfold pickedByte fIndex
  rw [first_index]
  rfl

theorem actual_output (cursor : Cursor) :
    RetainedArc4GenerateOutput.outputByte (inputs cursor) = CookieClicker.Arc4Orbit.output (project cursor) := by
  have slot : RetainedArc4GenerateOutput.outputSlot (inputs cursor) =
      movedByte (inputs cursor) + pickedByte (inputs cursor) :=
    Arc4ByteArithmetic.add_mask (movedByte (inputs cursor)) (pickedByte (inputs cursor))
  unfold RetainedArc4GenerateOutput.outputByte RetainedArc4GenerateOutput.outputIndex
  rw [slot]
  change (project (next cursor)).bytes (movedByte (inputs cursor) + pickedByte (inputs cursor)) = _
  rw [project_next]
  unfold CookieClicker.Arc4Orbit.output CookieClicker.Arc4Orbit.next
  simp only [CookieClicker.Arc4Orbit.swap_left,CookieClicker.Arc4Orbit.swap_right]
  simp only [project,movedByte,pickedByte,gIndex,fIndex,second_index,first_index]
  rfl

theorem project_traverse (count : Nat) (stage : RetainedArc4GenerateComplete.Stage)
    (bound : count ≤ stage.cursor.remaining) :
    project (RetainedArc4GenerateComplete.traverse count stage bound).cursor =
      FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next count (project stage.cursor) := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [RetainedArc4GenerateComplete.traverse]
    rw [induction]
    change FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next count
      (project (next stage.cursor)) = _
    rw [project_next,←FiniteInvertibleOrbit.run_succ_start]

end CookieClicker.JavaScript.RetainedArc4SourceOrbit

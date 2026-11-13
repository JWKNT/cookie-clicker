import CookieClicker.JavaScriptArc4ConstructorMemory

/-! The actual identity, scheduling swaps, and generator swaps retain an inverse
for the 256 native byte slots. No condition on the key bytes is required. -/
namespace CookieClicker.JavaScript.Arc4Permutation
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def IsPermutation (bytes : Nat → UInt8) : Prop :=
  ∃ inverse : UInt8 → Fin 256,
    (∀ slot : Fin 256, inverse (bytes slot.val) = slot) ∧
    (∀ byte : UInt8, bytes (inverse byte).val = byte)

def exchange (a b slot : Fin 256) : Fin 256 :=
  if slot = a then b else if slot = b then a else slot

theorem exchange_twice (a b slot : Fin 256) : exchange a b (exchange a b slot) = slot := by
  by_cases first : slot = a
  · subst slot
    by_cases same : a = b
    · subst b; simp [exchange]
    · simp [exchange,same,Ne.symm same]
  · by_cases second : slot = b
    · subst slot; simp [exchange,first]
    · simp [exchange,first,second]

theorem swapped_bytes (bytes : Nat → UInt8) (a b slot : Fin 256) :
    MixkeyArray.nextBytes (MixkeyArray.nextBytes bytes a.val (bytes b.val)) b.val (bytes a.val) slot.val =
      bytes (exchange a b slot).val := by
  by_cases first : slot = a
  · subst slot
    by_cases same : a = b
    · subst b; simp [MixkeyArray.nextBytes,exchange]
    · have distinct : a.val ≠ b.val := fun h => same (Fin.ext h)
      simp [MixkeyArray.nextBytes,exchange,distinct]
  · have firstVal : slot.val ≠ a.val := fun h => first (Fin.ext h)
    by_cases second : slot = b
    · subst slot; simp [MixkeyArray.nextBytes,exchange,first,firstVal]
    · have secondVal : slot.val ≠ b.val := fun h => second (Fin.ext h)
      simp [MixkeyArray.nextBytes,exchange,first,second,firstVal,secondVal]

theorem swapped (bytes : Nat → UInt8) (a b : Fin 256) (permutation : IsPermutation bytes) :
    IsPermutation (MixkeyArray.nextBytes (MixkeyArray.nextBytes bytes a.val (bytes b.val)) b.val (bytes a.val)) := by
  rcases permutation with ⟨inverse,left,right⟩
  refine ⟨fun byte => exchange a b (inverse byte),?_,?_⟩
  · intro slot
    simp only [swapped_bytes,left,exchange_twice]
  · intro byte
    rw [swapped_bytes,exchange_twice,right]

theorem identity : IsPermutation (fun slot => UInt8.ofNat slot) := by
  refine ⟨fun byte => ⟨byte.toNat,byte.toNat_lt⟩,?_,?_⟩
  · intro slot
    apply Fin.ext
    simp [UInt8.toNat_ofNat,Nat.mod_eq_of_lt slot.isLt]
  · intro byte
    exact UInt8.ofNat_toNat

theorem injective (bytes : Nat → UInt8) (permutation : IsPermutation bytes)
    (a b : Fin 256) (same : bytes a.val = bytes b.val) : a = b := by
  rcases permutation with ⟨inverse,left,_⟩
  have h := congrArg inverse same
  simpa only [left] using h

theorem contains (bytes : Nat → UInt8) (permutation : IsPermutation bytes) (byte : UInt8) :
    ∃ slot : Fin 256, bytes slot.val = byte := by
  rcases permutation with ⟨inverse,_,right⟩
  exact ⟨inverse byte,right byte⟩

theorem schedule_next (cursor : Arc4ScheduleCursor.Cursor) (small : cursor.index < 256)
    (permutation : IsPermutation cursor.arrayFrame.bytes) :
    IsPermutation (Arc4ScheduleCursor.next cursor small).arrayFrame.bytes := by
  rw [Arc4ScheduleCursor.successor_array]
  exact swapped cursor.arrayFrame.bytes ⟨cursor.index,small⟩
    ⟨Arc4Schedule.nextIndex (Arc4ScheduleCursor.inputs cursor small),
      Arc4Schedule.next_small (Arc4ScheduleCursor.inputs cursor small)⟩ permutation

theorem generate_next (cursor : Arc4GenerateCursor.Cursor)
    (permutation : IsPermutation cursor.arrayFrame.bytes) :
    IsPermutation (Arc4GenerateCursor.next cursor).arrayFrame.bytes := by
  rw [Arc4GenerateCursor.next_permutation]
  exact swapped cursor.arrayFrame.bytes
    ⟨Arc4Generate.fIndex (Arc4GenerateCursor.inputs cursor),Arc4Generate.f_small _⟩
    ⟨Arc4Generate.gIndex (Arc4GenerateCursor.inputs cursor),Arc4Generate.g_small _⟩ permutation

theorem schedule_traverse (count : Nat) (stage : Arc4ScheduleComplete.Stage)
    (bound : stage.cursor.index + count ≤ 256) (permutation : IsPermutation stage.cursor.arrayFrame.bytes) :
    IsPermutation (Arc4ScheduleComplete.traverse count stage bound).cursor.arrayFrame.bytes := by
  induction count generalizing stage with
  | zero => exact permutation
  | succ count induction =>
    simp only [Arc4ScheduleComplete.traverse]
    apply induction
    exact schedule_next stage.cursor _ permutation

theorem generate_traverse (count : Nat) (stage : Arc4GenerateComplete.Stage)
    (bound : count ≤ stage.cursor.remaining) (permutation : IsPermutation stage.cursor.arrayFrame.bytes) :
    IsPermutation (Arc4GenerateComplete.traverse count stage bound).cursor.arrayFrame.bytes := by
  induction count generalizing stage with
  | zero => exact permutation
  | succ count induction =>
    simp only [Arc4GenerateComplete.traverse]
    apply induction
    exact generate_next stage.cursor permutation

theorem schedule_finished (stage : Arc4ScheduleComplete.Stage)
    (permutation : IsPermutation stage.cursor.arrayFrame.bytes) :
    IsPermutation (Arc4ScheduleComplete.finished stage).cursor.arrayFrame.bytes :=
  schedule_traverse _ stage _ permutation

theorem generate_finished (stage : Arc4GenerateComplete.Stage)
    (permutation : IsPermutation stage.cursor.arrayFrame.bytes) :
    IsPermutation (Arc4GenerateComplete.finished stage).cursor.arrayFrame.bytes :=
  generate_traverse _ stage _ permutation

theorem constructor_schedule (input : Arc4ConstructorLoops.Inputs) :
    IsPermutation (Arc4ConstructorLoops.schedule input).cursor.arrayFrame.bytes := by
  apply schedule_finished
  exact identity

attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

theorem constructor_generated (input : Arc4ConstructorSetup.Inputs)
    (missing : Arc4ConstructorMemory.Final input) :
    IsPermutation (Arc4ConstructorMemory.generated input missing).cursor.arrayFrame.bytes := by
  apply generate_finished
  exact constructor_schedule (Arc4ConstructorPrefix.loops input)

theorem transport_bytes {before after : Heap} {array : ObjectId}
    (frame : Arc4Bytes.Frame before array) (same : after.objects = before.objects) :
    (Arc4Bytes.transport frame same).bytes = frame.bytes := rfl

theorem return_frame_bytes (input : Arc4GeneratorReturn.Inputs) (array : ObjectId)
    (frame : Arc4Bytes.Frame (Arc4Generate.objectHeap input.source input.objects) array)
    (different : input.receiver ≠ array)
    (arrayDifferent : input.receiver ≠ frame.prototype.arrayId)
    (rootDifferent : input.receiver ≠ frame.prototype.rootId) :
    (Arc4ConstructorMemory.returnFrame input array frame different arrayDifferent rootDifferent).bytes = frame.bytes := rfl

theorem generated_frame_bytes (input : Arc4ConstructorSetup.Inputs)
    (missing : Arc4ConstructorMemory.Final input) :
    (Arc4ConstructorMemory.generatedFrame input missing).bytes =
      (Arc4ConstructorMemory.generated input missing).cursor.arrayFrame.bytes := transport_bytes _ _

theorem returned_bytes (input : Arc4ConstructorSetup.Inputs)
    (missing : Arc4ConstructorMemory.Final input) :
    (Arc4ConstructorMemory.stateFrame input missing).bytes =
      (Arc4ConstructorMemory.generated input missing).cursor.arrayFrame.bytes :=
  (transport_bytes _ _).trans ((return_frame_bytes _ _ _ _ _ _).trans (generated_frame_bytes input missing))

theorem constructor_returned (input : Arc4ConstructorSetup.Inputs)
    (missing : Arc4ConstructorMemory.Final input) :
    IsPermutation (Arc4ConstructorMemory.stateFrame input missing).bytes := by
  rw [returned_bytes]
  exact constructor_generated input missing

theorem actual_constructor_has_permutation (input : Arc4ConstructorSetup.Inputs)
    (missing : Arc4ConstructorMemory.Final input) :
    ∃ array : ObjectId, ∃ object : JSObject, ∃ bytes : Nat → UInt8,
      checkedObject
        (Builtins.run (Arc4ConstructorPrefix.steps input + 34931)
          (Arc4ConstructorDispatch.start input)).heap array = .ok object ∧
      MixkeyArray.Shape object 256 bytes ∧ IsPermutation bytes := by
  rw [Arc4ConstructorComplete.actual_complete_state input missing]
  let frame := Arc4ConstructorMemory.stateFrame input missing
  refine ⟨_,frame.object,frame.bytes,frame.present,?_,constructor_returned input missing⟩
  have shape := frame.shape
  have full : frame.length = 256 := Arc4ConstructorMemory.state_full input missing
  simpa only [full] using shape

theorem returned_contains_nonzero (input : Arc4ConstructorSetup.Inputs)
    (missing : Arc4ConstructorMemory.Final input) :
    ∃ slot : Fin 256, (Arc4ConstructorMemory.stateFrame input missing).bytes slot.val = 1 :=
  contains _ (constructor_returned input missing) 1

end CookieClicker.JavaScript.Arc4Permutation

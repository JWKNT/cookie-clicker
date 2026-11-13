import CookieClicker.JavaScriptArc4NamedProperty

/-! The two actual constructor loops retain the instance and its named
properties while replacing numeric slots of S. -/
namespace CookieClicker.JavaScript.Arc4ConstructorRetained
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

open Arc4Locals

theorem identity_next_lookup {i : Inputs} {argument array : Nat} {v : Values}
    (cursor : Arc4IdentityLoop.Cursor i argument array v) (small : cursor.index<256) (id : ObjectId) :
    lookupProperty (Arc4Schedule.objectHeap i (Arc4IdentityLoop.next cursor small).objects) id (JSString.ofString "g")=
      lookupProperty (Arc4Schedule.objectHeap i cursor.objects) id (JSString.ofString "g") :=
  Arc4NamedProperty.dense_lookup (Arc4Schedule.objectHeap i cursor.objects) array id
    cursor.frame.object cursor.frame.length cursor.index (.number (Number.ofNat cursor.index)) small
    (Arc4Initialized.checked_present cursor.frame.present)

theorem identity_lookup {i : Inputs} {argument array : Nat} {v : Values}
    (count : Nat) (stage : Arc4IdentityComplete.Stage i argument array v)
    (bound : stage.cursor.index+count≤256) (id : ObjectId) :
    lookupProperty (Arc4Schedule.objectHeap i (Arc4IdentityComplete.traverse count stage bound).cursor.objects)
      id (JSString.ofString "g")=lookupProperty (Arc4Schedule.objectHeap i stage.cursor.objects) id (JSString.ofString "g") := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [Arc4IdentityComplete.traverse]
    rw [induction]
    exact identity_next_lookup stage.cursor _ id

theorem schedule_next_other (cursor : Arc4ScheduleCursor.Cursor) (small : cursor.index<256)
    (id : ObjectId) (different : cursor.array≠id) :
    (Arc4ScheduleCursor.next cursor small).objects[id]?=cursor.objects[id]? := by
  simp [Arc4ScheduleCursor.next,Arc4ScheduleCursor.inputs,Arc4ScheduleWrites.secondObjects,
    Arc4ScheduleWrites.firstObjects,Arc4Schedule.array,Arc4Schedule.objects,
    Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different]

theorem schedule_other (count : Nat) (stage : Arc4ScheduleComplete.Stage)
    (bound : stage.cursor.index+count≤256) (id : ObjectId) (different : stage.cursor.array≠id) :
    (Arc4ScheduleComplete.traverse count stage bound).cursor.objects[id]?=stage.cursor.objects[id]? := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [Arc4ScheduleComplete.traverse]
    rw [induction (Arc4ScheduleComplete.advance stage _) _ (show (Arc4ScheduleComplete.advance stage _).cursor.array≠id from different)]
    exact schedule_next_other stage.cursor _ id different

theorem schedule_fields (count : Nat) (stage : Arc4ScheduleComplete.Stage)
    (bound : stage.cursor.index+count≤256) :
    (Arc4ScheduleComplete.traverse count stage bound).cursor.source=stage.cursor.source ∧
    (Arc4ScheduleComplete.traverse count stage bound).cursor.array=stage.cursor.array ∧
    (Arc4ScheduleComplete.traverse count stage bound).cursor.argument=stage.cursor.argument ∧
    (Arc4ScheduleComplete.traverse count stage bound).cursor.receiver=stage.cursor.receiver := by
  induction count generalizing stage with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ count induction =>
    simp only [Arc4ScheduleComplete.traverse]
    exact induction _ _

theorem schedule_next_lookup (cursor : Arc4ScheduleCursor.Cursor) (small : cursor.index<256) (id : ObjectId) :
    lookupProperty (Arc4Schedule.objectHeap cursor.source (Arc4ScheduleCursor.next cursor small).objects) id (JSString.ofString "g")=
      lookupProperty (Arc4Schedule.objectHeap cursor.source cursor.objects) id (JSString.ofString "g") := by
  let q := Arc4ScheduleCursor.inputs cursor small
  have first := Arc4NamedProperty.byte_lookup (Arc4Schedule.objectHeap cursor.source cursor.objects)
    cursor.array id q.arrayFrame.object q.arrayFrame.length (Arc4Schedule.index q) (Arc4Schedule.movedByte q)
    small (Arc4Initialized.checked_present q.arrayFrame.present)
  have second := Arc4NamedProperty.byte_lookup
    (Arc4Schedule.objectHeap cursor.source (Arc4ScheduleWrites.firstObjects q)) cursor.array id
    (Arc4ScheduleWrites.firstFrame q).object (Arc4ScheduleWrites.firstFrame q).length
    (Arc4Schedule.nextIndex q) (Arc4Schedule.oldByte q) (by exact (Arc4Schedule.nextG q).toNat_lt)
    (Arc4Initialized.checked_present (Arc4ScheduleWrites.firstFrame q).present)
  exact second.trans first

theorem schedule_lookup (count : Nat) (stage : Arc4ScheduleComplete.Stage)
    (bound : stage.cursor.index+count≤256) (id : ObjectId) :
    lookupProperty (Arc4Schedule.objectHeap (Arc4ScheduleComplete.traverse count stage bound).cursor.source
      (Arc4ScheduleComplete.traverse count stage bound).cursor.objects) id (JSString.ofString "g")=
      lookupProperty (Arc4Schedule.objectHeap stage.cursor.source stage.cursor.objects) id (JSString.ofString "g") := by
  induction count generalizing stage with
  | zero => rfl
  | succ count induction =>
    simp only [Arc4ScheduleComplete.traverse]
    rw [induction]
    exact schedule_next_lookup stage.cursor _ id

end CookieClicker.JavaScript.Arc4ConstructorRetained

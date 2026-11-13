import CookieClicker.JavaScriptArc4GenerateRetained

/-! The complete native generator body from its hoisted source declarations
through initializer reads, every swap/output iteration, saved instance indices
and actual caller return. -/
namespace CookieClicker.JavaScript.Arc4GeneratorBodyComplete
open Arc4GeneratorInitialize
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def initial (i : Inputs) : Arc4GenerateComplete.Stage := ⟨cursor i,none⟩
def completed (i : Inputs) := Arc4GenerateComplete.finished (initial i)

theorem instance_different (i : Inputs) : i.array≠i.receiver := by
  intro same
  have read := i.arrayFrame.present
  conv at read => lhs; rw [same]
  have objects : i.instanceObject=i.arrayFrame.object := Except.ok.inj (i.instanceRead.symm.trans read)
  have kind := congrArg JSObject.kind objects
  rw [i.instanceShape.kind,i.arrayFrame.shape.kind] at kind
  contradiction

def returnInputs (i : Inputs) : Arc4GeneratorReturn.Inputs := {
  source := (completed i).cursor.source, objects := (completed i).cursor.objects
  argument := (completed i).cursor.argument, array := (completed i).cursor.array
  receiver := i.receiver
  oldF := i.oldF, oldG := i.oldG, newF := (completed i).cursor.oldF, newG := (completed i).cursor.oldG
  oldB := (completed i).cursor.oldB, accumulator := (completed i).cursor.accumulator
  instanceObject := i.instanceObject
  instanceRead := Arc4GenerateRetained.checked_other (initial i) i.receiver i.instanceObject
    (instance_different i) i.instanceRead
  instanceShape := by
    change Arc4Instance.Shape i.instanceObject i.oldF i.oldG (Arc4GenerateComplete.finished (initial i)).cursor.array
    rw [Arc4GenerateRetained.finished_array]
    exact i.instanceShape
  receiverRead := by
    change (Arc4GenerateComplete.finished (initial i)).cursor.source.constructorValues.e=.object i.receiver
    rw [Arc4GenerateRetained.finished_source]
    exact i.receiverRead }

def finish (i : Inputs) (caller : ExecutionContext) (tail : List Frame) :=
  Arc4GeneratorReturn.finish (returnInputs i) caller tail

theorem actual_body (i : Inputs) (caller : ExecutionContext) (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*i.count+82+fuel)
      (start i (.callBoundary caller none :: tail))=Builtins.run fuel (finish i caller tail) := by
  rw [show 136*i.count+82+fuel=38+(136*i.count+8+(36+fuel)) by omega,actual_initialization]
  change Builtins.run (136*(initial i).cursor.remaining+8+(36+fuel))
    (Arc4GenerateCursor.start (initial i).cursor (initial i).previous
      (.statementList [returnStatement] none :: .callBoundary caller none :: tail)) = _
  rw [Arc4GenerateComplete.actual_complete_loop]
  change Builtins.run (36+fuel)
    (Arc4GeneratorReturn.start (returnInputs i) (completed i).previous caller tail) = _
  rw [Arc4GeneratorReturn.actual_return]
  rfl

theorem discard_body (i : Inputs) (count : i.count=256) (caller : ExecutionContext) (tail : List Frame) (fuel : Nat) :
    Builtins.run (34898+fuel) (start i (.callBoundary caller none :: tail))=
      Builtins.run fuel (finish i caller tail) := by
  have native := actual_body i caller tail fuel
  simpa only [count] using native

end CookieClicker.JavaScript.Arc4GeneratorBodyComplete

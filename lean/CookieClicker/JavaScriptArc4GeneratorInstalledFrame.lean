import CookieClicker.JavaScriptArc4GeneratorInstall

/-! Frames derived from native generator allocation and its instance-field
write. The call receives the actual newly allocated source closure. -/
namespace CookieClicker.JavaScript.Arc4GeneratorInstalledFrame
open Arc4GeneratorInstall
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  install : Arc4GeneratorInstall.Inputs
  array : ObjectId
  oldF : UInt8
  oldG : UInt8
  shape : Arc4Instance.Shape install.instanceObject oldF oldG array
  arrayFrame : Arc4Bytes.Frame (Arc4Generate.objectHeap install.source install.objects) array
  full : arrayFrame.length=256
  different : install.receiver≠array
  arrayDifferent : install.receiver≠arrayFrame.prototype.arrayId
  rootDifferent : install.receiver≠arrayFrame.prototype.rootId

def heap (i : Inputs) := Arc4Generate.objectHeap i.install.source (installedObjects i.install)

theorem receiver_bound (i : Inputs) : i.install.receiver<i.install.objects.size :=
  (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present i.install.instanceRead)).1

theorem allocated_extension (i : Inputs) : HeapExtension.Extends
    (Arc4Generate.objectHeap i.install.source i.install.objects)
    (Arc4Generate.objectHeap i.install.source (allocatedObjects i.install)) :=
  HeapExtension.trans
    (HeapExtension.same_objects (before := Arc4Generate.objectHeap i.install.source i.install.objects)
      (after := (beforeAllocation i.install []).heap) rfl)
    (HeapExtension.trans (Arc4GeneratorAllocation.extension (beforeAllocation i.install [])
      (Arc4GeneratorLocals.constructorIndex i.install.source)) (HeapExtension.same_objects rfl))

theorem other_read (i : Inputs) (id : ObjectId) (object : JSObject)
    (different : i.install.receiver≠id)
    (present : checkedObject (Arc4Generate.objectHeap i.install.source i.install.objects) id=.ok object) :
    checkedObject (heap i) id=.ok object := by
  have after := HeapExtension.checked_object (allocated_extension i) id object present
  simp only [checkedObject,Heap.object?,heap,Arc4Generate.objectHeap,installedObjects,
    Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,receiver,different,↓reduceIte]
  exact after

theorem instance_read (i : Inputs) : checkedObject (heap i) i.install.receiver=.ok (installedObject i.install) := by
  have bound : i.install.receiver<(allocatedObjects i.install).size := Nat.lt_of_lt_of_le (receiver_bound i) (allocated_extension i).size
  simp [checkedObject,Heap.object?,heap,Arc4Generate.objectHeap,installedObjects,receiver,bound]

theorem installed_shape (i : Inputs) : Arc4Instance.Shape (installedObject i.install) i.oldF i.oldG i.array := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [installedObject,PropertyFrame.set_kind] using i.shape.kind
  · simpa [installedObject,PropertyFrame.set_unresolved] using i.shape.unresolved
  · rw [installedObject,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact i.shape.indexI
  · rw [installedObject,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact i.shape.indexJ
  · rw [installedObject,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact i.shape.stateS

def arrayFrame (i : Inputs) : Arc4Bytes.Frame (heap i) i.array := {
  object := i.arrayFrame.object, length := i.arrayFrame.length, bytes := i.arrayFrame.bytes, shape := i.arrayFrame.shape
  present := other_read i _ _ i.different i.arrayFrame.present
  prototype := i.arrayFrame.prototype.transport rfl
    (other_read i _ _ i.arrayDifferent i.arrayFrame.prototype.arrayRead)
    (other_read i _ _ i.rootDifferent i.arrayFrame.prototype.rootRead)
  room := by
    have bound := Nat.le_trans i.arrayFrame.room (allocated_extension i).size
    simpa [heap,Arc4Generate.objectHeap,installedObjects] using bound
  bound := by
    have bound := Nat.lt_of_lt_of_le i.arrayFrame.bound (allocated_extension i).size
    simpa [heap,Arc4Generate.objectHeap,installedObjects] using bound
  arrayDifferent := i.arrayFrame.arrayDifferent, rootDifferent := i.arrayFrame.rootDifferent }

def functionObject (i : Inputs) := Arc4GeneratorAllocation.functionObject (beforeAllocation i.install [])
  (Arc4GeneratorLocals.constructorIndex i.install.source)

theorem function_read (i : Inputs) : checkedObject (heap i) (functionIndex i.install)=.ok (functionObject i) := by
  have different : i.install.receiver≠functionIndex i.install := Nat.ne_of_lt (receiver_bound i)
  have found := Arc4GeneratorAllocation.function_present (beforeAllocation i.install [])
    (Arc4GeneratorLocals.constructorIndex i.install.source)
  simp only [checkedObject,Heap.object?,heap,Arc4Generate.objectHeap,installedObjects,
    Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,receiver,different,↓reduceIte]
  exact found

def call (i : Inputs) : Arc4GeneratorCall.Inputs := {
  source := i.install.source, objects := installedObjects i.install
  receiver := i.install.receiver, array := i.array, callee := functionIndex i.install
  count := 256, small := by decide, oldF := i.oldF, oldG := i.oldG
  instanceObject := installedObject i.install, instanceRead := instance_read i
  instanceShape := installed_shape i, receiverRead := i.install.receiverRead
  arrayFrame := arrayFrame i, full := i.full
  functionObject := functionObject i, functionRead := function_read i, functionKind := rfl }

def finish (i : Inputs) (tail : List Frame) := Arc4GeneratorCall.finish (call i) (.expressionStatement :: tail)

theorem actual_statement (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (34926+fuel) (Arc4GeneratorInstall.start i.install tail)=Builtins.run fuel (finish i tail) := by
  rw [show 34926+fuel=17+(34909+fuel) by omega,Arc4GeneratorInstall.actual_install]
  change Builtins.run (34909+fuel) (Arc4GeneratorCall.caller (call i) (.expressionStatement :: tail))=_
  rw [Arc4GeneratorCall.discard_call (call i) rfl]
  rfl

end CookieClicker.JavaScript.Arc4GeneratorInstalledFrame

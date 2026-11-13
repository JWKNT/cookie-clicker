import CookieClicker.JavaScriptRetainedArc4GeneratorCall
import CookieClicker.JavaScriptRetainedArc4Orbit

/-! The complete retained call exposes its saved generator state, appended
activation and unchanged caller data without expanding the byte traversal. -/
namespace CookieClicker.JavaScript.RetainedArc4GeneratorMemory
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem return_other (input : RetainedArc4GeneratorReturn.Inputs) (id : ObjectId) (object : JSObject)
    (different : input.receiver≠id)
    (read : checkedObject (RetainedArc4Generate.objectHeap input.source input.objects) id=.ok object) :
    checkedObject (RetainedArc4GeneratorLocals.heap input.source
      (RetainedArc4GeneratorReturn.secondObjects input) input.argument (RetainedArc4GeneratorReturn.values input)) id=.ok object := by
  simpa only [RetainedArc4Generate.objectHeap,RetainedArc4GeneratorLocals.heap,checkedObject,Heap.object?,
    RetainedArc4GeneratorReturn.secondObjects,RetainedArc4GeneratorReturn.firstObjects,
    RetainedArc4GeneratorReturn.receiver,RetainedArc4GeneratorReturn.objects,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,different,↓reduceIte] using read

theorem return_instance (input : RetainedArc4GeneratorReturn.Inputs) :
    checkedObject (RetainedArc4GeneratorLocals.heap input.source
      (RetainedArc4GeneratorReturn.secondObjects input) input.argument (RetainedArc4GeneratorReturn.values input)) input.receiver=
      .ok (Arc4Instance.withJ (Arc4Instance.withI input.instanceObject input.newF) input.newG) := by
  have raw := Arc4Initialized.checked_present input.instanceRead
  have bound := (Array.getElem?_eq_some_iff.mp raw).1
  change input.receiver<input.objects.size at bound
  simp [RetainedArc4GeneratorLocals.heap,checkedObject,Heap.object?,RetainedArc4GeneratorReturn.secondObjects,
    RetainedArc4GeneratorReturn.firstObjects,RetainedArc4GeneratorReturn.receiver,RetainedArc4GeneratorReturn.objects,bound]

theorem return_size (input : RetainedArc4GeneratorReturn.Inputs) :
    (RetainedArc4GeneratorReturn.secondObjects input).size=input.objects.size := by
  simp [RetainedArc4GeneratorReturn.secondObjects,RetainedArc4GeneratorReturn.firstObjects,RetainedArc4GeneratorReturn.objects]

def returnFrame (input : RetainedArc4GeneratorReturn.Inputs) (array : ObjectId)
    (frame : Arc4Bytes.Frame (RetainedArc4Generate.objectHeap input.source input.objects) array)
    (different : input.receiver≠array)
    (arrayDifferent : input.receiver≠frame.prototype.arrayId)
    (rootDifferent : input.receiver≠frame.prototype.rootId) :
    Arc4Bytes.Frame (RetainedArc4GeneratorLocals.heap input.source
      (RetainedArc4GeneratorReturn.secondObjects input) input.argument (RetainedArc4GeneratorReturn.values input)) array := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := return_other input _ _ different frame.present
  prototype := frame.prototype.transport rfl
    (return_other input _ _ arrayDifferent frame.prototype.arrayRead)
    (return_other input _ _ rootDifferent frame.prototype.rootRead)
  room := by change 2≤(RetainedArc4GeneratorReturn.secondObjects input).size; rw [return_size]; exact frame.room
  bound := by change array<(RetainedArc4GeneratorReturn.secondObjects input).size; rw [return_size]; exact frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }


def initialized (i : RetainedArc4GeneratorCall.Inputs) := RetainedArc4GeneratorCall.initialized i
def completed (i : RetainedArc4GeneratorCall.Inputs) := RetainedArc4GeneratorBodyComplete.completed (initialized i)
def resultInput (i : RetainedArc4GeneratorCall.Inputs) := RetainedArc4GeneratorBodyComplete.returnInputs (initialized i)
def objects (i : RetainedArc4GeneratorCall.Inputs) := RetainedArc4GeneratorReturn.secondObjects (resultInput i)
def value (i : RetainedArc4GeneratorCall.Inputs) := (resultInput i).accumulator

theorem source_same (i : RetainedArc4GeneratorCall.Inputs) : (resultInput i).source=i.source :=
  RetainedArc4GenerateRetained.finished_source (RetainedArc4GeneratorBodyComplete.initial (initialized i))
theorem array_same (i : RetainedArc4GeneratorCall.Inputs) : (resultInput i).array=i.array :=
  RetainedArc4GenerateRetained.finished_array (RetainedArc4GeneratorBodyComplete.initial (initialized i))
theorem argument_same (i : RetainedArc4GeneratorCall.Inputs) : (resultInput i).argument=i.objects.size :=
  RetainedArc4GenerateRetained.finished_argument (RetainedArc4GeneratorBodyComplete.initial (initialized i))

def appended (i : RetainedArc4GeneratorCall.Inputs) : LexicalEnvironment :=
  ⟨.declarative (RetainedArc4GeneratorLocals.locals i.objects.size
    (RetainedArc4GeneratorReturn.values (resultInput i))),
    some (RetainedArc4GeneratorLocals.constructorIndex i.source)⟩

theorem finish_form (i : RetainedArc4GeneratorCall.Inputs) (tail : List Frame) :
    RetainedArc4GeneratorCall.finish i tail=
      {RetainedArc4GeneratorLocals.base i.source with
       heap := ⟨objects i,(RetainedArc4GeneratorLocals.constructorEnvironments i.source).push (appended i)⟩
       context := (RetainedArc4GeneratorCall.caller i tail).context
       control := .expressionResult (.value (.number (value i))),continuation := tail} := by
  change RetainedArc4GeneratorReturn.finish (resultInput i) _ _ = _
  simp only [RetainedArc4GeneratorReturn.finish,RetainedArc4GeneratorReturn.source,
    RetainedArc4GeneratorReturn.argument,RetainedArc4GeneratorReturn.accumulator,
    RetainedArc4GeneratorLocals.heap,source_same,argument_same]
  rfl

theorem completed_other (i : RetainedArc4GeneratorCall.Inputs) (id : ObjectId) (object : JSObject)
    (different : i.array≠id)
    (read : checkedObject (RetainedArc4Generate.objectHeap i.source i.objects) id=.ok object) :
    checkedObject (RetainedArc4Generate.objectHeap (resultInput i).source (resultInput i).objects) id=.ok object :=
  RetainedArc4GenerateRetained.checked_other (RetainedArc4GeneratorBodyComplete.initial (initialized i)) id object
    different (HeapExtension.checked_object (RetainedArc4GeneratorCall.extension i) id object read)

theorem final_other (i : RetainedArc4GeneratorCall.Inputs) (id : ObjectId) (object : JSObject)
    (differentArray : i.array≠id) (differentReceiver : i.receiver≠id)
    (read : checkedObject (RetainedArc4Generate.objectHeap i.source i.objects) id=.ok object) :
    checkedObject ⟨objects i,#[]⟩ id=.ok object :=
  return_other (resultInput i) id object differentReceiver (completed_other i id object differentArray read)

theorem traversal_array_prototype (count : Nat) (stage : RetainedArc4GenerateComplete.Stage)
    (bound : count≤stage.cursor.remaining) :
    (RetainedArc4GenerateComplete.traverse count stage bound).cursor.arrayFrame.prototype.arrayId=
      stage.cursor.arrayFrame.prototype.arrayId := by
  induction count generalizing stage with
  | zero => rfl
  | succ count ih =>
    simp only [RetainedArc4GenerateComplete.traverse]
    rw [ih]
    rfl

theorem traversal_root_prototype (count : Nat) (stage : RetainedArc4GenerateComplete.Stage)
    (bound : count≤stage.cursor.remaining) :
    (RetainedArc4GenerateComplete.traverse count stage bound).cursor.arrayFrame.prototype.rootId=
      stage.cursor.arrayFrame.prototype.rootId := by
  induction count generalizing stage with
  | zero => rfl
  | succ count ih =>
    simp only [RetainedArc4GenerateComplete.traverse]
    rw [ih]
    rfl

theorem completed_array_prototype (i : RetainedArc4GeneratorCall.Inputs) :
    (completed i).cursor.arrayFrame.prototype.arrayId=i.arrayFrame.prototype.arrayId :=
  traversal_array_prototype _ _ _

theorem completed_root_prototype (i : RetainedArc4GeneratorCall.Inputs) :
    (completed i).cursor.arrayFrame.prototype.rootId=i.arrayFrame.prototype.rootId :=
  traversal_root_prototype _ _ _

def generatedFrame (i : RetainedArc4GeneratorCall.Inputs) :
    Arc4Bytes.Frame (RetainedArc4Generate.objectHeap (resultInput i).source (resultInput i).objects) i.array := {
  object := (completed i).cursor.arrayFrame.object
  length := (completed i).cursor.arrayFrame.length
  bytes := (completed i).cursor.arrayFrame.bytes
  shape := (completed i).cursor.arrayFrame.shape
  present := by rw [←array_same i]; exact (completed i).cursor.arrayFrame.present
  prototype := (completed i).cursor.arrayFrame.prototype
  room := (completed i).cursor.arrayFrame.room
  bound := by rw [←array_same i]; exact (completed i).cursor.arrayFrame.bound
  arrayDifferent := by rw [←array_same i]; exact (completed i).cursor.arrayFrame.arrayDifferent
  rootDifferent := by rw [←array_same i]; exact (completed i).cursor.arrayFrame.rootDifferent }

theorem receiver_array (i : RetainedArc4GeneratorCall.Inputs) : i.receiver≠i.array :=
  Ne.symm (RetainedArc4GeneratorBodyComplete.instance_different (initialized i))

def stateFrame (i : RetainedArc4GeneratorCall.Inputs)
    (arrayDifferent : i.receiver≠i.arrayFrame.prototype.arrayId)
    (rootDifferent : i.receiver≠i.arrayFrame.prototype.rootId) : Arc4Bytes.Frame ⟨objects i,#[]⟩ i.array :=
  Arc4Bytes.transport
    (returnFrame (resultInput i) i.array (generatedFrame i) (receiver_array i)
      (by change i.receiver≠(completed i).cursor.arrayFrame.prototype.arrayId
          rw [completed_array_prototype];exact arrayDifferent)
      (by change i.receiver≠(completed i).cursor.arrayFrame.prototype.rootId
          rw [completed_root_prototype];exact rootDifferent)) rfl

theorem state_full (i : RetainedArc4GeneratorCall.Inputs)
    (arrayDifferent : i.receiver≠i.arrayFrame.prototype.arrayId)
    (rootDifferent : i.receiver≠i.arrayFrame.prototype.rootId) :
    (stateFrame i arrayDifferent rootDifferent).length=256 := (completed i).cursor.full

theorem state_array_prototype (i : RetainedArc4GeneratorCall.Inputs)
    (arrayDifferent : i.receiver≠i.arrayFrame.prototype.arrayId)
    (rootDifferent : i.receiver≠i.arrayFrame.prototype.rootId) :
    (stateFrame i arrayDifferent rootDifferent).prototype.arrayId=i.arrayFrame.prototype.arrayId :=
  completed_array_prototype i

theorem state_root_prototype (i : RetainedArc4GeneratorCall.Inputs)
    (arrayDifferent : i.receiver≠i.arrayFrame.prototype.arrayId)
    (rootDifferent : i.receiver≠i.arrayFrame.prototype.rootId) :
    (stateFrame i arrayDifferent rootDifferent).prototype.rootId=i.arrayFrame.prototype.rootId :=
  completed_root_prototype i

end CookieClicker.JavaScript.RetainedArc4GeneratorMemory

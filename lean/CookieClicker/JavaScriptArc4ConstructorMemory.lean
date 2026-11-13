import CookieClicker.JavaScriptArc4ConstructorComplete

/-! The completed source constructor retains every original lexical environment.
The final state array and instance fields are the actual discarded-generator result. -/
namespace CookieClicker.JavaScript.Arc4ConstructorMemory
open Arc4ConstructorSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

abbrev Final (i : Inputs) := lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none

def installed (i : Inputs) (missing : Final i) : Arc4GeneratorInstalledFrame.Inputs := Arc4ConstructorFinalFrame.frame i missing
def call (i : Inputs) (missing : Final i) : Arc4GeneratorCall.Inputs := Arc4GeneratorInstalledFrame.call (installed i missing)
def initialized (i : Inputs) (missing : Final i) : Arc4GeneratorInitialize.Inputs := Arc4GeneratorCall.initialized (call i missing)
def generated (i : Inputs) (missing : Final i) : Arc4GenerateComplete.Stage := Arc4GeneratorBodyComplete.completed (initialized i missing)
def resultInput (i : Inputs) (missing : Final i) : Arc4GeneratorReturn.Inputs := Arc4GeneratorBodyComplete.returnInputs (initialized i missing)
def resultHeap (i : Inputs) (missing : Final i) : Heap :=
  Arc4GeneratorLocals.heap (resultInput i missing).source
    (Arc4GeneratorReturn.secondObjects (resultInput i missing))
    (resultInput i missing).argument (Arc4GeneratorReturn.values (resultInput i missing))


theorem returned_heap (i : Inputs) (missing : Final i) :
    (Arc4ConstructorComplete.returned i missing).heap=resultHeap i missing := by
  simp only [Arc4ConstructorComplete.returned,Arc4ConstructorFinalFrame.finish,
    Arc4GeneratorInstalledFrame.finish,Arc4GeneratorCall.finish,Arc4GeneratorBodyComplete.finish,
    Arc4GeneratorReturn.finish,Arc4GeneratorReturn.source,Arc4GeneratorReturn.argument,resultHeap,resultInput,initialized,call,installed]

theorem body_result_source (input : Arc4GeneratorInitialize.Inputs) :
    (Arc4GeneratorBodyComplete.returnInputs input).source=input.source :=
  Arc4GenerateRetained.finished_source (Arc4GeneratorBodyComplete.initial input)

theorem installed_call_source (input : Arc4GeneratorInstalledFrame.Inputs) :
    (Arc4GeneratorCall.initialized (Arc4GeneratorInstalledFrame.call input)).source=input.install.source := rfl

theorem result_source (i : Inputs) (missing : Final i) :
    (resultInput i missing).source=(initialized i missing).source :=
  body_result_source (initialized i missing)

theorem constructor_source (i : Inputs) (missing : Final i) :
    (initialized i missing).source.constructor=(setup i).source := by
  have first : (initialized i missing).source=(installed i missing).install.source :=
    installed_call_source (installed i missing)
  rw [first]
  exact (Arc4ConstructorFinalFrame.final_fields i).1.trans (Arc4ConstructorInstance.loop_source i)

theorem result_base (i : Inputs) (missing : Final i) :
    Arc4GeneratorLocals.base (resultInput i missing).source=allocatedBase i := by
  rw [result_source]
  unfold Arc4GeneratorLocals.base
  rw [constructor_source]
  rfl

theorem original_environment (i : Inputs) (missing : Final i) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (Arc4Locals.base i.source).heap id=.ok environment) :
    checkedEnvironment (Arc4ConstructorComplete.returned i missing).heap id=.ok environment := by
  rw [returned_heap]
  unfold resultHeap Arc4GeneratorLocals.heap Arc4GeneratorLocals.constructorEnvironments
  have readBase : checkedEnvironment (Arc4GeneratorLocals.base (resultInput i missing).source).heap id=.ok environment := by
    rw [result_base]
    exact read
  let before := Arc4GeneratorLocals.base (resultInput i missing).source
  let added : LexicalEnvironment := ⟨.declarative
    (Arc4Locals.locals (resultInput i missing).source.constructorArgument
      (resultInput i missing).source.constructorValues),
    some (Arc4GeneratorLocals.libraryIndex (resultInput i missing).source)⟩
  let objects := Arc4GeneratorReturn.secondObjects (resultInput i missing)
  let last : LexicalEnvironment := ⟨.declarative
    (Arc4GeneratorLocals.locals (resultInput i missing).argument
      (Arc4GeneratorReturn.values (resultInput i missing))),
    some (Arc4GeneratorLocals.constructorIndex (resultInput i missing).source)⟩
  exact EnvironmentAppend.checked_old (EnvironmentAppend.append before.heap objects added)
    objects last environment id
    (EnvironmentAppend.checked_old before.heap objects added environment id readBase)

theorem environment_size (i : Inputs) (missing : Final i) :
    (Arc4ConstructorComplete.returned i missing).heap.environments.size=
      (Arc4Locals.base i.source).heap.environments.size+2 := by
  rw [returned_heap]
  unfold resultHeap
  rw [Arc4GeneratorLocals.environment_size,result_base]
  rfl

theorem receiver_fresh (i : Inputs) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) : receiver i≠id := by
  have bound := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present read)).1
  exact Nat.ne_of_gt bound

theorem array_fresh (i : Inputs) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    (Arc4ConstructorPrefix.loops i).array≠id := by
  rw [Arc4ConstructorInstance.loop_array,(Arc4Initialized.sizes (setup i)).2.2.1]
  have bound := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present read)).1
  change (objects i).size≠id
  simp only [objects,Array.size_push,allocatedBase,Arc4ConstructorEntry.withInstance]
  change (Arc4Locals.base i.source).heap.objects.size+1+1≠id
  omega

theorem loop_original (i : Inputs) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    checkedObject (Arc4Schedule.objectHeap (Arc4ConstructorPrefix.loops i).source
      (Arc4ConstructorPrefix.loops i).objects) id=.ok object := by
  have allocated := HeapExtension.checked_object (extension i) id object read
  have initialized := Arc4Initialized.retained_checked (setup i) id object (receiver_fresh i id object read) allocated
  unfold Arc4ConstructorPrefix.loops
  split
  · exact HeapExtension.checked_object (Arc4EmptyKeyFrame.extension (setup i)) id object initialized
  · exact initialized

theorem scheduled_original (i : Inputs) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    checkedObject (Arc4Schedule.objectHeap (Arc4ConstructorFinalFrame.completed i).cursor.source
      (Arc4ConstructorFinalFrame.completed i).cursor.objects) id=.ok object := by
  simp only [checkedObject,Heap.object?,Arc4Schedule.objectHeap]
  unfold Arc4ConstructorFinalFrame.completed Arc4ConstructorLoops.schedule Arc4ScheduleComplete.finished
  rw [Arc4ConstructorRetained.schedule_other _ (Arc4ConstructorFinalFrame.scheduleInitial i) _ _ (array_fresh i id object read)]
  change (match (Arc4ConstructorFinalFrame.identity i).cursor.objects[id]? with
    | some value => (Except.ok value : Checked JSObject)
    | none => .error (.fault (.missingObject id)))=_
  unfold Arc4ConstructorFinalFrame.identity Arc4ConstructorLoops.identity
  rw [Arc4IdentityRetained.finished_other (Arc4ConstructorFinalFrame.initial i) _ (array_fresh i id object read)]
  exact loop_original i id object read

theorem installed_original (i : Inputs) (missing : Final i) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    checkedObject (Arc4GeneratorInstalledFrame.heap (installed i missing)) id=.ok object :=
  Arc4GeneratorInstalledFrame.other_read (installed i missing) id object (receiver_fresh i id object read)
    (scheduled_original i id object read)

theorem initialized_original (i : Inputs) (missing : Final i) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    checkedObject (Arc4Generate.objectHeap (initialized i missing).source (initialized i missing).objects) id=.ok object :=
  HeapExtension.checked_object (Arc4GeneratorCall.extension (call i missing)) id object (installed_original i missing id object read)

theorem initialized_array (i : Inputs) (missing : Final i) :
    (initialized i missing).array=(Arc4ConstructorPrefix.loops i).array := by
  change (Arc4ConstructorFinalFrame.completed i).cursor.array=_
  exact (Arc4ConstructorFinalFrame.final_fields i).2.1

theorem generated_original (i : Inputs) (missing : Final i) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    checkedObject (Arc4Generate.objectHeap (generated i missing).cursor.source (generated i missing).cursor.objects) id=.ok object :=
  Arc4GenerateRetained.checked_other (Arc4GeneratorBodyComplete.initial (initialized i missing)) id object
    (by change (initialized i missing).array≠id; rw [initialized_array]; exact array_fresh i id object read)
    (initialized_original i missing id object read)

theorem return_other (input : Arc4GeneratorReturn.Inputs) (id : ObjectId) (object : JSObject)
    (different : input.receiver≠id)
    (read : checkedObject (Arc4Generate.objectHeap input.source input.objects) id=.ok object) :
    checkedObject (Arc4GeneratorLocals.heap input.source
      (Arc4GeneratorReturn.secondObjects input) input.argument (Arc4GeneratorReturn.values input)) id=.ok object := by
  simpa only [Arc4Generate.objectHeap,Arc4GeneratorLocals.heap,checkedObject,Heap.object?,
    Arc4GeneratorReturn.secondObjects,Arc4GeneratorReturn.firstObjects,
    Arc4GeneratorReturn.receiver,Arc4GeneratorReturn.objects,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,different,↓reduceIte] using read

theorem return_instance (input : Arc4GeneratorReturn.Inputs) :
    checkedObject (Arc4GeneratorLocals.heap input.source
      (Arc4GeneratorReturn.secondObjects input) input.argument (Arc4GeneratorReturn.values input)) input.receiver=
      .ok (Arc4Instance.withJ (Arc4Instance.withI input.instanceObject input.newF) input.newG) := by
  have raw := Arc4Initialized.checked_present input.instanceRead
  have bound := (Array.getElem?_eq_some_iff.mp raw).1
  change input.receiver<input.objects.size at bound
  simp [Arc4GeneratorLocals.heap,checkedObject,Heap.object?,Arc4GeneratorReturn.secondObjects,
    Arc4GeneratorReturn.firstObjects,Arc4GeneratorReturn.receiver,Arc4GeneratorReturn.objects,bound]

theorem return_size (input : Arc4GeneratorReturn.Inputs) :
    (Arc4GeneratorReturn.secondObjects input).size=input.objects.size := by
  simp [Arc4GeneratorReturn.secondObjects,Arc4GeneratorReturn.firstObjects,Arc4GeneratorReturn.objects]

theorem body_objects (input : Arc4GeneratorInitialize.Inputs) :
    (Arc4GeneratorBodyComplete.returnInputs input).objects=(Arc4GeneratorBodyComplete.completed input).cursor.objects := rfl

theorem body_source (input : Arc4GeneratorInitialize.Inputs) :
    (Arc4GeneratorBodyComplete.returnInputs input).source=(Arc4GeneratorBodyComplete.completed input).cursor.source := rfl

theorem body_receiver (input : Arc4GeneratorInitialize.Inputs) :
    (Arc4GeneratorBodyComplete.returnInputs input).receiver=input.receiver := rfl

theorem installed_call_receiver (input : Arc4GeneratorInstalledFrame.Inputs) :
    (Arc4GeneratorCall.initialized (Arc4GeneratorInstalledFrame.call input)).receiver=input.install.receiver := rfl

theorem result_objects (i : Inputs) (missing : Final i) :
    (resultInput i missing).objects=(generated i missing).cursor.objects := body_objects (initialized i missing)

theorem result_generated_source (i : Inputs) (missing : Final i) :
    (resultInput i missing).source=(generated i missing).cursor.source := body_source (initialized i missing)

theorem result_receiver (i : Inputs) (missing : Final i) :
    (resultInput i missing).receiver=receiver i := by
  have h := body_receiver (initialized i missing)
  have h2 := installed_call_receiver (installed i missing)
  exact h.trans h2

theorem original_object (i : Inputs) (missing : Final i) (id : ObjectId) (object : JSObject)
    (read : checkedObject (Arc4Locals.base i.source).heap id=.ok object) :
    checkedObject (Arc4ConstructorComplete.returned i missing).heap id=.ok object := by
  rw [returned_heap]
  apply return_other (resultInput i missing) id object
  · rw [result_receiver]; exact receiver_fresh i id object read
  · rw [result_objects,result_generated_source]
    exact generated_original i missing id object read

theorem extension (i : Inputs) (missing : Final i) :
    HeapExtension.Extends (Arc4Locals.base i.source).heap (Arc4ConstructorComplete.returned i missing).heap := by
  constructor
  · by_cases empty : (Arc4Locals.base i.source).heap.objects.size=0
    · rw [empty]; omega
    · let id := (Arc4Locals.base i.source).heap.objects.size-1
      have bounded : id<(Arc4Locals.base i.source).heap.objects.size := by unfold id; omega
      let object := (Arc4Locals.base i.source).heap.objects[id]
      have found : checkedObject (Arc4Locals.base i.source).heap id=.ok object := by
        simp [checkedObject,Heap.object?,Array.getElem?_eq_getElem,bounded,object]
      have after := original_object i missing id object found
      have later := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present after)).1
      unfold id at later
      omega
  · intro id object found
    apply Arc4Initialized.checked_present
    apply original_object i missing id object
    simp [checkedObject,found]

def instanceObject (i : Inputs) (missing : Final i) :=
  Arc4Instance.withJ (Arc4Instance.withI (resultInput i missing).instanceObject (resultInput i missing).newF)
    (resultInput i missing).newG

theorem instance_read (i : Inputs) (missing : Final i) :
    checkedObject (Arc4ConstructorComplete.returned i missing).heap (receiver i)=.ok (instanceObject i missing) := by
  rw [returned_heap]
  change checkedObject (resultHeap i missing) (receiver i)=_
  rw [←result_receiver i missing]
  exact return_instance (resultInput i missing)

theorem instance_shape (i : Inputs) (missing : Final i) :
    Arc4Instance.Shape (instanceObject i missing) (resultInput i missing).newF (resultInput i missing).newG
      (resultInput i missing).array :=
  Arc4Instance.shape_j (Arc4Instance.shape_i (resultInput i missing).instanceShape _) _

theorem final_other (i : Inputs) (missing : Final i) (id : ObjectId) (object : JSObject)
    (different : receiver i≠id)
    (read : checkedObject (Arc4Generate.objectHeap (generated i missing).cursor.source
      (generated i missing).cursor.objects) id=.ok object) :
    checkedObject (Arc4ConstructorComplete.returned i missing).heap id=.ok object := by
  rw [returned_heap]
  apply return_other (resultInput i missing) id object
  · rw [result_receiver]; exact different
  · rw [result_objects,result_generated_source]
    exact read

theorem receiver_array (i : Inputs) (missing : Final i) : receiver i≠(generated i missing).cursor.array := by
  have same := Arc4GenerateRetained.finished_array (Arc4GeneratorBodyComplete.initial (initialized i missing))
  change (generated i missing).cursor.array=(initialized i missing).array at same
  rw [same,initialized_array,Arc4ConstructorInstance.loop_array,(Arc4Initialized.sizes (setup i)).2.2.1]
  change receiver i≠(objects i).size
  simp only [receiver,objects,allocatedBase,Arc4ConstructorEntry.withInstance,Array.size_push]
  omega

theorem receiver_array_prototype (i : Inputs) (missing : Final i) :
    receiver i≠(generated i missing).cursor.arrayFrame.prototype.arrayId := by
  intro same
  have read := (generated i missing).cursor.arrayFrame.prototype.arrayRead
  have own := (resultInput i missing).instanceRead
  rw [result_generated_source,result_objects,result_receiver] at own
  rw [←same] at read
  have kinds := congrArg JSObject.kind (Except.ok.inj (own.symm.trans read))
  rw [(resultInput i missing).instanceShape.kind,(generated i missing).cursor.arrayFrame.prototype.arrayKind] at kinds
  contradiction

theorem receiver_root_prototype (i : Inputs) (missing : Final i) :
    receiver i≠(generated i missing).cursor.arrayFrame.prototype.rootId := by
  intro same
  have read := (generated i missing).cursor.arrayFrame.prototype.rootRead
  have own := (resultInput i missing).instanceRead
  rw [result_generated_source,result_objects,result_receiver] at own
  rw [←same] at read
  have parents := congrArg JSObject.prototype (Except.ok.inj (own.symm.trans read))
  have parent : (resultInput i missing).instanceObject.prototype=some i.prototype := rfl
  rw [parent,(generated i missing).cursor.arrayFrame.prototype.rootParent] at parents
  contradiction

def returnFrame (input : Arc4GeneratorReturn.Inputs) (array : ObjectId)
    (frame : Arc4Bytes.Frame (Arc4Generate.objectHeap input.source input.objects) array)
    (different : input.receiver≠array)
    (arrayDifferent : input.receiver≠frame.prototype.arrayId)
    (rootDifferent : input.receiver≠frame.prototype.rootId) :
    Arc4Bytes.Frame (Arc4GeneratorLocals.heap input.source
      (Arc4GeneratorReturn.secondObjects input) input.argument (Arc4GeneratorReturn.values input)) array := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := return_other input _ _ different frame.present
  prototype := frame.prototype.transport rfl
    (return_other input _ _ arrayDifferent frame.prototype.arrayRead)
    (return_other input _ _ rootDifferent frame.prototype.rootRead)
  room := by change 2≤(Arc4GeneratorReturn.secondObjects input).size; rw [return_size]; exact frame.room
  bound := by change array<(Arc4GeneratorReturn.secondObjects input).size; rw [return_size]; exact frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

def generatedFrame (i : Inputs) (missing : Final i) :
    Arc4Bytes.Frame (Arc4Generate.objectHeap (resultInput i missing).source
      (resultInput i missing).objects) (generated i missing).cursor.array :=
  Arc4Bytes.transport
    (before := Arc4Generate.objectHeap (generated i missing).cursor.source (generated i missing).cursor.objects)
    (after := Arc4Generate.objectHeap (resultInput i missing).source (resultInput i missing).objects)
    (array := (generated i missing).cursor.array)
    (generated i missing).cursor.arrayFrame (result_objects i missing)

theorem transport_array_id {before after : Heap} {array : ObjectId}
    (frame : Arc4Bytes.Frame before array) (same : after.objects=before.objects) :
    (Arc4Bytes.transport frame same).prototype.arrayId=frame.prototype.arrayId := rfl

theorem transport_root_id {before after : Heap} {array : ObjectId}
    (frame : Arc4Bytes.Frame before array) (same : after.objects=before.objects) :
    (Arc4Bytes.transport frame same).prototype.rootId=frame.prototype.rootId := rfl

theorem transport_length {before after : Heap} {array : ObjectId}
    (frame : Arc4Bytes.Frame before array) (same : after.objects=before.objects) :
    (Arc4Bytes.transport frame same).length=frame.length := rfl

theorem generated_array_id (i : Inputs) (missing : Final i) :
    (generatedFrame i missing).prototype.arrayId=(generated i missing).cursor.arrayFrame.prototype.arrayId :=
  transport_array_id _ _

theorem generated_root_id (i : Inputs) (missing : Final i) :
    (generatedFrame i missing).prototype.rootId=(generated i missing).cursor.arrayFrame.prototype.rootId :=
  transport_root_id _ _

theorem generated_length (i : Inputs) (missing : Final i) :
    (generatedFrame i missing).length=(generated i missing).cursor.arrayFrame.length :=
  transport_length _ _

theorem return_length (input : Arc4GeneratorReturn.Inputs) (array : ObjectId)
    (frame : Arc4Bytes.Frame (Arc4Generate.objectHeap input.source input.objects) array)
    (different : input.receiver≠array)
    (arrayDifferent : input.receiver≠frame.prototype.arrayId)
    (rootDifferent : input.receiver≠frame.prototype.rootId) :
    (returnFrame input array frame different arrayDifferent rootDifferent).length=frame.length := rfl

attribute [local irreducible] generatedFrame returnFrame

def stateFrame (i : Inputs) (missing : Final i) :
    Arc4Bytes.Frame (Arc4ConstructorComplete.returned i missing).heap (generated i missing).cursor.array :=
  Arc4Bytes.transport
    (before := resultHeap i missing) (after := (Arc4ConstructorComplete.returned i missing).heap)
    (array := (generated i missing).cursor.array)
    (returnFrame (resultInput i missing) (generated i missing).cursor.array (generatedFrame i missing)
    (by rw [result_receiver]; exact receiver_array i missing)
    (by rw [result_receiver,generated_array_id]; exact receiver_array_prototype i missing)
    (by rw [result_receiver,generated_root_id]; exact receiver_root_prototype i missing))
      (congrArg Heap.objects (returned_heap i missing))

theorem state_full (i : Inputs) (missing : Final i) : (stateFrame i missing).length=256 := by
  exact (transport_length _ _).trans ((return_length _ _ _ _ _ _).trans
    ((generated_length i missing).trans (generated i missing).cursor.full))

end CookieClicker.JavaScript.Arc4ConstructorMemory

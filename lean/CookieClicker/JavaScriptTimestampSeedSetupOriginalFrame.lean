import CookieClicker.JavaScriptSeedrandomFrameTransport

/-! Original native library objects and environments are retained through
timestamp mixing, the source constructor, and the q assignment. -/
namespace CookieClicker.JavaScript.TimestampSeedSetupOriginalFrame
open TimestampSeedEntropyFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

def origin (i : Inputs) := i.constructor.prelude.mixing.globals.base
def after (i : Inputs) := TimestampSeedEntropyEntry.atReturn i.constructor

theorem local_different (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (origin i).heap id=.ok environment) :
    TimestampSeedEntropyEntry.localScope i.constructor≠id := by
  have bound := (Array.getElem?_eq_some_iff.mp (SeedrandomFrameTransport.raw read)).1
  exact Nat.ne_of_gt bound

theorem before_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (origin i).heap id=.ok environment) :
    checkedEnvironment (TimestampSeedArc4Prelude.beforeCall i.constructor.prelude).heap id=.ok environment := by
  change checkedEnvironment (BindingWrite.changedHeap (TimestampSeedMixing.returned i.constructor.prelude.mixing).heap
    (TimestampSeedReturnedEnvironment.localIndex i.constructor.prelude.mixing)
    (TimestampSeedReturnedEnvironment.localBindings i.constructor.prelude.mixing)
    (some i.constructor.prelude.mixing.globals.scope) "p" (.string (TimestampSeedMixing.text i.constructor.prelude.mixing))) id=_
  have different : TimestampSeedReturnedEnvironment.localIndex i.constructor.prelude.mixing≠id := local_different i id environment read
  rw [BindingWrite.changed_checked_other _ _ _ _ _ _ _ different]
  exact TimestampSeedReturnedEnvironment.original_environment i.constructor.prelude.mixing id environment read

theorem original_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (origin i).heap id=.ok environment) :
    checkedEnvironment (after i).heap id=.ok environment := by
  change checkedEnvironment (BindingWrite.changedHeap (TimestampSeedEntropyEntry.base i.constructor).heap
    (TimestampSeedEntropyEntry.localScope i.constructor) (TimestampSeedEntropyEntry.originalLocals i.constructor)
    (some (TimestampSeedEntropyEntry.scope i.constructor)) "q" (.object (TimestampSeedEntropyEntry.receiverId i.constructor))) id=_
  rw [BindingWrite.changed_checked_other _ _ _ _ _ _ _ (local_different i id environment read)]
  exact Arc4ConstructorMemory.original_environment (TimestampSeedArc4Complete.constructorFrame i.constructor)
    (TimestampSeedArc4Complete.missing_g i.constructor) id environment (before_environment i id environment read)

theorem environment_size (i : Inputs) : (after i).heap.environments.size=(origin i).heap.environments.size+6 := by
  have first : (TimestampSeedEntropyEntry.base i.constructor).heap.environments.size=
      (TimestampSeedArc4Prelude.beforeCall i.constructor.prelude).heap.environments.size+2 :=
    Arc4ConstructorMemory.environment_size (TimestampSeedArc4Complete.constructorFrame i.constructor)
      (TimestampSeedArc4Complete.missing_g i.constructor)
  have second : (TimestampSeedArc4Prelude.beforeCall i.constructor.prelude).heap.environments.size=
      (origin i).heap.environments.size+4 := TimestampSeedArc4Prelude.environment_size i.constructor.prelude
  change (BindingWrite.changedHeap (TimestampSeedEntropyEntry.base i.constructor).heap
    (TimestampSeedEntropyEntry.localScope i.constructor) (TimestampSeedEntropyEntry.originalLocals i.constructor)
    (some (TimestampSeedEntropyEntry.scope i.constructor)) "q" (.object (TimestampSeedEntropyEntry.receiverId i.constructor))).environments.size=_
  simp only [BindingWrite.changedHeap,Array.size_set!]
  rw [first,second]

def environments (i : Inputs) : SeedrandomFrameTransport.Environments (origin i).heap (after i).heap :=
  ⟨by rw [environment_size]; omega,original_environment i⟩

theorem extension (i : Inputs) : HeapExtension.Extends (origin i).heap (after i).heap :=
  HeapExtension.trans (TimestampSeedArc4Frame.extension i.constructor.prelude)
    (HeapExtension.trans (Arc4ConstructorMemory.extension (TimestampSeedArc4Complete.constructorFrame i.constructor)
      (TimestampSeedArc4Complete.missing_g i.constructor))
      (HeapExtension.same_objects (before := (TimestampSeedEntropyEntry.base i.constructor).heap)
        (after := (after i).heap) rfl))

theorem original_binding (i : Inputs) (id : EnvId) (name : String) (value : Value)
    (read : readBinding (origin i).heap id name=.ok value) :
    readBinding (after i).heap id name=.ok value :=
  SeedrandomSetupLocals.read_transport id name value (original_environment i) read

theorem global_same (i : Inputs) : (after i).globalObject=(origin i).globalObject := by
  change (Arc4GeneratorLocals.base (Arc4ConstructorMemory.resultInput
    (TimestampSeedArc4Complete.constructorFrame i.constructor) (TimestampSeedArc4Complete.missing_g i.constructor)).source).globalObject=_
  rw [Arc4ConstructorMemory.result_base]
  rfl

theorem exclusions_same (i : Inputs) : (after i).objectEnvironmentExclusions=(origin i).objectEnvironmentExclusions := by
  change (Arc4GeneratorLocals.base (Arc4ConstructorMemory.resultInput
    (TimestampSeedArc4Complete.constructorFrame i.constructor) (TimestampSeedArc4Complete.missing_g i.constructor)).source).objectEnvironmentExclusions=_
  rw [Arc4ConstructorMemory.result_base]
  rfl

theorem string_same (i : Inputs) : (after i).stringPrototype=(origin i).stringPrototype := by
  change (Arc4GeneratorLocals.base (Arc4ConstructorMemory.resultInput
    (TimestampSeedArc4Complete.constructorFrame i.constructor) (TimestampSeedArc4Complete.missing_g i.constructor)).source).stringPrototype=_
  rw [Arc4ConstructorMemory.result_base]
  rfl


theorem elapsed_same (i : Inputs) : (after i).elapsed=(origin i).elapsed := by
  change (Arc4GeneratorLocals.base (Arc4ConstructorMemory.resultInput
    (TimestampSeedArc4Complete.constructorFrame i.constructor) (TimestampSeedArc4Complete.missing_g i.constructor)).source).elapsed=_
  rw [Arc4ConstructorMemory.result_base]
  rfl

theorem free_draws_same (i : Inputs) : (after i).freeDrawCount=(origin i).freeDrawCount := by
  change (Arc4GeneratorLocals.base (Arc4ConstructorMemory.resultInput
    (TimestampSeedArc4Complete.constructorFrame i.constructor) (TimestampSeedArc4Complete.missing_g i.constructor)).source).freeDrawCount=_
  rw [Arc4ConstructorMemory.result_base]
  rfl

def stateArray (i : Inputs) := (Arc4ConstructorMemory.generated
  (TimestampSeedArc4Complete.constructorFrame (TimestampSeedEntropyFrame.constructor i)) (TimestampSeedArc4Complete.missing_g (TimestampSeedEntropyFrame.constructor i))).cursor.array

def globals (i : Inputs) : MixkeyToString.Inputs :=
  SeedrandomFrameTransport.globals i.constructor.prelude.mixing.globals (after i)
    (stateArray i) (extension i) (environments i) (global_same i) (exclusions_same i)

theorem body_array (i : Arc4GeneratorInitialize.Inputs) :
    (Arc4GeneratorBodyComplete.returnInputs i).array=(Arc4GeneratorBodyComplete.completed i).cursor.array := rfl

theorem result_array (i : Arc4ConstructorSetup.Inputs) (missing : Arc4ConstructorMemory.Final i) :
    (Arc4ConstructorMemory.resultInput i missing).array=(Arc4ConstructorMemory.generated i missing).cursor.array :=
  body_array (Arc4ConstructorMemory.initialized i missing)

attribute [local irreducible] Arc4ConstructorMemory.resultInput Arc4ConstructorMemory.generated

theorem entry_array (i : Inputs) : (TimestampSeedEntropyFrame.entry i).array=stateArray i := by
  change (Arc4ConstructorMemory.resultInput (TimestampSeedArc4Complete.constructorFrame (TimestampSeedEntropyFrame.constructor i))
    (TimestampSeedArc4Complete.missing_g (TimestampSeedEntropyFrame.constructor i))).array=stateArray i
  unfold stateArray
  exact result_array (TimestampSeedArc4Complete.constructorFrame (TimestampSeedEntropyFrame.constructor i)) (TimestampSeedArc4Complete.missing_g (TimestampSeedEntropyFrame.constructor i))

def state (i : Inputs) : Arc4Bytes.Frame (after i).heap (stateArray i) :=
  Arc4Bytes.transport
    (before := (Arc4ConstructorComplete.returned (TimestampSeedArc4Complete.constructorFrame (TimestampSeedEntropyFrame.constructor i))
      (TimestampSeedArc4Complete.missing_g (TimestampSeedEntropyFrame.constructor i))).heap)
    (after := (after i).heap) (array := stateArray i)
    (Arc4ConstructorMemory.stateFrame (TimestampSeedArc4Complete.constructorFrame (TimestampSeedEntropyFrame.constructor i))
      (TimestampSeedArc4Complete.missing_g (TimestampSeedEntropyFrame.constructor i))) rfl

theorem state_full (i : Inputs) : (state i).length=256 :=
  (Arc4ConstructorMemory.transport_length _ _).trans
    (Arc4ConstructorMemory.state_full (TimestampSeedArc4Complete.constructorFrame (TimestampSeedEntropyFrame.constructor i))
      (TimestampSeedArc4Complete.missing_g (TimestampSeedEntropyFrame.constructor i)))

def data (i : Inputs) : MixkeyToString.ArrayData (globals i) := {
  object := (state i).object, length := (state i).length, bytes := (state i).bytes, shape := (state i).shape
  present := (state i).present, prototype := (state i).prototype, room := (state i).room }

def string (i : Inputs) : SeedrandomEntropyString.Inputs := {
  entry := TimestampSeedEntropyFrame.entry i
  globals := globals i
  baseSame := rfl, scopeSame := rfl, calleeSame := rfl, arraySame := (entry_array i).symm
  data := data i
  full := state_full i
  object := i.constructor.prelude.mixing.helperObject
  present := HeapExtension.checked_object (extension i) _ _ i.constructor.prelude.mixing.helperPresent
  kind := i.constructor.prelude.mixing.helperKind }

end CookieClicker.JavaScript.TimestampSeedSetupOriginalFrame

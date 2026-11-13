import CookieClicker.JavaScriptTimestampSeedSetupOriginalFrame

/-! Canonical setup inputs are built from original library and entropy-pool
frames. No post-constructor helper or mixing frame is supplied. -/
namespace CookieClicker.JavaScript.TimestampSeedSetupFactory
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

structure Inputs where
  source : TimestampSeedEntropyFrame.Inputs
  pool : Arc4Bytes.Frame (TimestampSeedSetupOriginalFrame.origin source).heap source.pool
  nonempty : 0<pool.length
  helperDifferent : source.pool≠source.constructor.prelude.mixing.globals.callee
  windowDifferent : source.pool≠source.constructor.prelude.mixing.globals.base.globalObject
  constructorDifferent : source.pool≠source.constructor.prelude.mixing.globals.constructorId
  codesDifferent : source.pool≠source.constructor.prelude.mixing.globals.codes
  applyDifferent : source.pool≠source.constructor.prelude.mixing.globals.applyId
  stringDifferent : source.pool≠source.constructor.prelude.mixing.stringPrototype.prototype
  methodDifferent : source.pool≠source.constructor.prelude.mixing.stringPrototype.method
  stringSafe : MixkeyRetention.SafePath source.pool source.constructor.prelude.mixing.globals.base.heap
    (JSString.ofString "String") (.object source.constructor.prelude.mixing.globals.constructorId)
    source.constructor.prelude.mixing.globals.base.globalObject source.constructor.prelude.mixing.globals.stringDepth
  constructorSafe : MixkeyRetention.SafePath source.pool source.constructor.prelude.mixing.globals.base.heap
    (JSString.ofString "fromCharCode") (.object source.constructor.prelude.mixing.globals.codes)
    source.constructor.prelude.mixing.globals.constructorId source.constructor.prelude.mixing.globals.constructorDepth
  applySafe : MixkeyRetention.SafePath source.pool source.constructor.prelude.mixing.globals.base.heap
    (JSString.ofString "apply") (.object source.constructor.prelude.mixing.globals.applyId)
    source.constructor.prelude.mixing.globals.codes source.constructor.prelude.mixing.globals.applyDepth
  mathObject : JSObject
  randomValue : Value
  enumerable : Bool
  configurable : Bool
  mathRead : checkedObject source.constructor.prelude.mixing.globals.base.heap source.math=.ok mathObject
  poolMathDifferent : source.pool≠source.math
  mathKind : mathObject.kind=.ordinary
  randomOwn : ownProperty mathObject (JSString.ofString "random")=some (.data randomValue true enumerable configurable)
  randomInspected : mathObject.unresolvedOwnNames.contains (JSString.ofString "random")=false

def original (i : Inputs) := i.source.constructor.prelude.mixing
def string (i : Inputs) := TimestampSeedSetupOriginalFrame.string i.source
def base (i : Inputs) := SeedrandomEntropyMixing.atCall (string i)

theorem extension (i : Inputs) : HeapExtension.Extends (original i).globals.base.heap (base i).heap :=
  HeapExtension.trans (TimestampSeedSetupOriginalFrame.extension i.source)
    (MixkeyToString.allocation_extends (SeedrandomEntropyString.globals (string i)))

theorem original_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (original i).globals.base.heap id=.ok environment) :
    checkedEnvironment (base i).heap id=.ok environment :=
  SeedrandomEntropyString.original_environment (string i) id environment
    (TimestampSeedSetupOriginalFrame.original_environment i.source id environment read)

def environments (i : Inputs) : SeedrandomFrameTransport.Environments (original i).globals.base.heap (base i).heap := {
  size := by
    change (original i).globals.base.heap.environments.size≤
      (MixkeyToString.heap (SeedrandomEntropyString.globals (string i))).environments.size
    rw [MixkeyToString.environment_size]
    change (TimestampSeedSetupOriginalFrame.origin i.source).heap.environments.size≤
      (TimestampSeedSetupOriginalFrame.after i.source).heap.environments.size+1
    rw [TimestampSeedSetupOriginalFrame.environment_size]
    omega
  read := original_environment i }

theorem global_same (i : Inputs) : (base i).globalObject=(original i).globals.base.globalObject :=
  TimestampSeedSetupOriginalFrame.global_same i.source

theorem exclusions_same (i : Inputs) : (base i).objectEnvironmentExclusions=(original i).globals.base.objectEnvironmentExclusions :=
  TimestampSeedSetupOriginalFrame.exclusions_same i.source

theorem string_same (i : Inputs) : (base i).stringPrototype=(original i).globals.base.stringPrototype :=
  TimestampSeedSetupOriginalFrame.string_same i.source

def globals (i : Inputs) : MixkeyToString.Inputs :=
  SeedrandomFrameTransport.globals (original i).globals (base i) i.source.pool
    (extension i) (environments i) (global_same i) (exclusions_same i)

theorem original_binding (i : Inputs) (name : String) (value : Value)
    (read : readBinding (original i).globals.base.heap (original i).globals.scope name=.ok value) :
    readBinding (base i).heap (original i).globals.scope name=.ok value :=
  SeedrandomSetupLocals.read_transport _ _ _ (original_environment i) read

def library (i : Inputs) : NativeMixkeyComplete.Library := {
  globals := globals i
  seed := (SeedrandomEntropyString.text (string i)).toArray
  seedSize := by simpa using SeedrandomEntropyString.text_size (string i)
  bindings := (original i).bindings, outer := (original i).outer
  scopeRead := original_environment i _ _ (original i).scopeRead
  maskDeclared := (original i).maskDeclared
  maskRead := original_binding i _ _ (original i).maskRead
  helperDeclared := (original i).helperDeclared
  helperRead := original_binding i _ _ (original i).helperRead
  helperObject := (original i).helperObject
  helperPresent := HeapExtension.checked_object (extension i) _ _ (original i).helperPresent
  helperKind := (original i).helperKind
  helperDifferent := i.helperDifferent
  windowDifferent := by
    change i.source.pool≠(base i).globalObject
    rw [global_same]
    exact i.windowDifferent
  constructorDifferent := i.constructorDifferent, codesDifferent := i.codesDifferent, applyDifferent := i.applyDifferent
  stringSafe := by
    change MixkeyRetention.SafePath i.source.pool (base i).heap (JSString.ofString "String")
      (.object (original i).globals.constructorId) (base i).globalObject (original i).globals.stringDepth
    rw [global_same]
    exact TimestampSeedMixingFrame.safe_extend (extension i) i.stringSafe
  constructorSafe := TimestampSeedMixingFrame.safe_extend (extension i) i.constructorSafe
  applySafe := TimestampSeedMixingFrame.safe_extend (extension i) i.applySafe }

def loop (i : Inputs) := NativeMixkeyComplete.source (library i)

def pool (i : Inputs) : Arc4Bytes.Frame (base i).heap i.source.pool :=
  SeedrandomFrameTransport.bytes i.pool (extension i)

def loopPool (i : Inputs) : Arc4Bytes.Frame (NativeMixkeyFrame.referenceHeap (loop i) (base i).heap.objects) i.source.pool :=
  Arc4Bytes.transport (pool i) rfl

def frame (i : Inputs) : NativeMixkeyFrame.Frame (loop i) (base i).heap.objects := {
  object := (loopPool i).object, length := (loopPool i).length, bytes := (loopPool i).bytes
  shape := (loopPool i).shape, present := (loopPool i).present, prototype := (loopPool i).prototype
  stringFrame := {
    prototype := (original i).stringPrototype.prototype
    method := (original i).stringPrototype.method
    object := (original i).stringPrototype.object
    linked := (string_same i).trans (original i).stringPrototype.linked
    present := HeapExtension.checked_object (extension i) _ _ (original i).stringPrototype.present
    inspected := (original i).stringPrototype.inspected
    member := (original i).stringPrototype.member }
  methodObject := (original i).charCodeObject
  methodPresent := HeapExtension.checked_object (extension i) _ _ (original i).charCodePresent
  methodKind := (original i).charCodeKind
  arrayDifferent := (loopPool i).arrayDifferent, rootDifferent := (loopPool i).rootDifferent
  stringDifferent := i.stringDifferent, methodDifferent := i.methodDifferent
  room := (loopPool i).room, keyBound := (loopPool i).bound }

def mixing (i : Inputs) : NativeMixkeyComplete.Inputs := {
  library := library i, frame := frame i, callee := (original i).mixkey }

def entropy (i : Inputs) : SeedrandomEntropyMixing.Inputs := {
  string := string i, mixing := mixing i
  baseSame := rfl, scopeSame := rfl, seedSame := rfl, poolSame := rfl, calleeSame := rfl
  object := (original i).mixkeyObject
  present := HeapExtension.checked_object (extension i) _ _ (original i).mixkeyPresent
  kind := (original i).mixkeyKind }

def setup (i : Inputs) : SeedrandomSetupComplete.Inputs := {
  entropy := entropy i
  mathObject := i.mathObject, randomValue := i.randomValue, enumerable := i.enumerable, configurable := i.configurable
  mathRead := HeapExtension.checked_object (TimestampSeedSetupOriginalFrame.extension i.source) _ _ i.mathRead
  poolDifferent := i.poolMathDifferent
  mathKind := i.mathKind, randomOwn := i.randomOwn, randomInspected := i.randomInspected }

def timestamp (i : Inputs) : SeedrandomSetupComplete.TimestampInputs := {
  source := i.source, setup := setup i, entrySame := rfl }

theorem initial_pool_nonempty (i : Inputs) : 0<(mixing i).frame.length := i.nonempty

theorem exact_entropy_input (i : Inputs) : (mixing i).library.seed=
    (SeedrandomEntropyString.text (string i)).toArray := rfl

theorem actual_setup (i : Inputs) (fuel : Nat) :
    Builtins.run (TimestampSeedArc4Complete.steps i.source.constructor+25003+fuel)
      (TimestampSeedMixing.returned i.source.constructor.prelude.mixing)=
      Builtins.run fuel (SeedrandomSetupComplete.timestampReturned (timestamp i)) :=
  SeedrandomSetupComplete.actual_mixed_key_to_setup_return (timestamp i) fuel

theorem returned_p (i : Inputs) : (SeedrandomSetupComplete.timestampReturned (timestamp i)).control=
    .expressionResult (.value (.string (TimestampSeedMixing.text (original i)))) := rfl


theorem returned_elapsed (i : Inputs) : (SeedrandomSetupComplete.timestampReturned (timestamp i)).elapsed=
    (original i).globals.base.elapsed :=
  (SeedrandomSetupComplete.returned_elapsed (setup i)).trans (TimestampSeedSetupOriginalFrame.elapsed_same i.source)

theorem returned_free_draws (i : Inputs) : (SeedrandomSetupComplete.timestampReturned (timestamp i)).freeDrawCount=
    (original i).globals.base.freeDrawCount :=
  (SeedrandomSetupComplete.returned_free_draws (setup i)).trans (TimestampSeedSetupOriginalFrame.free_draws_same i.source)

end CookieClicker.JavaScript.TimestampSeedSetupFactory

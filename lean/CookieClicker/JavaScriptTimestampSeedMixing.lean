import CookieClicker.JavaScriptTimestampSeedMixingFrame

/-! The tagged native seedrandom argument-selection, flatten and mixkey chain.
All helper closures and the fresh key array come from the retained source state. -/
namespace CookieClicker.JavaScript.TimestampSeedMixing
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  globals : MixkeyToString.Inputs
  seed : JSString
  receiver : ObjectId
  seedrandom : ObjectId
  mixkey : ObjectId
  flatten : ObjectId
  bindings : List Binding
  outer : Option EnvId
  scopeRead : checkedEnvironment globals.base.heap globals.scope = .ok ⟨.declarative bindings,outer⟩
  mixkeyDeclared : bindings.any (fun b => b.name == "m") = true
  flattenDeclared : bindings.any (fun b => b.name == "l") = true
  maskDeclared : bindings.any (fun b => b.name == "j") = true
  helperDeclared : bindings.any (fun b => b.name == "o") = true
  mixkeyRead : readBinding globals.base.heap globals.scope "m" = .ok (.object mixkey)
  flattenRead : readBinding globals.base.heap globals.scope "l" = .ok (.object flatten)
  maskRead : readBinding globals.base.heap globals.scope "j" = .ok (.number (Number.ofNat 255))
  helperRead : readBinding globals.base.heap globals.scope "o" = .ok (.object globals.callee)
  mixkeyObject : JSObject
  mixkeyPresent : checkedObject globals.base.heap mixkey = .ok mixkeyObject
  mixkeyKind : mixkeyObject.kind = .function (TimestampMixkey.sourceClosure globals.scope)
  flattenObject : JSObject
  flattenPresent : checkedObject globals.base.heap flatten = .ok flattenObject
  flattenKind : flattenObject.kind = .function (TimestampSeedFlatten.closure globals.scope)
  helperObject : JSObject
  helperPresent : checkedObject globals.base.heap globals.callee = .ok helperObject
  helperKind : helperObject.kind = .function (MixkeyToString.closure globals.scope)
  arrayPrototype : MixkeyArray.PrototypeFrame globals.base.heap (TimestampSeedFlatten.emptyArray globals.base)
  stringPrototype : MixkeyString.PrototypeFrame globals.base
  charCodeObject : JSObject
  charCodePresent : checkedObject globals.base.heap stringPrototype.method = .ok charCodeObject
  charCodeKind : charCodeObject.kind = .builtin MixkeyString.methodId
  room : 2 ≤ globals.base.heap.objects.size

def setup (i : Inputs) : TimestampSeedSetup.Inputs := {
  base := i.globals.base, scope := i.globals.scope, receiver := i.receiver, callee := i.seedrandom
  seed := i.seed, mixkey := i.mixkey, flatten := i.flatten, bindings := i.bindings, outer := i.outer
  scopeRead := i.scopeRead, mixkeyDeclared := i.mixkeyDeclared, flattenDeclared := i.flattenDeclared
  mixkeyRead := i.mixkeyRead, flattenRead := i.flattenRead }

def beforeMixing (i : Inputs) := TimestampSeedSetup.atMixkey (setup i)
def key (i : Inputs) := TimestampSeedMixingFrame.key (setup i)
def extension (i : Inputs) : HeapExtension.Extends i.globals.base.heap (beforeMixing i).heap :=
  TimestampSeedSetup.atMixkey_extends (setup i)

def globals (i : Inputs) : MixkeyToString.Inputs := {
  base := beforeMixing i, scope := i.globals.scope, callee := i.globals.callee, array := key i
  globalScope := i.globals.globalScope, globalOuter := i.globals.globalOuter
  provideThis := i.globals.provideThis, depth := i.globals.depth
  chain := TimestampSeedMixingFrame.original_path (setup i) _ _ _ _ i.globals.chain
  depthBound := by rw [show (beforeMixing i).heap.environments.size=i.globals.base.heap.environments.size+2
                       from TimestampSeedMixingFrame.environment_size (setup i)]
                   exact Nat.le_trans i.globals.depthBound (Nat.le_add_right _ 2)
  globalRead := TimestampSeedMixingFrame.original_environment (setup i) _ _ i.globals.globalRead
  exclusions := i.globals.exclusions
  constructorId := i.globals.constructorId, codes := i.globals.codes, applyId := i.globals.applyId
  windowObject := i.globals.windowObject, constructorObject := i.globals.constructorObject
  codesObject := i.globals.codesObject, applyObject := i.globals.applyObject
  windowRead := HeapExtension.checked_object (extension i) _ _ i.globals.windowRead
  constructorRead := HeapExtension.checked_object (extension i) _ _ i.globals.constructorRead
  codesRead := HeapExtension.checked_object (extension i) _ _ i.globals.codesRead
  applyRead := HeapExtension.checked_object (extension i) _ _ i.globals.applyRead
  windowNotArguments := i.globals.windowNotArguments
  constructorKind := i.globals.constructorKind, codesKind := i.globals.codesKind, applyKind := i.globals.applyKind
  stringDepth := i.globals.stringDepth, constructorDepth := i.globals.constructorDepth, applyDepth := i.globals.applyDepth
  stringPath := DataPropertyPath.extend (extension i) i.globals.stringPath
  constructorPath := DataPropertyPath.extend (extension i) i.globals.constructorPath
  applyPath := DataPropertyPath.extend (extension i) i.globals.applyPath
  stringBound := Nat.le_trans i.globals.stringBound (extension i).size
  constructorBound := Nat.le_trans i.globals.constructorBound (extension i).size
  applyBound := Nat.le_trans i.globals.applyBound (extension i).size }

def library (i : Inputs) : TimestampMixkeyComplete.Library := {
  globals := globals i, seed := i.seed.toArray, bindings := i.bindings, outer := i.outer
  scopeRead := TimestampSeedMixingFrame.original_environment (setup i) _ _ i.scopeRead
  maskDeclared := i.maskDeclared
  maskRead := TimestampSeedMixingFrame.original_binding (setup i) _ _ _ _ i.scopeRead i.maskRead
  helperDeclared := i.helperDeclared
  helperRead := TimestampSeedMixingFrame.original_binding (setup i) _ _ _ _ i.scopeRead i.helperRead
  helperObject := i.helperObject
  helperPresent := HeapExtension.checked_object (extension i) _ _ i.helperPresent
  helperKind := i.helperKind
  helperDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.helperPresent
  windowDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.globals.windowRead
  constructorDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.globals.constructorRead
  codesDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.globals.codesRead
  applyDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.globals.applyRead
  stringSafe := TimestampSeedMixingFrame.safe_extend (extension i)
    (TimestampSeedMixingFrame.safe_fresh_path i.globals.stringPath (key i) (Nat.le_of_lt (TimestampSeedMixingFrame.key_fresh (setup i))))
  constructorSafe := TimestampSeedMixingFrame.safe_extend (extension i)
    (TimestampSeedMixingFrame.safe_fresh_path i.globals.constructorPath (key i) (Nat.le_of_lt (TimestampSeedMixingFrame.key_fresh (setup i))))
  applySafe := TimestampSeedMixingFrame.safe_extend (extension i)
    (TimestampSeedMixingFrame.safe_fresh_path i.globals.applyPath (key i) (Nat.le_of_lt (TimestampSeedMixingFrame.key_fresh (setup i)))) }

def source (i : Inputs) := TimestampMixkeyComplete.source (library i)

def frame (i : Inputs) : TimestampMixkeyFrame.Frame (source i) (beforeMixing i).heap.objects := {
  object := TimestampSeedFlatten.emptyArray i.globals.base
  length := 0, bytes := fun _ => 0, shape := TimestampSeedMixingFrame.empty_shape _
  present := TimestampSeedMixingFrame.key_present (setup i)
  prototype := i.arrayPrototype.transport rfl
    (HeapExtension.checked_object (extension i) _ _ i.arrayPrototype.arrayRead)
    (HeapExtension.checked_object (extension i) _ _ i.arrayPrototype.rootRead)
  stringFrame := {
    prototype := i.stringPrototype.prototype, method := i.stringPrototype.method, object := i.stringPrototype.object
    linked := i.stringPrototype.linked
    present := HeapExtension.checked_object (extension i) _ _ i.stringPrototype.present
    inspected := i.stringPrototype.inspected, member := i.stringPrototype.member }
  methodObject := i.charCodeObject
  methodPresent := HeapExtension.checked_object (extension i) _ _ i.charCodePresent
  methodKind := i.charCodeKind
  arrayDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.arrayPrototype.arrayRead
  rootDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.arrayPrototype.rootRead
  stringDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.stringPrototype.present
  methodDifferent := TimestampSeedMixingFrame.key_different (setup i) _ _ i.charCodePresent
  room := Nat.le_trans i.room (extension i).size
  keyBound := by
    have present : checkedObject (beforeMixing i).heap (key i) = .ok (TimestampSeedFlatten.emptyArray i.globals.base) :=
      TimestampSeedMixingFrame.key_present (setup i)
    unfold checkedObject Heap.object? at present
    cases found : (beforeMixing i).heap.objects[key i]? with
    | none => simp [found] at present
    | some object => exact Array.getElem?_eq_some_iff.mp found |>.1 }

def mixing (i : Inputs) : TimestampMixkeyComplete.Inputs := {
  library := library i, frame := frame i, empty := rfl, callee := i.mixkey }

def returned (i : Inputs) := TimestampMixkeyComplete.returned (mixing i)
def text (i : Inputs) := TimestampMixkeyComplete.text (mixing i)

theorem actual_setup_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (128+fuel) (SeedrandomInvocation.preparedText i.globals.base i.globals.scope i.receiver i.seed i.seedrandom) =
      Builtins.run fuel (beforeMixing i) :=
  TimestampSeedSetup.actual_seedrandom_to_mixkey (setup i) _ i.flattenPresent i.flattenKind fuel

theorem actual_captured_mixing (i : Inputs) :
    (TimestampText.invoke (beforeMixing i) i.mixkey .undefined [.timestampText i.seed.toArray,.object (key i)]).map
      (Builtins.run (88+93*i.seed.toArray.size+2*(TimestampMixkeyComplete.arrayData (mixing i)).length)) =
      .ok (returned i) :=
  TimestampMixkeyComplete.actual_captured_helper (mixing i) i.mixkeyObject
    (HeapExtension.checked_object (extension i) _ _ i.mixkeyPresent) i.mixkeyKind

theorem actual_mixing_result_size (i : Inputs) : (text i).length = min i.seed.length 256 := by
  simpa [text,mixing,library] using TimestampMixkeyComplete.returned_text_size (mixing i)

theorem elapsed (i : Inputs) : (returned i).elapsed = i.globals.base.elapsed := rfl

theorem free_draws (i : Inputs) : (returned i).freeDrawCount = i.globals.base.freeDrawCount := rfl

end CookieClicker.JavaScript.TimestampSeedMixing

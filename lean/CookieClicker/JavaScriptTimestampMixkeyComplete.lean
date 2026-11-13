import CookieClicker.JavaScriptTimestampMixkeyReturn

/-! Complete source mixing and return for tagged timestamp text. Existing
objects are retained except for the native key-array byte writes. -/
namespace CookieClicker.JavaScript.TimestampMixkeyComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Library where
  globals : MixkeyToString.Inputs
  seed : Array UInt16
  bindings : List Binding
  outer : Option EnvId
  scopeRead : checkedEnvironment globals.base.heap globals.scope = .ok ⟨.declarative bindings,outer⟩
  maskDeclared : bindings.any (fun b => b.name == "j") = true
  maskRead : readBinding globals.base.heap globals.scope "j" = .ok (.number (Number.ofNat 255))
  helperDeclared : bindings.any (fun b => b.name == "o") = true
  helperRead : readBinding globals.base.heap globals.scope "o" = .ok (.object globals.callee)
  helperObject : JSObject
  helperPresent : checkedObject globals.base.heap globals.callee = .ok helperObject
  helperKind : helperObject.kind = .function (MixkeyToString.closure globals.scope)
  helperDifferent : globals.array ≠ globals.callee
  windowDifferent : globals.array ≠ globals.base.globalObject
  constructorDifferent : globals.array ≠ globals.constructorId
  codesDifferent : globals.array ≠ globals.codes
  applyDifferent : globals.array ≠ globals.applyId
  stringSafe : MixkeyRetention.SafePath globals.array globals.base.heap (JSString.ofString "String")
    (.object globals.constructorId) globals.base.globalObject globals.stringDepth
  constructorSafe : MixkeyRetention.SafePath globals.array globals.base.heap (JSString.ofString "fromCharCode")
    (.object globals.codes) globals.constructorId globals.constructorDepth
  applySafe : MixkeyRetention.SafePath globals.array globals.base.heap (JSString.ofString "apply")
    (.object globals.applyId) globals.codes globals.applyDepth

def source (library : Library) : TimestampMixkeyLoop.Inputs := {
  base := library.globals.base, scope := library.globals.scope, seed := library.seed, key := library.globals.array
  bindings := library.bindings, outer := library.outer, scopeRead := library.scopeRead
  maskDeclared := library.maskDeclared, maskRead := library.maskRead }

structure Inputs where
  library : Library
  frame : TimestampMixkeyFrame.Frame (source library) library.globals.base.heap.objects
  empty : frame.length = 0
  callee : ObjectId

def loop (i : Inputs) := source i.library
def global (i : Inputs) := i.library.globals
def state (i : Inputs) := TimestampMixkeyTraversal.traversed (loop i) i.frame i.empty i.callee

def exited (i : Inputs) := TimestampMixkeyTraversal.exited (loop i) (state i)

def retained (i : Inputs) : MixkeyRetention.Preserves (global i).array (global i).base.heap (exited i).heap :=
  MixkeyRetention.complete_preserves (loop i) i.frame i.empty i.callee

def finalFrame (i : Inputs) := TimestampMixkeyTraversal.guardFrame (loop i) (state i)

def returnInput (i : Inputs) : TimestampMixkeyReturn.Inputs := {
  source := loop i
  objects := (state i).objects.push (TimestampMixkey.stringWrapper (global i).base i.library.seed)
  smear := TimestampMixkeyLoop.smearValue (state i).smear
  index := (state i).index
  previous := (state i).previous
  callee := (global i).callee
  declared := i.library.helperDeclared
  read := i.library.helperRead
  object := i.library.helperObject
  present := (retained i).read _ _ i.library.helperDifferent i.library.helperPresent
  kind := i.library.helperKind }

def call (i : Inputs) := TimestampMixkeyReturn.beforeCall (returnInput i)

def toStringInput (i : Inputs) : MixkeyToString.Inputs := {
  base := call i
  scope := (global i).scope
  callee := (global i).callee
  array := (global i).array
  globalScope := (global i).globalScope
  globalOuter := (global i).globalOuter
  provideThis := (global i).provideThis
  depth := (global i).depth
  chain := HasEnvironment.append_path _ _ _ _ _ _ (global i).chain
  depthBound := by
    change (global i).depth ≤ (TimestampMixkeyReturn.sourceHeap (returnInput i)).environments.size
    rw [TimestampMixkeyReturn.size]
    exact Nat.le_trans (global i).depthBound (Nat.le_succ _)
  globalRead := EnvironmentAppend.checked_old _ _ _ _ _ (global i).globalRead
  exclusions := (global i).exclusions
  constructorId := (global i).constructorId
  codes := (global i).codes
  applyId := (global i).applyId
  windowObject := (global i).windowObject
  constructorObject := (global i).constructorObject
  codesObject := (global i).codesObject
  applyObject := (global i).applyObject
  windowRead := (retained i).read _ _ i.library.windowDifferent (global i).windowRead
  constructorRead := (retained i).read _ _ i.library.constructorDifferent (global i).constructorRead
  codesRead := (retained i).read _ _ i.library.codesDifferent (global i).codesRead
  applyRead := (retained i).read _ _ i.library.applyDifferent (global i).applyRead
  windowNotArguments := (global i).windowNotArguments
  constructorKind := (global i).constructorKind
  codesKind := (global i).codesKind
  applyKind := (global i).applyKind
  stringDepth := (global i).stringDepth
  constructorDepth := (global i).constructorDepth
  applyDepth := (global i).applyDepth
  stringPath := MixkeyRetention.path (retained i) i.library.stringSafe
  constructorPath := MixkeyRetention.path (retained i) i.library.constructorSafe
  applyPath := MixkeyRetention.path (retained i) i.library.applySafe
  stringBound := Nat.le_trans (global i).stringBound (retained i).size
  constructorBound := Nat.le_trans (global i).constructorBound (retained i).size
  applyBound := Nat.le_trans (global i).applyBound (retained i).size }

def arrayData (i : Inputs) : MixkeyToString.ArrayData (toStringInput i) := {
  object := (finalFrame i).object
  length := (finalFrame i).length
  bytes := (finalFrame i).bytes
  shape := (finalFrame i).shape
  present := (finalFrame i).present
  prototype := (finalFrame i).prototype.transport rfl (finalFrame i).prototype.arrayRead (finalFrame i).prototype.rootRead
  room := (finalFrame i).room }

def text (i : Inputs) := MixkeyToString.text (toStringInput i) (arrayData i)
def completedHeap (i : Inputs) := MixkeyToString.heap (toStringInput i)
def afterInnerReturn (i : Inputs) := MixkeyToString.returned (toStringInput i) (arrayData i)
def returned (i : Inputs) := result {(global i).base with heap := completedHeap i} (.string (text i))

attribute [local cbv_opaque] global loop state completedHeap text

theorem actual_outer_return (i : Inputs) (fuel : Nat) :
    Builtins.run (3+fuel) (afterInnerReturn i) = Builtins.run fuel (returned i) := by
  change Builtins.run (3+fuel) {
    (global i).base with
    heap := completedHeap i
    context := ⟨TimestampMixkey.localIndex (global i).base,TimestampMixkey.localIndex (global i).base,
      .object (global i).base.globalObject,false⟩
    control := .expressionResult (.value (.string (text i)))
    continuation := .returnValue :: .statementList [] (state i).previous ::
      .callBoundary (global i).base.context none :: (global i).base.continuation } = _
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_complete_helper (i : Inputs) (fuel : Nat) :
    Builtins.run (88+93*i.library.seed.size+2*(arrayData i).length+fuel)
      (TimestampMixkey.prepared (global i).base (global i).scope i.library.seed (global i).array i.callee) =
      Builtins.run fuel (returned i) := by
  rw [show 88+93*i.library.seed.size+2*(arrayData i).length+fuel =
    (26+93*i.library.seed.size+14)+(12+(33+2*(arrayData i).length+(3+fuel))) by omega]
  change Builtins.run (26+93*(TimestampMixkeyLoop.seed (loop i)).size+14+
    (12+(33+2*(arrayData i).length+(3+fuel))))
      (TimestampMixkey.prepared (TimestampMixkeyLoop.base (loop i)) (TimestampMixkeyLoop.scope (loop i))
        (TimestampMixkeyLoop.seed (loop i)) (TimestampMixkeyLoop.key (loop i)) i.callee) = _
  rw [TimestampMixkeyTraversal.actual_source_loop (loop i) i.frame i.empty i.callee]
  change Builtins.run (12+(33+2*(arrayData i).length+(3+fuel))) (TimestampMixkeyReturn.start (returnInput i)) = _
  rw [TimestampMixkeyReturn.actual_return_call]
  change Builtins.run (33+2*(arrayData i).length+(3+fuel)) (MixkeyToString.start (toStringInput i)) = _
  rw [MixkeyToString.actual_source_helper]
  exact actual_outer_return i fuel

theorem final_length (i : Inputs) : (arrayData i).length = min i.library.seed.size 256 :=
  TimestampMixkeyTraversal.traversed_length (loop i) i.frame i.empty i.callee

theorem returned_text_size (i : Inputs) : (text i).length = min i.library.seed.size 256 := by
  change ((List.range (arrayData i).length).map _).length = _
  simp [final_length]


theorem actual_captured_helper (i : Inputs) (object : JSObject)
    (present : checkedObject (global i).base.heap i.callee = .ok object)
    (kind : object.kind = .function (TimestampMixkey.sourceClosure (global i).scope)) :
    (TimestampText.invoke (global i).base i.callee .undefined [.timestampText i.library.seed,.object (global i).array]).map
      (Builtins.run (88+93*i.library.seed.size+2*(arrayData i).length)) = .ok (returned i) := by
  rw [TimestampMixkey.actual_captured_invocation _ _ _ _ _ _ present kind]
  change Except.ok (Builtins.run (88+93*i.library.seed.size+2*(arrayData i).length+0) _) = _
  rw [actual_complete_helper]
  rfl

theorem returned_key (i : Inputs) : checkedObject (returned i).heap (global i).array = .ok (finalFrame i).object :=
  HeapExtension.checked_object (MixkeyToString.allocation_extends (toStringInput i)) _ _ (arrayData i).present

theorem returned_key_shape (i : Inputs) :
    MixkeyArray.Shape (finalFrame i).object (min i.library.seed.size 256) (finalFrame i).bytes := by
  have h := (arrayData i).shape
  rw [final_length] at h
  exact h

theorem returned_elapsed (i : Inputs) : (returned i).elapsed = (global i).base.elapsed := rfl

theorem returned_free_draws (i : Inputs) : (returned i).freeDrawCount = (global i).base.freeDrawCount := rfl

theorem returned_context (i : Inputs) : (returned i).context = (global i).base.context := rfl

theorem returned_continuation (i : Inputs) : (returned i).continuation = (global i).base.continuation := rfl

theorem retained_objects (i : Inputs) : MixkeyRetention.Preserves (global i).array (global i).base.heap (returned i).heap :=
  MixkeyRetention.trans (retained i)
    (MixkeyRetention.from_extension _ (MixkeyToString.allocation_extends (toStringInput i)))

end CookieClicker.JavaScript.TimestampMixkeyComplete

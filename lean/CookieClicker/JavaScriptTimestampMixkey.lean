import CookieClicker.JavaScriptBindingWrite
import CookieClicker.JavaScriptTimestampTextSemantics
import CookieClicker.JavaScriptIndexBits

/-! The retained timestamp-text mixkey source. The index carrier is selected
only by the checked captured activation; byte operations remain native Numbers. -/
namespace CookieClicker.JavaScript.TimestampMixkey
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

open SeedrandomMixkeySyntax

def sourceClosure (scope : EnvId) : FunctionClosure :=
  ⟨some "m",["a","b"],TimestampText.nativeBody,scope,false,some mixkeyText⟩
def closure (scope : EnvId) : FunctionClosure := TimestampText.activation (sourceClosure scope)
def body := TimestampText.activationBody
def localIndex (base : Machine) := base.heap.environments.size
def argumentIndex (base : Machine) := base.heap.objects.size
def initialLocals (base : Machine) (seed : Array UInt16) (key : ObjectId) : List Binding :=
  [{name := "a",value := .timestampText seed},{name := "b",value := .object key},
    {name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (seed : Array UInt16) (key callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a"),(JSString.ofString "1",localIndex base,"b")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.timestampText seed) true true true⟩,
    ⟨JSString.ofString "1",.data (.object key) true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false true⟩] ++
    argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeap (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId)
    (locals : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObject base seed key callee)
  environments := base.heap.environments.push ⟨.declarative locals,some scope⟩ }
def prepared (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope seed key callee (initialLocals base seed key)
  context := ⟨localIndex base,localIndex base,.object base.globalObject,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem captured_body_matches (scope : EnvId) :
    TimestampText.nativeClosure (sourceClosure scope) = true := by
  change TimestampText.nativeClosure (sourceClosure 0) = true
  decide +kernel

theorem actual_prepare (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) :
    prepareCall (callee := some callee) base (closure scope) .undefined [.timestampText seed,.object key] none =
      .ok (prepared base scope seed key callee) := by
  simp [prepareCall,body,closure,TimestampText.activation,sourceClosure,actualThis,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,localIndex,argumentIndex,initialLocals,argumentObject,
    argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_captured_invocation (base : Machine) (scope : EnvId) (seed : Array UInt16)
    (key callee : ObjectId) (object : JSObject)
    (present : checkedObject base.heap callee = .ok object)
    (kind : object.kind = .function (sourceClosure scope)) :
    TimestampText.invoke base callee .undefined [.timestampText seed,.object key] =
      .ok (prepared base scope seed key callee) := by
  simp only [TimestampText.invoke,present,kind,captured_body_matches, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.bind,bind,Except.pure,pure]
  exact actual_prepare base scope seed key callee

def withD (base : Machine) (seed : Array UInt16) (key : ObjectId) := initialLocals base seed key ++ [{name := "d"}]
def withC (base : Machine) (seed : Array UInt16) (key : ObjectId) := withD base seed key ++ [{name := "c"}]
def withE (base : Machine) (seed : Array UInt16) (key : ObjectId) := withC base seed key ++ [{name := "e"}]

theorem hoist_d (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed key callee (initialLocals base seed key)) (localIndex base) "d" .undefined false =
      .ok (allocatedHeap base scope seed key callee (withD base seed key)) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withD,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem hoist_c (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed key callee (withD base seed key)) (localIndex base) "c" .undefined false =
      .ok (allocatedHeap base scope seed key callee (withC base seed key)) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withD,withC,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem hoist_e (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed key callee (withC base seed key)) (localIndex base) "e" .undefined false =
      .ok (allocatedHeap base scope seed key callee (withE base seed key)) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withD,withC,withE,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

def hoisted (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) : Machine := {
  prepared base scope seed key callee with
  heap := allocatedHeap base scope seed key callee (withE base seed key)
  control := .declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withD withC withE defineBinding
attribute [local cbv_eval] hoist_d hoist_c hoist_e

theorem actual_hoist (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) (fuel : Nat) :
    Builtins.run (8+fuel) (prepared base scope seed key callee) =
      Builtins.run fuel (hoisted base scope seed key callee) := by
  rw [Nat.add_comm 8 fuel]
  cbv


def scopeLocals (base : Machine) (seed : Array UInt16) (key : ObjectId) (d c e : Value) : List Binding :=
  initialLocals base seed key ++ [{name := "d",value := d},{name := "c",value := c},{name := "e",value := e}]
def bodyHeap (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d c e : Value) : Heap := {
  objects := objects
  environments := base.heap.environments.push ⟨.declarative (scopeLocals base seed key d c e),some scope⟩ }
def objectsWithArgument (base : Machine) (seed : Array UInt16) (key callee : ObjectId) :=
  base.heap.objects.push (argumentObject base seed key callee)
def test : Expr := match body.head? with
  | some (.forLoop _ (some test) _ _) => test
  | _ => .literal (.boolean false)
def loopBody : Stmt := match body.head? with
  | some (.forLoop _ _ _ statement) => statement
  | _ => .empty
def returnStatement : Stmt := body[1]?.getD .empty

theorem checked_body_local (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d c e : Value) :
    checkedEnvironment (bodyHeap base scope seed key objects d c e) (localIndex base) =
      .ok ⟨.declarative (scopeLocals base seed key d c e),some scope⟩ := by
  simp [checkedEnvironment,bodyHeap,localIndex,Heap.environment?]

theorem body_environment_size (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d c e : Value) :
    (bodyHeap base scope seed key objects d c e).environments.size = base.heap.environments.size + 1 := by
  simp [bodyHeap]

theorem write_c (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d c e value : Value) :
    setBinding (bodyHeap base scope seed key objects d c e) (localIndex base) "c" value false =
      .ok (bodyHeap base scope seed key objects d value e) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,checked_body_local,scopeLocals,initialLocals,bodyHeap,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem write_e (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d c e value : Value) :
    setBinding (bodyHeap base scope seed key objects d c e) (localIndex base) "e" value false =
      .ok (bodyHeap base scope seed key objects d c value) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,checked_body_local,scopeLocals,initialLocals,bodyHeap,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem append_empty (seed : Array UInt16) :
    binary .add (.timestampText seed) (.string []) = .ok (.timestampText seed) := by
  simp [binary,textResult,timestampTextSource,toJSString,Except.bind,bind,Except.pure,pure]

theorem initial_scope (base : Machine) (seed : Array UInt16) (key : ObjectId) :
    initialLocals base seed key = [{name := "a",value := .timestampText seed},{name := "b",value := .object key},
      {name := "arguments",value := .object (argumentIndex base)}] := rfl

def atGuard (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Int) (previous : Option Value) : Machine := {
  base with
  heap := bodyHeap base scope seed key objects d (.timestampText seed) (.textIndex index)
  context := ⟨localIndex base,localIndex base,.object base.globalObject,false⟩
  control := .expression test
  continuation := .forTest (some test) none loopBody [] previous :: .statementList [returnStatement] none ::
    .callBoundary base.context none :: base.continuation }

attribute [local cbv_opaque] bodyHeap objectsWithArgument setBinding checkedEnvironment binary
attribute [local cbv_eval] checked_body_local body_environment_size write_c write_e append_empty initial_scope

theorem actual_initializers (base : Machine) (scope : EnvId) (seed : Array UInt16) (key callee : ObjectId) (fuel : Nat) :
    Builtins.run (18+fuel) (hoisted base scope seed key callee) =
      Builtins.run fuel (atGuard base scope seed key (objectsWithArgument base seed key callee) .undefined 0 none) := by
  change Builtins.run (18+fuel) {hoisted base scope seed key callee with
    heap := bodyHeap base scope seed key (objectsWithArgument base seed key callee) .undefined .undefined .undefined} = _
  rw [Nat.add_comm 18 fuel]
  cbv


def stringWrapper (machine : Machine) (seed : Array UInt16) : JSObject := {
  kind := .timestampTextWrapper seed, prototype := machine.stringPrototype }

theorem read_length (machine : Machine) (seed : Array UInt16) :
    readProperty machine (.timestampText seed) (JSString.ofString "length") =
      result {machine with heap := {machine.heap with objects := machine.heap.objects.push (stringWrapper machine seed)}}
        (.textIndex seed.size) := by
  simp [readProperty,toObject,Heap.allocateObject,readObjectProperty,checkedObject,Heap.object?,
    lookupProperty,findProperty,ownProperty,stringWrapper,checked,result,Except.bind,bind,Except.pure,pure]

theorem body_allocate (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d c e : Value) (object : JSObject) :
    (bodyHeap base scope seed key objects d c e).allocateObject object =
      (objects.size,bodyHeap base scope seed key (objects.push object) d c e) := rfl

theorem loop_compare (seed : Array UInt16) (index : Nat) :
    binary .greater (.textIndex seed.size) (.textIndex index) = .ok (.boolean (index < seed.size)) := by
  rw [TimestampTextSemantics.exact_loop_guard]
  simp

def atBody (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  atGuard base scope seed key objects d index previous with
  control := .statement loopBody
  continuation := .forBody (some test) none loopBody [] previous :: .statementList [returnStatement] none ::
    .callBoundary base.context none :: base.continuation }

def atExit (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  atGuard base scope seed key objects d index previous with
  control := .completion (.normal previous)
  continuation := .statementList [returnStatement] none :: .callBoundary base.context none :: base.continuation }

attribute [local cbv_opaque] Array.push Array.size readProperty
attribute [local cbv_eval] Array.size_push read_length body_allocate loop_compare


def atLength (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  atGuard base scope seed key objects d index previous with
  control := .getValue ⟨.property (.timestampText seed) (JSString.ofString "length"),false⟩
  continuation := .binaryLeft .greater (.identifier "e") ::
    .forTest (some test) none loopBody [] previous :: .statementList [returnStatement] none ::
    .callBoundary base.context none :: base.continuation }

def afterLength (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  atLength base scope seed key (objects.push (stringWrapper base seed)) d index previous with
  control := .expressionResult (.value (.textIndex seed.size)) }

theorem actual_guard_prefix (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    Builtins.run (7+fuel) (atGuard base scope seed key objects d index previous) =
      Builtins.run fuel (atLength base scope seed key objects d index previous) := by
  rw [Nat.add_comm 7 fuel]
  cbv

theorem actual_length_step (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :
    Builtins.builtinStep (atLength base scope seed key objects d index previous) =
      afterLength base scope seed key objects d index previous := by
  change {readProperty (atLength base scope seed key objects d index previous) (.timestampText seed)
    (JSString.ofString "length") with elapsed := base.elapsed} = _
  rw [read_length]
  rfl


def atComparison (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  afterLength base scope seed key objects d index previous with
  control := .expressionResult (.value (.textIndex index))
  continuation := .binaryRight .greater (.textIndex seed.size) ::
    .forTest (some test) none loopBody [] previous :: .statementList [returnStatement] none ::
    .callBoundary base.context none :: base.continuation }

def atBranch (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  afterLength base scope seed key objects d index previous with
  control := .expressionResult (.value (.boolean (index < seed.size)))
  continuation := .forTest (some test) none loopBody [] previous :: .statementList [returnStatement] none ::
    .callBoundary base.context none :: base.continuation }

theorem actual_guard_right (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    Builtins.run (4+fuel) (afterLength base scope seed key objects d index previous) =
      Builtins.run fuel (atComparison base scope seed key objects d index previous) := by
  rw [Nat.add_comm 4 fuel]
  cbv

theorem actual_compare_step (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :
    Builtins.builtinStep (atComparison base scope seed key objects d index previous) =
      atBranch base scope seed key objects d index previous := by
  let next : Machine := {
    atComparison base scope seed key objects d index previous with
    continuation := .forTest (some test) none loopBody [] previous ::
      .statementList [returnStatement] none :: .callBoundary base.context none :: base.continuation }
  change {checked next (binary .greater (.textIndex seed.size) (.textIndex index)) (result next)
    with elapsed := base.elapsed} = _
  rw [loop_compare]
  rfl

theorem actual_branch_step (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :
    Builtins.builtinStep (atBranch base scope seed key objects d index previous) =
      (if index < seed.size then atBody base scope seed key (objects.push (stringWrapper base seed)) d index previous
      else atExit base scope seed key (objects.push (stringWrapper base seed)) d index previous) := by
  by_cases before : index < seed.size
  · simp only [atBranch, before, decide_true, if_true]
    rfl
  · simp only [atBranch, before, decide_false, if_false]
    rfl

theorem actual_guard_suffix (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    Builtins.run (6+fuel) (afterLength base scope seed key objects d index previous) =
      Builtins.run fuel (if index < seed.size then
        atBody base scope seed key (objects.push (stringWrapper base seed)) d index previous
      else atExit base scope seed key (objects.push (stringWrapper base seed)) d index previous) := by
  rw [show 6+fuel=4+((fuel+1)+1) by omega, actual_guard_right]
  change Builtins.run fuel (Builtins.builtinStep (Builtins.builtinStep (atComparison base scope seed key objects d index previous))) = _
  rw [actual_compare_step,actual_branch_step]

theorem actual_guard (base : Machine) (scope : EnvId) (seed : Array UInt16) (key : ObjectId)
    (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) (fuel : Nat) :
    Builtins.run (14+fuel) (atGuard base scope seed key objects d index previous) =
      Builtins.run fuel (if index < seed.size then
        atBody base scope seed key (objects.push (stringWrapper base seed)) d index previous
      else atExit base scope seed key (objects.push (stringWrapper base seed)) d index previous) := by
  rw [show 14+fuel=7+(1+(6+fuel)) by omega, actual_guard_prefix]
  rw [Nat.add_comm 1 (6+fuel)]
  change Builtins.run (6+fuel) (Builtins.builtinStep (atLength base scope seed key objects d index previous)) = _
  rw [actual_length_step, actual_guard_suffix]

end CookieClicker.JavaScript.TimestampMixkey

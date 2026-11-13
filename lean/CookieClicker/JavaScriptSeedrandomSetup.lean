import CookieClicker.JavaScriptSeedrandomInvocation
import CookieClicker.JavaScriptSeedrandomFlatten
import CookieClicker.JavaScriptHeapExtension
/-! Actual string-seed source selection inside the retained seedrandom library.
The source resolves its real helper bindings and invokes flatten; no helper
result or random-generator installation is supplied as an execution contract. -/
namespace CookieClicker.JavaScript.SeedrandomSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open SeedrandomInvocation (body closure localIndex argumentIndex argumentObject allocatedHeap prepared)

def withJ (base : Machine) (seed : JSString) : List Binding := SeedrandomInvocation.locals base seed ++ [{name := "j"}]
def withP (base : Machine) (seed : JSString) : List Binding := withJ base seed ++ [{name := "p"}]
def withQ (base : Machine) (seed : JSString) : List Binding := withP base seed ++ [{name := "q"}]

theorem hoist_j (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed callee (SeedrandomInvocation.locals base seed)) (localIndex base) "j" .undefined false =
      .ok (allocatedHeap base scope seed callee (withJ base seed)) := by
  simp [defineBinding,allocatedHeap,localIndex,SeedrandomInvocation.locals,withJ,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem hoist_p (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed callee (withJ base seed)) (localIndex base) "p" .undefined false =
      .ok (allocatedHeap base scope seed callee (withP base seed)) := by
  simp [defineBinding,allocatedHeap,localIndex,SeedrandomInvocation.locals,withJ,withP,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem hoist_q (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed callee (withP base seed)) (localIndex base) "q" .undefined false =
      .ok (allocatedHeap base scope seed callee (withQ base seed)) := by
  simp [defineBinding,allocatedHeap,localIndex,SeedrandomInvocation.locals,withJ,withP,withQ,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

def hoisted (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  prepared base scope receiver seed callee with
  heap := allocatedHeap base scope seed callee (withQ base seed)
  control := .declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex SeedrandomInvocation.locals withJ withP withQ defineBinding
attribute [local cbv_eval] hoist_j hoist_p hoist_q

theorem actual_hoist (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (7+fuel) (prepared base scope receiver seed callee) =
      Builtins.run fuel (hoisted base scope receiver seed callee) := by
  rw [Nat.add_comm 7 fuel]
  cbv

structure Inputs where
  base : Machine
  scope : EnvId
  receiver : ObjectId
  callee : ObjectId
  seed : JSString
  mixkey : ObjectId
  flatten : ObjectId
  bindings : List Binding
  outer : Option EnvId
  scopeRead : checkedEnvironment base.heap scope = .ok ⟨.declarative bindings,outer⟩
  mixkeyDeclared : bindings.any (fun b => b.name == "m") = true
  flattenDeclared : bindings.any (fun b => b.name == "l") = true
  mixkeyRead : readBinding base.heap scope "m" = .ok (.object mixkey)
  flattenRead : readBinding base.heap scope "l" = .ok (.object flatten)

def base (i : Inputs) := i.base
def scope (i : Inputs) := i.scope
def receiver (i : Inputs) := i.receiver
def callee (i : Inputs) := i.callee
def seed (i : Inputs) := i.seed
def mixkey (i : Inputs) := i.mixkey
def flatten (i : Inputs) := i.flatten
def libraryBindings (i : Inputs) := i.bindings
def libraryOuter (i : Inputs) := i.outer

def localBindings (i : Inputs) (j : Value) : List Binding :=
  SeedrandomInvocation.locals (base i) (seed i) ++ [{name := "j",value := j},{name := "p"},{name := "q"}]
def sourceHeap (i : Inputs) (objects : Array JSObject) (j : Value) : Heap := {
  objects := objects
  environments := (base i).heap.environments.push ⟨.declarative (localBindings i j),some (scope i)⟩ }
def initialObjects (i : Inputs) : Array JSObject :=
  (base i).heap.objects.push (argumentObject (base i) (seed i) (callee i))
def sourceStart (i : Inputs) : Machine := hoisted (base i) (scope i) (receiver i) (seed i) (callee i)

theorem scope_bound (i : Inputs) : scope i < (base i).heap.environments.size := by
  have present := i.scopeRead
  unfold checkedEnvironment Heap.environment? at present
  cases h : i.base.heap.environments[i.scope]? with
  | none => simp [h] at present
  | some environment =>
    exact Array.getElem?_eq_some_iff.mp h |>.1

theorem checked_local (i : Inputs) (objects : Array JSObject) (j : Value) :
    checkedEnvironment (sourceHeap i objects j) (localIndex (base i)) =
      .ok ⟨.declarative (localBindings i j),some (scope i)⟩ := by
  simp [sourceHeap,localIndex,checkedEnvironment,Heap.environment?]

theorem checked_library (i : Inputs) (objects : Array JSObject) (j : Value) :
    checkedEnvironment (sourceHeap i objects j) (scope i) =
      .ok ⟨.declarative (libraryBindings i),libraryOuter i⟩ := by
  have different : i.scope ≠ i.base.heap.environments.size := Nat.ne_of_lt (scope_bound i)
  simpa only [checkedEnvironment,Heap.environment?,sourceHeap,Array.getElem?_push,if_neg different,base,scope,libraryBindings,libraryOuter] using i.scopeRead

theorem library_contains_m (i : Inputs) : (libraryBindings i).any (fun b => b.name == "m") = true := i.mixkeyDeclared
theorem library_contains_l (i : Inputs) : (libraryBindings i).any (fun b => b.name == "l") = true := i.flattenDeclared

theorem library_read_m (i : Inputs) (objects : Array JSObject) (j : Value) :
    readBinding (sourceHeap i objects j) (scope i) "m" = .ok (.object (mixkey i)) := by
  have original := i.mixkeyRead
  unfold readBinding at original ⊢
  rw [i.scopeRead] at original
  rw [checked_library]
  exact original

theorem library_read_l (i : Inputs) (objects : Array JSObject) (j : Value) :
    readBinding (sourceHeap i objects j) (scope i) "l" = .ok (.object (flatten i)) := by
  have original := i.flattenRead
  unfold readBinding at original ⊢
  rw [i.scopeRead] at original
  rw [checked_library]
  exact original

theorem read_a (i : Inputs) (objects : Array JSObject) (j : Value) :
    readBinding (sourceHeap i objects j) (localIndex (base i)) "a" = .ok (.string (seed i)) := by
  simp [readBinding,checked_local,localBindings,SeedrandomInvocation.locals,Except.bind,bind,Except.pure,pure]

theorem read_f (i : Inputs) (objects : Array JSObject) (j : Value) :
    readBinding (sourceHeap i objects j) (localIndex (base i)) "f" = .ok .undefined := by
  simp [readBinding,checked_local,localBindings,SeedrandomInvocation.locals,Except.bind,bind,Except.pure,pure]

theorem read_arguments (i : Inputs) (objects : Array JSObject) (j : Value) :
    readBinding (sourceHeap i objects j) (localIndex (base i)) "arguments" = .ok (.object (argumentIndex (base i))) := by
  simp [readBinding,checked_local,localBindings,SeedrandomInvocation.locals,Except.bind,bind,Except.pure,pure]

theorem read_j (i : Inputs) (objects : Array JSObject) (j : Value) :
    readBinding (sourceHeap i objects j) (localIndex (base i)) "j" = .ok j := by
  simp [readBinding,checked_local,localBindings,SeedrandomInvocation.locals,Except.bind,bind,Except.pure,pure]

theorem write_j (i : Inputs) (objects : Array JSObject) (j value : Value) :
    setBinding (sourceHeap i objects j) (localIndex (base i)) "j" value false =
      .ok (sourceHeap i objects value) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,checked_local,localBindings,SeedrandomInvocation.locals,sourceHeap,replaceEnvironment,Heap.writeEnvironment,
    localIndex,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem source_environment_size (i : Inputs) (objects : Array JSObject) (j : Value) :
    (sourceHeap i objects j).environments.size = (base i).heap.environments.size+1 := by simp [sourceHeap]

theorem source_allocate (i : Inputs) (objects : Array JSObject) (j : Value) (object : JSObject) :
    Heap.allocateObject (sourceHeap i objects j) object =
      (objects.size,sourceHeap i (objects.push object) j) := rfl

theorem arguments_lookup (i : Inputs) (extra : JSObject) (j : Value) :
    lookupProperty (sourceHeap i ((initialObjects i).push extra) j) (argumentIndex (base i)) (JSString.ofString "0") =
      .ok (some (.data (.string (seed i)) true true true)) := by
  simp [lookupProperty,sourceHeap,initialObjects,argumentIndex,argumentObject,
    findProperty,checkedObject,Heap.object?,ownProperty,Array.getElem?_push,
    argumentsCalleeUnknown,Except.bind,bind,Except.pure,pure]

theorem arguments_present (i : Inputs) (extra : JSObject) (j : Value) :
    binaryWithHeap (sourceHeap i ((initialObjects i).push extra) j) .inOp (.number Number.positiveZero)
      (.object (argumentIndex (base i))) = .ok (.boolean true) := by
  simp [binaryWithHeap,SeedrandomInvocation.zero_to_string,arguments_lookup,Except.bind,bind,Except.pure,pure]

theorem arguments_present_literal (i : Inputs) (extra : JSObject) (j : Value) :
    binaryWithHeap (sourceHeap i ((initialObjects i).push extra) j) .inOp (.number 0)
      (.object (argumentIndex (base i))) = .ok (.boolean true) := by
  simpa only [Number.positiveZero] using arguments_present i extra j

def remainingVariables : List (String × Option Expr) := match body.headD .empty with
  | .variable ds => ds.drop 2
  | _ => []

def atFlatten (i : Inputs) : Machine := {
  sourceStart i with
  heap := sourceHeap i ((initialObjects i).push (SeedrandomFlatten.emptyArray (base i))) (.object (initialObjects i).size)
  control := .invoke (.object (flatten i)) .undefined [.string (seed i),.number 4613937818241073152] false
  continuation := .callArguments (.object (mixkey i)) .undefined [] [.identifier "j"] false ::
    .assignmentRight .assign ⟨.environment (localIndex (base i)) "p",false⟩ none ::
    .variableWrite remainingVariables :: .statementList (body.drop 1) none ::
    .callBoundary (base i).context none :: (base i).continuation }

theorem source_locals (i : Inputs) : SeedrandomInvocation.locals (base i) (seed i) =
    [{name := "a",value := .string (seed i)},{name := "f"},
      {name := "arguments",value := .object (argumentIndex (base i))}] := rfl
attribute [local cbv_eval] source_locals

attribute [local cbv_opaque] base scope receiver callee seed mixkey flatten libraryBindings libraryOuter
attribute [local cbv_opaque] sourceHeap initialObjects checkedEnvironment readBinding setBinding Heap.allocateObject binaryWithHeap
attribute [local cbv_opaque] Array.push Array.size
attribute [local cbv_eval] Array.size_push
attribute [local cbv_eval] checked_local checked_library library_contains_m library_contains_l library_read_m library_read_l
attribute [local cbv_eval] read_a read_f read_arguments read_j write_j source_environment_size source_allocate arguments_present arguments_present_literal

theorem actual_flatten_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (38+fuel) (sourceStart i) = Builtins.run fuel (atFlatten i) := by
  change Builtins.run (38+fuel) {sourceStart i with heap := sourceHeap i (initialObjects i) .undefined} = _
  rw [Nat.add_comm 38 fuel]
  cbv
  simp only [source_environment_size]
  cbv
  all_goals (simp only [source_environment_size]; cbv)
  all_goals (simp only [arguments_present_literal]; cbv)

theorem atFlatten_extends (i : Inputs) : HeapExtension.Extends (base i).heap (atFlatten i).heap := by
  let first := ((base i).heap.allocateObject (argumentObject (base i) (seed i) (callee i))).2
  let second := (first.allocateObject (SeedrandomFlatten.emptyArray (base i))).2
  have left : HeapExtension.Extends (base i).heap first := HeapExtension.append_object _ _
  have right : HeapExtension.Extends first second := HeapExtension.append_object _ _
  exact HeapExtension.trans (HeapExtension.trans left right)
    (HeapExtension.same_objects (before := second) (after := (atFlatten i).heap) rfl)

theorem flatten_bare_prepare (machine : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    prepareCall (callee := some callee) machine (SeedrandomFlatten.closure scope) .undefined
      [.string seed,.number 4613937818241073152] none =
      .ok (SeedrandomFlatten.prepared machine scope machine.globalObject seed callee) := by
  exact SeedrandomFlatten.actual_prepare machine scope machine.globalObject seed callee

theorem actual_flatten_step (i : Inputs) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i) = .ok object)
    (kind : object.kind = .function (SeedrandomFlatten.closure (scope i))) :
    Builtins.builtinStep (atFlatten i) =
      SeedrandomFlatten.prepared (atFlatten i) (scope i) (base i).globalObject (seed i) (flatten i) := by
  have presentAfter := HeapExtension.checked_object (atFlatten_extends i) _ _ present
  change {invoke (atFlatten i) (.object (flatten i)) .undefined [.string (seed i),.number 4613937818241073152] false
    with elapsed := (base i).elapsed} = _
  simp only [invoke,presentAfter,kind,checked,flatten_bare_prepare]
  rfl

def afterFlatten (i : Inputs) : Machine := SeedrandomFlatten.returned (atFlatten i) (scope i) (seed i) (flatten i)

theorem actual_flatten_return (i : Inputs) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i) = .ok object)
    (kind : object.kind = .function (SeedrandomFlatten.closure (scope i))) (fuel : Nat) :
    Builtins.run (78+fuel) (atFlatten i) = Builtins.run fuel (afterFlatten i) := by
  rw [show 78+fuel = (77+fuel)+1 by omega]
  change Builtins.run (77+fuel) (Builtins.builtinStep (atFlatten i)) = _
  rw [actual_flatten_step _ _ present kind,SeedrandomFlatten.actual_prepared_return]
  rfl

theorem actual_seedrandom_string_path (i : Inputs) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i) = .ok object)
    (kind : object.kind = .function (SeedrandomFlatten.closure (scope i))) (fuel : Nat) :
    Builtins.run (123+fuel) (prepared (base i) (scope i) (receiver i) (seed i) (callee i)) =
      Builtins.run fuel (afterFlatten i) := by
  calc
    _ = Builtins.run (116+fuel) (sourceStart i) := by
      simpa only [← Nat.add_assoc,sourceStart] using actual_hoist (base i) (scope i) (receiver i) (seed i) (callee i) (116+fuel)
    _ = Builtins.run (78+fuel) (atFlatten i) := by
      simpa only [← Nat.add_assoc] using actual_flatten_prefix i (78+fuel)
    _ = _ := actual_flatten_return i object present kind fuel

theorem afterFlatten_elapsed (i : Inputs) : (afterFlatten i).elapsed = (base i).elapsed := rfl

theorem afterFlatten_free_draws (i : Inputs) : (afterFlatten i).freeDrawCount = (base i).freeDrawCount := rfl

def retainedHeap (i : Inputs) : Heap := (afterFlatten i).heap

theorem retained_checked_local (i : Inputs) :
    checkedEnvironment (retainedHeap i) (localIndex (base i)) =
      .ok ⟨.declarative (localBindings i (.object (initialObjects i).size)),some (scope i)⟩ := by
  have bound : localIndex (base i) < (atFlatten i).heap.environments.size := by
    simp [localIndex,atFlatten,sourceHeap]
  have same := SeedrandomFlatten.returned_original_environment (atFlatten i) (scope i) (seed i) (flatten i)
    (localIndex (base i)) bound
  change checkedEnvironment (SeedrandomFlatten.returned (atFlatten i) (scope i) (seed i) (flatten i)).heap _ = _
  unfold checkedEnvironment Heap.environment?
  rw [same]
  exact checked_local i _ _

theorem retained_read_j (i : Inputs) :
    readBinding (retainedHeap i) (localIndex (base i)) "j" = .ok (.object (initialObjects i).size) := by
  simp [readBinding,retained_checked_local,localBindings,SeedrandomInvocation.locals,Except.bind,bind,Except.pure,pure]

def afterFlattenView (i : Inputs) : Machine := {
  atFlatten i with
  heap := retainedHeap i
  control := .expressionResult (.value (.string (seed i))) }

theorem afterFlatten_view (i : Inputs) : afterFlatten i = afterFlattenView i := rfl

def atMixkey (i : Inputs) : Machine := {
  afterFlattenView i with
  control := .invoke (.object (mixkey i)) .undefined [.string (seed i),.object (initialObjects i).size] false
  continuation := .assignmentRight .assign ⟨.environment (localIndex (base i)) "p",false⟩ none ::
    .variableWrite remainingVariables :: .statementList (body.drop 1) none ::
    .callBoundary (base i).context none :: (base i).continuation }

attribute [local cbv_opaque] retainedHeap
attribute [local cbv_eval] retained_checked_local retained_read_j

theorem actual_mixkey_arguments (i : Inputs) (fuel : Nat) :
    Builtins.run (5+fuel) (afterFlatten i) = Builtins.run fuel (atMixkey i) := by
  rw [afterFlatten_view]
  rw [Nat.add_comm 5 fuel]
  cbv

theorem actual_seedrandom_to_mixkey (i : Inputs) (object : JSObject)
    (present : checkedObject (base i).heap (flatten i) = .ok object)
    (kind : object.kind = .function (SeedrandomFlatten.closure (scope i))) (fuel : Nat) :
    Builtins.run (128+fuel) (prepared (base i) (scope i) (receiver i) (seed i) (callee i)) =
      Builtins.run fuel (atMixkey i) := by
  calc
    _ = Builtins.run (5+fuel) (afterFlatten i) := by
      simpa only [← Nat.add_assoc] using actual_seedrandom_string_path i object present kind (5+fuel)
    _ = _ := actual_mixkey_arguments i fuel

theorem atMixkey_extends (i : Inputs) : HeapExtension.Extends (base i).heap (atMixkey i).heap := by
  have extended : HeapExtension.Extends (atFlatten i).heap (afterFlatten i).heap := by
    constructor
    · simp [afterFlatten,SeedrandomFlatten.returned,SeedrandomFlatten.bodyHeap,
        SeedrandomFlatten.resultObjects,SeedrandomFlatten.objectsWithArgument]
      exact Nat.le_add_right _ 3
    · intro id object found
      have bound := Array.getElem?_eq_some_iff.mp found |>.1
      have preserved := SeedrandomFlatten.returned_original_object (atFlatten i) (scope i) (seed i) (flatten i) id bound
      simpa only [afterFlatten,Heap.object?,preserved] using found
  exact HeapExtension.trans (atFlatten_extends i) extended

theorem atMixkey_preserves_property (i : Inputs) (id : ObjectId) (name : JSString) (descriptor : Option PropertyDescriptor)
    (present : lookupProperty (base i).heap id name = .ok descriptor) :
    lookupProperty (atMixkey i).heap id name = .ok descriptor :=
  HeapExtension.lookup_property (atMixkey_extends i) _ _ _ present

theorem atMixkey_arguments (i : Inputs) :
    (atMixkey i).control = .invoke (.object (mixkey i)) .undefined [.string (seed i),.object (initialObjects i).size] false := rfl

theorem atMixkey_elapsed (i : Inputs) : (atMixkey i).elapsed = (base i).elapsed := rfl

theorem atMixkey_free_draws (i : Inputs) : (atMixkey i).freeDrawCount = (base i).freeDrawCount := rfl

end CookieClicker.JavaScript.SeedrandomSetup

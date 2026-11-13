import CookieClicker.JavaScriptSeedrandomSyntax
import CookieClicker.JavaScriptBindingWrite
/-! The pinned flatten helper on a string seed takes its actual string branch.
Its object-recursion and entropy-related callers remain in the source syntax. -/
namespace CookieClicker.JavaScript.SeedrandomFlatten
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def body : List Stmt := match SeedrandomSyntax.flattenBody with | .block statements => statements | other => [other]
def closure (scope : EnvId) : FunctionClosure := ⟨some "l",["a","b"],body,scope,false,some SeedrandomSyntax.flattenText⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def initialLocals (base : Machine) (seed : JSString) : List Binding :=
  [{name := "a",value := .string seed},{name := "b",value := .number 4613937818241073152},
   {name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (seed : JSString) (callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a"),(JSString.ofString "1",localIndex base,"b")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.string seed) true true true⟩,
    ⟨JSString.ofString "1",.data (.number 4613937818241073152) true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false true⟩] ++ argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeap (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) (locals : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObject base seed callee)
  environments := base.heap.environments.push ⟨.declarative locals,some scope⟩ }
def prepared (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope seed callee (initialLocals base seed)
  context := ⟨localIndex base,localIndex base,.object receiver,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem actual_prepare (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    prepareCall (callee := some callee) base (closure scope) (.object receiver)
      [.string seed,.number 4613937818241073152] none = .ok (prepared base scope receiver seed callee) := by
  simp [prepareCall,closure,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    localIndex,argumentIndex,initialLocals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

def withE (base : Machine) (seed : JSString) : List Binding := initialLocals base seed ++ [{name := "e"}]
def withC (base : Machine) (seed : JSString) : List Binding := withE base seed ++ [{name := "c"}]
def withD (base : Machine) (seed : JSString) : List Binding := withC base seed ++ [{name := "d"}]

theorem hoist_e (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed callee (initialLocals base seed)) (localIndex base) "e" .undefined false =
      .ok (allocatedHeap base scope seed callee (withE base seed)) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withE,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem hoist_c (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed callee (withE base seed)) (localIndex base) "c" .undefined false =
      .ok (allocatedHeap base scope seed callee (withC base seed)) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withE,withC,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

theorem hoist_d (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    defineBinding (allocatedHeap base scope seed callee (withC base seed)) (localIndex base) "d" .undefined false =
      .ok (allocatedHeap base scope seed callee (withD base seed)) := by
  simp [defineBinding,allocatedHeap,localIndex,initialLocals,withE,withC,withD,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind]

def hoisted (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  prepared base scope receiver seed callee with
  heap := allocatedHeap base scope seed callee (withD base seed)
  control := .declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex initialLocals withE withC withD defineBinding
attribute [local cbv_eval] hoist_e hoist_c hoist_d

theorem actual_hoist (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (13+fuel) (prepared base scope receiver seed callee) =
      Builtins.run fuel (hoisted base scope receiver seed callee) := by
  rw [Nat.add_comm 13 fuel]
  cbv
def scopeLocals (base : Machine) (seed : JSString) (c d : Value) : List Binding :=
  initialLocals base seed ++ [{name := "e"},{name := "c",value := c},{name := "d",value := d}]
def bodyHeap (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d : Value) : Heap := {
  objects := objects
  environments := base.heap.environments.push ⟨.declarative (scopeLocals base seed c d),some scope⟩ }
def objectsWithArgument (base : Machine) (seed : JSString) (callee : ObjectId) : Array JSObject :=
  base.heap.objects.push (argumentObject base seed callee)
def emptyArray (base : Machine) : JSObject := {
  kind := .array
  prototype := base.arrayPrototype
  properties := [⟨JSString.ofString "length",.data (.number Number.positiveZero) true false false⟩] }
def typeWrapper (base : Machine) : JSObject := {
  kind := .stringWrapper (JSString.ofString "string")
  prototype := base.stringPrototype }
def resultObjects (base : Machine) (seed : JSString) (callee : ObjectId) : Array JSObject :=
  ((objectsWithArgument base seed callee).push (emptyArray base)).push (typeWrapper base)
def afterBody (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  hoisted base scope receiver seed callee with
  heap := bodyHeap base scope seed (resultObjects base seed callee)
    (.object (objectsWithArgument base seed callee).size) (.string (JSString.ofString "s"))
  control := .completion (.return (.string seed))
  continuation := .statementList [] none :: .callBoundary base.context none :: base.continuation }

theorem checked_body_local (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d : Value) :
    checkedEnvironment (bodyHeap base scope seed objects c d) (localIndex base) =
      .ok ⟨.declarative (scopeLocals base seed c d),some scope⟩ := by
  simp [bodyHeap,localIndex,checkedEnvironment,Heap.environment?]

theorem body_environment_size (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d : Value) :
    (bodyHeap base scope seed objects c d).environments.size = base.heap.environments.size+1 := by
  simp [bodyHeap]

theorem body_allocate (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d : Value) (object : JSObject) :
    Heap.allocateObject (bodyHeap base scope seed objects c d) object =
      (objects.size,bodyHeap base scope seed (objects.push object) c d) := rfl

theorem write_c (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d value : Value) :
    setBinding (bodyHeap base scope seed objects c d) (localIndex base) "c" value false =
      .ok (bodyHeap base scope seed objects value d) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,checked_body_local,scopeLocals,initialLocals,bodyHeap,replaceEnvironment,Heap.writeEnvironment,
    localIndex,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem write_d (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d value : Value) :
    setBinding (bodyHeap base scope seed objects c d) (localIndex base) "d" value false =
      .ok (bodyHeap base scope seed objects c value) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,checked_body_local,scopeLocals,initialLocals,bodyHeap,replaceEnvironment,Heap.writeEnvironment,
    localIndex,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem checked_array (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d : Value) :
    checkedObject (bodyHeap base scope seed ((objects.push (emptyArray base)).push (typeWrapper base)) c d) objects.size =
      .ok (emptyArray base) := by
  simp [checkedObject,bodyHeap,Heap.object?,Array.getElem?_push,show objects.size ≠ objects.size+1 by omega]

theorem array_length_zero (base : Machine) (scope : EnvId) (seed : JSString) (objects : Array JSObject) (c d : Value) :
    lookupProperty (bodyHeap base scope seed ((objects.push (emptyArray base)).push (typeWrapper base)) c d) objects.size
      (JSString.ofString "length") = .ok (some (.data (.number Number.positiveZero) true false false)) := by
  simp [lookupProperty,bodyHeap,findProperty,checkedObject,Heap.object?,Array.getElem?_push,emptyArray,ownProperty,
    show objects.size ≠ objects.size+1 by omega,Except.bind,bind,Except.pure,pure]

theorem read_type_zero (machine : Machine) :
    readProperty machine (.string [115,116,114,105,110,103]) [48] =
      {machine with
        heap := {machine.heap with objects := machine.heap.objects.push ({kind := .stringWrapper [115,116,114,105,110,103],prototype := machine.stringPrototype} : JSObject)}
        control := .expressionResult (.value (.string [115]))} := by
  simp [readProperty,toObject,Heap.allocateObject,readObjectProperty,checked,checkedObject,
    Heap.object?,lookupProperty,findProperty,ownProperty,arrayIndex,result,JSString.ofString,
    Except.bind,bind,Except.pure,pure]

attribute [local cbv_opaque] Array.push Array.size
attribute [local cbv_eval] Array.size_push
attribute [local cbv_opaque] bodyHeap objectsWithArgument setBinding Heap.allocateObject checkedEnvironment checkedObject lookupProperty readProperty
attribute [local cbv_eval] read_type_zero checked_body_local body_environment_size body_allocate write_c write_d


theorem initial_locals (base : Machine) (seed : JSString) :
    initialLocals base seed = [{name := "a",value := .string seed},{name := "b",value := .number 4613937818241073152},
      {name := "arguments",value := .object (argumentIndex base)}] := rfl
attribute [local cbv_eval] initial_locals

def atType (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  hoisted base scope receiver seed callee with
  heap := bodyHeap base scope seed ((objectsWithArgument base seed callee).push (emptyArray base))
    (.object (objectsWithArgument base seed callee).size) .undefined
  control := .getValue ⟨.property (.string (JSString.ofString "string")) (JSString.ofString "0"),false⟩
  continuation := .assignmentRight .assign ⟨.environment (localIndex base) "d",false⟩ none ::
    .variableWrite [] :: .statementList (body.drop 1) none ::
    .callBoundary base.context none :: base.continuation }

theorem actual_type_prefix (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (16+fuel) (hoisted base scope receiver seed callee) =
      Builtins.run fuel (atType base scope receiver seed callee) := by
  change Builtins.run (16+fuel) {hoisted base scope receiver seed callee with
    heap := bodyHeap base scope seed (objectsWithArgument base seed callee) .undefined .undefined} = _
  rw [Nat.add_comm 16 fuel]
  cbv

def afterType (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  atType base scope receiver seed callee with
  heap := bodyHeap base scope seed (resultObjects base seed callee)
    (.object (objectsWithArgument base seed callee).size) .undefined
  control := .expressionResult (.value (.string (JSString.ofString "s"))) }

theorem actual_type_step (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    Builtins.builtinStep (atType base scope receiver seed callee) = afterType base scope receiver seed callee := by
  change {readProperty (atType base scope receiver seed callee)
    (.string (JSString.ofString "string")) (JSString.ofString "0") with elapsed := base.elapsed} = _
  rw [show JSString.ofString "string" = [115,116,114,105,110,103] by rfl,
    show JSString.ofString "0" = [48] by rfl,read_type_zero]
  rfl

def returnAlternative : Expr := match (body[2]? : Option Stmt) with
  | some (.return (some (.conditional _ _ alternate))) => alternate
  | _ => .literal .null

def atLength (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  afterBody base scope receiver seed callee with
  control := .getValue ⟨.property (.object (objectsWithArgument base seed callee).size) (JSString.ofString "length"),false⟩
  continuation := .conditional (.identifier "c") returnAlternative :: .returnValue :: .statementList [] none ::
    .callBoundary base.context none :: base.continuation }

theorem actual_branch_prefix (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (28+fuel) (afterType base scope receiver seed callee) =
      Builtins.run fuel (atLength base scope receiver seed callee) := by
  rw [Nat.add_comm 28 fuel]
  cbv

def afterLength (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  atLength base scope receiver seed callee with control := .expressionResult (.value (.number Number.positiveZero)) }

theorem actual_length_step (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    Builtins.builtinStep (atLength base scope receiver seed callee) = afterLength base scope receiver seed callee := by
  have present : checkedObject (atLength base scope receiver seed callee).heap
      (objectsWithArgument base seed callee).size = .ok (emptyArray base) :=
    checked_array base scope seed (objectsWithArgument base seed callee) _ _
  have property : lookupProperty (atLength base scope receiver seed callee).heap
      (objectsWithArgument base seed callee).size (JSString.ofString "length") =
      .ok (some (.data (.number Number.positiveZero) true false false)) :=
    array_length_zero base scope seed (objectsWithArgument base seed callee) _ _
  have get : readProperty (atLength base scope receiver seed callee)
      (.object (objectsWithArgument base seed callee).size) (JSString.ofString "length") =
      afterLength base scope receiver seed callee := by
    simp only [readProperty,toObject,checked,readObjectProperty,present,property,emptyArray,result]
    rfl
  change {readProperty (atLength base scope receiver seed callee)
    (.object (objectsWithArgument base seed callee).size) (JSString.ofString "length") with elapsed := base.elapsed} = _
  rw [get]
  rfl

theorem actual_return_suffix (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (16+fuel) (afterLength base scope receiver seed callee) =
      Builtins.run fuel (afterBody base scope receiver seed callee) := by
  rw [Nat.add_comm 16 fuel]
  cbv

theorem actual_type_resume (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) (atType base scope receiver seed callee) =
      Builtins.run fuel (afterType base scope receiver seed callee) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (atType base scope receiver seed callee)) = _
  rw [actual_type_step]

theorem actual_length_resume (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) (atLength base scope receiver seed callee) =
      Builtins.run fuel (afterLength base scope receiver seed callee) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (atLength base scope receiver seed callee)) = _
  rw [actual_length_step]

theorem actual_body_return (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (62+fuel) (hoisted base scope receiver seed callee) =
      Builtins.run fuel (afterBody base scope receiver seed callee) := by
  calc
    _ = Builtins.run (46+fuel) (atType base scope receiver seed callee) := by
      simpa only [← Nat.add_assoc] using actual_type_prefix base scope receiver seed callee (46+fuel)
    _ = Builtins.run (45+fuel) (afterType base scope receiver seed callee) := by
      simpa only [← Nat.add_assoc] using actual_type_resume base scope receiver seed callee (45+fuel)
    _ = Builtins.run (17+fuel) (atLength base scope receiver seed callee) := by
      simpa only [← Nat.add_assoc] using actual_branch_prefix base scope receiver seed callee (17+fuel)
    _ = Builtins.run (16+fuel) (afterLength base scope receiver seed callee) := by
      simpa only [← Nat.add_assoc] using actual_length_resume base scope receiver seed callee (16+fuel)
    _ = _ := actual_return_suffix base scope receiver seed callee fuel

def returned (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  base with
  heap := bodyHeap base scope seed (resultObjects base seed callee)
    (.object (objectsWithArgument base seed callee).size) (.string (JSString.ofString "s"))
  control := .expressionResult (.value (.string seed)) }

theorem actual_restore_caller (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (2+fuel) (afterBody base scope receiver seed callee) =
      Builtins.run fuel (returned base scope seed callee) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem actual_prepared_return (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) (fuel : Nat) :
    Builtins.run (77+fuel) (prepared base scope receiver seed callee) =
      Builtins.run fuel (returned base scope seed callee) := by
  calc
    _ = Builtins.run (64+fuel) (hoisted base scope receiver seed callee) := by
      simpa only [← Nat.add_assoc] using actual_hoist base scope receiver seed callee (64+fuel)
    _ = Builtins.run (2+fuel) (afterBody base scope receiver seed callee) := by
      simpa only [← Nat.add_assoc] using actual_body_return base scope receiver seed callee (2+fuel)
    _ = _ := actual_restore_caller base scope receiver seed callee fuel

theorem actual_invoke (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee = .ok object)
    (kind : object.kind = .function (closure scope)) :
    invoke base (.object callee) (.object receiver) [.string seed,.number 4613937818241073152] false =
      prepared base scope receiver seed callee := by
  simp [invoke,present,kind,checked,actual_prepare]

def callStart (base : Machine) (receiver : ObjectId) (seed : JSString) (callee : ObjectId) : Machine := {
  base with control := .invoke (.object callee) (.object receiver) [.string seed,.number 4613937818241073152] false }

theorem actual_call_step (base : Machine) (scope : EnvId) (receiver : ObjectId) (seed : JSString) (callee : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee = .ok object)
    (kind : object.kind = .function (closure scope)) :
    Builtins.builtinStep (callStart base receiver seed callee) = prepared base scope receiver seed callee := by
  change {invoke (callStart base receiver seed callee) (.object callee) (.object receiver)
    [.string seed,.number 4613937818241073152] false with elapsed := base.elapsed} = _
  rw [actual_invoke (callStart base receiver seed callee) scope receiver seed callee object present kind]
  rfl

theorem actual_source_call (base : Machine) (scope : EnvId) (receiver : ObjectId) (seed : JSString) (callee : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee = .ok object)
    (kind : object.kind = .function (closure scope)) (fuel : Nat) :
    Builtins.run (78+fuel) (callStart base receiver seed callee) = Builtins.run fuel (returned base scope seed callee) := by
  rw [show 78+fuel = (77+fuel)+1 by omega]
  change Builtins.run (77+fuel) (Builtins.builtinStep (callStart base receiver seed callee)) = _
  rw [actual_call_step _ _ _ _ _ _ present kind,actual_prepared_return]

theorem returned_original_object (base : Machine) (scope : EnvId) (seed : JSString) (callee id : ObjectId)
    (bound : id < base.heap.objects.size) :
    (returned base scope seed callee).heap.objects[id]? = base.heap.objects[id]? := by
  have first := Nat.ne_of_lt bound
  have second := Nat.ne_of_lt (Nat.lt.step bound)
  have third := Nat.ne_of_lt (Nat.lt.step (Nat.lt.step bound))
  simp [returned,bodyHeap,resultObjects,objectsWithArgument,Array.getElem?_push,first,second,third]

theorem returned_original_environment (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) (id : EnvId)
    (bound : id < base.heap.environments.size) :
    (returned base scope seed callee).heap.environments[id]? = base.heap.environments[id]? := by
  have different := Nat.ne_of_lt bound
  simp [returned,bodyHeap,Array.getElem?_push,different]

theorem returned_caller_context (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    (returned base scope seed callee).context = base.context := rfl

theorem returned_caller_continuation (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    (returned base scope seed callee).continuation = base.continuation := rfl

theorem returned_elapsed (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    (returned base scope seed callee).elapsed = base.elapsed := rfl

theorem returned_free_draws (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) :
    (returned base scope seed callee).freeDrawCount = base.freeDrawCount := rfl

end CookieClicker.JavaScript.SeedrandomFlatten

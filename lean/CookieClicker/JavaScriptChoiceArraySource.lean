import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptChoiceSyntax
import CookieClicker.JavaScriptRandomSmallChoiceBridge
import CookieClicker.JavaScriptExecution

/-! The intact pinned choose callback body at an IID53 Math.random boundary.
The entry contract retains arbitrary native object identities and the complete
lexical Math path. All source reads/calls use the actual Builtins driver.
Invocation/argument allocation, initialization, generator-phase preservation and
composition with clickLump remain separate obligations.
-/
namespace CookieClicker.JavaScript.ChoiceArraySource
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

structure Inputs where
  length : Nat
  heap : Heap
  localScope : Nat
  globalScope : Nat
  depth : Nat
  window : ObjectId
  math : ObjectId
  random : ObjectId
  floor : ObjectId
  array : ObjectId
  windowObject : JSObject
  mathObject : JSObject
  randomObject : JSObject
  floorObject : JSObject
  arrayObject : JSObject
  bindings : List Binding
  outer : Option EnvId
  localRead : checkedEnvironment heap localScope = .ok ⟨.declarative bindings,outer⟩
  arrDeclared : bindings.any (fun b => b.name == "arr") = true
  arrRead : readBinding heap localScope "arr" = .ok (.object array)
  mathPath : HasEnvironment.DeclarativePath heap.environments "Math" localScope globalScope depth
  depthBound : depth ≤ heap.environments.size
  globalRead : checkedEnvironment heap globalScope = .ok ⟨.object window false,none⟩
  windowRead : checkedObject heap window = .ok windowObject
  windowKind : windowObject.kind = .host "Window" 0
  mathRead : checkedObject heap math = .ok mathObject
  mathKind : mathObject.kind = .ordinary
  randomRead : checkedObject heap random = .ok randomObject
  randomKind : randomObject.kind = .builtin ⟨"Math","random"⟩
  floorRead : checkedObject heap floor = .ok floorObject
  floorKind : floorObject.kind = .builtin ⟨"Math","floor"⟩
  arrayRead : checkedObject heap array = .ok arrayObject
  arrayKind : arrayObject.kind = .array
  windowMath : lookupProperty heap window (JSString.ofString "Math") = .ok (some (.data (.object math) true false true))
  mathRandom : lookupProperty heap math (JSString.ofString "random") = .ok (some (.data (.object random) true false true))
  mathFloor : lookupProperty heap math (JSString.ofString "floor") = .ok (some (.data (.object floor) true false true))
  arrayLength : lookupProperty heap array (JSString.ofString "length") = .ok (some (.data (.number (Number.ofNat length)) true false false))

def smallKey : Nat → JSString
  | 0 => JSString.ofString "0"
  | 1 => JSString.ofString "1"
  | 2 => JSString.ofString "2"
  | 3 => JSString.ofString "3"
  | 4 => JSString.ofString "4"
  | _ => JSString.ofString "5"

theorem small_index_string : ∀ index : Fin 6,
    toJSString (.number (Number.ofNat index.val)) =
      .ok (smallKey index.val) := by
  intro ⟨n,bound⟩
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases cases with h|h|h|h|h|h <;> subst n <;> simp only [Fin.mk_val] <;> rfl

def heap (i : Inputs) : Heap := i.heap

def localScope (i : Inputs) : Nat := i.localScope

def globalScope (i : Inputs) : Nat := i.globalScope

def window (i : Inputs) : ObjectId := i.window

def math (i : Inputs) : ObjectId := i.math

def random (i : Inputs) : ObjectId := i.random

def floor (i : Inputs) : ObjectId := i.floor

def array (i : Inputs) : ObjectId := i.array

def windowObject (i : Inputs) : JSObject := i.windowObject

def mathObject (i : Inputs) : JSObject := i.mathObject

def randomObject (i : Inputs) : JSObject := i.randomObject

def floorObject (i : Inputs) : JSObject := i.floorObject

def arrayObject (i : Inputs) : JSObject := i.arrayObject

def ambient (base : Machine) (i : Inputs) : Machine := {base with
  heap := heap i
  context := ⟨localScope i,localScope i,base.context.thisValue,false⟩
  globalObject := window i
  objectEnvironmentExclusions := []}

theorem checked_local (i : Inputs) : checkedEnvironment (heap i) (localScope i) = .ok ⟨.declarative i.bindings,i.outer⟩ := i.localRead
theorem checked_global (i : Inputs) : checkedEnvironment (heap i) (globalScope i) = .ok ⟨.object (window i) false,none⟩ := i.globalRead
theorem read_arr (i : Inputs) : readBinding (heap i) (localScope i) "arr" = .ok (.object (array i)) := i.arrRead

theorem checked_window (i : Inputs) : checkedObject (heap i) (window i) = .ok (windowObject i) := i.windowRead
theorem window_kind (i : Inputs) : (windowObject i).kind = .host "Window" 0 := i.windowKind

theorem checked_math (i : Inputs) : checkedObject (heap i) (math i) = .ok (mathObject i) := i.mathRead
theorem math_kind (i : Inputs) : (mathObject i).kind = .ordinary := i.mathKind

theorem checked_random (i : Inputs) : checkedObject (heap i) (random i) = .ok (randomObject i) := i.randomRead
theorem random_kind (i : Inputs) : (randomObject i).kind = .builtin ⟨"Math","random"⟩ := i.randomKind

theorem checked_floor (i : Inputs) : checkedObject (heap i) (floor i) = .ok (floorObject i) := i.floorRead
theorem floor_kind (i : Inputs) : (floorObject i).kind = .builtin ⟨"Math","floor"⟩ := i.floorKind

theorem checked_array (i : Inputs) : checkedObject (heap i) (array i) = .ok (arrayObject i) := i.arrayRead
theorem array_kind (i : Inputs) : (arrayObject i).kind = .array := i.arrayKind

theorem windowMath_read (i : Inputs) : lookupProperty (heap i) (window i) (JSString.ofString "Math") = .ok (some (.data (.object (math i)) true false true)) := i.windowMath

theorem mathRandom_read (i : Inputs) : lookupProperty (heap i) (math i) (JSString.ofString "random") = .ok (some (.data (.object (random i)) true false true)) := i.mathRandom

theorem mathFloor_read (i : Inputs) : lookupProperty (heap i) (math i) (JSString.ofString "floor") = .ok (some (.data (.object (floor i)) true false true)) := i.mathFloor

theorem arrayLength_read (i : Inputs) : lookupProperty (heap i) (array i) (JSString.ofString "length") = .ok (some (.data (.number (Number.ofNat i.length)) true false false)) := i.arrayLength

theorem identifier_math (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "Math" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (globalScope i) "Math",false⟩)} := by
  exact IdentifierPath.identifier (ambient base i) "Math" (globalScope i) i.depth (window i)
    (.data (.object (math i)) true false true) i.mathPath i.depthBound i.globalRead i.windowMath rfl

theorem identifier_arr (base : Machine) (i : Inputs) :
    Environment.identifier (ambient base i) "arr" =
      {ambient base i with control := .expressionResult (.reference ⟨.environment (localScope i) "arr",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _ i.localRead i.arrDeclared

theorem identifier_math_explicit (i : Inputs)
    (thisValue : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat)
    : Environment.identifier {
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} "Math" =
    {({
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (globalScope i) "Math",false⟩)} := by
  exact identifier_math {
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} i

theorem identifier_arr_explicit (i : Inputs)
    (thisValue : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat)
    : Environment.identifier {
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} "arr" =
    {({
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (localScope i) "arr",false⟩)} := by
  exact identifier_arr {
      heap := heap i
      context := ⟨localScope i,localScope i,thisValue,false⟩
      globalObject := window i
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} i

def state (base : Machine) (i : Inputs) : Machine := {ambient base i with control := .statement ChoiceSyntax.body}

attribute [local cbv_opaque] heap localScope globalScope window math random floor array
attribute [local cbv_opaque] windowObject mathObject randomObject floorObject arrayObject
attribute [local cbv_opaque] JSString.ofString checkedObject lookupProperty Environment.identifier
attribute [local cbv_opaque] checkedEnvironment readBinding Number.mul Number.floor Number.ofNat
attribute [local cbv_eval] checked_local checked_global read_arr
attribute [local cbv_eval] checked_window window_kind checked_math math_kind checked_random random_kind checked_floor floor_kind checked_array array_kind
attribute [local cbv_eval] windowMath_read mathRandom_read mathFloor_read arrayLength_read

def request (base : Machine) (i : Inputs) : Machine := {ambient base i with
  control := .unresolved .freeRandom
  continuation :=
    .binaryLeft .multiply (.member (.identifier "arr") (.identifier "length") false) ::
    .callArguments (.object (floor i)) (.object (math i)) [] [] false ::
    .memberProperty (.object (array i)) ::
    .returnValue :: .statementList [] none :: base.continuation }

set_option pp.deepTerms false in
set_option pp.proofs false in
theorem request_prefix (base : Machine) (i : Inputs) :
    Builtins.run 28 (state base i) = request base i := by
  cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv

def resumed (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53) : Machine :=
  {request base i with
   control := .expressionResult (.value (.number (Random.encode draw)))
   freeDrawCount := base.freeDrawCount+1}

def returned (base : Machine) (i : Inputs) (value : Value) : Machine :=
  {ambient base i with
   control := .completion (.return value)
   continuation := base.continuation
   freeDrawCount := base.freeDrawCount+1}

attribute [local cbv_opaque] Random.encode toJSString

theorem resumed_at (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (index : UInt64) (key : JSString) (value : Value)
    (chosen : Number.floor (Number.mul (Random.encode draw) (Number.ofNat i.length)) = index)
    (stringIndex : toJSString (.number index) = .ok key)
    (selected : lookupProperty (heap i) (array i) key = .ok (some (.data value true true true)))
    (fuel : Nat) :
    Builtins.run (17+fuel) (resumed base i draw) = Builtins.run fuel (returned base i value) := by
  rw [Nat.add_comm 17 fuel]
  cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv
  try simp only [chosen,stringIndex,selected,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read]
  try cbv


open CookieClicker.FullGame.UniformRandom
open RandomSmallChoiceBridge

def Values (i : Inputs) (values : Nat → Value) : Prop :=
  ∀ index, index < i.length →
    lookupProperty (heap i) (array i) (smallKey index) =
      .ok (some (.data (values index) true true true))

theorem resumed_small_choice (base : Machine) (i : Inputs) (draw : Draw 53)
    (small : i.length=5 ∨ i.length=6) (values : Nat → Value)
    (selected : Values i values) (fuel : Nat) :
    Builtins.run (17+fuel) (resumed base i draw) =
      Builtins.run fuel (returned base i (values (projection i.length draw.val))) := by
  have valid : draw.val < denominator := draw.isLt
  have support := projection_support i.length draw.val small valid
  have six : projection i.length draw.val < 6 := by rcases small with h|h <;> omega
  have choice : Number.floor (Number.mul (Random.encode draw) (Number.ofNat i.length)) =
      Number.ofNat (projection i.length draw.val) := native_small_choice draw i.length small
  exact resumed_at base i draw (Number.ofNat (projection i.length draw.val))
    (smallKey (projection i.length draw.val))
    (values (projection i.length draw.val)) choice
    (small_index_string ⟨_,six⟩) (selected _ support) fuel

theorem source_small_choice (base : Machine) (i : Inputs) (draw : Draw 53)
    (small : i.length=5 ∨ i.length=6) (values : Nat → Value)
    (selected : Values i values) :
    Builtins.run 17 (resumed base i draw) =
      returned base i (values (projection i.length draw.val)) := by
  simpa only [Nat.add_zero,Builtins.run] using resumed_small_choice base i draw small values selected 0

theorem actual_draw_response (browser : Browser.State) (base : Machine) (i : Inputs)
    (draw : Draw 53) :
    (Execution.afterDraw {browser with machine := request base i} draw).machine = resumed base i draw := rfl

theorem actual_small_choice (browser : Browser.State) (base : Machine) (i : Inputs) (draw : Draw 53)
    (small : i.length=5 ∨ i.length=6) (values : Nat → Value)
    (selected : Values i values) :
    Builtins.run 17 (Execution.afterDraw {browser with machine := request base i} draw).machine =
      returned base i (values (projection i.length draw.val)) := by
  rw [actual_draw_response,source_small_choice base i draw small values selected]

def sourceEvent (base : Machine) (i : Inputs) (accept : Value → Bool) (index : Nat) : Bool :=
  if bound : index < size 53 then
    match (Builtins.run 17 (resumed base i ⟨index,bound⟩)).control with
    | .completion (.return value) => accept value
    | _ => false
  else false

def projectedEvent (c : Nat) (values : Nat → Value) (accept : Value → Bool) (index : Nat) : Bool :=
  if index < size 53 then accept (values (projection c index)) else false

theorem source_event_projection (base : Machine) (i : Inputs)
    (small : i.length=5 ∨ i.length=6) (values : Nat → Value)
    (selected : Values i values) (accept : Value → Bool) :
    sourceEvent base i accept = projectedEvent i.length values accept := by
  funext index
  by_cases bound : index < size 53
  · simp only [sourceEvent,bound,↓reduceDIte,source_small_choice base i _ small values selected,
      returned,projectedEvent,↓reduceIte]
  · simp only [sourceEvent,bound,↓reduceDIte,projectedEvent,↓reduceIte]

theorem source_event_mass (base : Machine) (i : Inputs)
    (small : i.length=5 ∨ i.length=6) (values : Nat → Value)
    (selected : Values i values) (accept : Value → Bool) :
    eventMass 53 (sourceEvent base i accept) =
      eventMass 53 (projectedEvent i.length values accept) := by
  rw [source_event_projection base i small values selected accept]

end CookieClicker.JavaScript.ChoiceArraySource

import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptChoiceSyntax
import CookieClicker.JavaScriptRandomChoiceBridge
import CookieClicker.JavaScriptExecution

/-! The intact pinned choose callback body at an IID53 Math.random boundary.
The entry contract retains arbitrary native object identities and the complete
lexical Math path. All source reads/calls use the actual Builtins driver.
Invocation/argument allocation, initialization, generator-phase preservation and
composition with clickLump remain separate obligations.
-/
namespace CookieClicker.JavaScript.ChoiceSource
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

structure Inputs where
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
  arrayLength : lookupProperty heap array (JSString.ofString "length") = .ok (some (.data (.number (Number.ofNat 2)) true false false))
  arrayZero : lookupProperty heap array (JSString.ofString "0") = .ok (some (.data (.number 0) true true true))
  arrayOne : lookupProperty heap array (JSString.ofString "1") = .ok (some (.data (.number Number.one) true true true))

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

theorem arrayLength_read (i : Inputs) : lookupProperty (heap i) (array i) (JSString.ofString "length") = .ok (some (.data (.number (Number.ofNat 2)) true false false)) := i.arrayLength

theorem arrayZero_read (i : Inputs) : lookupProperty (heap i) (array i) (JSString.ofString "0") = .ok (some (.data (.number 0) true true true)) := i.arrayZero

theorem arrayOne_read (i : Inputs) : lookupProperty (heap i) (array i) (JSString.ofString "1") = .ok (some (.data (.number Number.one) true true true)) := i.arrayOne

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
attribute [local cbv_eval] windowMath_read mathRandom_read mathFloor_read arrayLength_read arrayZero_read arrayOne_read

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
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv

def resumed (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53) : Machine :=
  {request base i with
   control := .expressionResult (.value (.number (Random.encode draw)))
   freeDrawCount := base.freeDrawCount+1}

def returned (base : Machine) (i : Inputs) (value : UInt64) : Machine :=
  {ambient base i with
   control := .completion (.return (.number value))
   continuation := base.continuation
   freeDrawCount := base.freeDrawCount+1}

theorem string_zero : toJSString (.number 0) = .ok (JSString.ofString "0") := by rfl
theorem string_one : toJSString (.number Number.one) = .ok (JSString.ofString "1") := by rfl

attribute [local cbv_opaque] Random.encode toJSString
attribute [local cbv_eval] string_zero string_one

theorem resumed_zero (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (chosen : Number.floor (Number.mul (Random.encode draw) (Number.ofNat 2)) = 0) (fuel : Nat) :
    Builtins.run (17+fuel) (resumed base i draw) = Builtins.run fuel (returned base i 0) := by
  rw [Nat.add_comm 17 fuel]
  cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
theorem resumed_one (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (chosen : Number.floor (Number.mul (Random.encode draw) (Number.ofNat 2)) = Number.one) (fuel : Nat) :
    Builtins.run (17+fuel) (resumed base i draw) = Builtins.run fuel (returned base i Number.one) := by
  rw [Nat.add_comm 17 fuel]
  cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv
  try simp only [chosen,string_zero,string_one,identifier_math_explicit,identifier_arr_explicit,checked_local,checked_global,read_arr,checked_window,window_kind,checked_math,math_kind,checked_random,random_kind,checked_floor,floor_kind,checked_array,array_kind,windowMath_read,mathRandom_read,mathFloor_read,arrayLength_read,arrayZero_read,arrayOne_read]
  try cbv

theorem resumed_draw (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (fuel : Nat) :
    Builtins.run (17+fuel) (resumed base i draw) =
      Builtins.run fuel (returned base i (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw))) := by
  have support := CookieClicker.FullGame.UniformRandom.choose_two_support draw
  have choice := RandomChoiceBridge.native_choose_two draw
  have cases : CookieClicker.FullGame.UniformRandom.chooseTwo draw=0 ∨
      CookieClicker.FullGame.UniformRandom.chooseTwo draw=1 := by omega
  rcases cases with h | h
  · rw [h]
    have selected : Number.floor (Number.mul (Random.encode draw) (Number.ofNat 2)) = 0 := by
      simpa only [h,show Number.ofNat 0=0 from rfl] using choice
    exact resumed_zero base i draw selected fuel
  · rw [h]
    have selected : Number.floor (Number.mul (Random.encode draw) (Number.ofNat 2)) = Number.one := by
      simpa only [h,show Number.ofNat 1=Number.one from rfl] using choice
    exact resumed_one base i draw selected fuel

theorem source_draw_result (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53) :
    Builtins.run 17 (resumed base i draw) =
      returned base i (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw)) := by
  simpa only [Nat.add_zero,Builtins.run] using resumed_draw base i draw 0

theorem source_success_iff (base : Machine) (i : Inputs) (draw : CookieClicker.FullGame.UniformRandom.Draw 53) :
    (Builtins.run 17 (resumed base i draw)).control = .completion (.return (.number Number.one)) ↔
      2^52 ≤ draw.val := by
  rw [source_draw_result]
  change (.completion (.return (.number (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw)))) : Control) =
      .completion (.return (.number Number.one)) ↔ _
  simp only [Control.completion.injEq,Completion.return.injEq,Value.number.injEq]
  rw [← RandomChoiceBridge.native_choose_two]
  exact RandomChoiceBridge.native_choose_two_success draw

theorem actual_draw_response (browser : Browser.State) (base : Machine) (i : Inputs)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53) :
    (Execution.afterDraw {browser with machine := request base i} draw).machine = resumed base i draw := by rfl

theorem actual_draw_body (browser : Browser.State) (base : Machine) (i : Inputs)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53) :
    Builtins.run 17 (Execution.afterDraw {browser with machine := request base i} draw).machine =
      returned base i (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw)) := by
  rw [actual_draw_response,source_draw_result]

def sourceSuccess (base : Machine) (i : Inputs) (index : Nat) : Bool :=
  if bound : index < CookieClicker.FullGame.UniformRandom.size 53 then
    match (Builtins.run 17 (resumed base i ⟨index,bound⟩)).control with
    | .completion (.return (.number value)) => value == Number.one
    | _ => false
  else false

theorem source_success_event (base : Machine) (i : Inputs) :
    sourceSuccess base i = CookieClicker.FullGame.UniformRandom.interval
      (CookieClicker.FullGame.UniformRandom.size 52) (CookieClicker.FullGame.UniformRandom.size 53) := by
  funext index
  by_cases bound : index < CookieClicker.FullGame.UniformRandom.size 53
  · simp only [sourceSuccess,bound,↓reduceDIte,source_draw_result,returned,
      CookieClicker.FullGame.UniformRandom.interval]
    have equivalence := RandomChoiceBridge.native_choose_two_success ⟨index,bound⟩
    rw [RandomChoiceBridge.native_choose_two] at equivalence
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,decide_eq_true_eq,bound,and_true,CookieClicker.FullGame.UniformRandom.size] using equivalence
  · simp [sourceSuccess,CookieClicker.FullGame.UniformRandom.interval,bound]

theorem actual_source_success_mass (base : Machine) (i : Inputs) :
    CookieClicker.FullGame.UniformRandom.eventMass 53 (sourceSuccess base i) = 1/2 := by
  rw [source_success_event]
  exact CookieClicker.FullGame.UniformRandom.uniform53_unripe_success_mass

end CookieClicker.JavaScript.ChoiceSource

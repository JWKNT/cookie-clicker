import CookieClicker.JavaScriptHasEnvironment
import CookieClicker.JavaScriptProductionSyntax

/-! The intact native ComputeCps callback with zero multiplier and bonus.
Object positions, the declarative closure path and the caller are arbitrary.
Only the actual native Math/pow bindings and parameter cells are constrained.
-/
namespace CookieClicker.JavaScript.ComputeCps
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

structure Objects where
  objects : Array JSObject
  window : ObjectId
  math : ObjectId
  pow : ObjectId
  windowObject : JSObject
  mathObject : JSObject
  powObject : JSObject
  windowRead : objects[window]? = some windowObject
  mathRead : objects[math]? = some mathObject
  powRead : objects[pow]? = some powObject
  windowKnown : windowObject.unresolvedOwnNames = []
  mathKnown : mathObject.unresolvedOwnNames = []
  windowKind : windowObject.kind = .host "Window" 0
  mathKind : mathObject.kind = .ordinary
  powKind : powObject.kind = .builtin ⟨"Math","pow"⟩
  windowMath : ownProperty windowObject (JSString.ofString "Math") =
    some (.data (.object math) true false true)
  mathPow : ownProperty mathObject (JSString.ofString "pow") =
    some (.data (.object pow) true false true)

def windowIndex (objects : Objects) : ObjectId := objects.window
def windowObject (objects : Objects) : JSObject := objects.windowObject

def mathIndex (objects : Objects) : ObjectId := objects.math
def mathObject (objects : Objects) : JSObject := objects.mathObject

def powIndex (objects : Objects) : ObjectId := objects.pow
def powObject (objects : Objects) : JSObject := objects.powObject

structure Scopes (window : ObjectId) where
  environments : Array LexicalEnvironment
  closureScope : Nat
  globalScope : Nat
  depth : Nat
  chain : HasEnvironment.DeclarativePath environments "Math" closureScope globalScope depth
  globalRead : environments[globalScope]? = some ⟨.object window false,none⟩
  depthBound : depth < environments.size

structure Locals where
  extra : List Binding := []
  clean : ∀ b ∈ extra, b.name ≠ "base" ∧ b.name ≠ "mult" ∧ b.name ≠ "bonus" ∧ b.name ≠ "Math"

def localIndex {window : ObjectId} (scopes : Scopes window) : EnvId := scopes.environments.size

def bindings (locals : Locals) (value : UInt64) : List Binding :=
  [{name := "base",value := .number value}, {name := "mult",value := .number 0},
   {name := "bonus",value := .number 0}] ++ locals.extra

def heap (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) : Heap := {
  objects := objects.objects
  environments := scopes.environments.push ⟨.declarative (bindings locals value),some scopes.closureScope⟩ }

theorem heap_size (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    (heap objects scopes locals value).environments.size = scopes.environments.size+1 := by simp [heap]

theorem checked_local (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    checkedEnvironment (heap objects scopes locals value) (localIndex scopes) =
      .ok ⟨.declarative (bindings locals value),some scopes.closureScope⟩ := by
  simp [checkedEnvironment,heap,localIndex,Heap.environment?]

theorem checked_global (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    checkedEnvironment (heap objects scopes locals value) scopes.globalScope =
      .ok ⟨.object (windowIndex objects) false,none⟩ := by
  have read := HasEnvironment.append_old_read scopes.environments
    ⟨.declarative (bindings locals value),some scopes.closureScope⟩
    ⟨.object (windowIndex objects) false,none⟩ scopes.globalScope scopes.globalRead
  simp [checkedEnvironment,heap,Heap.environment?,read]

theorem no_math (locals : Locals) (value : UInt64) :
    (bindings locals value).any (fun b => b.name == "Math") = false := by
  have clean : locals.extra.any (fun b => b.name == "Math") = false := by
    apply List.any_eq_false.mpr
    intro b member
    simpa using (locals.clean b member).2.2.2
  simp [bindings,clean]

theorem set_bonus (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    setBinding (heap objects scopes locals value) (localIndex scopes) "bonus" (.number 0) false =
      .ok (heap objects scopes locals value) := by
  have clean : locals.extra.map (fun b => if b.name == "bonus" then {b with value := .number 0,initialized := true} else b) = locals.extra := by
    calc
      _ = locals.extra.map id := List.map_congr_left (by intro b member; simp [(locals.clean b member).2.2.1])
      _ = locals.extra := List.map_id locals.extra
  simp only [beq_iff_eq] at clean
  simp only [setBinding,checked_local]
  simp [bindings,clean,replaceEnvironment,Heap.writeEnvironment,heap,
    localIndex,Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_push,bind,Except.bind]

theorem read_base (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    readBinding (heap objects scopes locals value) (localIndex scopes) "base" = .ok (.number value) := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_mult (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    readBinding (heap objects scopes locals value) (localIndex scopes) "mult" = .ok (.number 0) := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_bonus (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    readBinding (heap objects scopes locals value) (localIndex scopes) "bonus" = .ok (.number 0) := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem checked_window (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    checkedObject (heap objects scopes locals value) (windowIndex objects) = .ok (windowObject objects) := by
  simp [windowIndex,mathIndex,powIndex,windowObject,mathObject,powObject,checkedObject,heap,Heap.object?,objects.windowRead]

theorem checked_math (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    checkedObject (heap objects scopes locals value) (mathIndex objects) = .ok (mathObject objects) := by
  simp [windowIndex,mathIndex,powIndex,windowObject,mathObject,powObject,checkedObject,heap,Heap.object?,objects.mathRead]

theorem checked_pow (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    checkedObject (heap objects scopes locals value) (powIndex objects) = .ok (powObject objects) := by
  simp [windowIndex,mathIndex,powIndex,windowObject,mathObject,powObject,checkedObject,heap,Heap.object?,objects.powRead]

theorem window_kind (objects : Objects) : (windowObject objects).kind = .host "Window" 0 := objects.windowKind

theorem math_kind (objects : Objects) : (mathObject objects).kind = .ordinary := objects.mathKind

theorem pow_kind (objects : Objects) : (powObject objects).kind = .builtin ⟨"Math","pow"⟩ := objects.powKind

theorem window_math (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    lookupProperty (heap objects scopes locals value) (windowIndex objects) (JSString.ofString "Math") =
      .ok (some (.data (.object (mathIndex objects)) true false true)) := by
  simp [windowIndex,mathIndex,powIndex,windowObject,mathObject,powObject,lookupProperty,findProperty,checkedObject,Heap.object?,heap,objects.windowRead,
    objects.windowKnown,objects.windowMath,Except.bind,Except.pure,bind,pure]

theorem math_pow (objects : Objects) (scopes : Scopes (windowIndex objects)) (locals : Locals) (value : UInt64) :
    lookupProperty (heap objects scopes locals value) (mathIndex objects) (JSString.ofString "pow") =
      .ok (some (.data (.object (powIndex objects)) true false true)) := by
  simp [windowIndex,mathIndex,powIndex,windowObject,mathObject,powObject,lookupProperty,findProperty,checkedObject,Heap.object?,heap,objects.mathRead,
    objects.mathKnown,objects.mathPow,Except.bind,Except.pure,bind,pure]

def ambient (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) : Machine := {
  base with
  heap := heap objects scopes locals value
  context := ⟨localIndex scopes,localIndex scopes,base.context.thisValue,false⟩
  globalObject := (windowIndex objects)
  objectEnvironmentExclusions := [] }

theorem identifier_math (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) :
    Environment.identifier (ambient base objects scopes locals value) "Math" =
      {ambient base objects scopes locals value with
       control := .expressionResult (.reference ⟨.environment scopes.globalScope "Math",false⟩)} := by
  let machine := ambient base objects scopes locals value
  have localRead : checkedEnvironment machine.heap (localIndex scopes) =
      .ok ⟨.declarative (bindings locals value),some scopes.closureScope⟩ := checked_local objects scopes locals value
  have globalRead : checkedEnvironment machine.heap scopes.globalScope =
      .ok ⟨.object (windowIndex objects) false,none⟩ := checked_global objects scopes locals value
  have chain : HasEnvironment.DeclarativePath machine.heap.environments "Math"
      scopes.closureScope scopes.globalScope scopes.depth :=
    HasEnvironment.append_path scopes.environments _ "Math" _ _ _ scopes.chain
  have count : scopes.environments.size+1 = scopes.depth+(scopes.environments.size-scopes.depth+1) := by
    have bound := scopes.depthBound; omega
  change Environment.resolve ((heap objects scopes locals value).environments.size+1)
    machine (localIndex scopes) "Math" false = _
  rw [heap_size,Environment.resolve]
  simp only [localRead,JavaScript.checked,no_math,Bool.false_eq_true,↓reduceIte]
  rw [count,HasEnvironment.resolve_path machine "Math" false _ _ _ _ chain]
  rw [Environment.resolve,globalRead]
  simp only [JavaScript.checked,machine,ambient,window_math]
  rfl

theorem identifier_math_explicit (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64)
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
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } "Math" =
    {({
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } : Machine) with control := .expressionResult (.reference ⟨.environment scopes.globalScope "Math",false⟩)} := by
  exact identifier_math {
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } objects scopes locals value

theorem identifier_base (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) :
    Environment.identifier (ambient base objects scopes locals value) "base" =
      {ambient base objects scopes locals value with
       control := .expressionResult (.reference ⟨.environment (localIndex scopes) "base",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local objects scopes locals value) (by simp [bindings])

theorem identifier_base_explicit (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64)
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
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } "base" =
    {({
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "base",false⟩)} := by
  exact identifier_base {
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } objects scopes locals value

theorem identifier_mult (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) :
    Environment.identifier (ambient base objects scopes locals value) "mult" =
      {ambient base objects scopes locals value with
       control := .expressionResult (.reference ⟨.environment (localIndex scopes) "mult",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local objects scopes locals value) (by simp [bindings])

theorem identifier_mult_explicit (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64)
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
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } "mult" =
    {({
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "mult",false⟩)} := by
  exact identifier_mult {
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } objects scopes locals value

theorem identifier_bonus (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) :
    Environment.identifier (ambient base objects scopes locals value) "bonus" =
      {ambient base objects scopes locals value with
       control := .expressionResult (.reference ⟨.environment (localIndex scopes) "bonus",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local objects scopes locals value) (by simp [bindings])

theorem identifier_bonus_explicit (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64)
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
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } "bonus" =
    {({
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "bonus",false⟩)} := by
  exact identifier_bonus {
      heap := heap objects scopes locals value
      context := ⟨localIndex scopes,localIndex scopes,thisValue,false⟩
      globalObject := (windowIndex objects)
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
      freeDrawCount := freeDrawCount
    } objects scopes locals value

theorem native_pow_two_zero : Math.pow 4611686018427387904 0 = Number.one := by decide +kernel

def state (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) : Machine :=
  {ambient base objects scopes locals value with control := .statement ProductionSyntax.ComputeCpsBody}

attribute [local cbv_opaque] windowIndex mathIndex powIndex windowObject mathObject powObject
attribute [local cbv_opaque] heap localIndex JSString.ofString checkedObject lookupProperty Environment.identifier
attribute [local cbv_opaque] checkedEnvironment readBinding setBinding
attribute [local cbv_opaque] Number.mul Number.add Math.pow
attribute [local cbv_eval] heap_size checked_local checked_global set_bonus read_base read_mult read_bonus
attribute [local cbv_eval] checked_window checked_math checked_pow window_kind math_kind pow_kind window_math math_pow
attribute [local cbv_eval] native_pow_two_zero

set_option linter.unusedSimpArgs false in
theorem native_body_prefix (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) (fuel : Nat) :
    let before := state base objects scopes locals value
    Builtins.run (49+fuel) before = Builtins.run fuel {before with
      control := .completion (.return (.number (Number.add (Number.mul value Number.one) 0)))} := by
  rw [Nat.add_comm 49 fuel]
  cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv
  try simp only [identifier_math_explicit,identifier_base_explicit,identifier_mult_explicit,identifier_bonus_explicit,checked_local,checked_global,read_base,read_mult,read_bonus,set_bonus,checked_window,checked_math,checked_pow,window_kind,math_kind,pow_kind,window_math,math_pow,native_pow_two_zero]
  try cbv

theorem native_body (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (value : UInt64) :
    let before := state base objects scopes locals value
    Builtins.run 49 before = {before with
      control := .completion (.return (.number (Number.add (Number.mul value Number.one) 0)))} := by
  simpa only [Nat.add_zero,Builtins.run] using native_body_prefix base objects scopes locals value 0

theorem cursor_arithmetic :
    Number.add (Number.mul 4591870180066957722 Number.one) 0 = 4591870180066957722 := by decide +kernel

theorem native_cursor_base (base : Machine) (objects : Objects) (scopes : Scopes (windowIndex objects))
    (locals : Locals) (fuel : Nat) :
    let before := state base objects scopes locals 4591870180066957722
    Builtins.run (49+fuel) before = Builtins.run fuel {before with
      control := .completion (.return (.number 4591870180066957722))} := by
  simpa only [cursor_arithmetic] using native_body_prefix base objects scopes locals 4591870180066957722 fuel

end CookieClicker.JavaScript.ComputeCps

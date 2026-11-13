import CookieClicker.JavaScriptArc4ConstructorPrefix

/-! The nested native generator retains its constructor environment and the
original library environment. Its own scope does not copy inherited bindings. -/
namespace CookieClicker.JavaScript.Arc4GeneratorLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  constructor : Arc4Locals.Inputs
  constructorArgument : ObjectId
  constructorValues : Arc4Locals.Values

def base (i : Inputs) := Arc4Locals.base i.constructor
def constructorIndex (i : Inputs) := Arc4Locals.localIndex i.constructor
def libraryIndex (i : Inputs) := Arc4Locals.scope i.constructor
def constructorEnvironments (i : Inputs) := (base i).heap.environments.push
  ⟨.declarative (Arc4Locals.locals i.constructorArgument i.constructorValues),some (libraryIndex i)⟩
def localIndex (i : Inputs) := (constructorEnvironments i).size
structure Values where
  a : Value := .undefined
  b : Value := .undefined
  c : Value := .undefined
  f : Value := .undefined
  g : Value := .undefined
  h : Value := .undefined

def locals (argument : ObjectId) (v : Values) : List Binding :=
  [{name := "a",value := v.a},{name := "arguments",value := .object argument},
   {name := "b",value := v.b},{name := "c",value := v.c},
   {name := "f",value := v.f},{name := "g",value := v.g},{name := "h",value := v.h}]
def heap (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) : Heap := {
  objects := objects
  environments := (constructorEnvironments i).push
    ⟨.declarative (locals argument v),some (constructorIndex i)⟩ }
def machine (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (tail : List Frame) : Machine := {
  base i with
  heap := heap i objects argument v
  context := ⟨localIndex i,localIndex i,.object (base i).globalObject,false⟩
  control := control, continuation := tail }

theorem environment_size (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    (heap i objects argument v).environments.size=(base i).heap.environments.size+2 := by simp [heap,constructorEnvironments]

theorem checked_local (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    checkedEnvironment (heap i objects argument v) (localIndex i)=
      .ok ⟨.declarative (locals argument v),some (constructorIndex i)⟩ := by
  simp [checkedEnvironment,Heap.environment?,heap,localIndex]

theorem checked_constructor (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    checkedEnvironment (heap i objects argument v) (constructorIndex i)=
      .ok ⟨.declarative (Arc4Locals.locals i.constructorArgument i.constructorValues),some (libraryIndex i)⟩ := by
  simp [checkedEnvironment,Heap.environment?,heap,constructorEnvironments,constructorIndex,Arc4Locals.localIndex,base,Array.getElem?_push]

theorem checked_library (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    checkedEnvironment (heap i objects argument v) (libraryIndex i)=
      .ok ⟨.declarative (Arc4Locals.libraryBindings i.constructor),Arc4Locals.libraryOuter i.constructor⟩ := by
  have bound := Arc4Locals.scope_bound i.constructor
  have room : (Arc4Locals.base i.constructor).heap.environments.size<(constructorEnvironments i).size := by
    simp [constructorEnvironments,base]
  have different : Arc4Locals.scope i.constructor≠(constructorEnvironments i).size :=
    Nat.ne_of_lt (Nat.lt_trans bound room)
  have older := Arc4Locals.checked_library i.constructor objects i.constructorArgument i.constructorValues
  change (match ((constructorEnvironments i).push
    ⟨.declarative (locals argument v),some (constructorIndex i)⟩)[Arc4Locals.scope i.constructor]? with
      | some environment => (Except.ok environment : Checked LexicalEnvironment)
      | none => .error (.fault (.missingEnvironment (Arc4Locals.scope i.constructor)))) = _
  rw [Array.getElem?_push,if_neg different]
  exact older

theorem read_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "a"=.ok v.a := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "a" value false=
      .ok (heap i objects argument {v with a := value}) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,heap,locals,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem read_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "b"=.ok v.b := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "b" value false=
      .ok (heap i objects argument {v with b := value}) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,heap,locals,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem read_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "c"=.ok v.c := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "c" value false=
      .ok (heap i objects argument {v with c := value}) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,heap,locals,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem read_f (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "f"=.ok v.f := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_f (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "f" value false=
      .ok (heap i objects argument {v with f := value}) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,heap,locals,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem read_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "g"=.ok v.g := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "g" value false=
      .ok (heap i objects argument {v with g := value}) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,heap,locals,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem read_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "h"=.ok v.h := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "h" value false=
      .ok (heap i objects argument {v with h := value}) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,heap,locals,localIndex,replaceEnvironment,
    Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem read_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (constructorIndex i) "e"=.ok i.constructorValues.e := by
  simp [readBinding,checked_constructor,Arc4Locals.locals,Except.bind,bind,Except.pure,pure]

theorem read_d (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (libraryIndex i) "d"=.ok (.number (Number.ofNat 256)) := by
  have original := i.constructor.widthRead
  unfold readBinding at original ⊢
  rw [i.constructor.scopeRead] at original
  rw [checked_library]
  exact original

theorem read_j (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (libraryIndex i) "j"=.ok (.number (Number.ofNat 255)) := by
  have original := i.constructor.maskRead
  unfold readBinding at original ⊢
  rw [i.constructor.scopeRead] at original
  rw [checked_library]
  exact original

theorem identifier_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "a"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "a",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "b"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "b",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "c"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "c",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_f (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "f"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "f",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "g"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "g",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "h"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "h",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "e"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (constructorIndex i) "e",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_d (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "d"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (libraryIndex i) "d",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

theorem identifier_j (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId)
    (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId)
    (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "j"=
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (libraryIndex i) "j",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,checked_constructor,checked_library,locals,Arc4Locals.locals,
    Arc4Locals.contains_width,Arc4Locals.contains_mask,checked]
  rfl

end CookieClicker.JavaScript.Arc4GeneratorLocals

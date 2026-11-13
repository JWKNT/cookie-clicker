import CookieClicker.JavaScriptSeedrandomArc4Syntax
import CookieClicker.JavaScriptDenseArrayState

/-! The retained ARC4 constructor environment. Source bindings and every
heap object are represented explicitly through its initialization loops. -/
namespace CookieClicker.JavaScript.Arc4Locals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  base : Machine
  scope : EnvId
  bindings : List Binding
  outer : Option EnvId
  scopeRead : checkedEnvironment base.heap scope = .ok ⟨.declarative bindings,outer⟩
  widthDeclared : bindings.any (fun b => b.name == "d") = true
  widthRead : readBinding base.heap scope "d" = .ok (.number (Number.ofNat 256))
  maskDeclared : bindings.any (fun b => b.name == "j") = true
  maskRead : readBinding base.heap scope "j" = .ok (.number (Number.ofNat 255))

def base (i : Inputs) := i.base
def scope (i : Inputs) := i.scope
def libraryBindings (i : Inputs) := i.bindings
def libraryOuter (i : Inputs) := i.outer

def localIndex (i : Inputs) := (base i).heap.environments.size
structure Values where
  a : Value := .undefined
  b : Value := .undefined
  c : Value := .undefined
  e : Value := .undefined
  f : Value := .undefined
  g : Value := .undefined
  h : Value := .undefined

def locals (argument : ObjectId) (v : Values) : List Binding :=
  [{name := "a",value := v.a},{name := "arguments",value := .object argument},
   {name := "b",value := v.b},{name := "c",value := v.c},{name := "e",value := v.e},
   {name := "f",value := v.f},{name := "g",value := v.g},{name := "h",value := v.h}]
def heap (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) : Heap := {
  objects := objects
  environments := (base i).heap.environments.push ⟨.declarative (locals argument v),some (scope i)⟩ }
def machine (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) : Machine := {
  base i with
  heap := heap i objects argument v
  context := ⟨localIndex i,localIndex i,v.e,false⟩
  control := control, continuation := continuation }

theorem scope_bound (i : Inputs) : scope i < (base i).heap.environments.size := by
  have present := i.scopeRead
  unfold checkedEnvironment Heap.environment? at present
  cases h : i.base.heap.environments[i.scope]? with
  | none => simp [h] at present
  | some environment => exact Array.getElem?_eq_some_iff.mp h |>.1

theorem checked_library (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    checkedEnvironment (heap i objects argument v) (scope i) =
      .ok ⟨.declarative (libraryBindings i),libraryOuter i⟩ := by
  have different : i.scope ≠ i.base.heap.environments.size := Nat.ne_of_lt (scope_bound i)
  simpa only [heap,checkedEnvironment,Heap.environment?,Array.getElem?_push,
    if_neg different,base,scope,libraryBindings,libraryOuter] using i.scopeRead

theorem checked_local (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    checkedEnvironment (heap i objects argument v) (localIndex i) =
      .ok ⟨.declarative (locals argument v),some (scope i)⟩ := by
  simp [checkedEnvironment,heap,localIndex,Heap.environment?]

theorem environment_size (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    (heap i objects argument v).environments.size = (base i).heap.environments.size+1 := by simp [heap]

theorem contains_width (i : Inputs) : (libraryBindings i).any (fun b => b.name == "d") = true := i.widthDeclared

theorem read_width (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (scope i) "d" = .ok (.number (Number.ofNat 256)) := by
  have original := i.widthRead
  unfold readBinding at original ⊢
  rw [i.scopeRead] at original
  rw [checked_library]
  exact original

theorem contains_mask (i : Inputs) : (libraryBindings i).any (fun b => b.name == "j") = true := i.maskDeclared

theorem read_mask (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (scope i) "j" = .ok (.number (Number.ofNat 255)) := by
  have original := i.maskRead
  unfold readBinding at original ⊢
  rw [i.scopeRead] at original
  rw [checked_library]
  exact original

theorem read_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "a" = .ok v.a := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "a" value false =
      .ok (heap i objects argument {v with a := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "b" = .ok v.b := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "b" value false =
      .ok (heap i objects argument {v with b := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "c" = .ok v.c := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "c" value false =
      .ok (heap i objects argument {v with c := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "e" = .ok v.e := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "e" value false =
      .ok (heap i objects argument {v with e := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_f (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "f" = .ok v.f := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_f (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "f" value false =
      .ok (heap i objects argument {v with f := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "g" = .ok v.g := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "g" value false =
      .ok (heap i objects argument {v with g := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) :
    readBinding (heap i objects argument v) (localIndex i) "h" = .ok v.h := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (value : Value) :
    setBinding (heap i objects argument v) (localIndex i) "h" value false =
      .ok (heap i objects argument {v with h := value}) := by
  simp [heap,setBinding,checkedEnvironment,Heap.environment?,locals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem identifier_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "a" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "a",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "b" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "b",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "c" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "c",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "e" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "e",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_f (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "f" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "f",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "g" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "g",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "h" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (localIndex i) "h",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked]
  rfl

theorem identifier_d (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "d" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (scope i) "d",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_j (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (control : Control) (continuation : List Frame) :
    Environment.identifier (machine i objects argument v control continuation) "j" =
      {machine i objects argument v control continuation with
        control := .expressionResult (.reference ⟨.environment (scope i) "j",false⟩)} := by
  unfold Environment.identifier machine
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_a_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "a" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "a",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_b_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "b" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "b",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_c_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "c" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "c",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_e_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "e" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "e",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_f_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "f" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "f",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_g_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "g" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "g",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_h_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "h" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "h",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_d_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "d" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "d",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

theorem identifier_j_record (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "j" =
    Machine.mk (heap i objects argument v) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "j",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,checked,checked_library,contains_width,contains_mask]
  rfl

end CookieClicker.JavaScript.Arc4Locals

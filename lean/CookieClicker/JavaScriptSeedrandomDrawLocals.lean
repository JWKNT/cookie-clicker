import CookieClicker.JavaScriptSeedrandomRandomClosure
import CookieClicker.JavaScriptRetainedArc4GeneratorCall
import CookieClicker.JavaScriptBindingWrite

/-! The random activation keeps its lexical position while nested generator
calls append environments. All local writes retain the appended environments. -/
namespace CookieClicker.JavaScript.SeedrandomDrawLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def libraryName (name : String) : Prop :=
  name="d" ∨ name="e" ∨ name="g" ∨ name="h" ∨ name="i"
structure Inputs where
  base : Machine
  capture : EnvId
  library : EnvId
  captured : List Binding
  bindings : List Binding
  outer : Option EnvId
  captureRead : checkedEnvironment base.heap capture=.ok ⟨.declarative captured,some library⟩
  libraryRead : checkedEnvironment base.heap library=.ok ⟨.declarative bindings,outer⟩
  absent : ∀ name, libraryName name → captured.any (fun b => b.name==name)=false
  declared : ∀ name, libraryName name → bindings.any (fun b => b.name==name)=true
  qDeclared : captured.any (fun b => b.name=="q")=true
  generator : ObjectId
  qRead : readBinding base.heap capture "q"=.ok (.object generator)
  dRead : readBinding base.heap library "d"=.ok (.number (Number.ofNat 256))
  eRead : readBinding base.heap library "e"=.ok (.number (Number.ofNat 6))
  gRead : readBinding base.heap library "g"=.ok (.number (Number.ofNat (2^48)))
  hRead : readBinding base.heap library "h"=.ok (.number (Number.ofNat (2^52)))
  iRead : readBinding base.heap library "i"=.ok (.number (Number.ofNat (2^53)))
  thisObject : ObjectId

def base (i : Inputs) := i.base
def capture (i : Inputs) := i.capture
def library (i : Inputs) := i.library
def localIndex (i : Inputs) := i.base.heap.environments.size
structure Values where
  a : Value := .undefined
  b : Value := .undefined
  c : Value := .undefined

def locals (argument : ObjectId) (v : Values) : List Binding :=
  [{name := "arguments",value := .object argument},{name := "a",value := v.a},
   {name := "b",value := v.b},{name := "c",value := v.c}]
def heap (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) : Heap := {
  objects := objects
  environments := (i.base.heap.environments.push ⟨.declarative (locals argument v),some i.capture⟩) ++ history }
def machine (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) (control : Control) (tail : List Frame) : Machine := {
  i.base with
  heap := heap i objects argument v history
  context := ⟨localIndex i,localIndex i,.object i.thisObject,false⟩
  control := control,continuation := tail }

theorem checked_local (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    checkedEnvironment (heap i objects argument v history) (localIndex i)=
      .ok ⟨.declarative (locals argument v),some i.capture⟩ := by
  simp only [checkedEnvironment,Heap.environment?,heap,localIndex]
  rw [Array.getElem?_append_left (by simp)]
  simp

theorem checked_old (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment i.base.heap id=.ok environment) :
    checkedEnvironment (heap i objects argument v history) id=.ok environment := by
  have bound : id<i.base.heap.environments.size := by
    cases raw : i.base.heap.environments[id]? with
    | none => simp [checkedEnvironment,Heap.environment?,raw] at read
    | some e => exact (Array.getElem?_eq_some_iff.mp raw).1
  simp only [checkedEnvironment,Heap.environment?,heap]
  rw [Array.getElem?_append_left (by simpa only [Array.size_push] using Nat.lt_succ_of_lt bound),
    Array.getElem?_push,if_neg (Nat.ne_of_lt bound)]
  exact read

theorem checked_capture (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    checkedEnvironment (heap i objects argument v history) i.capture=
      .ok ⟨.declarative i.captured,some i.library⟩ :=
  checked_old i objects argument v history _ _ i.captureRead

theorem checked_library (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    checkedEnvironment (heap i objects argument v history) i.library=
      .ok ⟨.declarative i.bindings,i.outer⟩ :=
  checked_old i objects argument v history _ _ i.libraryRead

theorem environment_size (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    (heap i objects argument v history).environments.size=i.base.heap.environments.size+history.size+1 := by
  simp [heap,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem prefix_positive (i : Inputs) : 0<i.base.heap.environments.size := by
  exact Nat.lt_of_le_of_lt (Nat.zero_le i.capture)
    (BindingWrite.local_bound _ _ _ _ i.captureRead)

theorem read_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (localIndex i) "a"=.ok v.a := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) (value : Value) :
    setBinding (heap i objects argument v history) (localIndex i) "a" value false=
      .ok (heap i objects argument {v with a := value} history) := by
  have bound : localIndex i < (heap i objects argument v history).environments.size := by
    simp [localIndex,heap]; omega
  have rawBound : i.base.heap.environments.size < i.base.heap.environments.size+1+history.size := by omega
  simp only [setBinding,checked_local]
  simp [rawBound,locals,replaceEnvironment,Heap.writeEnvironment,bound,
    heap,localIndex,Array.setIfInBounds_append_left,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (localIndex i) "b"=.ok v.b := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) (value : Value) :
    setBinding (heap i objects argument v history) (localIndex i) "b" value false=
      .ok (heap i objects argument {v with b := value} history) := by
  have bound : localIndex i < (heap i objects argument v history).environments.size := by
    simp [localIndex,heap]; omega
  have rawBound : i.base.heap.environments.size < i.base.heap.environments.size+1+history.size := by omega
  simp only [setBinding,checked_local]
  simp [rawBound,locals,replaceEnvironment,Heap.writeEnvironment,bound,
    heap,localIndex,Array.setIfInBounds_append_left,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (localIndex i) "c"=.ok v.c := by
  simp [readBinding,checked_local,locals,Except.bind,bind,Except.pure,pure]

theorem write_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) (value : Value) :
    setBinding (heap i objects argument v history) (localIndex i) "c" value false=
      .ok (heap i objects argument {v with c := value} history) := by
  have bound : localIndex i < (heap i objects argument v history).environments.size := by
    simp [localIndex,heap]; omega
  have rawBound : i.base.heap.environments.size < i.base.heap.environments.size+1+history.size := by omega
  simp only [setBinding,checked_local]
  simp [rawBound,locals,replaceEnvironment,Heap.writeEnvironment,bound,
    heap,localIndex,Array.setIfInBounds_append_left,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

theorem read_q (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) i.capture "q"=.ok (.object i.generator) := by
  have before := i.qRead
  unfold readBinding
  rw [checked_capture]
  simpa only [readBinding,i.captureRead] using before

theorem read_d (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) i.library "d"=.ok (.number (Number.ofNat 256)) := by
  have before := i.dRead
  unfold readBinding
  rw [checked_library]
  simpa only [readBinding,i.libraryRead] using before

theorem read_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) i.library "e"=.ok (.number (Number.ofNat 6)) := by
  have before := i.eRead
  unfold readBinding
  rw [checked_library]
  simpa only [readBinding,i.libraryRead] using before

theorem read_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) i.library "g"=.ok (.number (Number.ofNat (2^48))) := by
  have before := i.gRead
  unfold readBinding
  rw [checked_library]
  simpa only [readBinding,i.libraryRead] using before

theorem read_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) i.library "h"=.ok (.number (Number.ofNat (2^52))) := by
  have before := i.hRead
  unfold readBinding
  rw [checked_library]
  simpa only [readBinding,i.libraryRead] using before

theorem read_i (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) i.library "i"=.ok (.number (Number.ofNat (2^53))) := by
  have before := i.iRead
  unfold readBinding
  rw [checked_library]
  simpa only [readBinding,i.libraryRead] using before

theorem identifier_a (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "a"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "a",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  simp [Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_b (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "b"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "b",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  simp [Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_c (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "c"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localIndex i) "c",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  simp [Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_q (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "q"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (capture i) "q",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  simp [Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_d (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "d"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (library i) "d",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  have absent := i.absent "d" (by simp [libraryName])
  have declared := i.declared "d" (by simp [libraryName])
  simp [absent,declared,Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_e (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "e"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (library i) "e",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  have absent := i.absent "e" (by simp [libraryName])
  have declared := i.declared "e" (by simp [libraryName])
  simp [absent,declared,Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_g (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "g"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (library i) "g",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  have absent := i.absent "g" (by simp [libraryName])
  have declared := i.declared "g" (by simp [libraryName])
  simp [absent,declared,Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_h (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "h"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (library i) "h",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  have absent := i.absent "h" (by simp [libraryName])
  have declared := i.declared "h" (by simp [libraryName])
  simp [absent,declared,Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem identifier_i (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "i"=
    Machine.mk (heap i objects argument v history) ⟨localIndex i,localIndex i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (library i) "i",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := prefix_positive i; omega⟩
  rw [size]
  have absent := i.absent "i" (by simp [libraryName])
  have declared := i.declared "i" (by simp [libraryName])
  simp [absent,declared,Environment.resolve,checked_local,checked_capture,checked_library,locals,
    i.qDeclared,i.absent,i.declared,libraryName,checked,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rfl

theorem checked_capture_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    checkedEnvironment (heap i objects argument v history) (capture i)=
      .ok ⟨.declarative i.captured,some i.library⟩ :=
  checked_capture i objects argument v history

theorem checked_library_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    checkedEnvironment (heap i objects argument v history) (library i)=
      .ok ⟨.declarative i.bindings,i.outer⟩ :=
  checked_library i objects argument v history

theorem read_q_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (capture i) "q"=.ok (.object i.generator) :=
  read_q i objects argument v history

theorem read_d_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (library i) "d"=.ok (.number (Number.ofNat 256)) :=
  read_d i objects argument v history

theorem read_e_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (library i) "e"=.ok (.number (Number.ofNat 6)) :=
  read_e i objects argument v history

theorem read_g_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (library i) "g"=.ok (.number (Number.ofNat (2^48))) :=
  read_g i objects argument v history

theorem read_h_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (library i) "h"=.ok (.number (Number.ofNat (2^52))) :=
  read_h i objects argument v history

theorem read_i_at (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (history : Array LexicalEnvironment) :
    readBinding (heap i objects argument v history) (library i) "i"=.ok (.number (Number.ofNat (2^53))) :=
  read_i i objects argument v history

end CookieClicker.JavaScript.SeedrandomDrawLocals

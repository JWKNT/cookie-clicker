import CookieClicker.JavaScriptTimestampSeedEntropyEntry
import CookieClicker.JavaScriptNativeMixkeyComplete

/-! Lexical frames for the retained setup return sequence. Every lookup uses
its actual declarative binding and the source caller activation. -/
namespace CookieClicker.JavaScript.SeedrandomSetupLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Inputs where
  base : Machine
  localScope : EnvId
  scope : EnvId
  receiver : Value
  caller : ExecutionContext
  tail : List Frame
  locals : List Binding
  bindings : List Binding
  outer : Option EnvId
  localRead : checkedEnvironment base.heap localScope=.ok ⟨.declarative locals,some scope⟩
  libraryRead : checkedEnvironment base.heap scope=.ok ⟨.declarative bindings,outer⟩
  absent : ∀ name, name="m" ∨ name="o" ∨ name="b" ∨ name="c" → locals.any (fun b => b.name==name)=false
  declared : ∀ name, name="m" ∨ name="o" ∨ name="b" ∨ name="c" → bindings.any (fun b => b.name==name)=true
  qDeclared : locals.any (fun b => b.name=="q")=true
  pDeclared : locals.any (fun b => b.name=="p")=true
  generator : ObjectId
  pool : ObjectId
  math : ObjectId
  mixkey : ObjectId
  helper : ObjectId
  text : JSString
  qRead : readBinding base.heap localScope "q"=.ok (.object generator)
  pRead : readBinding base.heap localScope "p"=.ok (.string text)
  mRead : readBinding base.heap scope "m"=.ok (.object mixkey)
  oRead : readBinding base.heap scope "o"=.ok (.object helper)
  bRead : readBinding base.heap scope "b"=.ok (.object pool)
  cRead : readBinding base.heap scope "c"=.ok (.object math)

def heap (i : Inputs) := i.base.heap
def localScope (i : Inputs) := i.localScope
def scope (i : Inputs) := i.scope

def machine (i : Inputs) (control : Control) (continuation : List Frame) : Machine := {
  i.base with
  heap := heap i
  context := ⟨localScope i,localScope i,i.receiver,false⟩
  control := control
  continuation := continuation }

def returnTail (i : Inputs) : List Frame :=
  .returnValue :: .statementList [] none :: .callBoundary i.caller none :: i.tail

theorem size_positive (i : Inputs) : 0<i.base.heap.environments.size := by
  exact Nat.lt_of_le_of_lt (Nat.zero_le i.localScope)
    (BindingWrite.local_bound i.base.heap i.localScope i.locals (some i.scope) i.localRead)

theorem local_identifier (i : Inputs) (name : String) (control : Control) (continuation : List Frame)
    (found : i.locals.any (fun b => b.name==name)=true) :
    Environment.identifier (machine i control continuation) name=
      machine i (.expressionResult (.reference ⟨.environment i.localScope name,false⟩)) continuation :=
  Environment.resolve_declared _ _ _ _ _ _ _ i.localRead found

theorem library_identifier (i : Inputs) (name : String) (control : Control) (continuation : List Frame)
    (named : name="m" ∨ name="o" ∨ name="b" ∨ name="c") :
    Environment.identifier (machine i control continuation) name=
      machine i (.expressionResult (.reference ⟨.environment i.scope name,false⟩)) continuation := by
  unfold Environment.identifier
  have positive := size_positive i
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 := ⟨i.base.heap.environments.size-1,by omega⟩
  change Environment.resolve (i.base.heap.environments.size+1) _ _ _ _ = _
  rw [size]
  simp only [Environment.resolve,machine,heap,localScope,scope,i.localRead,i.libraryRead,checked,i.absent name named,i.declared name named,
    Bool.false_eq_true,↓reduceIte]
  rfl

theorem identifier_q (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "q"=
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localScope i) "q",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  exact Environment.resolve_declared _ _ _ _ _ _ _ i.localRead i.qDeclared

theorem identifier_p (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "p"=
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localScope i) "p",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  exact Environment.resolve_declared _ _ _ _ _ _ _ i.localRead i.pDeclared

theorem identifier_m (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "m"=
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "m",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := size_positive i; omega⟩
  change Environment.resolve (i.base.heap.environments.size+1) _ _ _ _ = _
  rw [size]
  have named : "m"="m" ∨ "m"="o" ∨ "m"="b" ∨ "m"="c" := by simp
  simp only [Environment.resolve,heap,localScope,scope,i.localRead,i.libraryRead,checked,i.absent _ named,i.declared _ named,
    Bool.false_eq_true,↓reduceIte]
  rfl

theorem identifier_o (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "o"=
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "o",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := size_positive i; omega⟩
  change Environment.resolve (i.base.heap.environments.size+1) _ _ _ _ = _
  rw [size]
  have named : "o"="m" ∨ "o"="o" ∨ "o"="b" ∨ "o"="c" := by simp
  simp only [Environment.resolve,heap,localScope,scope,i.localRead,i.libraryRead,checked,i.absent _ named,i.declared _ named,
    Bool.false_eq_true,↓reduceIte]
  rfl

theorem identifier_b (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "b"=
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "b",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := size_positive i; omega⟩
  change Environment.resolve (i.base.heap.environments.size+1) _ _ _ _ = _
  rw [size]
  have named : "b"="m" ∨ "b"="o" ∨ "b"="b" ∨ "b"="c" := by simp
  simp only [Environment.resolve,heap,localScope,scope,i.localRead,i.libraryRead,checked,i.absent _ named,i.declared _ named,
    Bool.false_eq_true,↓reduceIte]
  rfl

theorem identifier_c (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId)
    (objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic : Option ObjectId)
    (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId)
    (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "c"=
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "c",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  obtain ⟨count,size⟩ : ∃ count, i.base.heap.environments.size=count+1 :=
    ⟨i.base.heap.environments.size-1,by have := size_positive i; omega⟩
  change Environment.resolve (i.base.heap.environments.size+1) _ _ _ _ = _
  rw [size]
  have named : "c"="m" ∨ "c"="o" ∨ "c"="b" ∨ "c"="c" := by simp
  simp only [Environment.resolve,heap,localScope,scope,i.localRead,i.libraryRead,checked,i.absent _ named,i.declared _ named,
    Bool.false_eq_true,↓reduceIte]
  rfl

theorem checked_transport {before after : Heap} (same : after.objects=before.objects)
    (id : ObjectId) (object : JSObject) (read : checkedObject before id=.ok object) :
    checkedObject after id=.ok object := by
  simpa only [checkedObject,Heap.object?,same] using read

theorem read_transport {before after : Heap} (id : EnvId) (name : String) (value : Value)
    (preserved : ∀ id environment, checkedEnvironment before id=.ok environment → checkedEnvironment after id=.ok environment)
    (read : readBinding before id name=.ok value) : readBinding after id name=.ok value := by
  unfold readBinding at read ⊢
  cases found : checkedEnvironment before id with
  | error failure => simp [found,Except.bind,bind] at read
  | ok environment => rw [preserved id environment found]; simpa only [found,Except.bind,bind] using read

def transport (i : Inputs) (base : Machine)
    (preserved : ∀ id environment, checkedEnvironment i.base.heap id=.ok environment → checkedEnvironment base.heap id=.ok environment) : Inputs := {
  i with
  base := base
  localRead := preserved _ _ i.localRead
  libraryRead := preserved _ _ i.libraryRead
  qRead := read_transport _ _ _ preserved i.qRead
  pRead := read_transport _ _ _ preserved i.pRead
  mRead := read_transport _ _ _ preserved i.mRead
  oRead := read_transport _ _ _ preserved i.oRead
  bRead := read_transport _ _ _ preserved i.bRead
  cRead := read_transport _ _ _ preserved i.cRead }

end CookieClicker.JavaScript.SeedrandomSetupLocals

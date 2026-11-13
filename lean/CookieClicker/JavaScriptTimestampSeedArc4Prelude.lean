import CookieClicker.JavaScriptTimestampSeedReturnedEnvironment

/-! The source seedrandom initializer stores the actual mixed-key text in p,
then resolves its retained k binding and invokes new k(j). -/
namespace CookieClicker.JavaScript.TimestampSeedArc4Prelude
open TimestampSeedReturnedEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  mixing : TimestampSeedMixing.Inputs
  constructor : ObjectId
  declared : mixing.bindings.any (fun b => b.name=="k")=true
  read : readBinding mixing.globals.base.heap mixing.globals.scope "k"=.ok (.object constructor)

def mixing (i : Inputs) := i.mixing
def base (i : Inputs) := afterAssignment (mixing i)
def heap (i : Inputs) := assignedHeap (mixing i)
def scope (i : Inputs) := (mixing i).globals.scope
def localScope (i : Inputs) := localIndex (mixing i)
def constructor (i : Inputs) := i.constructor
def key (i : Inputs) := TimestampSeedMixing.key (mixing i)
def locals (i : Inputs) := BindingWrite.changedBindings "p" (.string (TimestampSeedMixing.text (mixing i))) (localBindings (mixing i))
def library (i : Inputs) := (mixing i).bindings
def outer (i : Inputs) := (mixing i).outer

theorem checked_local (i : Inputs) : checkedEnvironment (heap i) (localScope i)=
    .ok ⟨.declarative (locals i),some (scope i)⟩ :=
  BindingWrite.changed_checked _ _ _ _ _ _ (local_environment (mixing i))

theorem different (i : Inputs) : localScope i≠scope i :=
  Nat.ne_of_gt (TimestampSeedSetup.scope_bound (TimestampSeedMixing.setup (mixing i)))

theorem checked_library (i : Inputs) : checkedEnvironment (heap i) (scope i)=
    .ok ⟨.declarative (library i),outer i⟩ := by
  change checkedEnvironment (BindingWrite.changedHeap (TimestampSeedMixing.returned (mixing i)).heap
    (localScope i) (localBindings (mixing i)) (some (scope i)) "p" (.string (TimestampSeedMixing.text (mixing i)))) (scope i)=_
  rw [BindingWrite.changed_checked_other _ _ _ _ _ _ _ (different i)]
  exact original_environment (mixing i) _ _ (mixing i).scopeRead

theorem environment_size (i : Inputs) : (heap i).environments.size=(mixing i).globals.base.heap.environments.size+4 := by
  simp only [heap,assignedHeap,BindingWrite.changedHeap,Array.size_set!]
  rw [show (TimestampSeedMixing.returned (mixing i)).heap.environments.size=
    (TimestampSeedMixing.beforeMixing (mixing i)).heap.environments.size+2 from
      mixing_environment_size (TimestampSeedMixing.mixing (mixing i))]
  change (TimestampSeedSetup.atMixkey (TimestampSeedMixing.setup (mixing i))).heap.environments.size+2=_
  rw [TimestampSeedMixingFrame.environment_size (TimestampSeedMixing.setup (mixing i))]
  change (mixing i).globals.base.heap.environments.size+2+2=(mixing i).globals.base.heap.environments.size+4
  omega

theorem read_k (i : Inputs) : readBinding (heap i) (scope i) "k"=.ok (.object (constructor i)) := by
  have original := i.read
  unfold readBinding at original ⊢
  rw [i.mixing.scopeRead] at original
  rw [checked_library]
  exact original

theorem read_j (i : Inputs) : readBinding (heap i) (localScope i) "j"=.ok (.object (key i)) := by
  simp [readBinding,checked_local,locals,localBindings,TimestampSeedSetup.localBindings,
    SeedrandomInvocation.localsText,BindingWrite.changedBindings,BindingWrite.changedBinding,key,
    Except.bind,bind,Except.pure,pure]

def beforeCall (i : Inputs) : Machine := {
  base i with
  control := .invoke (.object (constructor i)) .undefined [.object (key i)] true
  continuation := .assignmentRight .assign ⟨.environment (localScope i) "q",false⟩ none ::
    .variableWrite [] :: .statementList (SeedrandomInvocation.body.drop 1) none ::
    .callBoundary (mixing i).globals.base.context none :: (mixing i).globals.base.continuation }

theorem identifier_j (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "j" =
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (localScope i) "j",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,localBindings,TimestampSeedSetup.localBindings,
    SeedrandomInvocation.localsText,BindingWrite.changedBindings,BindingWrite.changedBinding,checked,
    checked_library,library,mixing,i.declared]
  rfl

theorem identifier_k (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    Environment.identifier (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "k" =
    Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      (.expressionResult (.reference ⟨.environment (scope i) "k",false⟩)) continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws := by
  unfold Environment.identifier
  rw [environment_size]
  simp [Environment.resolve,checked_local,locals,localBindings,TimestampSeedSetup.localBindings,
    SeedrandomInvocation.localsText,BindingWrite.changedBindings,BindingWrite.changedBinding,checked,
    checked_library,library,mixing,i.declared]
  rfl

theorem reference_q (i : Inputs)
    (receiver : Value) (control : Control) (continuation : List Frame) (global : ObjectId) (objectProto : Option ObjectId) (functionProto : Option ObjectId) (arrayProto : Option ObjectId) (stringProto : Option ObjectId) (numberProto : Option ObjectId) (booleanProto : Option ObjectId) (regexpProto : Option ObjectId) (dateProto : Option ObjectId) (throwIntrinsic : Option ObjectId) (exclusions : List (EnvId × List JSString)) (events : List ScheduledEvent) (nextEvent : EventId) (elapsed : Rat) (epoch : Int) (freeDraws : Nat) :
    identifierReference (Machine.mk (heap i) ⟨localScope i,localScope i,receiver,false⟩
      control continuation global objectProto functionProto arrayProto stringProto numberProto booleanProto regexpProto dateProto throwIntrinsic exclusions events nextEvent elapsed epoch freeDraws) "q" =
      .ok ⟨.environment (localScope i) "q",false⟩ := by
  simp [identifierReference,resolveName,checked_local,locals,localBindings,TimestampSeedSetup.localBindings,
    SeedrandomInvocation.localsText,BindingWrite.changedBindings,BindingWrite.changedBinding,
    Except.bind,bind,Except.pure,pure]

attribute [local cbv_opaque] mixing base heap scope localScope constructor key locals library outer
  checkedEnvironment readBinding setBinding Environment.identifier identifierReference Array.size List.length Number.ofNat
  TimestampSeedMixing.text
attribute [local cbv_eval] checked_local checked_library environment_size read_k read_j identifier_k identifier_j reference_q

theorem base_heap (i : Inputs) : (base i).heap=heap i := rfl

theorem base_context (i : Inputs) : (base i).context=⟨localScope i,localScope i,.object (mixing i).receiver,false⟩ := rfl

theorem base_control (i : Inputs) : (base i).control=.expressionResult (.value (.string (TimestampSeedMixing.text (mixing i)))) := rfl

theorem base_continuation (i : Inputs) : (base i).continuation=
    .variableWrite TimestampSeedSetup.remainingVariables ::
      .statementList (SeedrandomInvocation.body.drop 1) none ::
      .callBoundary (mixing i).globals.base.context none :: (mixing i).globals.base.continuation := rfl

theorem base_view (i : Inputs) :
    base i = {
    base i with
    heap := heap i
    context := ⟨localScope i,localScope i,.object (mixing i).receiver,false⟩
    control := .expressionResult (.value (.string (TimestampSeedMixing.text (mixing i))))
    continuation := .variableWrite TimestampSeedSetup.remainingVariables ::
      .statementList (SeedrandomInvocation.body.drop 1) none ::
      .callBoundary (mixing i).globals.base.context none :: (mixing i).globals.base.continuation } := by
  rw [←base_heap i,←base_context i,←base_control i,←base_continuation i]


theorem actual_constructor_arguments (i : Inputs) (fuel : Nat) :
    Builtins.run (10+fuel) (base i)=Builtins.run fuel (beforeCall i) := by
  conv => lhs; arg 2; rw [base_view i]
  rw [Nat.add_comm 10 fuel]
  cbv

theorem actual_mixing_to_constructor (i : Inputs) (fuel : Nat) :
    Builtins.run (12+fuel) (TimestampSeedMixing.returned (mixing i))=Builtins.run fuel (beforeCall i) := by
  rw [show 12+fuel=2+(10+fuel) by omega,actual_assignment]
  exact actual_constructor_arguments i fuel

end CookieClicker.JavaScript.TimestampSeedArc4Prelude

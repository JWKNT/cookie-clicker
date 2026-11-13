import CookieClicker.JavaScriptBindingWrite
import CookieClicker.JavaScriptSourceRead

/-! Source variable writes in the existing caller environment. No local layout
is replaced: all binding names, flags, other values, and outer links remain. -/
namespace CookieClicker.JavaScript.SourceBinding
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Slot (base : Machine) (name : String) where
  bindings : List Binding
  outer : Option EnvId
  binding : Binding
  present : checkedEnvironment base.heap base.context.lexicalEnvironment=
    .ok ⟨.declarative bindings,outer⟩
  found : bindings.find? (fun b=>b.name==name)=some binding
  mutable : binding.mutable=true

def Slot.after {base : Machine} {name : String} (slot : Slot base name) (value : Value) : Machine :=
  {base with
    heap:=BindingWrite.changedHeap base.heap base.context.lexicalEnvironment
      slot.bindings slot.outer name value}

def Slot.withContinuation {base : Machine} {name : String} (slot : Slot base name)
    (continuation : List Frame) : Slot {base with continuation} name :=
  ⟨slot.bindings,slot.outer,slot.binding,slot.present,slot.found,slot.mutable⟩

theorem Slot.exists {base : Machine} {name : String} (slot : Slot base name) :
    slot.bindings.any (fun b=>b.name==name)=true := by
  have same := List.find?_some slot.found
  exact List.any_eq_true.mpr ⟨slot.binding,List.mem_of_find?_eq_some slot.found,same⟩

theorem Slot.reference {base : Machine} {name : String} (slot : Slot base name) :
    identifierReference base name=.ok ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ := by
  simp [identifierReference,resolveName,slot.present,slot.exists,Except.bind,bind,Except.pure,pure]

theorem Slot.write {base : Machine} {name : String} (slot : Slot base name) (value : Value) :
    setBinding base.heap base.context.lexicalEnvironment name value base.context.strict=
      .ok (slot.after value).heap :=
  BindingWrite.native_set _ _ _ _ _ _ _ _ slot.present slot.found slot.mutable

theorem Slot.updated_present {base : Machine} {name : String} (slot : Slot base name) (value : Value) :
    checkedEnvironment (slot.after value).heap base.context.lexicalEnvironment=
      .ok ⟨.declarative (BindingWrite.changedBindings name value slot.bindings),slot.outer⟩ :=
  BindingWrite.changed_checked _ _ _ _ _ _ slot.present

theorem Slot.value_read {base : Machine} {name : String} (slot : Slot base name) (value : Value) :
    Reads (slot.after value) (.identifier name) value 3 := by
  apply local_identifier _ name value (BindingWrite.changedBindings name value slot.bindings) slot.outer
  · exact slot.updated_present value
  · simpa only [BindingWrite.same_names] using slot.exists
  · exact BindingWrite.changed_read _ _ _ _ _ _ _ slot.present slot.found

theorem Slot.other_read {base : Machine} {name : String} (slot : Slot base name) (value : Value)
    (what : String) (different : what≠name) :
    readBinding (slot.after value).heap base.context.lexicalEnvironment what=
      readBinding base.heap base.context.lexicalEnvironment what :=
  BindingWrite.changed_read_other _ _ _ _ _ _ _ different slot.present

def Slot.otherSlot {base : Machine} {name what : String} (slot : Slot base name)
    (other : Slot base what) (different : what≠name) (value : Value) : Slot (slot.after value) what := {
  bindings:=BindingWrite.changedBindings name value slot.bindings
  outer:=slot.outer
  binding:=other.binding
  present:=slot.updated_present value
  found:=by
    have same : slot.bindings=other.bindings ∧ slot.outer=other.outer := by
      have h:=slot.present.symm.trans other.present
      simpa using h
    rw [BindingWrite.changed_find_other name what value slot.bindings different,same.1]
    exact other.found
  mutable:=other.mutable }

theorem Slot.objects_preserved {base : Machine} {name : String} (slot : Slot base name) (value : Value) :
    (slot.after value).heap.objects=base.heap.objects := rfl

theorem Slot.other_environment {base : Machine} {name : String} (slot : Slot base name) (value : Value)
    (id : EnvId) (different : base.context.lexicalEnvironment≠id) :
    checkedEnvironment (slot.after value).heap id=checkedEnvironment base.heap id :=
  BindingWrite.changed_checked_other _ _ _ _ _ _ _ different

theorem variable_initializer (base : Machine) (name : String) (slot : Slot base name)
    (expression : Expr) (value : Value) (ticks : Nat)
    (read : Reads base expression value ticks) (noName : nameFrames expression (JSString.ofString name)=[])
    (fuel : Nat) :
    Builtins.run (ticks+4+fuel) {base with control:=.statement (.variable [(name,some expression)])}=
      Builtins.run fuel {slot.after value with control:=.completion (.normal none)} := by
  rw [show ticks+4+fuel=1+(ticks+(3+fuel)) by omega,Nat.add_comm 1 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {variables {base with
    control:=.statement (.variable [(name,some expression)])} [(name,some expression)]
    with elapsed:=base.elapsed}=_
  have referenced:=slot.reference
  simp only [variables,identifierReference] at referenced ⊢
  rw [referenced]
  simp only [checked,noName,List.nil_append]
  rw [read _ (by rfl),show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ value
    continuation:=.variableWrite []::base.continuation}=_
  rw [show 2+fuel=1+(1+fuel) by omega,Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) {putReference {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ value
    continuation:=.variableWrite []::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ value with elapsed:=base.elapsed}=_
  simp only [putReference,slot.present,checked,slot.write,result]
  rw [Nat.add_comm 1 fuel]
  rfl

/-- The selected native enumeration key is assigned to the existing local.
The original source body and for-in continuation are retained. -/
theorem forIn_next (base : Machine) (name : String) (slot : Slot base name)
    (loop : ForInState) (key : JSString) (remaining : List JSString)
    (keys : loop.remaining=key::remaining) (binding : loop.binding=.variable name)
    (shape : enumerationShape base.heap (base.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (3+fuel) {base with control:=.forInNext loop}=
      Builtins.run fuel {slot.after (.string key) with
        control:=.statement loop.body
        continuation:=.forInBody {loop with remaining}::base.continuation} := by
  have shapeSame : (!EnumerationEquality.check loop.shape loop.shape)=false := by simp [EnumerationEquality.check]
  have first : nextForIn {base with control:=.forInNext loop} loop=
      {base with
        control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ (.string key)
        continuation:=.forInAssigned {loop with remaining}::base.continuation} := by
    simp only [nextForIn,shape,checked,shapeSame,Bool.false_eq_true,↓reduceIte,keys,binding]
    rw [show identifierReference {base with control:=.forInNext loop} name=
      .ok ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ from slot.reference]
  rw [Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {nextForIn {base with control:=.forInNext loop} loop with elapsed:=base.elapsed}=_
  rw [first]
  change Builtins.run (fuel+1) {putReference {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ (.string key)
    continuation:=.forInAssigned {loop with remaining}::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ (.string key)
    with elapsed:=base.elapsed}=_
  simp only [putReference,slot.present,checked,slot.write,result]
  rfl

end CookieClicker.JavaScript.SourceBinding

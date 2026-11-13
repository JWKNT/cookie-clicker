import CookieClicker.JavaScriptBuildingStore

namespace CookieClicker.JavaScript.BuildingDigits
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure Slot (base : Machine) where
  bindings : List Binding
  outer : Option EnvId
  oldValue : Value
  deletable : Bool
  present : checkedEnvironment base.heap base.context.lexicalEnvironment=
    .ok ⟨.declarative bindings,outer⟩
  found : bindings.find? (fun binding=>binding.name=="digits")=
    some {name:="digits",value:=oldValue,deletable}

def Slot.updated {base : Machine} (slot : Slot base) (value : Value) : List Binding :=
  slot.bindings.map fun binding=>if binding.name=="digits" then {binding with value,initialized:=true} else binding

def Slot.after {base : Machine} (slot : Slot base) (value : Value) : Machine := {
  base with
  heap:={base.heap with
    environments:=base.heap.environments.set! base.context.lexicalEnvironment
      ⟨.declarative (slot.updated value),slot.outer⟩} }

theorem Slot.exists {base : Machine} (slot : Slot base) :
    slot.bindings.any (fun binding=>binding.name=="digits")=true := by
  apply List.any_eq_true.mpr
  exact ⟨_,List.mem_of_find?_eq_some slot.found,rfl⟩

theorem Slot.bound {base : Machine} (slot : Slot base) :
    base.context.lexicalEnvironment<base.heap.environments.size := by
  cases found:base.heap.environments[base.context.lexicalEnvironment]? with
  | none =>
    have present:=slot.present
    simp [checkedEnvironment,Heap.environment?,found] at present
  | some value => exact (Array.getElem?_eq_some_iff.mp found).1

theorem Slot.reference {base : Machine} (slot : Slot base) :
    identifierReference base "digits"=
      .ok ⟨.environment base.context.lexicalEnvironment "digits",base.context.strict⟩ := by
  simp [identifierReference,resolveName,slot.present,slot.exists,Except.bind,bind,Except.pure,pure]

theorem Slot.write {base : Machine} (slot : Slot base) (value : Value) :
    setBinding base.heap base.context.lexicalEnvironment "digits" value base.context.strict=
      .ok (slot.after value).heap := by
  simp [setBinding,slot.present,slot.found,replaceEnvironment,Heap.writeEnvironment,slot.bound,
    Slot.after,Slot.updated,Except.bind,bind,Except.pure,pure]

theorem Slot.updated_present {base : Machine} (slot : Slot base) (value : Value) :
    checkedEnvironment (slot.after value).heap base.context.lexicalEnvironment=
      .ok ⟨.declarative (slot.updated value),slot.outer⟩ := by
  simp [Slot.after,checkedEnvironment,Heap.environment?,slot.bound,Array.set!_eq_setIfInBounds]

theorem Slot.updated_found {base : Machine} (slot : Slot base) (value : Value) :
    (slot.updated value).find? (fun binding=>binding.name=="digits")=
      some {name:="digits",value,deletable:=slot.deletable} := by
  have same : (fun (binding : Binding)=>
      (if binding.name=="digits" then {binding with value,initialized:=true} else binding).name=="digits")=
      (fun binding=>binding.name=="digits") := by
    funext binding
    split <;> rfl
  simp only [Slot.updated,List.find?_map,Function.comp_def,same,slot.found,Option.map_some]
  rfl

theorem Slot.read {base : Machine} (slot : Slot base) (value : Value) :
    Reads (slot.after value) (.identifier "digits") value 3 := by
  apply local_identifier _ "digits" value (slot.updated value) slot.outer
  · exact slot.updated_present value
  · apply List.any_eq_true.mpr
    exact ⟨_,List.mem_of_find?_eq_some (slot.updated_found value),rfl⟩
  · change readBinding (slot.after value).heap base.context.lexicalEnvironment "digits"=.ok value
    simp [readBinding,slot.updated_present value,slot.updated_found value,Except.bind,bind,Except.pure,pure]

theorem native_variable (base : Machine) (slot : Slot base) (expression : Expr) (value : Value) (ticks : Nat)
    (read : Reads base expression value ticks) (noName : nameFrames expression (JSString.ofString "digits")=[])
    (fuel : Nat) :
    Builtins.run (ticks+4+fuel) {base with control:=.statement (.variable [("digits",some expression)])}=
      Builtins.run fuel {slot.after value with control:=.completion (.normal none)} := by
  rw [show ticks+4+fuel=1+(ticks+(3+fuel)) by omega,Nat.add_comm 1 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {variables {base with
    control:=.statement (.variable [("digits",some expression)])} [("digits",some expression)]
    with elapsed:=base.elapsed}=_
  have referenced:=slot.reference
  simp only [variables,identifierReference] at referenced ⊢
  rw [referenced]
  simp only [checked,noName,List.nil_append]
  rw [read _ (by rfl),show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment "digits",base.context.strict⟩ value
    continuation:=.variableWrite []::base.continuation}=_
  rw [show 2+fuel=1+(1+fuel) by omega,Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) {putReference {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment "digits",base.context.strict⟩ value
    continuation:=.variableWrite []::base.continuation}
    ⟨.environment base.context.lexicalEnvironment "digits",base.context.strict⟩ value with elapsed:=base.elapsed}=_
  simp only [putReference,slot.present,checked,slot.write,result]
  rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.BuildingDigits

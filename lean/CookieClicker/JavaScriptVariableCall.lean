import CookieClicker.JavaScriptSourceBinding

/-! Native variable initializers that call functions and retain allocations.
The prefix stops at the original expression. The suffix writes its returned
value through the existing caller binding. -/
namespace CookieClicker.JavaScript.VariableCall
open SourceBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def frames (base : Machine) (name : String) : List Frame :=
  .assignmentRight .assign ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ none::
    .variableWrite []::base.continuation

theorem source_prefix (base : Machine) (name : String) (slot : Slot base name)
    (expression : Expr) (noName : nameFrames expression (JSString.ofString name)=[]) (fuel : Nat) :
    Builtins.run (1+fuel) {base with control:=.statement (.variable [(name,some expression)])}=
      Builtins.run fuel {base with control:=.expression expression,continuation:=frames base name} := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {variables {base with
    control:=.statement (.variable [(name,some expression)])} [(name,some expression)]
    with elapsed:=base.elapsed}=_
  simp only [variables,show identifierReference {base with
    control:=.statement (.variable [(name,some expression)])} name=
      .ok ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ from slot.reference,
    checked,noName,List.nil_append]
  rfl

theorem source_suffix (base : Machine) (name : String) (slot : Slot base name)
    (value : Value) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value value)
      continuation:=frames base name}=
      Builtins.run fuel {slot.after value with control:=.completion (.normal none)} := by
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
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

def appended (base : Machine) (objects : Array JSObject) (added : Array LexicalEnvironment) : Machine :=
  {base with heap:=⟨objects,base.heap.environments++added⟩}

theorem checked_appended (base : Machine) (objects : Array JSObject) (added : Array LexicalEnvironment)
    (id : EnvId) (environment : LexicalEnvironment)
    (present : checkedEnvironment base.heap id=.ok environment) :
    checkedEnvironment (appended base objects added).heap id=.ok environment := by
  cases read : base.heap.environment? id with
  | none => simp [checkedEnvironment,read] at present
  | some old =>
    have same : old=environment := by simpa [checkedEnvironment,read] using present
    have inside:= (Array.getElem?_eq_some_iff.mp read).1
    have kept : (base.heap.environments++added)[id]?=some old := by
      simpa only [Array.getElem?_append,if_pos inside,Heap.environment?] using read
    simp only [appended,checkedEnvironment,Heap.environment?,kept,same]

/-- The binding frame after any retained finite block of callee allocations. -/
def appended_slot {base : Machine} {name : String} (slot : Slot base name)
    (objects : Array JSObject) (added : Array LexicalEnvironment) :
    Slot (appended base objects added) name := {
  bindings:=slot.bindings
  outer:=slot.outer
  binding:=slot.binding
  present:=checked_appended base objects added _ _ slot.present
  found:=slot.found
  mutable:=slot.mutable }

end CookieClicker.JavaScript.VariableCall

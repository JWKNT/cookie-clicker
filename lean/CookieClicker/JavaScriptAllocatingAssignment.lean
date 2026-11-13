import CookieClicker.JavaScriptAllocatingInitializer

/-! Assignment to an existing local can retain the actual heap and environment
allocations of its right-hand call. The original reference remains unchanged. -/
namespace CookieClicker.JavaScript.AllocatingAssignment
open SourceBinding AllocatingInitializer
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def reference (base : Machine) (name : String) : Reference :=
  ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
def frames (base : Machine) (name : String) : List Frame :=
  .assignmentRight .assign (reference base name) none::.expressionStatement::base.continuation

theorem source_prefix (base : Machine) (name : String) (slot : Slot base name)
    (expression : Expr) (noName : nameFrames expression (JSString.ofString name)=[]) (fuel : Nat) :
    Builtins.run (4+fuel) {base with
      control:=.statement (.expression (.assignment .assign (.identifier name) expression))}=
    Builtins.run fuel {base with control:=.expression expression,continuation:=frames base name} := by
  conv => lhs;arg 1;rw [show 4+fuel=3+(1+fuel) by omega,Nat.add_comm 3 (1+fuel)]
  change Builtins.run (1+fuel) (Environment.identifier {base with
    control:=.expression (.identifier name)
    continuation:=.assignmentLeft .assign expression::.expressionStatement::base.continuation} name)=_
  simp only [Environment.identifier,Environment.resolve,slot.present,slot.exists,checked]
  conv => lhs;arg 1;rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {base with
    control:=.expression expression,continuation:=nameFrames expression (JSString.ofString name)++frames base name}=_
  rw [noName,List.nil_append]

theorem source_suffix (base : Machine) (name : String) (slot : Slot base name) (value : Value) (fuel : Nat) :
    Builtins.run (3+fuel) {base with control:=.expressionResult (.value value),continuation:=frames base name}=
      Builtins.run fuel {slot.after value with control:=.completion (.normal (some value))} := by
  conv => lhs;arg 1;rw [show 3+fuel=2+(1+fuel) by omega,Nat.add_comm 2 (1+fuel)]
  change Builtins.run (1+fuel) {putReference {base with
    control:=.putValue (reference base name) value,continuation:=.expressionStatement::base.continuation}
    (reference base name) value with elapsed:=base.elapsed}=_
  simp only [putReference,reference,slot.present,checked,slot.write,result]
  conv => lhs;arg 1;rw [Nat.add_comm 1 fuel]
  rfl

def after (base : Machine) (name : String) (slot : Slot base name) (output : Result base) (value : Value) : Machine :=
  {(output.slot slot).after value with control:=.completion (.normal (some value))}

theorem compose (base : Machine) (name : String) (slot : Slot base name)
    (expression : Expr) (noName : nameFrames expression (JSString.ofString name)=[])
    (value : Value) (steps : Nat) (output : Result base)
    (sourceCall : ∀ fuel, Builtins.run (steps+fuel) {base with
      control:=.expression expression,continuation:=frames base name}=
      Builtins.run fuel {output.machine with
        control:=.expressionResult (.value value),continuation:=frames base name}) (fuel : Nat) :
    Builtins.run (steps+7+fuel) {base with control:=.statement (.expression (.assignment .assign (.identifier name) expression))}=
      Builtins.run fuel (after base name slot output value) := by
  rw [show steps+7+fuel=4+(steps+(3+fuel)) by omega,source_prefix base name slot expression noName,sourceCall]
  exact source_suffix output.machine name (output.slot slot) value fuel

end CookieClicker.JavaScript.AllocatingAssignment

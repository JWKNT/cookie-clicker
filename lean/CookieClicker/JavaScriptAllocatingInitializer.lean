import CookieClicker.JavaScriptVariableCall

/-! Variable initializers can retain real allocations from a complete call.
The caller binding is read from its original entry and derived after the call. -/
namespace CookieClicker.JavaScript.AllocatingInitializer
open SourceBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Result (base : Machine) where
  heap : Heap
  suffix : Array LexicalEnvironment
  environments : heap.environments=base.heap.environments++suffix

def Result.machine {base : Machine} (output : Result base) : Machine := {base with heap:=output.heap}

def Result.slot {base : Machine} (output : Result base) {name : String} (original : Slot base name) :
    Slot output.machine name := {
  bindings:=original.bindings,outer:=original.outer,binding:=original.binding
  found:=original.found,mutable:=original.mutable
  present:=by
    have kept:=VariableCall.checked_appended base output.heap.objects output.suffix
      base.context.lexicalEnvironment _ original.present
    simpa only [Result.machine,VariableCall.appended,checkedEnvironment,Heap.environment?,output.environments] using kept }

def Result.after {base : Machine} (output : Result base) {name : String}
    (original : Slot base name) (value : Value) : Machine :=
  {(output.slot original).after value with control:=.completion (.normal none)}

theorem compose (base : Machine) (name : String) (slot : Slot base name)
    (expression : Expr) (noName : nameFrames expression (JSString.ofString name)=[])
    (value : Value) (steps : Nat) (output : Result base)
    (sourceCall : ∀ fuel, Builtins.run (steps+fuel) {base with
      control:=.expression expression,continuation:=VariableCall.frames base name}=
      Builtins.run fuel {output.machine with
        control:=.expressionResult (.value value)
        continuation:=VariableCall.frames base name}) (fuel : Nat) :
    Builtins.run (steps+4+fuel) {base with control:=.statement (.variable [(name,some expression)])}=
      Builtins.run fuel (output.after slot value) := by
  rw [show steps+4+fuel=1+(steps+(3+fuel)) by omega,
    VariableCall.source_prefix base name slot expression noName,sourceCall]
  exact VariableCall.source_suffix output.machine name (output.slot slot) value fuel

end CookieClicker.JavaScript.AllocatingInitializer

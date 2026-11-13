import CookieClicker.JavaScriptGodzamokLocalTransport
import CookieClicker.JavaScriptPropertyUpdate

namespace CookieClicker.JavaScript.LocalNumeric
open SourceRead SourceBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

 theorem source_update (base : Machine) (name : String) (slot : Slot base name)
    (old : UInt64) (read : readBinding base.heap base.context.lexicalEnvironment name=.ok (.number old))
    (operator : UpdateOp) (isPrefix : Bool) (fuel : Nat) :
    Builtins.run (9+fuel) {base with
      control:=.statement (.expression (.update operator (.identifier name) isPrefix))}=
    Builtins.run fuel {slot.after (.number (PropertyUpdate.changedNumber operator old)) with
      control:=.completion (.normal (some (.number (if isPrefix then PropertyUpdate.changedNumber operator old else old))))} := by
  conv => lhs; arg 1; rw [show 9+fuel=3+(6+fuel) by omega,Nat.add_comm 3 (6+fuel)]
  change Builtins.run (6+fuel) (Environment.identifier {base with
    control:=.expression (.identifier name)
    continuation:=.update operator isPrefix::.expressionStatement::base.continuation} name)=_
  simp only [Environment.identifier,Environment.resolve,slot.present,slot.exists,checked]
  conv => lhs; arg 1; rw [show 6+fuel=1+(5+fuel) by omega,Nat.add_comm 1 (5+fuel)]
  change Builtins.run (5+fuel) {base with
    control:=.getValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
    continuation:=.updateRead operator ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ isPrefix::
      .expressionStatement::base.continuation}=_
  conv => lhs; arg 1; rw [show 5+fuel=1+(4+fuel) by omega,Nat.add_comm 1 (4+fuel)]
  change Builtins.run (4+fuel) {getReference {base with
    control:=.getValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
    continuation:=.updateRead operator ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ isPrefix::
      .expressionStatement::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ with elapsed:=base.elapsed}=_
  simp only [getReference,slot.present,checked,read,result]
  conv => lhs; arg 1; rw [show 4+fuel=1+(3+fuel) by omega,Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
      (.number (PropertyUpdate.changedNumber operator old))
    continuation:=.putResult (.number (if isPrefix then PropertyUpdate.changedNumber operator old else old))::
      .expressionStatement::base.continuation}=_
  conv => lhs; arg 1; rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {putReference {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
      (.number (PropertyUpdate.changedNumber operator old))
    continuation:=.putResult (.number (if isPrefix then PropertyUpdate.changedNumber operator old else old))::
      .expressionStatement::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
      (.number (PropertyUpdate.changedNumber operator old)) with elapsed:=base.elapsed}=_
  simp only [putReference,slot.present,checked,slot.write,result]
  conv => lhs; arg 1; rw [Nat.add_comm 2 fuel]
  rfl

 theorem source_add (base : Machine) (name : String) (slot : Slot base name)
    (old credit : UInt64) (expression : Expr) (ticks : Nat)
    (oldRead : readBinding base.heap base.context.lexicalEnvironment name=.ok (.number old))
    (creditRead : Reads base expression (.number credit) ticks) (fuel : Nat) :
    Builtins.run (ticks+10+fuel) {base with
      control:=.statement (.expression (.assignment .add (.identifier name) expression))}=
    Builtins.run fuel {slot.after (.number (Number.add old credit)) with
      control:=.completion (.normal (some (.number (Number.add old credit))))} := by
  conv => lhs; arg 1; rw [show ticks+10+fuel=3+(1+(1+(1+(ticks+(4+fuel))))) by omega,Nat.add_comm 3 (1+(1+(1+(ticks+(4+fuel)))))]
  change Builtins.run (1+(1+(1+(ticks+(4+fuel))))) (Environment.identifier {base with
    control:=.expression (.identifier name)
    continuation:=.assignmentLeft .add expression::.expressionStatement::base.continuation} name)=_
  simp only [Environment.identifier,Environment.resolve,slot.present,slot.exists,checked]
  conv => lhs; arg 1; rw [Nat.add_comm 1 (1+(1+(ticks+(4+fuel))))]
  change Builtins.run (1+(1+(ticks+(4+fuel)))) {base with
    control:=.getValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
    continuation:=.assignmentRead .add ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ expression::
      .expressionStatement::base.continuation}=_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (1+(ticks+(4+fuel)))]
  change Builtins.run (1+(ticks+(4+fuel))) {getReference {base with
    control:=.getValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
    continuation:=.assignmentRead .add ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ expression::
      .expressionStatement::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ with elapsed:=base.elapsed}=_
  simp only [getReference,slot.present,checked,oldRead,result]
  conv => lhs; arg 1; rw [Nat.add_comm 1 (ticks+(4+fuel))]
  change Builtins.run (ticks+(4+fuel)) {base with
    control:=.expression expression
    continuation:=.assignmentRight .add ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ (some (.number old))::
      .expressionStatement::base.continuation}=_
  rw [creditRead _ (by rfl)]
  conv => lhs; arg 1; rw [show 4+fuel=3+(1+fuel) by omega,Nat.add_comm 3 (1+fuel)]
  change Builtins.run (1+fuel) {putReference {base with
    control:=.putValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ (.number (Number.add old credit))
    continuation:=.expressionStatement::base.continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ (.number (Number.add old credit)) with elapsed:=base.elapsed}=_
  simp only [putReference,slot.present,checked,slot.write,result]
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.LocalNumeric

import CookieClicker.JavaScriptSourceRead

/-! Reads through a retained declarative closure path. The target binding,
its value, and every intervening environment remain explicit. -/
namespace CookieClicker.JavaScript.CapturedRead
open SourceRead

theorem identifier (base : Machine) (name : String) (value : Value)
    (target depth : Nat) (bindings : List Binding) (outer : Option EnvId)
    (path : HasEnvironment.DeclarativePath base.heap.environments name
      base.context.lexicalEnvironment target depth)
    (room : depth≤base.heap.environments.size)
    (present : checkedEnvironment base.heap target=.ok ⟨.declarative bindings,outer⟩)
    (found : bindings.any (fun b=>b.name==name)=true)
    (read : readBinding base.heap target name=.ok value) :
    Reads base (.identifier name) value 3 := by
  intro continuation ordinary fuel
  let start : Machine := {base with control:=.expression (.identifier name),continuation}
  have identified : Environment.identifier start name={start with
      control:=.expressionResult (.reference ⟨.environment target name,base.context.strict⟩)} := by
    unfold Environment.identifier
    rw [show start.heap.environments.size+1=depth+(start.heap.environments.size-depth+1) by
      dsimp only [start]; omega]
    rw [HasEnvironment.resolve_path start name base.context.strict _ target depth _ path,
      Environment.resolve_declared start _ target name base.context.strict bindings outer present found]
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) (Environment.identifier start name)=_
  rw [identified]
  apply reference_value {base with continuation} _ _ ordinary
  simp only [getReference,present,read,checked,result]

end CookieClicker.JavaScript.CapturedRead

import CookieClicker.JavaScriptSourceRead

namespace CookieClicker.JavaScript.SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem typeof_local (base : Machine) (name : String) (value resultValue : Value)
    (bindings : List Binding) (outer : Option EnvId)
    (environment : checkedEnvironment base.heap base.context.lexicalEnvironment=
      .ok ⟨.declarative bindings,outer⟩)
    (found : bindings.any (fun b=>b.name==name)=true)
    (read : readBinding base.heap base.context.lexicalEnvironment name=.ok value)
    (typed : unary base.heap .typeOf value=.ok resultValue) :
    Reads base (.unary .typeOf (.identifier name)) resultValue 5 := by
  intro continuation ordinary fuel
  let entered := {base with
    control:=.expression (.identifier name)
    continuation:=.unary .typeOf::continuation}
  have identified : Environment.identifier entered name=
      {entered with control:=.expressionResult (.reference
        ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩)} :=
    Environment.resolve_declared entered base.heap.environments.size base.context.lexicalEnvironment
      name base.context.strict bindings outer environment found
  rw [Nat.add_comm 5 fuel]
  change Builtins.run (fuel+3) (Environment.identifier entered name)=_
  rw [identified]
  change Builtins.run (fuel+1) {getReference {base with
    control:=.getValue ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩
    continuation:=.unary .typeOf::continuation}
    ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩ with elapsed:=base.elapsed}=_
  simp only [getReference,environment,read,checked,result]
  change Builtins.run (fuel+1) {base with
    control:=.expressionResult (.value value)
    continuation:=.unary .typeOf::continuation}=_
  change Builtins.run fuel (Builtins.builtinStep {base with
    control:=.expressionResult (.value value)
    continuation:=.unary .typeOf::continuation})=_
  simp [Builtins.builtinStep,step,internalStep,consumeValue,typed,checked,result]

end CookieClicker.JavaScript.SourceRead

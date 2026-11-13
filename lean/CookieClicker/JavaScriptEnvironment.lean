import CookieClicker.JavaScriptEval

/-! Resumable identifier resolution through lexical object environments.
HasProperty requests retain the enclosing resolution operation; a native boolean
response cannot accidentally become the identifier's value. Initial native
unscopables metadata is supported only while Symbol mutation is unresolved.
-/
namespace CookieClicker.JavaScript.Environment

private def referenceResult (machine : Machine) (reference : Reference) : Machine :=
  { machine with control := .expressionResult (.reference reference) }

private def unbound (machine : Machine) (name : String) (strict : Bool) : Machine :=
  referenceResult machine ⟨.unresolvable name,strict⟩

private def excluded (machine : Machine) (environment : EnvId) (name : JSString) : Bool :=
  (machine.objectEnvironmentExclusions.find? (fun entry => entry.1 == environment)).any
    (fun entry => entry.2.contains name)

def resolve : Nat → Machine → EnvId → String → Bool → Machine
  | 0,machine,_,_,_ => fail machine (.fault .cyclicEnvironment)
  | fuel+1,machine,id,name,strict =>
    checked machine (checkedEnvironment machine.heap id) fun environment =>
      let found := referenceResult machine ⟨.environment id name,strict⟩
      let outer := fun (_ : Unit) => match environment.outer with
        | some next => resolve fuel machine next name strict
        | none => unbound machine name strict
      match environment.record with
      | .declarative bindings =>
        if bindings.any (fun binding => binding.name == name) then found else outer ()
      | .object object _ =>
        if excluded machine id (JSString.ofString name) then outer () else
        match lookupProperty machine.heap object (JSString.ofString name) with
        | .ok (some _) => found
        | .ok none => outer ()
        | .error (.unresolved (.hostGet className hostId property)) =>
          let continuation : BuiltinContinuation := {
            id := ⟨"Environment",name⟩, phase := "hasBinding", thisValue := .undefined,
            indices := [fuel,id,if strict then 1 else 0] }
          { machine with
            control := .unresolved (.hostHas className hostId property)
            continuation := .builtin continuation :: machine.continuation }
        | .error failure => fail machine failure

def identifier (machine : Machine) (name : String) : Machine :=
  resolve (machine.heap.environments.size+1) machine machine.context.lexicalEnvironment
    name machine.context.strict

theorem resolve_declared (machine : Machine) (fuel id : Nat) (name : String)
    (strict : Bool) (bindings : List Binding) (outer : Option EnvId)
    (environment : checkedEnvironment machine.heap id = .ok ⟨.declarative bindings,outer⟩)
    (found : bindings.any (fun binding => binding.name == name) = true) :
    resolve (fuel+1) machine id name strict =
      { machine with control := .expressionResult (.reference ⟨.environment id name,strict⟩) } := by
  simp [resolve, environment, checked, found, referenceResult]

theorem identifier_declared_eq_original (machine : Machine) (name : String)
    (bindings : List Binding) (outer : Option EnvId)
    (environment : checkedEnvironment machine.heap machine.context.lexicalEnvironment =
      .ok ⟨.declarative bindings,outer⟩)
    (found : bindings.any (fun binding => binding.name == name) = true) :
    identifier machine name = evaluateExpression machine (.identifier name) := by
  unfold identifier
  rw [resolve_declared machine machine.heap.environments.size machine.context.lexicalEnvironment
    name machine.context.strict bindings outer environment found]
  simp [evaluateExpression, identifierReference, resolveName, environment, checked, found,
    Except.bind, Except.pure, pure, bind]

def resume (machine : Machine) (continuation : BuiltinContinuation) (value : Value) : Machine :=
  match continuation.phase,continuation.indices,value with
  | "hasBinding",[fuel,id,strict],.boolean found =>
    if found then referenceResult machine ⟨.environment id continuation.id.name,strict != 0⟩
    else checked machine (checkedEnvironment machine.heap id) fun environment =>
      match environment.outer with
      | some outer => resolve fuel machine outer continuation.id.name (strict != 0)
      | none => unbound machine continuation.id.name (strict != 0)
  | _,_,_ => fail machine (.fault (.invalidContinuation "Identifier HasProperty response"))

end CookieClicker.JavaScript.Environment

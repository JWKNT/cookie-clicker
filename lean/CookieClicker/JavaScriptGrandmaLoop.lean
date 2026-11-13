import CookieClicker.JavaScriptGrandmaCount

namespace CookieClicker.JavaScript.GrandmaLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem local_i_reference (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment) :
    identifierReference (GrandmaLocals.start base objects leading outer v suffix) "i"=
      .ok ⟨.environment (GrandmaLocals.slotIndex leading) "i",false⟩ := by
  simp [identifierReference,resolveName,GrandmaLocals.start,GrandmaLocals.checked_local,
    GrandmaLocals.bindings,Except.bind,bind,pure,Except.pure]

/-- Native for-in chooses the next key, writes the original caller local i,
and enters the intact source body with its enumeration continuation retained. -/
theorem native_next (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment)
    (loop : ForInState) (key : JSString) (remaining : List JSString)
    (keys : loop.remaining=key::remaining) (binding : loop.binding=.variable "i")
    (shape : enumerationShape (GrandmaLocals.heap objects leading outer v suffix) (objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    let before := GrandmaLocals.start base objects leading outer v suffix
    Builtins.run (3+fuel) {before with control:=.forInNext loop}=
      Builtins.run fuel {before with
        heap := GrandmaLocals.heap objects leading outer {v with i:=.string key} suffix
        control := .statement loop.body
        continuation := .forInBody {loop with remaining}::base.continuation} := by
  let before := GrandmaLocals.start base objects leading outer v suffix
  have shapeSame : (!EnumerationEquality.check loop.shape loop.shape)=false := by simp [EnumerationEquality.check]
  have first : nextForIn {before with control:=.forInNext loop} loop=
      {before with
        control:=.putValue ⟨.environment (GrandmaLocals.slotIndex leading) "i",false⟩ (.string key)
        continuation:=.forInAssigned {loop with remaining}::base.continuation} := by
    simp only [nextForIn,show enumerationShape before.heap (before.heap.objects.size+1) loop.object=.ok loop.shape from shape,
      checked,shapeSame,Bool.false_eq_true,↓reduceIte,keys,binding]
    rw [show identifierReference {before with control:=.forInNext loop} "i"=
      .ok ⟨.environment (GrandmaLocals.slotIndex leading) "i",false⟩ from
      local_i_reference base objects leading outer v suffix]
    rfl
  dsimp only
  rw [Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {nextForIn {before with control:=.forInNext loop} loop with elapsed:=base.elapsed}=_
  rw [first]
  change Builtins.run (fuel+1) {putReference {before with
    control:=.putValue ⟨.environment (GrandmaLocals.slotIndex leading) "i",false⟩ (.string key)
    continuation:=.forInAssigned {loop with remaining}::base.continuation}
    ⟨.environment (GrandmaLocals.slotIndex leading) "i",false⟩ (.string key) with elapsed:=base.elapsed}=_
  simp only [putReference,before,GrandmaLocals.start,GrandmaLocals.checked_local,GrandmaLocals.set_i,checked,result]
  rfl

theorem body_to_next (base : Machine) (loop : ForInState) (value : Option Value) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal value)
      continuation:=.forInBody loop::base.continuation}=
      Builtins.run fuel {base with control:=.forInNext {loop with previous:=value.or loop.previous}} := by
  cases value <;> rw [Nat.add_comm 1 fuel] <;> rfl

end CookieClicker.JavaScript.GrandmaLoop
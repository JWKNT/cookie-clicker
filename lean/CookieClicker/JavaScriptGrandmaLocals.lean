import CookieClicker.JavaScriptGrandmaSource
import CookieClicker.JavaScriptIdentifierPath

/-! Actual Grandma callback locals, including native declaration order and
arbitrary trailing environments left by source calls. -/

namespace CookieClicker.JavaScript.GrandmaLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  me : Value
  arguments : Value
  mult : Value := .undefined
  i : Value := .undefined
  add : Value := .undefined
  num : Value := .undefined

def bindings (v : Values) : List Binding := [
  {name := "me",value := v.me},{name := "arguments",value := v.arguments},
  {name := "mult",value := v.mult},{name := "i",value := v.i},
  {name := "add",value := v.add},{name := "num",value := v.num}]

def slotIndex (leading : Array LexicalEnvironment) : EnvId := leading.size

def heap (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) : Heap := {
  objects
  environments := (leading.push ⟨.declarative (bindings v),some outer⟩) ++ suffix }

theorem checked_local (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    checkedEnvironment (heap objects leading outer v suffix) (slotIndex leading) =
      .ok ⟨.declarative (bindings v),some outer⟩ := by
  simp [checkedEnvironment,Heap.environment?,heap,slotIndex,Array.getElem?_append_left]

theorem replace_local (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v next : Values) (suffix : Array LexicalEnvironment) :
    replaceEnvironment (heap objects leading outer v suffix) (slotIndex leading)
      ⟨.declarative (bindings next),some outer⟩ =
      .ok (heap objects leading outer next suffix) := by
  have bound : leading.size < leading.size+1+suffix.size := by omega
  simp [replaceEnvironment,Heap.writeEnvironment,heap,slotIndex,bound,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_append_left,Array.set_push]

theorem read_me (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "me" = .ok v.me := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments" = .ok v.arguments := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_add (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "add" = .ok v.add := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_mult (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "mult" = .ok v.mult := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_num (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "num" = .ok v.num := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_i (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "i" = .ok v.i := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_add (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "add" next false =
      .ok (heap objects leading outer {v with add := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with add := next} suffix

theorem has_add (v : Values) :
    (bindings v).any (fun binding => binding.name == "add") = true := by
  simp [bindings]

theorem set_mult (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "mult" next false =
      .ok (heap objects leading outer {v with mult := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with mult := next} suffix

theorem has_mult (v : Values) :
    (bindings v).any (fun binding => binding.name == "mult") = true := by
  simp [bindings]

theorem set_num (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "num" next false =
      .ok (heap objects leading outer {v with num := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with num := next} suffix

theorem has_num (v : Values) :
    (bindings v).any (fun binding => binding.name == "num") = true := by
  simp [bindings]

theorem set_i (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "i" next false =
      .ok (heap objects leading outer {v with i := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with i := next} suffix

theorem has_i (v : Values) :
    (bindings v).any (fun binding => binding.name == "i") = true := by
  simp [bindings]

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap objects leading outer v suffix
  context := ⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control := .statement ProductionSyntax.GrandmaCpsBody }

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding
attribute [local cbv_eval] checked_local set_mult has_mult

theorem actual_initial_mult_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before := start base objects leading outer v suffix
    Builtins.run (6+fuel) before = Builtins.run fuel {before with
      heap := heap objects leading outer {v with mult := .number Number.one} suffix
      control := .completion (.normal none)
      continuation := .statementList GrandmaSource.body.tail none :: base.continuation} := by
  rw [Nat.add_comm 6 fuel]
  cbv
  try simp only [checked_local,has_mult,set_mult]
  try cbv
  try simp only [checked_local,has_mult,set_mult]
  try cbv

end CookieClicker.JavaScript.GrandmaLocals

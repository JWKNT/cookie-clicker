import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptIdentifierPath

/-! Native local state for the intact Cursor sell-multiplier callback.
The arguments and giveBack bindings remain before nested-call allocations. -/

namespace CookieClicker.JavaScript.CursorSellLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  arguments : Value
  giveBack : Value := .undefined

def bindings (v : Values) : List Binding := [
  {name := "arguments",value := v.arguments},
  {name := "giveBack",value := v.giveBack}]

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

theorem read_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments" = .ok v.arguments := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_giveBack (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "giveBack" = .ok v.giveBack := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_giveBack (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "giveBack" next false =
      .ok (heap objects leading outer {v with giveBack := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with giveBack := next} suffix

theorem has_giveBack (v : Values) :
    (bindings v).any (fun binding => binding.name == "giveBack") = true := by
  simp [bindings]

def body : List Stmt := match CursorCycleSyntax.getSellMultiplierBody with
  | .block statements => statements
  | other => [other]

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap objects leading outer v suffix
  context := ⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control := .statement CursorCycleSyntax.getSellMultiplierBody }

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding
attribute [local cbv_eval] checked_local set_giveBack has_giveBack

theorem actual_initial_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before := start base objects leading outer v suffix
    Builtins.run (6+fuel) before = Builtins.run fuel {before with
      heap := heap objects leading outer {v with giveBack := .number 4598175219545276416} suffix
      control := .completion (.normal none)
      continuation := .statementList body.tail none :: base.continuation} := by
  rw [Nat.add_comm 6 fuel]
  cbv
  try simp only [checked_local,has_giveBack,set_giveBack]
  try cbv
  try simp only [checked_local,has_giveBack,set_giveBack]
  try cbv

end CookieClicker.JavaScript.CursorSellLocals

import CookieClicker.JavaScriptGainHelpersSyntax
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptIdentifierPath

/-! Native local state for the common runModHookOnValue callback.
The actual four bindings persist before allocations left by nested calls. -/

namespace CookieClicker.JavaScript.ModHookLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  hook : Value
  val : Value
  arguments : Value
  i : Value := .undefined

def bindings (v : Values) : List Binding := [
  {name := "hook",value := v.hook},{name := "val",value := v.val},{name := "arguments",value := v.arguments},
  {name := "i",value := v.i}]

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

theorem read_hook (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "hook" = .ok v.hook := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_val (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "val" = .ok v.val := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments" = .ok v.arguments := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_i (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "i" = .ok v.i := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_i (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "i" next false =
      .ok (heap objects leading outer {v with i := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with i := next} suffix

theorem has_i (v : Values) :
    (bindings v).any (fun binding => binding.name == "i") = true := by
  simp [bindings]

def body : List Stmt := match GainHelpersSyntax.runModHookOnValueBody with
  | .block statements => statements
  | other => [other]

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap objects leading outer v suffix
  context := ⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control := .statement GainHelpersSyntax.runModHookOnValueBody }

end CookieClicker.JavaScript.ModHookLocals

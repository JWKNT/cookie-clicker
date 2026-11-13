import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptIdentifierPath

/-! Native local state for the intact Cursor price callback.
The n, arguments and price bindings remain before nested-call allocations. -/

namespace CookieClicker.JavaScript.CursorGetPriceLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  n : Value
  arguments : Value
  price : Value := .undefined

def bindings (v : Values) : List Binding := [
  {name := "n",value := v.n},
  {name := "arguments",value := v.arguments},
  {name := "price",value := v.price}]

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

theorem read_price (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "price" = .ok v.price := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_price (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "price" next false =
      .ok (heap objects leading outer {v with price := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with price := next} suffix

theorem has_price (v : Values) :
    (bindings v).any (fun binding => binding.name == "price") = true := by
  simp [bindings]

def body : List Stmt := match CursorCycleSyntax.getPriceBody with
  | .block statements => statements
  | other => [other]

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap objects leading outer v suffix
  context := ⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control := .statement CursorCycleSyntax.getPriceBody }


end CookieClicker.JavaScript.CursorGetPriceLocals

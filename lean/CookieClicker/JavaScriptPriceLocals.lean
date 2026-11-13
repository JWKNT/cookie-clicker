import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptIdentifierPath

/-! Native local state for the complete building-price modifier.
The actual parameter, arguments and godLvl bindings precede nested-call allocations. -/

namespace CookieClicker.JavaScript.PriceLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  building : Value
  price : Value
  arguments : Value
  godLvl : Value := .undefined

def bindings (v : Values) : List Binding := [
  {name := "building",value := v.building},{name := "price",value := v.price},
  {name := "arguments",value := v.arguments},{name := "godLvl",value := v.godLvl}]

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

theorem read_building (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "building" = .ok v.building := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_building (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "building" next false =
      .ok (heap objects leading outer {v with building := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with building := next} suffix

theorem has_building (v : Values) :
    (bindings v).any (fun binding => binding.name == "building") = true := by
  simp [bindings]

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

theorem read_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments" = .ok v.arguments := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments" next false =
      .ok (heap objects leading outer {v with arguments := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with arguments := next} suffix

theorem has_arguments (v : Values) :
    (bindings v).any (fun binding => binding.name == "arguments") = true := by
  simp [bindings]

theorem read_godLvl (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "godLvl" = .ok v.godLvl := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_godLvl (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "godLvl" next false =
      .ok (heap objects leading outer {v with godLvl := next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with godLvl := next} suffix

theorem has_godLvl (v : Values) :
    (bindings v).any (fun binding => binding.name == "godLvl") = true := by
  simp [bindings]

def body : List Stmt := match CursorCycleSyntax.modifyBuildingPriceBody with
  | .block statements => statements
  | other => [other]

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap objects leading outer v suffix
  context := ⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control := .statement CursorCycleSyntax.modifyBuildingPriceBody }


end CookieClicker.JavaScript.PriceLocals

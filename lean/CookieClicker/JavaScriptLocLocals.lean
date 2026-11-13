import CookieClicker.JavaScriptLocSource
import CookieClicker.JavaScriptSourceRead

namespace CookieClicker.JavaScript.LocLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

structure Values where
  arguments : Value
  fallback : Value := .undefined
  found : Value := .undefined
  str : Value := .undefined

def text : JSString := JSString.ofString "Achievement unlocked"
def bindings (v : Values) : List Binding := [
  {name:="id",value:=.string text},{name:="params",value:=.undefined},{name:="baseline",value:=.undefined},
  {name:="arguments",value:=v.arguments},{name:="fallback",value:=v.fallback},
  {name:="found",value:=v.found},{name:="str",value:=v.str}]
def slotIndex (leading : Array LexicalEnvironment) : EnvId := leading.size
def heap (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) : Heap := {
  objects
  environments:=(leading.push ⟨.declarative (bindings v),some outer⟩)++suffix }
def state (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap:=heap objects leading outer v suffix
  context:=⟨slotIndex leading,slotIndex leading,.object base.globalObject,false⟩ }

theorem checked_local (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    checkedEnvironment (heap objects leading outer v suffix) (slotIndex leading)=
      .ok ⟨.declarative (bindings v),some outer⟩ := by
  simp [checkedEnvironment,Heap.environment?,heap,slotIndex,Array.getElem?_append_left]

theorem replace_local (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v next : Values) (suffix : Array LexicalEnvironment) :
    replaceEnvironment (heap objects leading outer v suffix) (slotIndex leading)
      ⟨.declarative (bindings next),some outer⟩=.ok (heap objects leading outer next suffix) := by
  have bound : leading.size<leading.size+1+suffix.size := by omega
  simp [replaceEnvironment,Heap.writeEnvironment,heap,slotIndex,bound,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_append_left,Array.set_push]

theorem read_id (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "id"=.ok (.string text) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem read_params (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "params"=.ok (.undefined) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem read_baseline (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "baseline"=.ok (.undefined) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem read_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments"=.ok (v.arguments) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem read_fallback (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "fallback"=.ok (v.fallback) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem read_found (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "found"=.ok (v.found) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem read_str (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "str"=.ok (v.str) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem set_fallback (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "fallback" next false=
      .ok (heap objects leading outer {v with fallback:=next} suffix) := by
  simp [setBinding,checked_local,bindings,Except.bind,bind]
  exact replace_local objects leading outer v {v with fallback:=next} suffix

theorem set_found (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "found" next false=
      .ok (heap objects leading outer {v with found:=next} suffix) := by
  simp [setBinding,checked_local,bindings,Except.bind,bind]
  exact replace_local objects leading outer v {v with found:=next} suffix

theorem set_str (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "str" next false=
      .ok (heap objects leading outer {v with str:=next} suffix) := by
  simp [setBinding,checked_local,bindings,Except.bind,bind]
  exact replace_local objects leading outer v {v with str:=next} suffix

end CookieClicker.JavaScript.LocLocals

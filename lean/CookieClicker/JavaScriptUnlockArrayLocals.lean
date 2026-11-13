import CookieClicker.JavaScriptUnlockAlready
import CookieClicker.JavaScriptSourceBinding
import CookieClicker.JavaScriptPriceRegistryAdvance

/-! The retained local environment of the array branch of Game.Unlock. -/
namespace CookieClicker.JavaScript.UnlockArrayLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  what : Value
  arguments : Value
  i : Value := .undefined

def bindings (v : Values) : List Binding :=
  [{name:="what",value:=v.what},{name:="arguments",value:=v.arguments},{name:="i",value:=v.i}]

def heap (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Heap :=
  ⟨objects,leading.push ⟨.declarative (bindings v),some outer⟩ ++ suffix⟩

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap:=heap objects leading outer v suffix
  context:=⟨leading.size,leading.size,base.context.thisValue,false⟩ }

theorem checked_local (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    checkedEnvironment (heap objects leading outer v suffix) leading.size=
      .ok ⟨.declarative (bindings v),some outer⟩ := by
  simp [checkedEnvironment,heap,Heap.environment?,Array.getElem?_append_left]

theorem replace_local (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v next : Values) (suffix : Array LexicalEnvironment) :
    replaceEnvironment (heap objects leading outer v suffix) leading.size
      ⟨.declarative (bindings next),some outer⟩=
      .ok (heap objects leading outer next suffix) := by
  have bound : leading.size < leading.size+1+suffix.size := by omega
  simp [replaceEnvironment,heap,Heap.writeEnvironment,bound,Array.set!_eq_setIfInBounds,
    Array.setIfInBounds,Array.set_append_left,Array.set_push]

theorem read_what (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) leading.size "what"=.ok v.what := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem read_i (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) leading.size "i"=.ok v.i := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem set_i (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) leading.size "i" next false=
      .ok (heap objects leading outer {v with i:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with i:=next} suffix

theorem what_read (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    SourceRead.Reads (start base objects leading outer v suffix) (.identifier "what") v.what 3 := by
  exact SourceRead.local_identifier _ "what" v.what (bindings v) (some outer)
    (checked_local objects leading outer v suffix) (by simp [bindings])
    (read_what objects leading outer v suffix)

theorem i_read (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    SourceRead.Reads (start base objects leading outer v suffix) (.identifier "i") v.i 3 := by
  exact SourceRead.local_identifier _ "i" v.i (bindings v) (some outer)
    (checked_local objects leading outer v suffix) (by simp [bindings])
    (read_i objects leading outer v suffix)

theorem i_reference (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    identifierReference (start base objects leading outer v suffix) "i"=
      .ok ⟨.environment leading.size "i",false⟩ := by
  simp [identifierReference,resolveName,start,checked_local,bindings,Except.bind,bind,Except.pure,pure]

end CookieClicker.JavaScript.UnlockArrayLocals

import CookieClicker.JavaScriptNotificationSyntax
import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptIdentifierPath

/-! Native Notify local state. The actual six bindings persist before
allocations left by nested replacement, constructor and log calls. -/

namespace CookieClicker.JavaScript.NotifyLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  title : Value
  desc : Value
  pic : Value
  quick : Value := .undefined
  noLog : Value := .undefined
  arguments : Value

def bindings (v : Values) : List Binding := [
  {name:="title",value:=v.title},{name:="desc",value:=v.desc},{name:="pic",value:=v.pic},
  {name:="quick",value:=v.quick},{name:="noLog",value:=v.noLog},{name:="arguments",value:=v.arguments}]

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

theorem read_title (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "title"=.ok v.title := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_title (v : Values) :
    (bindings v).any (fun binding=>binding.name=="title")=true := by simp [bindings]

theorem read_desc (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "desc"=.ok v.desc := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_desc (v : Values) :
    (bindings v).any (fun binding=>binding.name=="desc")=true := by simp [bindings]

theorem read_pic (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "pic"=.ok v.pic := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_pic (v : Values) :
    (bindings v).any (fun binding=>binding.name=="pic")=true := by simp [bindings]

theorem read_quick (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "quick"=.ok v.quick := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_quick (v : Values) :
    (bindings v).any (fun binding=>binding.name=="quick")=true := by simp [bindings]

theorem read_noLog (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "noLog"=.ok v.noLog := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_noLog (v : Values) :
    (bindings v).any (fun binding=>binding.name=="noLog")=true := by simp [bindings]

theorem read_arguments (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "arguments"=.ok v.arguments := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_arguments (v : Values) :
    (bindings v).any (fun binding=>binding.name=="arguments")=true := by simp [bindings]

theorem set_desc (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "desc" next false=
      .ok (heap objects leading outer {v with desc:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with desc:=next} suffix

theorem set_quick (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "quick" next false=
      .ok (heap objects leading outer {v with quick:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with quick:=next} suffix

def body : List Stmt := match NotificationSyntax.NotifyBody with
  | .block statements => statements
  | other => [other]

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap := heap objects leading outer v suffix
  context := ⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control := .statement NotificationSyntax.NotifyBody }

end CookieClicker.JavaScript.NotifyLocals

import CookieClicker.JavaScriptBuildingSellInvocation
import CookieClicker.JavaScriptSourceBinding

/-! The native sale-local layout, with all older and later environments kept.
These facts concern writes to real mutable bindings, including mapped arguments. -/
namespace CookieClicker.JavaScript.BuildingSellLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Values where
  amount : Value
  bypass : Value
  arguments : Value
  success : Value := .undefined
  moni : Value := .undefined
  sold : Value := .undefined
  i : Value := .undefined
  price : Value := .undefined
  giveBack : Value := .undefined
  godLvl : Value := .undefined
  old : Value := .undefined
  highestBuilding : Value := .undefined
  buffsN : Value := .undefined
  ii : Value := .undefined

def bindings (v : Values) : List Binding := [
  {name:="amount",value:=v.amount},
  {name:="bypass",value:=v.bypass},
  {name:="arguments",value:=v.arguments},
  {name:="success",value:=v.success},
  {name:="moni",value:=v.moni},
  {name:="sold",value:=v.sold},
  {name:="i",value:=v.i},
  {name:="price",value:=v.price},
  {name:="giveBack",value:=v.giveBack},
  {name:="godLvl",value:=v.godLvl},
  {name:="old",value:=v.old},
  {name:="highestBuilding",value:=v.highestBuilding},
  {name:="buffsN",value:=v.buffsN},
  {name:="ii",value:=v.ii}]

def slotIndex (leading : Array LexicalEnvironment) : EnvId := leading.size

def heap (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) : Heap := {
  objects
  environments:=(leading.push ⟨.declarative (bindings v),some outer⟩)++suffix }

theorem checked_local (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    checkedEnvironment (heap objects leading outer v suffix) (slotIndex leading)=
      .ok ⟨.declarative (bindings v),some outer⟩ := by
  simp [checkedEnvironment,Heap.environment?,heap,slotIndex,Array.getElem?_append_left]

theorem replace_local (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v next : Values) (suffix : Array LexicalEnvironment) :
    replaceEnvironment (heap objects leading outer v suffix) (slotIndex leading)
      ⟨.declarative (bindings next),some outer⟩=
      .ok (heap objects leading outer next suffix) := by
  have bound : leading.size<leading.size+1+suffix.size := by omega
  simp [replaceEnvironment,Heap.writeEnvironment,heap,slotIndex,bound,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_append_left,Array.set_push]

theorem read_amount (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "amount"=.ok v.amount := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_amount (v : Values) :
    (bindings v).any (fun binding=>binding.name=="amount")=true := by simp [bindings]

theorem read_success (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "success"=.ok v.success := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_success (v : Values) :
    (bindings v).any (fun binding=>binding.name=="success")=true := by simp [bindings]

theorem read_moni (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "moni"=.ok v.moni := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_moni (v : Values) :
    (bindings v).any (fun binding=>binding.name=="moni")=true := by simp [bindings]

theorem read_sold (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "sold"=.ok v.sold := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_sold (v : Values) :
    (bindings v).any (fun binding=>binding.name=="sold")=true := by simp [bindings]

theorem read_i (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) :
    readBinding (heap objects leading outer v suffix) (slotIndex leading) "i"=.ok v.i := by
  simp [readBinding,checked_local,bindings,bind,Except.bind,pure,Except.pure]

theorem has_i (v : Values) :
    (bindings v).any (fun binding=>binding.name=="i")=true := by simp [bindings]

theorem set_success (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "success" next false=
      .ok (heap objects leading outer {v with success:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with success:=next} suffix

theorem set_moni (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "moni" next false=
      .ok (heap objects leading outer {v with moni:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with moni:=next} suffix

theorem set_sold (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "sold" next false=
      .ok (heap objects leading outer {v with sold:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with sold:=next} suffix

theorem set_i (objects : Array JSObject) (leading : Array LexicalEnvironment) (outer : EnvId)
    (v : Values) (suffix : Array LexicalEnvironment) (next : Value) :
    setBinding (heap objects leading outer v suffix) (slotIndex leading) "i" next false=
      .ok (heap objects leading outer {v with i:=next} suffix) := by
  simp [setBinding,checked_local,bindings,bind,Except.bind]
  exact replace_local objects leading outer v {v with i:=next} suffix

def start (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  base with
  heap:=heap objects leading outer v suffix
  context:=⟨slotIndex leading,slotIndex leading,base.context.thisValue,false⟩
  control:=.statement CursorCycleSyntax.sellBody }

theorem original_hoisted (base : Machine) (scope : EnvId) (building : ObjectId)
    (amount bypass : Value) (callee : Option ObjectId) :
    let ready:=BuildingSellInvocation.hoisted base scope building amount bypass callee
    start ready ready.heap.objects base.heap.environments scope
      {amount,bypass,arguments:=.object base.heap.objects.size} #[]= {ready with control:=.statement CursorCycleSyntax.sellBody} := by
  simp only [start,heap,BuildingSellInvocation.hoisted,BuildingSellInvocation.prepared,
    BuildingSellInvocation.allocatedHeap,BuildingSellInvocation.hoistedBindings,
    BuildingSellInvocation.locals,BuildingSellInvocation.localNames,BuildingSellInvocation.localIndex,
    BuildingSellInvocation.argumentIndex,bindings,slotIndex,Array.append_empty]
  rfl

end CookieClicker.JavaScript.BuildingSellLocals

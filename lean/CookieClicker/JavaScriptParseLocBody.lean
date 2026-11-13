import CookieClicker.JavaScriptParseLocCall

namespace CookieClicker.JavaScript.ParseLocBody
open ParseLocCall
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def bindings (base : Machine) (params : Value) : List Binding :=
  [{name:="str",value:=.string text},{name:="params",value:=params},
   {name:="arguments",value:=.object (argumentIndex base)}]++
  ["plurIndex","out","len","inPercent","i","it"].map fun name=>{name:=name}
def localHeap (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) : Heap := {
  objects
  environments:=base.heap.environments.push ⟨.declarative (bindings base params),some scope⟩ }
def state (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) : Machine := {
  base with
  heap:=localHeap base scope objects params
  context:=⟨localIndex base,localIndex base,.object base.globalObject,false⟩
  continuation:=.callBoundary base.context none::base.continuation }

theorem checked_local (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    checkedEnvironment (localHeap base scope objects params) (localIndex base)=
      .ok ⟨.declarative (bindings base params),some scope⟩ := by
  simp [localHeap,localIndex,checkedEnvironment,Heap.environment?]

theorem heap_objects (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    (localHeap base scope objects params).objects=objects := rfl

theorem heap_environments (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    (localHeap base scope objects params).environments=
      base.heap.environments.push ⟨.declarative (bindings base params),some scope⟩ := rfl

theorem allocate_object (base : Machine) (scope : EnvId) (objects : Array JSObject)
    (params : Value) (object : JSObject) :
    (localHeap base scope objects params).allocateObject object=
      (objects.size,localHeap base scope (objects.push object) params) := rfl

theorem params_write (base : Machine) (scope : EnvId) (objects : Array JSObject) (old value : Value) :
    setBinding (localHeap base scope objects old) (localIndex base) "params" value false=
      .ok (localHeap base scope objects value) := by
  simp [setBinding,checkedEnvironment,Heap.environment?,bindings,localHeap,localIndex,replaceEnvironment,Heap.writeEnvironment,
    Except.bind,Except.pure,bind,pure,Array.setIfInBounds,Array.set_push]

theorem params_read (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    readBinding (localHeap base scope objects params) (localIndex base) "params"=.ok params := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem str_read (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    readBinding (localHeap base scope objects params) (localIndex base) "str"=.ok (.string text) := by
  simp [readBinding,checked_local,bindings,Except.bind,Except.pure,bind,pure]

theorem checked_added (base : Machine) (scope : EnvId) (objects : Array JSObject)
    (params : Value) (object : JSObject) :
    checkedObject (localHeap base scope (objects.push object) params) objects.size=.ok object := by
  simp [checkedObject,localHeap,Heap.object?]

theorem array_checked (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    checkedObject (localHeap base scope (objects.push (emptyArray base)) params) objects.size=
      .ok (emptyArray base) := by
  simp [checkedObject,localHeap,Heap.object?]

theorem array_length (base : Machine) (scope : EnvId) (objects : Array JSObject) (params : Value) :
    lookupProperty (localHeap base scope (objects.push (emptyArray base)) params) objects.size
      (JSString.ofString "length")=.ok (some (.data (.number 0) true false false)) := by
  simp [lookupProperty,findProperty,array_checked,emptyArray,ownProperty,JSString.ofString,
    Except.bind,Except.pure,bind,pure,localHeap,checkedObject,Heap.object?]

attribute [local cbv_opaque] localHeap localIndex argumentIndex checkedEnvironment
  readBinding setBinding Heap.allocateObject checkedObject Array.push Array.size
attribute [local cbv_eval] checked_local heap_objects heap_environments allocate_object params_write
  params_read str_read checked_added array_checked array_length

/-- The intact source exits at the native params.length==0 return. It allocates
and retains the real empty array and writes the actual mapped params local. -/
theorem source_body (base : Machine) (scope : EnvId) (objects : Array JSObject) (fuel : Nat) :
    Builtins.run (49+fuel) {state base scope objects .undefined with
      control:=.statement LocalizationSyntax.parseLocBody}=
      Builtins.run fuel {base with
        heap:=localHeap base scope (objects.push (emptyArray base)) (.object objects.size)
        control:=.expressionResult (.value (.string text))} := by
  rw [Nat.add_comm 49 fuel]
  cbv

theorem prepared_returns (base : Machine) (scope function : Nat) (fuel : Nat) :
    Builtins.run (95+fuel) (prepared base scope function)=
      Builtins.run fuel (returned base scope function) := by
  rw [show 95+fuel=46+(49+fuel) by omega,actual_hoist]
  have startSame : Builtins.run (49+fuel) (hoisted base scope function)=
      Builtins.run (49+fuel) {state base scope (base.heap.objects.push (argumentObject base function)) .undefined with
        control:=.statement LocalizationSyntax.parseLocBody} := by
    rw [Nat.add_comm 49 fuel]
    rfl
  rw [startSame,source_body]
  simp only [Array.size_push]
  rfl

theorem actual_invoke (base : Machine) (scope function : Nat) (source : Option JSString)
    (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) :
    invoke base (.object function) .undefined [.string text,.undefined] false=
      prepared base scope function := by
  simp [invoke,present,kind,checked,actual_prepare]

theorem native_call (base : Machine) (scope function : Nat) (source : Option JSString)
    (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) (fuel : Nat) :
    Builtins.run (96+fuel) {base with control:=.invoke (.object function) .undefined [.string text,.undefined] false}=
      Builtins.run fuel (returned base scope function) := by
  rw [show 96+fuel=1+(95+fuel) by omega,Nat.add_comm 1 (95+fuel)]
  change Builtins.run (95+fuel) {invoke {base with
    control:=.invoke (.object function) .undefined [.string text,.undefined] false}
    (.object function) .undefined [.string text,.undefined] false with elapsed:=base.elapsed}=_
  rw [actual_invoke {base with control:=.invoke (.object function) .undefined [.string text,.undefined] false}
    scope function source object present kind]
  exact prepared_returns base scope function fuel

theorem returned_extends (base : Machine) (scope function : Nat) :
    HeapExtension.Extends base.heap (returned base scope function).heap :=
  HeapExtension.trans
    (HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base function))
      (HeapExtension.append_object _ (emptyArray base)))
    (HeapExtension.same_objects rfl)

end CookieClicker.JavaScript.ParseLocBody

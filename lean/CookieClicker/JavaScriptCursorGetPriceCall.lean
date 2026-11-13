import CookieClicker.JavaScriptCursorGetPriceSource
import CookieClicker.JavaScriptCursorGetPriceComplete
import CookieClicker.JavaScriptPriceRetention

/-! Complete native Cursor getPrice invocation and return. The function
retains its actual declaration scan, modifier graph, arithmetic bindings,
arguments objects, lexical environments and original caller continuation. -/
namespace CookieClicker.JavaScript.CursorGetPriceCall
open SourceRead CursorGetPriceComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def bodyBase (base : Machine) (cursor : ObjectId) : Machine := {base with
  context:={base.context with thisValue:=.object cursor}
  continuation:=.callBoundary base.context none::base.continuation}

def initial (base : Machine) (function : ObjectId) : State := {
  objects:=base.heap.objects.push (CursorGetPriceSource.argumentObject (callee:=some function) base)
  values:=⟨.undefined,.object base.heap.objects.size,.undefined⟩
  suffix:=#[] }

def state (base : Machine) (scope cursor function : ObjectId) : Machine :=
  machine (bodyBase base cursor) base.heap.environments scope (initial base function)

def returned (base : Machine) (scope cursor function : ObjectId) (basePrice amount free rate : UInt64)
    (h : Inputs (bodyBase base cursor) base.heap.environments scope (initial base function) basePrice amount free rate) : Machine := {base with
  heap:=(machine (bodyBase base cursor) base.heap.environments scope h.after).heap
  control:=.expressionResult (.value (.number (Number.ceil h.price))) }

theorem hoisted_state (base : Machine) (scope cursor function : ObjectId) :
    CursorGetPriceSource.hoisted (callee:=some function) base scope cursor=
      {state base scope cursor function with control:=.declarationFunctions [] CursorGetPriceSource.body} := by
  simp only [CursorGetPriceSource.hoisted,CursorGetPriceSource.prepared,CursorGetPriceSource.allocatedHeap,
    CursorGetPriceSource.locals,CursorGetPriceSource.localIndex,CursorGetPriceSource.argumentIndex,state,machine,
    CursorGetPriceLocals.start,CursorGetPriceLocals.heap,CursorGetPriceLocals.slotIndex,
    CursorGetPriceLocals.bindings,initial,bodyBase,Array.append_empty]
  rfl

theorem prepared_returns (base : Machine) (scope cursor function : ObjectId) (basePrice amount free rate : UInt64)
    (h : Inputs (bodyBase base cursor) base.heap.environments scope (initial base function) basePrice amount free rate)
    (stable : Number.mul h.price Number.one=h.price)
    (ceiling : BuildingMathRead.Binding (machine (bodyBase base cursor) base.heap.environments scope h.after) "ceil")
    (fuel : Nat) :
    Builtins.run (1296+fuel) (CursorGetPriceSource.prepared (callee:=some function) base scope cursor)=
      Builtins.run fuel (returned base scope cursor function basePrice amount free rate h) := by
  rw [show 1296+fuel=6+(1289+(1+fuel)) by omega,CursorGetPriceSource.actual_hoist_prefix (callee:=some function)]
  have body : Builtins.run (1289+(1+fuel)) (CursorGetPriceSource.hoisted (callee:=some function) base scope cursor)=
      Builtins.run (1289+(1+fuel)) (state base scope cursor function) := by
    rw [hoisted_state,Nat.add_comm 1289 (1+fuel)]
    rfl
  rw [body]
  unfold state
  rw [h.native_body stable ceiling,Nat.add_comm 1 fuel]
  rfl

theorem native_invoke (base : Machine) (scope cursor function : ObjectId) (basePrice amount free rate : UInt64)
    (h : Inputs (bodyBase base cursor) base.heap.environments scope (initial base function) basePrice amount free rate)
    (stable : Number.mul h.price Number.one=h.price)
    (ceiling : BuildingMathRead.Binding (machine (bodyBase base cursor) base.heap.environments scope h.after) "ceil")
    (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (CursorGetPriceSource.closure scope source)) (fuel : Nat) :
    Builtins.run (1296+fuel) (invoke base (.object function) (.object cursor) [] false)=
      Builtins.run fuel (returned base scope cursor function basePrice amount free rate h) := by
  simp only [invoke,present,kind,checked,CursorGetPriceSource.actual_prepare]
  exact prepared_returns base scope cursor function basePrice amount free rate h stable ceiling fuel

def expression : Expr := .call (.member .this (.identifier "getPrice") false) []

theorem expression_invoke (base : Machine) (cursor function : ObjectId) (object : JSObject)
    (receiver : base.context.thisValue=.object cursor)
    (present : checkedObject base.heap cursor=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap cursor (JSString.ofString "getPrice")=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (7+fuel) {base with control:=.expression expression}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object cursor) [] false} := by
  rw [show 7+fuel=3+(3+(1+fuel)) by omega,Nat.add_comm 3 (3+(1+fuel))]
  change Builtins.run (3+(1+fuel)) {base with
    control:=.expressionResult (.value base.context.thisValue)
    continuation:=.memberObject (.identifier "getPrice") false::.callCallee [] false::base.continuation}=_
  rw [receiver,Nat.add_comm 3 (1+fuel)]
  change Builtins.run (1+fuel) {readProperty {base with
    control:=.getValue ⟨.property (.object cursor) (JSString.ofString "getPrice"),base.context.strict⟩
    continuation:=.callResolved (.object cursor) [] false::base.continuation}
    (.object cursor) (JSString.ofString "getPrice") with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control:=.getValue ⟨.property (.object cursor) (JSString.ofString "getPrice"),base.context.strict⟩
    continuation:=.callResolved (.object cursor) [] false::base.continuation}
    cursor (JSString.ofString "getPrice") (.object function) object present (Or.inl kind) property,
    Nat.add_comm 1 fuel]
  rfl

theorem source_call (base : Machine) (scope cursor function : ObjectId) (basePrice amount free rate : UInt64)
    (h : Inputs (bodyBase base cursor) base.heap.environments scope (initial base function) basePrice amount free rate)
    (stable : Number.mul h.price Number.one=h.price)
    (ceiling : BuildingMathRead.Binding (machine (bodyBase base cursor) base.heap.environments scope h.after) "ceil")
    (source : Option JSString) (cursorObject functionObject : JSObject)
    (receiver : base.context.thisValue=.object cursor)
    (cursorPresent : checkedObject base.heap cursor=.ok cursorObject) (cursorKind : cursorObject.kind=.ordinary)
    (method : lookupProperty base.heap cursor (JSString.ofString "getPrice")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CursorGetPriceSource.closure scope source)) (fuel : Nat) :
    Builtins.run (1304+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (returned base scope cursor function basePrice amount free rate h) := by
  rw [show 1304+fuel=7+(1+(1296+fuel)) by omega,
    expression_invoke base cursor function cursorObject receiver cursorPresent cursorKind method,Nat.add_comm 1 (1296+fuel)]
  change Builtins.run (1296+fuel) {invoke {base with
    control:=.invoke (.object function) (.object cursor) [] false}
    (.object function) (.object cursor) [] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object cursor) [] false}
      (.object function) (.object cursor) [] false=
      CursorGetPriceSource.prepared (callee:=some function) base scope cursor := by
    simp only [invoke,functionPresent,functionKind,checked,CursorGetPriceSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope cursor function basePrice amount free rate h stable ceiling fuel

end CookieClicker.JavaScript.CursorGetPriceCall

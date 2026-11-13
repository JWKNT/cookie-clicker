import CookieClicker.JavaScriptCursorGetPriceCatalogue

/-! Complete original getPrice invocation without post-call frame premises. -/
namespace CookieClicker.JavaScript.CursorGetPriceOriginal
open CursorGetPriceCall CursorGetPriceCatalogue
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def bodyCatalogue {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) :
    Catalogue (bodyBase base cursor) scope cursor price owned free rate :=
  recontext catalogue {base.context with thisValue:=.object cursor}
    (.callBoundary base.context none::base.continuation)

def bodyInputs {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) :
    CursorGetPriceComplete.Inputs (bodyBase base cursor) base.heap.environments scope
      (initial base function) price owned free rate :=
  inputs (bodyCatalogue catalogue) (initial base function)
    (HeapExtension.append_object base.heap (CursorGetPriceSource.argumentObject (callee:=some function) base))

def after {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) : Machine :=
  returned base scope cursor function price owned free rate (bodyInputs catalogue function)

def finalCeiling {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) :
    BuildingMathRead.Binding
      (CursorGetPriceComplete.machine (bodyBase base cursor) base.heap.environments scope
        (bodyInputs catalogue function).after) "ceil" :=
  ceiling (bodyCatalogue catalogue) (initial base function)
    (HeapExtension.append_object base.heap (CursorGetPriceSource.argumentObject (callee:=some function) base))

theorem actual_source_call {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId)
    (stable : Number.mul (CursorGetPriceRead.rawValue price owned free rate) Number.one=
      CursorGetPriceRead.rawValue price owned free rate)
    (source : Option JSString) (cursorObject functionObject : JSObject)
    (receiver : base.context.thisValue=.object cursor)
    (cursorPresent : checkedObject base.heap cursor=.ok cursorObject)
    (cursorKind : cursorObject.kind=.ordinary)
    (method : lookupProperty base.heap cursor (JSString.ofString "getPrice")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CursorGetPriceSource.closure scope source)) (fuel : Nat) :
    Builtins.run (1304+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (after catalogue function) :=
  source_call base scope cursor function price owned free rate (bodyInputs catalogue function) stable
    (finalCeiling catalogue function) source cursorObject functionObject receiver cursorPresent
    cursorKind method functionPresent functionKind fuel

theorem retained_objects {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) :
    HeapExtension.Extends base.heap (after catalogue function).heap :=
  CursorGetPriceRetention.returned_extends base scope cursor function price owned free rate (bodyInputs catalogue function)

def environmentSuffix {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) : Array LexicalEnvironment :=
  #[⟨.declarative (CursorGetPriceLocals.bindings (bodyInputs catalogue function).after.values),some scope⟩]++
    (bodyInputs catalogue function).after.suffix

theorem retained_environments {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) :
    (after catalogue function).heap.environments=base.heap.environments++environmentSuffix catalogue function := by
  simp only [after,returned,CursorGetPriceComplete.machine,CursorGetPriceLocals.start,
    CursorGetPriceLocals.heap,bodyBase,environmentSuffix,Array.push_eq_append,Array.append_assoc]

theorem retained_caller {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (function : ObjectId) :
    (after catalogue function).context=base.context ∧
    (after catalogue function).continuation=base.continuation ∧
    (after catalogue function).elapsed=base.elapsed ∧
    (after catalogue function).epochMilliseconds=base.epochMilliseconds ∧
    (after catalogue function).freeDrawCount=base.freeDrawCount := ⟨rfl,rfl,rfl,rfl,rfl⟩

end CookieClicker.JavaScript.CursorGetPriceOriginal

import CookieClicker.JavaScriptCursorReverseComplete
import CookieClicker.JavaScriptCursorQuoteSource

/-! Full native one-copy getReverseSumPrice call after Cursor sale. The original
closure, mapped arguments, loop, price modifier, sell multiplier, Math.ceil and caller return
all execute. A single pre-call catalogue constructs the later call frames. -/
namespace CookieClicker.JavaScript.CursorReverseCall
open SourceRead CursorQuoteCatalogue
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def bodyBase (base : Machine) (cursor : ObjectId) : Machine := {base with
  context:={base.context with thisValue:=.object cursor}
  continuation:=.callBoundary base.context none::base.continuation}

def objects (base : Machine) (function : ObjectId) : Array JSObject :=
  base.heap.objects.push (CursorQuoteSource.argumentObject base (.number Number.one) (some function))

def values (base : Machine) : CursorQuoteLocals.Values :=
  ⟨.number Number.one,.object base.heap.objects.size,.undefined,.undefined⟩

def state (base : Machine) (scope cursor function : ObjectId) : Machine :=
  CursorQuoteRegistry.machine true (bodyBase base cursor) scope cursor (objects base function) (values base) #[]

theorem extension (base : Machine) (cursor function : ObjectId) :
    HeapExtension.Extends (bodyBase base cursor).heap {objects:=objects base function,environments:=base.heap.environments} :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (CursorQuoteSource.argumentObject base (.number Number.one) (some function))) (HeapExtension.same_objects rfl)

def after {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate) (function : ObjectId) : CursorQuoteTail.State :=
  CursorReverseComplete.after catalogue (objects base function) (values base) #[] (extension base cursor function)

def returned {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate) (function : ObjectId) : Machine := {base with
  heap:=(current true (bodyBase base cursor) scope cursor (after catalogue function)).heap
  control:=.expressionResult (.value (.number 0)) }

theorem hoisted_state (base : Machine) (scope cursor function : ObjectId) :
    CursorQuoteSource.hoisted true base scope cursor (.number Number.one) (some function)=
      {state base scope cursor function with control:=.declarationFunctions [] (CursorQuoteSource.body true)} := by
  simp only [CursorQuoteSource.hoisted,CursorQuoteSource.prepared,CursorQuoteSource.allocatedHeap,
    CursorQuoteSource.locals,CursorQuoteSource.localIndex,CursorQuoteSource.argumentIndex,state,CursorQuoteRegistry.machine,
    CursorQuoteLocals.start,CursorQuoteLocals.heap,CursorQuoteLocals.slotIndex,
    CursorQuoteLocals.bindings,objects,values,bodyBase,Array.append_empty]
  rfl

theorem prepared_returns (base : Machine) (scope cursor function : ObjectId) (price free rate : UInt64)
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate)
    (fuel : Nat) :
    Builtins.run (1520+fuel) (CursorQuoteSource.prepared true base scope cursor (.number Number.one) (some function))=
      Builtins.run fuel (returned catalogue function) := by
  have hoist:=CursorQuoteSource.actual_hoist_prefix true base scope cursor (.number Number.one) (1508+(1+fuel)) (callee:=some function)
  simp only [↓reduceIte] at hoist
  rw [show 1520+fuel=11+(1508+(1+fuel)) by omega,hoist]
  have body : Builtins.run (1508+(1+fuel)) (CursorQuoteSource.hoisted true base scope cursor (.number Number.one) (some function))=
      Builtins.run (1508+(1+fuel)) (state base scope cursor function) := by
    rw [hoisted_state,Nat.add_comm 1508 (1+fuel)]
    rfl
  rw [body]
  unfold state
  rw [CursorReverseComplete.native_body catalogue (objects base function) (values base) #[] rfl (extension base cursor function),
    Nat.add_comm 1 fuel]
  rfl

def expression (argument : Expr) : Expr := .call (.member .this (.identifier "getReverseSumPrice") false) [argument]

theorem expression_invoke (base : Machine) (cursor function : ObjectId) (object : JSObject)
    (argument : Expr) (ticks : Nat)
    (receiver : base.context.thisValue=.object cursor)
    (present : checkedObject base.heap cursor=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap cursor (JSString.ofString "getReverseSumPrice")=
      .ok (some (.data (.object function) true true true)))
    (argumentRead : Reads base argument (.number Number.one) ticks) (fuel : Nat) :
    Builtins.run (ticks+8+fuel) {base with control:=.expression (expression argument)}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object cursor) [.number Number.one] false} := by
  rw [show ticks+8+fuel=3+(3+(ticks+2+fuel)) by omega,Nat.add_comm 3 (3+(ticks+2+fuel))]
  change Builtins.run (3+(ticks+2+fuel)) {base with
    control:=.expressionResult (.value base.context.thisValue)
    continuation:=.memberObject (.identifier "getReverseSumPrice") false::.callCallee [argument] false::base.continuation}=_
  rw [receiver,MemberCall.callee_data base "getReverseSumPrice" argument cursor function object present kind property]
  exact MemberCall.argument_value base argument (.number Number.one) cursor function ticks argumentRead fuel

theorem source_call (base : Machine) (scope cursor function : ObjectId) (price free rate : UInt64)
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate)
    (source : Option JSString) (cursorObject functionObject : JSObject)
    (argument : Expr) (ticks : Nat)
    (receiver : base.context.thisValue=.object cursor)
    (cursorPresent : checkedObject base.heap cursor=.ok cursorObject) (cursorKind : cursorObject.kind=.ordinary)
    (method : lookupProperty base.heap cursor (JSString.ofString "getReverseSumPrice")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CursorQuoteSource.closure true scope source))
    (argumentRead : Reads base argument (.number Number.one) ticks) (fuel : Nat) :
    Builtins.run (ticks+1529+fuel) {base with control:=.expression (expression argument)}=
      Builtins.run fuel (returned catalogue function) := by
  rw [show ticks+1529+fuel=ticks+8+(1+(1520+fuel)) by omega,
    expression_invoke base cursor function cursorObject argument ticks receiver cursorPresent cursorKind method argumentRead,
    Nat.add_comm 1 (1520+fuel)]
  change Builtins.run (1520+fuel) {invoke {base with
    control:=.invoke (.object function) (.object cursor) [.number Number.one] false}
    (.object function) (.object cursor) [.number Number.one] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object cursor) [.number Number.one] false}
      (.object function) (.object cursor) [.number Number.one] false=
      CursorQuoteSource.prepared true base scope cursor (.number Number.one) (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,CursorQuoteSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope cursor function price free rate catalogue fuel

theorem retained_objects {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate) (function : ObjectId) :
    HeapExtension.Extends base.heap (returned catalogue function).heap :=
  CursorReverseComplete.retained catalogue (objects base function) (values base) #[] (extension base cursor function)


def returnedAdvance {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate) (function : ObjectId) :
    PriceRegistryAdvance.Advance base (returned catalogue function) := {
  heap:=retained_objects catalogue function
  suffix:=#[⟨.declarative (CursorQuoteLocals.bindings (after catalogue function).values),some scope⟩]++(after catalogue function).suffix
  environments:=by simp only [returned,current,CursorQuoteTail.machine,CursorQuoteLocals.start,CursorQuoteLocals.heap,
    bodyBase,CursorQuoteCatalogue.bodyBase,Array.push_eq_append,Array.append_assoc]
  global:=rfl,exclusions:=rfl }

theorem returned_time {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate) (function : ObjectId) :
    (returned catalogue function).elapsed=base.elapsed := rfl

theorem returned_draw_count {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue (bodyBase base cursor) scope cursor price free rate) (function : ObjectId) :
    (returned catalogue function).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.CursorReverseCall

import CookieClicker.JavaScriptCursorQuoteCatalogue
import CookieClicker.JavaScriptCursorQuoteMultiply
import CookieClicker.JavaScriptCursorSellRegistry

/-! The reverse quote's actual getSellMultiplier suffix is constructed from
one original catalogue. The empty quote price remains zero, while both real
nested calls and their allocated environments remain in the returned heap. -/
namespace CookieClicker.JavaScript.CursorReverseTail
open SourceRead CursorQuoteCatalogue PriceRegistryAdvance
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure Catalogue (base : Machine) (scope cursor : ObjectId) (price free rate : UInt64) where
  quote : CursorQuoteCatalogue.Catalogue base scope cursor price 0 free rate
  sellScope : PriceRegistryScope.ClosureScope base
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (CursorSellSource.closure sellScope.path.closureScope source)
  cursorObject : JSObject
  cursorPresent : checkedObject base.heap cursor=.ok cursorObject
  cursorKind : cursorObject.kind=.ordinary
  method : lookupProperty base.heap cursor (JSString.ofString "getSellMultiplier")=
    .ok (some (.data (.object function) true true true))

def returnStatement : Stmt := .return (some (BuildingMathRead.call "ceil" [.identifier "price"]))
def frames (leading : Array LexicalEnvironment) (continuation : List Frame) : List Frame :=
  .assignmentRight .multiply (CursorQuoteStep.reference leading) (some (.number 0))::.expressionStatement::
    .statementList [returnStatement] (some (.number 0))::continuation

def caller (base : Machine) (scope cursor : ObjectId) (s : CursorQuoteTail.State) : Machine := {
  current true base scope cursor s with continuation:=frames base.heap.environments base.continuation }

def advance (base : Machine) (scope cursor : ObjectId) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    Advance base (caller base scope cursor s) := {
  heap:=HeapExtension.trans extension (HeapExtension.same_objects rfl)
  suffix:=#[⟨.declarative (CursorQuoteLocals.bindings s.values),some scope⟩]++s.suffix
  environments:=by simp only [caller,current,CursorQuoteTail.machine,CursorQuoteLocals.start,
    CursorQuoteLocals.heap,Array.push_eq_append,Array.append_assoc]
  global:=rfl,exclusions:=rfl }

def Catalogue.inputs {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    CursorSellCall.Inputs (caller base scope cursor s) catalogue.sellScope.path.closureScope cursor catalogue.function :=
  CursorSellRegistry.inputs (caller base scope cursor s)
    ((advance base scope cursor s extension).world catalogue.quote.pricing)
    ((advance base scope cursor s extension).scope catalogue.sellScope) cursor catalogue.function

def Catalogue.after {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) : CursorQuoteTail.State := {
  objects:=(catalogue.inputs s extension).afterObjects
  values:=s.values
  suffix:=(s.suffix.push ⟨.declarative (CursorSellLocals.bindings (CursorSellCall.values (caller base scope cursor s)
    (.number CursorSellBody.quarter))),some catalogue.sellScope.path.closureScope⟩)++(catalogue.inputs s extension).afterSuffix
  previous:=s.previous }

theorem Catalogue.layout {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    (CursorSellCall.returned (caller base scope cursor s) catalogue.sellScope.path.closureScope cursor catalogue.function
      (catalogue.inputs s extension)).heap=(current true base scope cursor (catalogue.after s extension)).heap := by
  simp only [CursorSellCall.returned,CursorSellCall.Inputs.afterState,CursorSellLocals.start,CursorSellLocals.heap,
    Catalogue.after,caller,current,CursorQuoteTail.machine,CursorQuoteLocals.start,CursorQuoteLocals.heap,
    Array.push_append,Array.append_assoc]

theorem Catalogue.native_multiplier {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) (fuel : Nat) :
    Builtins.run (204+fuel) {caller base scope cursor s with control:=.expression CursorSellCall.expression}=
      Builtins.run fuel {current true base scope cursor (catalogue.after s extension) with
        control:=.expressionResult (.value (.number CursorSellBody.quarter))
        continuation:=frames base.heap.environments base.continuation} := by
  have ext:=(advance base scope cursor s extension).heap
  rw [CursorSellCall.source_call (caller base scope cursor s) catalogue.sellScope.path.closureScope cursor catalogue.function
    (catalogue.inputs s extension) catalogue.source catalogue.cursorObject catalogue.functionObject rfl
    (HeapExtension.checked_object ext _ _ catalogue.cursorPresent) catalogue.cursorKind
    (HeapExtension.lookup_property ext _ _ _ catalogue.method)
    (HeapExtension.checked_object ext _ _ catalogue.functionPresent) catalogue.functionKind]
  apply congrArg (Builtins.run fuel)
  exact congrArg (fun heap => {current true base scope cursor s with
    heap
    control:=.expressionResult (.value (.number CursorSellBody.quarter))
    continuation:=frames base.heap.environments base.continuation}) (catalogue.layout s extension)

theorem Catalogue.retained {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    HeapExtension.Extends base.heap (current true base scope cursor (catalogue.after s extension)).heap := by
  have retained:=CursorSellCall.returned_extends (caller base scope cursor s) catalogue.sellScope.path.closureScope cursor
    catalogue.function (catalogue.inputs s extension)
  rw [catalogue.layout] at retained
  exact HeapExtension.trans (advance base scope cursor s extension).heap retained

def Catalogue.ceiling {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    BuildingMathRead.Binding (current true base scope cursor (catalogue.after s extension)) "ceil" :=
  catalogue.quote.arithmetic.binding catalogue.quote.arithmetic.ceiling true
    (catalogue.after s extension).objects (catalogue.after s extension).values (catalogue.after s extension).suffix
    (catalogue.retained s extension)

private theorem zero_quarter : Number.mul 0 CursorSellBody.quarter=0 := by decide +kernel

theorem Catalogue.native_tail {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : Catalogue base scope cursor price free rate) (s : CursorQuoteTail.State)
    (value : s.values.price=.number 0)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) (fuel : Nat) :
    Builtins.run (234+fuel) {current true base scope cursor s with
      control:=.completion (.normal (some (.number 0)))
      continuation:=.statementList (CursorQuoteTail.rest true) s.previous::base.continuation}=
      Builtins.run fuel {current true base scope cursor (catalogue.after s extension) with
        control:=.completion (.return (.number 0))} := by
  rw [show 234+fuel=1+(6+(204+(4+(1+(18+fuel))))) by omega,Nat.add_comm 1 (6+(204+(4+(1+(18+fuel)))))]
  change Builtins.run (6+(204+(4+(1+(18+fuel))))) {CursorQuoteLocals.start true
    {bodyBase base cursor with continuation:=.statementList [returnStatement] (some (.number 0))::base.continuation}
    s.objects base.heap.environments scope s.values s.suffix with
    control:=.statement (.expression (.assignment .multiply (.identifier "price") CursorSellCall.expression))}=_
  rw [CursorQuoteMultiply.multiplication_prefix,value]
  change Builtins.run (204+(4+(1+(18+fuel)))) {caller base scope cursor s with control:=.expression CursorSellCall.expression}=_
  rw [catalogue.native_multiplier]
  change Builtins.run (4+(1+(18+fuel))) {CursorQuoteLocals.start true
    {bodyBase base cursor with continuation:=.statementList [returnStatement] (some (.number 0))::base.continuation}
    (catalogue.after s extension).objects base.heap.environments scope (catalogue.after s extension).values (catalogue.after s extension).suffix with
    control:=.expressionResult (.value (.number CursorSellBody.quarter))
    continuation:=.assignmentRight .multiply (CursorQuoteStep.reference base.heap.environments) (some (.number 0))::
      .expressionStatement::.statementList [returnStatement] (some (.number 0))::base.continuation}=_
  have sameValue : (catalogue.after s extension).values.price=.number 0:=value
  have suffixStep:=CursorQuoteMultiply.multiplication_suffix true
    {bodyBase base cursor with continuation:=.statementList [returnStatement] (some (.number 0))::base.continuation}
    (catalogue.after s extension).objects base.heap.environments scope
    (catalogue.after s extension).values (catalogue.after s extension).suffix 0 CursorSellBody.quarter sameValue (1+(18+fuel))
  simp only [sameValue] at suffixStep
  rw [suffixStep,zero_quarter]
  have vv : {(catalogue.after s extension).values with price:=.number 0}=(catalogue.after s extension).values := by
    cases eq:(catalogue.after s extension).values with
    | mk amount arguments old index =>
      have same : old=.number 0 := by simpa only [eq] using sameValue
      simp only [same]
  rw [vv,Nat.add_comm 1 (18+fuel)]
  exact CursorQuoteTail.native_return true (bodyBase base cursor) base.heap.environments scope
    (catalogue.after s extension) 0 sameValue (catalogue.ceiling s extension) fuel

end CookieClicker.JavaScript.CursorReverseTail

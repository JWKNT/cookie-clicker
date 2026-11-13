import CookieClicker.JavaScriptCursorReverseTail

/-! The full native reverse quote after selling the final Cursor. Its empty
loop still calls the source modifier and source getSellMultiplier. The result
is zero; all call allocations and the exact caller state are retained. -/
namespace CookieClicker.JavaScript.CursorReverseComplete
open SourceRead CursorQuoteCatalogue CursorReverseTail
set_option maxRecDepth 32768
set_option maxHeartbeats 14000000

def initial (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment) : CursorQuoteTail.State :=
  ⟨objects,CursorQuotePrefix.afterSell values,suffix,none⟩

def afterPrice {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue base scope cursor price free rate)
    (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) : CursorQuoteTail.State :=
  catalogue.quote.after true (initial objects values suffix) 0 rfl extension

theorem afterPrice_extends {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue base scope cursor price free rate)
    (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) :
    HeapExtension.Extends base.heap {
      objects:=(afterPrice catalogue objects values suffix extension).objects
      environments:=base.heap.environments} :=
  HeapExtension.trans (catalogue.quote.retained true (initial objects values suffix) 0 rfl extension)
    (HeapExtension.same_objects rfl)

def after {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue base scope cursor price free rate)
    (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) : CursorQuoteTail.State :=
  catalogue.after (afterPrice catalogue objects values suffix extension)
    (afterPrice_extends catalogue objects values suffix extension)

private theorem zero_one : Number.mul 0 Number.one=0 := by decide +kernel

theorem native_body {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue base scope cursor price free rate)
    (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (amount : values.amount=.number Number.one)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) (fuel : Nat) :
    Builtins.run (1508+fuel) (CursorQuoteRegistry.machine true base scope cursor objects values suffix)=
      Builtins.run fuel {current true base scope cursor (after catalogue objects values suffix extension) with
        control:=.completion (.return (.number 0))} := by
  rw [show 1508+fuel=64+(1210+(234+fuel)) by omega,
    CursorQuotePrefix.native_sell_prefix base scope cursor price free rate catalogue.quote.arithmetic objects values suffix amount extension]
  change Builtins.run (1210+(234+fuel)) {CursorQuoteTail.machine true (CursorQuoteCatalogue.bodyBase base cursor)
    base.heap.environments scope (initial objects values suffix) with
    control:=.completion (.normal none)
    continuation:=.statementList (CursorQuoteLoop.tail true) none::base.continuation}=_
  have modified := (catalogue.quote.inputs true (initial objects values suffix) 0 rfl extension).native_assignment zero_one (234+fuel)
  refine modified.trans ?_
  exact catalogue.native_tail (afterPrice catalogue objects values suffix extension) rfl
    (afterPrice_extends catalogue objects values suffix extension) fuel

theorem retained {base : Machine} {scope cursor : ObjectId} {price free rate : UInt64}
    (catalogue : CursorReverseTail.Catalogue base scope cursor price free rate)
    (objects : Array JSObject) (values : CursorQuoteLocals.Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) :
    HeapExtension.Extends base.heap (current true base scope cursor (after catalogue objects values suffix extension)).heap :=
  catalogue.retained (afterPrice catalogue objects values suffix extension)
    (afterPrice_extends catalogue objects values suffix extension)

end CookieClicker.JavaScript.CursorReverseComplete

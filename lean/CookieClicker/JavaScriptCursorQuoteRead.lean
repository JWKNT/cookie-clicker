import CookieClicker.JavaScriptCursorQuoteLocals
import CookieClicker.JavaScriptCursorGetPriceRead

/-! Actual native arithmetic reads in the sum/reverse-sum quote loops.
Math.max and Math.pow retain their native bindings and evaluation order. -/
namespace CookieClicker.JavaScript.CursorQuoteRead
open SourceRead TieredRead CursorGetPriceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def loop (reverse : Bool) : Stmt := ((CursorQuoteLocals.body reverse).drop 1).headD .empty
def initial (reverse : Bool) : Expr := match loop reverse with
  | .forLoop (some (.variables [(_,some expression)])) _ _ _=>expression
  | _=>.unsupported "quote loop initializer"
def test (reverse : Bool) : Expr := match loop reverse with
  | .forLoop _ (some expression) _ _=>expression | _=>.unsupported "quote loop test"
def update (reverse : Bool) : Expr := match loop reverse with
  | .forLoop _ _ (some expression) _=>expression | _=>.unsupported "quote loop update"
def loopBody (reverse : Bool) : Stmt := match loop reverse with
  | .forLoop _ _ _ body=>body | _=>.unsupported "quote loop body"
def raw (reverse : Bool) : Expr := match loopBody reverse with
  | .block [.expression (.assignment .add _ expression)]=>expression
  | _=>.unsupported "quote summand"

theorem local_amount (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : CursorQuoteLocals.Values)
    (suffix : Array LexicalEnvironment) :
    Reads (CursorQuoteLocals.start reverse base objects leading outer values suffix) (.identifier "amount") values.amount 3 := by
  apply local_identifier _ _ _ (CursorQuoteLocals.bindings values) (some outer)
    (CursorQuoteLocals.checked_local objects leading outer values suffix)
    (CursorQuoteLocals.has_amount values) (CursorQuoteLocals.read_amount objects leading outer values suffix)

theorem local_i (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : CursorQuoteLocals.Values)
    (suffix : Array LexicalEnvironment) :
    Reads (CursorQuoteLocals.start reverse base objects leading outer values suffix) (.identifier "i") values.i 3 := by
  apply local_identifier _ _ _ (CursorQuoteLocals.bindings values) (some outer)
    (CursorQuoteLocals.checked_local objects leading outer values suffix)
    (CursorQuoteLocals.has_i values) (CursorQuoteLocals.read_i objects leading outer values suffix)

theorem raw_read {base : Machine} {price owned free rate index : UInt64}
    (h : CursorGetPriceRead.Inputs base price owned free rate) (reverse : Bool)
    (indexRead : Reads base (.identifier "i") (.number index) 3) :
    Reads base (raw reverse) (.number (rawValue price index free rate)) 53 := by
  have receiver : Reads base .this (.object h.building) 1 := by
    simpa only [h.receiver] using this_read base
  have bp : Reads base (thisField "basePrice") (.number price) 5 := h.priceRead.dot _ 1 receiver
  have f : Reads base (thisField "free") (.number free) 5 := h.freeRead.dot _ 1 receiver
  have sub := binary_value base .subtract (.identifier "i") (thisField "free") (.number index) (.number free)
    (.number (Number.sub index free)) 3 5 indexRead f rfl rfl (by decide) (by rfl)
  have exp := maximum_read base h.maximum _ (Number.sub index free) 11 sub
  have inc : Reads base increase (.number rate) 7 := h.rateRead.dot _ 3 h.gameRead
  have pow := BuildingMathRead.pow_read base h.power increase _ rate
    (Number.maximum 0 (Number.sub index free)) 7 25 inc exp
  have read := binary_value base .multiply (thisField "basePrice") _ (.number price)
    (.number (Math.pow rate (Number.maximum 0 (Number.sub index free))))
    (.number (rawValue price index free rate)) 5 45 bp pow rfl rfl (by decide) (by rfl)
  cases reverse <;> exact read

theorem owned_read {base : Machine} {price owned free rate : UInt64}
    (h : CursorGetPriceRead.Inputs base price owned free rate) :
    Reads base (thisField "amount") (.number owned) 5 := by
  apply h.amountRead.dot _ 1
  simpa only [h.receiver] using this_read base

theorem initial_buy {base : Machine} {price owned free rate : UInt64}
    (h : CursorGetPriceRead.Inputs base price owned free rate) :
    Reads base (initial false) (.number (Number.maximum 0 owned)) 19 :=
  maximum_read base h.maximum _ owned 5 (owned_read h)

theorem initial_sell {base : Machine} {price owned free rate amount : UInt64}
    (h : CursorGetPriceRead.Inputs base price owned free rate)
    (amountRead : Reads base (.identifier "amount") (.number amount) 3) :
    Reads base (initial true) (.number (Number.maximum 0 (Number.sub owned amount))) 25 := by
  apply maximum_read base h.maximum _ (Number.sub owned amount) 11
  exact binary_value base .subtract _ _ (.number owned) (.number amount)
    (.number (Number.sub owned amount)) 5 3 (owned_read h) amountRead rfl rfl (by decide) (by rfl)


theorem test_buy {base : Machine} {price owned free rate amount index : UInt64}
    (h : CursorGetPriceRead.Inputs base price owned free rate)
    (amountRead : Reads base (.identifier "amount") (.number amount) 3)
    (indexRead : Reads base (.identifier "i") (.number index) 3) :
    Reads base (test false) (.boolean (Number.lessThan index (Number.maximum 0 (Number.add owned amount)))) 31 := by
  have sum := binary_value base .add _ _ (.number owned) (.number amount)
    (.number (Number.add owned amount)) 5 3 (owned_read h) amountRead rfl rfl (by decide) (by rfl)
  have upper := maximum_read base h.maximum _ (Number.add owned amount) 11 sum
  exact binary_value base .less _ _ (.number index) (.number (Number.maximum 0 (Number.add owned amount)))
    (.boolean (Number.lessThan index (Number.maximum 0 (Number.add owned amount)))) 3 25
    indexRead upper rfl rfl (by decide) (by rfl)

theorem test_sell {base : Machine} {price owned free rate index : UInt64}
    (h : CursorGetPriceRead.Inputs base price owned free rate)
    (indexRead : Reads base (.identifier "i") (.number index) 3) :
    Reads base (test true) (.boolean (Number.lessThan index (Number.maximum 0 owned))) 25 := by
  have upper := maximum_read base h.maximum _ owned 5 (owned_read h)
  exact binary_value base .less _ _ (.number index) (.number (Number.maximum 0 owned))
    (.boolean (Number.lessThan index (Number.maximum 0 owned))) 3 19
    indexRead upper rfl rfl (by decide) (by rfl)

end CookieClicker.JavaScript.CursorQuoteRead

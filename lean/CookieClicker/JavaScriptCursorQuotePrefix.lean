import CookieClicker.JavaScriptCursorQuoteRegistry

/-! The exact refresh quotes for the repeatable one-Cursor cycle: after
buyback the native sum loop runs once; after sale the reverse loop is empty.
The entry catalogue supplies every loop read after the actual local writes. -/
namespace CookieClicker.JavaScript.CursorQuotePrefix
open CursorQuoteLocals CursorQuoteRead CursorQuoteLoop CursorQuoteStep CursorQuoteRegistry
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def two : UInt64 := 4611686018427387904

def sum (price free rate : UInt64) : UInt64 :=
  Number.add 0 (CursorGetPriceRead.rawValue price Number.one free rate)

def afterBuy (values : Values) (price free rate : UInt64) : Values :=
  {values with price:=.number (sum price free rate),i:=.number two}

def afterSell (values : Values) : Values := {values with price:=.number 0,i:=.number 0}

private theorem initial_buy_value : Number.maximum 0 Number.one=Number.one := by decide +kernel
private theorem initial_sell_value : Number.maximum 0 (Number.sub 0 Number.one)=0 := by decide +kernel
private theorem buy_true : Number.lessThan Number.one (Number.maximum 0 (Number.add Number.one Number.one))=true := by decide +kernel
private theorem buy_false : Number.lessThan two (Number.maximum 0 (Number.add Number.one Number.one))=false := by decide +kernel
private theorem sell_false : Number.lessThan 0 (Number.maximum 0 0)=false := by decide +kernel
private theorem increment_one : Number.add Number.one Number.one=two := by decide +kernel

theorem native_buy_prefix (base : Machine) (scope cursor : ObjectId) (price free rate : UInt64)
    (world : World base scope cursor price Number.one free rate)
    (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment)
    (amount : values.amount=.number Number.one)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) (fuel : Nat) :
    Builtins.run (170+fuel) (machine false base scope cursor objects values suffix)=
      Builtins.run fuel {machine false base scope cursor objects (afterBuy values price free rate) suffix with
        control:=.completion (.normal (some (.number (sum price free rate))))
        continuation:=.statementList (tail false) none::base.continuation} := by
  let current (v : Values) := machine false base scope cursor objects v suffix
  have extended (v : Values) : HeapExtension.Extends base.heap (current v).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  let zero : Values := {values with price:=.number 0}
  let one : Values := {zero with i:=.number Number.one}
  let counted : Values := {one with price:=.number (sum price free rate)}
  have initial : SourceRead.Reads (current zero) (CursorQuoteRead.initial false) (.number Number.one) 19 := by
    simpa only [initial_buy_value] using initial_buy (world.raw false objects zero suffix (extended zero))
  have startGuard : SourceRead.Reads (current one) (test false) (.boolean true) 31 := by
    have arg : SourceRead.Reads (current one) (.identifier "amount") (.number Number.one) 3 := by
      simpa only [current,machine,one,zero,amount] using local_amount false {base with context:={base.context with thisValue:=.object cursor}}
        objects base.heap.environments scope one suffix
    have idx := local_i false {base with context:={base.context with thisValue:=.object cursor}}
      objects base.heap.environments scope one suffix
    simpa only [buy_true] using test_buy (world.raw false objects one suffix (extended one)) arg idx
  have summand : SourceRead.Reads (current one) (raw false)
      (.number (CursorGetPriceRead.rawValue price Number.one free rate)) 53 :=
    raw_read (world.raw false objects one suffix (extended one)) false
      (local_i false {base with context:={base.context with thisValue:=.object cursor}}
        objects base.heap.environments scope one suffix)
  have stopGuard : SourceRead.Reads (current (afterBuy values price free rate)) (test false) (.boolean false) 31 := by
    have arg : SourceRead.Reads (current (afterBuy values price free rate)) (.identifier "amount") (.number Number.one) 3 := by
      simpa only [current,machine,afterBuy,amount] using local_amount false {base with context:={base.context with thisValue:=.object cursor}}
        objects base.heap.environments scope (afterBuy values price free rate) suffix
    have idx := local_i false {base with context:={base.context with thisValue:=.object cursor}}
      objects base.heap.environments scope (afterBuy values price free rate) suffix
    simpa only [buy_false] using test_buy
      (world.raw false objects (afterBuy values price free rate) suffix (extended _)) arg idx
  dsimp only [current,machine] at initial startGuard summand stopGuard
  rw [show 170+fuel=6+(1+(25+(32+(65+(9+(32+fuel)))))) by omega]
  unfold machine
  rw [native_zero_price,Nat.add_comm 1 (25+(32+(65+(9+(32+fuel)))))]
  change Builtins.run (19+6+(32+(65+(9+(32+fuel))))) {current zero with
    control:=.statement (loop false)
    continuation:=.statementList (tail false) none::base.continuation}=_
  dsimp only [current,machine]
  rw [native_initial_index _ _ _ _ _ _ _ Number.one 19 initial]
  rw [native_guard_true _ _ _ _ _ _ _ 31 startGuard]
  rw [CursorQuoteStep.native_body _ _ _ _ _ _ _ 0 _ rfl summand]
  rw [native_update _ _ _ _ _ _ _ Number.one rfl,increment_one]
  exact native_guard_false _ _ _ _ _ _ _ 31 stopGuard fuel (some (.number (sum price free rate)))

theorem native_sell_prefix (base : Machine) (scope cursor : ObjectId) (price free rate : UInt64)
    (world : World base scope cursor price 0 free rate)
    (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment)
    (amount : values.amount=.number Number.one)
    (extension : HeapExtension.Extends base.heap {objects,environments:=base.heap.environments}) (fuel : Nat) :
    Builtins.run (64+fuel) (machine true base scope cursor objects values suffix)=
      Builtins.run fuel {machine true base scope cursor objects (afterSell values) suffix with
        control:=.completion (.normal none)
        continuation:=.statementList (tail true) none::base.continuation} := by
  let current (v : Values) := machine true base scope cursor objects v suffix
  have extended (v : Values) : HeapExtension.Extends base.heap (current v).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  let zero : Values := {values with price:=.number 0}
  have initial : SourceRead.Reads (current zero) (CursorQuoteRead.initial true) (.number 0) 25 := by
    have arg : SourceRead.Reads (current zero) (.identifier "amount") (.number Number.one) 3 := by
      simpa only [current,machine,zero,amount] using local_amount true {base with context:={base.context with thisValue:=.object cursor}}
        objects base.heap.environments scope zero suffix
    simpa only [initial_sell_value] using initial_sell (world.raw true objects zero suffix (extended zero)) arg
  have stopGuard : SourceRead.Reads (current (afterSell values)) (test true) (.boolean false) 25 := by
    have idx := local_i true {base with context:={base.context with thisValue:=.object cursor}}
      objects base.heap.environments scope (afterSell values) suffix
    simpa only [sell_false] using test_sell
      (world.raw true objects (afterSell values) suffix (extended _)) idx
  dsimp only [current,machine] at initial stopGuard
  rw [show 64+fuel=6+(1+(31+(26+fuel))) by omega]
  unfold machine
  rw [native_zero_price,Nat.add_comm 1 (31+(26+fuel))]
  change Builtins.run (25+6+(26+fuel)) {current zero with
    control:=.statement (loop true)
    continuation:=.statementList (tail true) none::base.continuation}=_
  dsimp only [current,machine]
  rw [native_initial_index _ _ _ _ _ _ _ 0 25 initial]
  exact native_guard_false _ _ _ _ _ _ _ 25 stopGuard fuel

end CookieClicker.JavaScript.CursorQuotePrefix

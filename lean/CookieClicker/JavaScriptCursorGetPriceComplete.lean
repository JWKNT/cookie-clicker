import CookieClicker.JavaScriptCursorGetPriceBody
import CookieClicker.JavaScriptPriceCall

/-! Complete native getPrice body. Its price modifier is the full source
call, and its arithmetic uses the real Math.max, Math.pow and Math.ceil
bindings. Original objects and all nested allocations remain present. -/
namespace CookieClicker.JavaScript.CursorGetPriceComplete
open SourceRead TieredRead
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure State where
  objects : Array JSObject
  values : CursorGetPriceLocals.Values
  suffix : Array LexicalEnvironment

def machine (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) : Machine :=
  CursorGetPriceLocals.start base s.objects leading outer s.values s.suffix

def priced (s : State) (price : UInt64) : State := {s with values:={s.values with price:=.number price}}

def caller (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) (price : UInt64) : Machine := {
  machine base leading outer (priced s price) with
  continuation:=CursorGetPriceBody.frames leading base.continuation }

structure Inputs (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (basePrice amount free rate : UInt64) where
  raw : CursorGetPriceRead.Inputs (machine base leading outer s) basePrice amount free rate
  scope : EnvId
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate)).heap raw.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate)).heap raw.game
    (JSString.ofString "modifyBuildingPrice")=.ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate)).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (PriceSource.closure scope source)
  gameRead : Reads (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate))
    (.identifier "Game") (.object raw.game) 3
  modifier : PriceComplete.Inputs
    (PriceCall.bodyBase (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate)) raw.game)
    (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate)).heap.environments scope
    (PriceCall.initial (caller base leading outer s (CursorGetPriceRead.rawValue basePrice amount free rate))
      raw.building function (CursorGetPriceRead.rawValue basePrice amount free rate))

abbrev Inputs.price {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {basePrice amount free rate : UInt64} (_ : Inputs base leading outer s basePrice amount free rate) : UInt64 :=
  CursorGetPriceRead.rawValue basePrice amount free rate

def Inputs.after {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {basePrice amount free rate : UInt64} (h : Inputs base leading outer s basePrice amount free rate) : State := {
  objects:=h.modifier.final.objects
  values:=(priced s h.price).values
  suffix:=(s.suffix.push ⟨.declarative (PriceLocals.bindings h.modifier.final.values),some h.scope⟩)++h.modifier.final.suffix }

theorem Inputs.layout {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {basePrice amount free rate : UInt64} (h : Inputs base leading outer s basePrice amount free rate) :
    (PriceCall.returned (caller base leading outer s h.price) h.scope h.raw.game h.raw.building h.function h.price h.modifier).heap=
      (machine base leading outer h.after).heap := by
  simp only [PriceCall.returned,PriceStages.machine,PriceLocals.start,PriceLocals.heap,Inputs.after,
    caller,machine,CursorGetPriceLocals.start,CursorGetPriceLocals.heap,Array.push_append,Array.append_assoc,priced]

theorem Inputs.native_modifier {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {basePrice amount free rate : UInt64} (h : Inputs base leading outer s basePrice amount free rate)
    (stable : Number.mul h.price Number.one=h.price) (fuel : Nat) :
    Builtins.run (1202+fuel) {caller base leading outer s h.price with control:=.expression CursorGetPriceBody.modifier}=
      Builtins.run fuel {machine base leading outer h.after with
        control:=.expressionResult (.value (.number h.price))
        continuation:=CursorGetPriceBody.frames leading base.continuation} := by
  have receiver : Reads (caller base leading outer s h.price) .this (.object h.raw.building) 1 := by
    have receiverValue : base.context.thisValue=.object h.raw.building := h.raw.receiver
    simpa only [machine,caller,CursorGetPriceLocals.start,receiverValue] using
      CursorGetPriceRead.this_read (caller base leading outer s h.price)
  have priceRead : Reads (caller base leading outer s h.price) (.identifier "price") (.number h.price) 3 := by
    apply local_identifier _ _ _ (CursorGetPriceLocals.bindings (priced s h.price).values) (some outer)
    · exact CursorGetPriceLocals.checked_local s.objects leading outer (priced s h.price).values s.suffix
    · exact CursorGetPriceLocals.has_price (priced s h.price).values
    · exact CursorGetPriceLocals.read_price s.objects leading outer (priced s h.price).values s.suffix
  change Builtins.run (1+3+1198+fuel) {caller base leading outer s h.price with
    control:=.expression (PriceCall.expression .this (.identifier "price"))}=_
  rw [PriceCall.source_call (caller base leading outer s h.price) h.scope h.raw.game h.raw.building
    h.function h.price h.modifier stable h.source h.gameObject h.functionObject .this (.identifier "price") 1 3
    h.gamePresent h.gameKind h.method h.functionPresent h.functionKind h.gameRead receiver priceRead]
  apply congrArg (Builtins.run fuel)
  exact congrArg (fun heap => {base with
    heap
    context:=(machine base leading outer s).context
    control:=.expressionResult (.value (.number h.price))
    continuation:=CursorGetPriceBody.frames leading base.continuation}) h.layout

theorem local_price (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) :
    Reads (machine base leading outer s) (.identifier "price") s.values.price 3 := by
  apply local_identifier _ _ _ (CursorGetPriceLocals.bindings s.values) (some outer)
  · exact CursorGetPriceLocals.checked_local s.objects leading outer s.values s.suffix
  · exact CursorGetPriceLocals.has_price s.values
  · exact CursorGetPriceLocals.read_price s.objects leading outer s.values s.suffix

theorem native_return (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (price : UInt64) (value : s.values.price=.number price)
    (ceiling : BuildingMathRead.Binding (machine base leading outer s) "ceil") (fuel : Nat) :
    Builtins.run (18+fuel) {machine base leading outer s with
      control:=.statement ((CursorGetPriceLocals.body.drop 2).headD .empty)
      continuation:=.statementList [] (some (.number price))::base.continuation}=
      Builtins.run fuel {machine base leading outer s with control:=.completion (.return (.number (Number.ceil price)))} := by
  have priceRead : Reads (machine base leading outer s) (.identifier "price") (.number price) 3 := by
    simpa only [value] using local_price base leading outer s
  have read:=BuildingMathRead.ceil_read (machine base leading outer s) ceiling (.identifier "price") price 3 priceRead
  rw [show 18+fuel=17+(1+fuel) by omega]
  change Builtins.run (15+2+(1+fuel)) {machine base leading outer s with
    control:=.statement (.return (some (BuildingMathRead.call "ceil" [.identifier "price"])))
    continuation:=.statementList [] (some (.number price))::base.continuation}=_
  rw [return_read {machine base leading outer s with continuation:=.statementList [] (some (.number price))::base.continuation}
    _ _ 15 read,Nat.add_comm 1 fuel]
  rfl

theorem Inputs.native_body {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {basePrice amount free rate : UInt64} (h : Inputs base leading outer s basePrice amount free rate)
    (stable : Number.mul h.price Number.one=h.price)
    (ceiling : BuildingMathRead.Binding (machine base leading outer h.after) "ceil") (fuel : Nat) :
    Builtins.run (1289+fuel) (machine base leading outer s)=
      Builtins.run fuel {machine base leading outer h.after with control:=.completion (.return (.number (Number.ceil h.price)))} := by
  rw [show 1289+fuel=60+(1+(4+(1202+(3+(1+(18+fuel)))))) by omega]
  unfold machine
  rw [CursorGetPriceBody.native_initial base s.objects leading outer s.values s.suffix basePrice amount free rate h.raw,
    Nat.add_comm 1 (4+(1202+(3+(1+(18+fuel)))))]
  change Builtins.run (4+(1202+(3+(1+(18+fuel))))) {CursorGetPriceLocals.start base s.objects leading outer
    (priced s h.price).values s.suffix with
    control:=.statement (.expression (.assignment .assign (.identifier "price") CursorGetPriceBody.modifier))
    continuation:=.statementList (CursorGetPriceLocals.body.drop 2) none::base.continuation}=_
  rw [CursorGetPriceBody.native_assignment_prefix]
  change Builtins.run (1202+(3+(1+(18+fuel)))) {caller base leading outer s h.price with
    control:=.expression CursorGetPriceBody.modifier}=_
  rw [h.native_modifier stable]
  change Builtins.run (3+(1+(18+fuel))) {CursorGetPriceLocals.start base h.after.objects leading outer h.after.values h.after.suffix with
    control:=.expressionResult (.value (.number h.price))
    continuation:=CursorGetPriceBody.frames leading base.continuation}=_
  rw [CursorGetPriceBody.native_assignment_suffix]
  have unchanged : {h.after.values with price:=.number h.price}=h.after.values := rfl
  rw [unchanged,Nat.add_comm 1 (18+fuel)]
  change Builtins.run (18+fuel) {machine base leading outer h.after with
    control:=.statement ((CursorGetPriceLocals.body.drop 2).headD .empty)
    continuation:=.statementList [] (some (.number h.price))::base.continuation}=_
  exact native_return base leading outer h.after h.price rfl ceiling fuel

end CookieClicker.JavaScript.CursorGetPriceComplete

import CookieClicker.JavaScriptCursorQuoteStep
import CookieClicker.JavaScriptPriceRegistryCall

/-! Native quote assignment calls the complete source price modifier. Its
later helper frames are constructed from one catalogue. Every argument object
and local environment remains in the returned heap. -/
namespace CookieClicker.JavaScript.CursorQuoteTail
open SourceRead TieredRead
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure State where
  objects : Array JSObject
  values : CursorQuoteLocals.Values
  suffix : Array LexicalEnvironment
  previous : Option Value

def machine (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) : Machine :=
  CursorQuoteLocals.start reverse base s.objects leading outer s.values s.suffix

def modifier : Expr := PriceCall.expression .this (.identifier "price")
def reference (leading : Array LexicalEnvironment) : Reference := ⟨.environment (CursorQuoteLocals.slotIndex leading) "price",false⟩
def rest (reverse : Bool) : List Stmt := (CursorQuoteLocals.body reverse).drop 3

def frames (reverse : Bool) (leading : Array LexicalEnvironment) (previous : Option Value) (continuation : List Frame) : List Frame :=
  .assignmentRight .assign (reference leading) none::.expressionStatement::
    .statementList (rest reverse) previous::continuation

def caller (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) : Machine := {
  machine reverse base leading outer s with continuation:=frames reverse leading s.previous base.continuation }

structure Inputs (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (price : UInt64) where
  game : ObjectId
  function : ObjectId
  world : PriceRegistry.World (PriceCall.bodyBase (caller reverse base leading outer s) game)
  profile : PriceRegistryComplete.Profile world
  sameGame : world.window.game=game
  source : Option JSString
  functionObject : JSObject
  method : lookupProperty (caller reverse base leading outer s).heap game
    (JSString.ofString "modifyBuildingPrice")=.ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (caller reverse base leading outer s).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (PriceSource.closure world.priceScope.path.closureScope source)
  gameRead : Reads (caller reverse base leading outer s) (.identifier "Game") (.object game) 3
  receiver : base.context.thisValue=.object profile.building
  priceValue : s.values.price=.number price

abbrev Inputs.priceInputs {reverse : Bool} {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {price : UInt64} (h : Inputs reverse base leading outer s price) :=
  PriceRegistryCall.inputs (caller reverse base leading outer s) h.game h.function price h.world h.profile

def Inputs.after {reverse : Bool} {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {price : UInt64} (h : Inputs reverse base leading outer s price) : State := {
  objects:=h.priceInputs.final.objects
  values:=s.values
  previous:=s.previous
  suffix:=(s.suffix.push ⟨.declarative (PriceLocals.bindings h.priceInputs.final.values),some h.world.priceScope.path.closureScope⟩)++h.priceInputs.final.suffix }

theorem Inputs.layout {reverse : Bool} {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {price : UInt64} (h : Inputs reverse base leading outer s price) :
    (PriceRegistryCall.returned (caller reverse base leading outer s) h.game h.function price h.world h.profile).heap=
      (machine reverse base leading outer h.after).heap := by
  simp only [Inputs.priceInputs,PriceRegistryCall.returned,PriceCall.returned,PriceStages.machine,PriceLocals.start,PriceLocals.heap,Inputs.after,
    caller,machine,CursorQuoteLocals.start,CursorQuoteLocals.heap,Array.push_append,Array.append_assoc]

theorem local_price (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) :
    Reads (machine reverse base leading outer s) (.identifier "price") s.values.price 3 := by
  apply local_identifier _ _ _ (CursorQuoteLocals.bindings s.values) (some outer)
  · exact CursorQuoteLocals.checked_local s.objects leading outer s.values s.suffix
  · exact CursorQuoteLocals.has_price s.values
  · exact CursorQuoteLocals.read_price s.objects leading outer s.values s.suffix

theorem Inputs.native_modifier {reverse : Bool} {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {price : UInt64} (h : Inputs reverse base leading outer s price)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1202+fuel) {caller reverse base leading outer s with control:=.expression modifier}=
      Builtins.run fuel {machine reverse base leading outer h.after with
        control:=.expressionResult (.value (.number price))
        continuation:=frames reverse leading s.previous base.continuation} := by
  have receiver : Reads (caller reverse base leading outer s) .this (.object h.profile.building) 1 := by
    simpa only [caller,machine,CursorQuoteLocals.start,h.receiver] using CursorGetPriceRead.this_read (caller reverse base leading outer s)
  have priceRead : Reads (caller reverse base leading outer s) (.identifier "price") (.number price) 3 := by
    simpa only [caller,SourceRead.Reads,h.priceValue] using local_price reverse base leading outer s
  change Builtins.run (1+3+1198+fuel) {caller reverse base leading outer s with
    control:=.expression (PriceCall.expression .this (.identifier "price"))}=_
  rw [PriceRegistryCall.source_call (caller reverse base leading outer s) h.game h.function price h.world h.profile
    h.source h.functionObject h.sameGame h.method h.functionPresent h.functionKind h.gameRead
    .this (.identifier "price") 1 3 receiver priceRead stable]
  apply congrArg (Builtins.run fuel)
  exact congrArg (fun heap => {base with
    heap
    context:=(machine reverse base leading outer s).context
    control:=.expressionResult (.value (.number price))
    continuation:=frames reverse leading s.previous base.continuation}) h.layout

theorem assignment_prefix (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId)
    (s : State) (fuel : Nat) (previous : Option Value) :
    Builtins.run (4+fuel) {machine reverse base leading outer s with
      control:=.statement (.expression (.assignment .assign (.identifier "price") modifier))
      continuation:=.statementList (rest reverse) previous::base.continuation}=
      Builtins.run fuel {machine reverse base leading outer s with
        control:=.expression modifier
        continuation:=.assignmentRight .assign (reference leading) none::.expressionStatement::
          .statementList (rest reverse) previous::base.continuation} := by
  rw [show 4+fuel=2+(1+(1+fuel)) by omega,Nat.add_comm 2 (1+(1+fuel))]
  change Builtins.run (1+(1+fuel)) {machine reverse base leading outer s with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .assign modifier::.expressionStatement::.statementList (rest reverse) previous::base.continuation}=_
  rw [Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) (Environment.identifier {machine reverse base leading outer s with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .assign modifier::.expressionStatement::.statementList (rest reverse) previous::base.continuation} "price")=_
  unfold machine
  rw [CursorQuoteStep.price_reference,Nat.add_comm 1 fuel]
  rfl

attribute [local cbv_opaque] CursorQuoteLocals.heap CursorQuoteLocals.slotIndex CursorQuoteLocals.bindings checkedEnvironment setBinding
attribute [local cbv_eval] CursorQuoteLocals.checked_local CursorQuoteLocals.set_price

theorem assignment_suffix (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId)
    (s : State) (price : UInt64) (fuel : Nat) (previous : Option Value) :
    Builtins.run (3+fuel) {machine reverse base leading outer s with
      control:=.expressionResult (.value (.number price))
      continuation:=.assignmentRight .assign (reference leading) none::.expressionStatement::
        .statementList (rest reverse) previous::base.continuation}=
      Builtins.run fuel {machine reverse base leading outer {s with values:={s.values with price:=.number price}} with
        control:=.completion (.normal (some (.number price)))
        continuation:=.statementList (rest reverse) previous::base.continuation} := by
  rw [Nat.add_comm 3 fuel]
  cbv


theorem native_return (reverse : Bool) (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (price : UInt64) (value : s.values.price=.number price)
    (ceiling : BuildingMathRead.Binding (machine reverse base leading outer s) "ceil") (fuel : Nat) :
    Builtins.run (18+fuel) {machine reverse base leading outer s with
      control:=.statement (.return (some (BuildingMathRead.call "ceil" [.identifier "price"])))
      continuation:=.statementList [] (some (.number price))::base.continuation}=
      Builtins.run fuel {machine reverse base leading outer s with control:=.completion (.return (.number (Number.ceil price)))} := by
  have priceRead : Reads (machine reverse base leading outer s) (.identifier "price") (.number price) 3 := by
    simpa only [value] using local_price reverse base leading outer s
  have read:=BuildingMathRead.ceil_read (machine reverse base leading outer s) ceiling (.identifier "price") price 3 priceRead
  rw [show 18+fuel=17+(1+fuel) by omega]
  rw [return_read {machine reverse base leading outer s with continuation:=.statementList [] (some (.number price))::base.continuation}
    _ _ 15 read,Nat.add_comm 1 fuel]
  rfl


theorem Inputs.native_assignment {reverse : Bool} {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {price : UInt64} (h : Inputs reverse base leading outer s price)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1210+fuel) {machine reverse base leading outer s with
      control:=.completion (.normal s.previous)
      continuation:=.statementList (CursorQuoteLoop.tail reverse) none::base.continuation}=
      Builtins.run fuel {machine reverse base leading outer h.after with
        control:=.completion (.normal (some (.number price)))
        continuation:=.statementList (rest reverse) s.previous::base.continuation} := by
  rw [show 1210+fuel=1+(4+(1202+(3+fuel))) by omega,Nat.add_comm 1 (4+(1202+(3+fuel)))]
  change Builtins.run (4+(1202+(3+fuel))) (Builtins.builtinStep {machine reverse base leading outer s with
    control:=.completion (.normal s.previous)
    continuation:=.statementList (CursorQuoteLoop.tail reverse) none::base.continuation})=_
  have first : Builtins.builtinStep {machine reverse base leading outer s with
      control:=.completion (.normal s.previous)
      continuation:=.statementList (CursorQuoteLoop.tail reverse) none::base.continuation}=
      {machine reverse base leading outer s with
        control:=.statement (.expression (.assignment .assign (.identifier "price") modifier))
        continuation:=.statementList (rest reverse) s.previous::base.continuation} := by
    cases reverse <;> cases eq:s.previous <;>
      simp [Builtins.builtinStep,step,internalStep,consumeCompletion,Completion.updateEmpty,statements,pushStatement,
        machine,CursorQuoteLocals.start,CursorQuoteLoop.tail,CursorQuoteLocals.body,CursorQuoteLocals.statement,
        CursorCycleSyntax.getSumPriceBody,CursorCycleSyntax.getReverseSumPriceBody,modifier,PriceCall.expression,rest]
  rw [first,assignment_prefix]
  change Builtins.run (1202+(3+fuel)) {caller reverse base leading outer s with control:=.expression modifier}=_
  rw [h.native_modifier stable]
  change Builtins.run (3+fuel) {machine reverse base leading outer h.after with
    control:=.expressionResult (.value (.number price))
    continuation:=.assignmentRight .assign (reference leading) none::.expressionStatement::
      .statementList (rest reverse) s.previous::base.continuation}=_
  rw [assignment_suffix]
  have vv : {s.values with price:=.number price}=s.values := by
    cases eq:s.values with
    | mk amount arguments old index =>
      have same : old=.number price := by simpa only [eq] using h.priceValue
      simp only [same]
  simp only [Inputs.after,vv]

theorem Inputs.native_sum_tail {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {price : UInt64} (h : Inputs false base leading outer s price)
    (stable : Number.mul price Number.one=price)
    (ceiling : BuildingMathRead.Binding (machine false base leading outer h.after) "ceil") (fuel : Nat) :
    Builtins.run (1229+fuel) {machine false base leading outer s with
      control:=.completion (.normal s.previous)
      continuation:=.statementList (CursorQuoteLoop.tail false) none::base.continuation}=
      Builtins.run fuel {machine false base leading outer h.after with control:=.completion (.return (.number (Number.ceil price)))} := by
  rw [show 1229+fuel=1+(4+(1202+(3+(1+(18+fuel))))) by omega,Nat.add_comm 1 (4+(1202+(3+(1+(18+fuel)))))]
  change Builtins.run (4+(1202+(3+(1+(18+fuel))))) (Builtins.builtinStep {machine false base leading outer s with
    control:=.completion (.normal s.previous)
    continuation:=.statementList (CursorQuoteLoop.tail false) none::base.continuation})=_
  have first : Builtins.builtinStep {machine false base leading outer s with
      control:=.completion (.normal s.previous)
      continuation:=.statementList (CursorQuoteLoop.tail false) none::base.continuation}=
      {machine false base leading outer s with
        control:=.statement (.expression (.assignment .assign (.identifier "price") modifier))
        continuation:=.statementList (rest false) s.previous::base.continuation} := by
    cases eq:s.previous <;> simp [Builtins.builtinStep,step,internalStep,consumeCompletion,Completion.updateEmpty,statements,pushStatement,
      machine,CursorQuoteLocals.start,CursorQuoteLoop.tail,CursorQuoteLocals.body,CursorQuoteLocals.statement,
      CursorCycleSyntax.getSumPriceBody,modifier,PriceCall.expression,rest]
  rw [first]
  rw [assignment_prefix]
  change Builtins.run (1202+(3+(1+(18+fuel)))) {caller false base leading outer s with control:=.expression modifier}=_
  rw [h.native_modifier stable]
  change Builtins.run (3+(1+(18+fuel))) {machine false base leading outer h.after with
    control:=.expressionResult (.value (.number price))
    continuation:=.assignmentRight .assign (reference leading) none::.expressionStatement::
      .statementList (rest false) s.previous::base.continuation}=_
  rw [assignment_suffix]
  have unchanged : {h.after with values:={h.after.values with price:=.number price}}=h.after := by
    have vv : {s.values with price:=.number price}=s.values := by
      cases eq:s.values with
      | mk amount arguments old index =>
        have same : old=.number price := by simpa only [eq] using h.priceValue
        simp only [same]
    simp only [Inputs.after,vv]
  rw [unchanged,Nat.add_comm 1 (18+fuel)]
  exact native_return false base leading outer h.after price h.priceValue ceiling fuel

end CookieClicker.JavaScript.CursorQuoteTail

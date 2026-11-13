import CookieClicker.JavaScriptPriceCalls

/-! Source statement semantics of the price modifier, including allocation by
all nested helper calls and native binary64 compound assignments. -/
namespace CookieClicker.JavaScript.PriceStatements
open SourceRead TieredRead PriceStages PriceCalls
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def statement (index : Nat) : Stmt := (PriceSource.body.drop index).headD .empty

def auraName : JSString := JSString.ofString "Fierce Hoarder"
def auraExpression : Expr := MemberCall.expression "auraMult" (.literal (.string auraName))
def factor : Expr := .binary .subtract (.literal (.number Number.one))
  (.binary .multiply auraExpression (.literal (.number 4581421828931458171)))
def effectName : JSString := JSString.ofString "buildingCost"
def effectExpression : Expr := MemberCall.expression "eff" (.literal (.string effectName))

theorem aura_source : statement 5=PriceArithmetic.multiplyStatement factor := rfl
theorem effect_source : statement 10=PriceArithmetic.multiplyStatement effectExpression := rfl

def auraFrames (leading : Array LexicalEnvironment) (price : UInt64) (continuation : List Frame) : List Frame :=
  .binaryLeft .multiply (.literal (.number 4581421828931458171))::
  .binaryRight .subtract (.number Number.one)::PriceArithmetic.callContinuation leading price continuation

private theorem mul_zero : Number.mul 0 4581421828931458171=0 := by decide +kernel
private theorem sub_zero : Number.sub Number.one 0=Number.one := by decide +kernel
attribute [local cbv_opaque] Number.mul Number.sub
attribute [local cbv_eval] mul_zero sub_zero

theorem arithmetic_tail (base : Machine) (leading : Array LexicalEnvironment) (price : UInt64)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (4+fuel) {base with
      control:=.expressionResult (.value (.number 0)),
      continuation:=auraFrames leading price continuation}=
      Builtins.run fuel {base with
        control:=.expressionResult (.value (.number Number.one)),
        continuation:=PriceArithmetic.callContinuation leading price continuation} := by
  rw [Nat.add_comm 4 fuel]
  cbv

theorem unchanged_price (v : PriceLocals.Values) (price : UInt64) (value : v.price=.number price) :
    {v with price:=.number price}=v := by cases v; simp_all

theorem native_aura {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Aura (machine base leading outer s) auraName) (price : UInt64)
    (value : s.values.price=.number price) (stable : Number.mul price Number.one=price)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (179+fuel) {machine base leading outer s with control:=.statement (statement 5),continuation}=
      Builtins.run fuel {machine base leading outer h.after with
        control:=.completion (.normal (some (.number price))),continuation} := by
  rw [aura_source,show 179+fuel=6+(4+(161+(4+(4+fuel)))) by omega]
  change Builtins.run (6+(4+(161+(4+(4+fuel))))) {PriceLocals.start {base with continuation}
    s.objects leading outer s.values s.suffix with control:=.statement (PriceArithmetic.multiplyStatement factor)}=_
  rw [PriceArithmetic.multiply_prefix _ _ _ _ _ _ price value factor,Nat.add_comm 4 (161+(4+(4+fuel)))]
  change Builtins.run (161+(4+(4+fuel))) {machine base leading outer s with
    control:=.expression auraExpression,continuation:=auraFrames leading price continuation}=_
  simp only [auraExpression]
  rw [h.native_call,arithmetic_tail]
  change Builtins.run (4+fuel) {PriceLocals.start {base with continuation} h.after.objects leading outer h.after.values h.after.suffix with
    control:=.expressionResult (.value (.number Number.one)),continuation:=PriceArithmetic.callContinuation leading price continuation}=_
  rw [PriceArithmetic.multiply_suffix,stable,unchanged_price h.after.values price value]
  rfl

theorem native_effect {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Effect (machine base leading outer s) effectName) (price : UInt64)
    (value : s.values.price=.number price) (stable : Number.mul price Number.one=price)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (68+fuel) {machine base leading outer s with control:=.statement (statement 10),continuation}=
      Builtins.run fuel {machine base leading outer h.after with
        control:=.completion (.normal (some (.number price))),continuation} := by
  rw [effect_source,show 68+fuel=6+(58+(4+fuel)) by omega]
  change Builtins.run (6+(58+(4+fuel))) {PriceLocals.start {base with continuation}
    s.objects leading outer s.values s.suffix with control:=.statement (PriceArithmetic.multiplyStatement effectExpression)}=_
  rw [PriceArithmetic.multiply_prefix _ _ _ _ _ _ price value effectExpression]
  change Builtins.run (58+(4+fuel)) {machine base leading outer s with
    control:=.expression effectExpression,continuation:=PriceArithmetic.callContinuation leading price continuation}=_
  simp only [effectExpression]
  rw [h.native_call]
  change Builtins.run (4+fuel) {PriceLocals.start {base with continuation} h.after.objects leading outer h.after.values h.after.suffix with
    control:=.expressionResult (.value (.number Number.one)),continuation:=PriceArithmetic.callContinuation leading price continuation}=_
  rw [PriceArithmetic.multiply_suffix,stable,unchanged_price h.after.values price value]
  rfl

def buffStatement (name : JSString) (yes : Stmt) : Stmt :=
  .ifThenElse (MemberCall.expression "hasBuff" (.literal (.string name))) yes none

theorem native_buff {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Buff (machine base leading outer s) name) (yes : Stmt)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (44+fuel) {machine base leading outer s with control:=.statement (buffStatement name yes),continuation}=
      Builtins.run fuel {machine base leading outer h.after with control:=.completion (.normal none),continuation} := by
  rw [show 44+fuel=1+(42+(1+fuel)) by omega,Nat.add_comm 1 (42+(1+fuel))]
  change Builtins.run (42+(1+fuel)) {machine base leading outer s with
    control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))
    continuation:=.ifTest yes none::continuation}=_
  rw [h.native_call,Nat.add_comm 1 fuel]
  rfl

def fortune : Expr := .member (.identifier "building") (.identifier "fortune") false
def fortuneArgument : Expr := .member fortune (.identifier "name") false
def fortuneYes : Stmt := match statement 9 with | .ifThenElse _ yes _=>yes | _=>.empty

theorem fortune_source : statement 9=.ifThenElse
    (.logical .and fortune (HasReadPrelude.call fortuneArgument)) fortuneYes none := rfl

theorem local_building (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) :
    Reads (machine base leading outer s) (.identifier "building") s.values.building 3 := by
  apply local_identifier _ _ _ (PriceLocals.bindings s.values) (some outer)
  · exact PriceLocals.checked_local s.objects leading outer s.values s.suffix
  · exact PriceLocals.has_building s.values
  · exact PriceLocals.read_building s.objects leading outer s.values s.suffix

theorem native_fortune {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : TieredSuffix.HasZero (machine base leading outer s) what)
    (building upgrade : ObjectId) (value : s.values.building=.object building)
    (selected : DataEdge (machine base leading outer s) building (JSString.ofString "fortune") (.object upgrade))
    (name : DataEdge (machine base leading outer s) upgrade (JSString.ofString "name") (.string what))
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (101+fuel) {machine base leading outer s with control:=.statement (statement 9),continuation}=
      Builtins.run fuel {machine base leading outer (afterHas base leading outer s
        h.scopes.closureScope h.function h.frame.upgrade what) with control:=.completion (.normal none),continuation} := by
  have buildingRead : Reads (machine base leading outer s) (.identifier "building") (.object building) 3 := by
    simpa only [value] using local_building base leading outer s
  have left : Reads (machine base leading outer s) fortune (.object upgrade) 7 := selected.dot _ 3 buildingRead
  have argument : Reads (machine base leading outer s) fortuneArgument (.string what) 11 := name.dot _ 7 left
  rw [fortune_source,show 101+fuel=2+(7+(1+(89+(2+fuel)))) by omega,
    Nat.add_comm 2 (7+(1+(89+(2+fuel))))]
  change Builtins.run (7+(1+(89+(2+fuel)))) {machine base leading outer s with
    control:=.expression fortune
    continuation:=.logical .and (HasReadPrelude.call fortuneArgument)::.ifTest fortuneYes none::continuation}=_
  rw [left _ (by rfl),Nat.add_comm 1 (89+(2+fuel))]
  change Builtins.run (89+(2+fuel)) {machine base leading outer s with
    control:=.expression (HasReadPrelude.call fortuneArgument)
    continuation:=.valueBoundary::.ifTest fortuneYes none::continuation}=_
  rw [HasReadPrelude.source_call {machine base leading outer s with
      continuation:=.valueBoundary::.ifTest fortuneYes none::continuation}
    fortuneArgument h.frame h.scopes h.objects h.environments h.global h.exclusions h.function h.source
    h.functionObject h.functionRead h.functionKind h.gameHas h.gameRead 11 argument,
    Nat.add_comm 2 fuel]
  change Builtins.run fuel (TieredZero.skipped {machine base leading outer s with continuation}
    h.scopes.closureScope h.frame.upgrade h.function what)=_
  congr 1
  have layout:=has_layout base leading outer s h.scopes.closureScope h.function h.frame.upgrade what
  simp only [TieredZero.skipped,machine,PriceLocals.start] at layout ⊢
  congr 1

end CookieClicker.JavaScript.PriceStatements

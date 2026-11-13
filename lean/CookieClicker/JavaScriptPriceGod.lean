import CookieClicker.JavaScriptPriceStatements

/-! The source creation-god discount guard. The actual Pantheon lookup
returns false from slots [Godzamok,-1,-1]; the three native comparisons
then leave the price unchanged. -/
namespace CookieClicker.JavaScript.PriceGod
open SourceRead TieredRead PriceStages PriceStatements
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def godCondition : Stmt := match statement 11 with
  | .ifThenElse _ (.block (_::condition::_)) _=>condition | _=>.empty

def godExpression : Expr := MemberCall.expression "hasGod" (.literal (.string PantheonRead.creation))
def godReference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (PriceLocals.slotIndex leading) "godLvl",false⟩
def godFrames (leading : Array LexicalEnvironment) (continuation : List Frame) : List Frame :=
  .assignmentRight .assign (godReference leading) none::.variableWrite []::
    .statementList [godCondition] none::continuation

structure Inputs (base : Machine) where
  scope : EnvId
  game : ObjectId
  function : ObjectId
  world : PantheonRead.World (PantheonCall.state base scope game function)
  capture : PantheonRead.CapturedM base.heap.environments scope world.m
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject base.heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap game (JSString.ofString "hasGod")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (PantheonSource.closure scope source)
  gameRead : Reads base (.identifier "Game") (.object game) 3

def Inputs.called {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs (machine base leading outer s)) : State := {
  objects:=s.objects.push (PantheonSource.argumentObject (machine base leading outer s)
    (.string PantheonRead.creation) (some h.function))
  values:=s.values
  suffix:=s.suffix.push ⟨.declarative (PantheonLocals.bindings {
    PantheonCall.values (machine base leading outer s) with god:=.object h.world.god,i:=.number (Number.ofNat 3)}),some h.scope⟩ }

def Inputs.after {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs (machine base leading outer s)) : State :=
  {h.called with values:={s.values with godLvl:=.boolean false}}

theorem Inputs.layout {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs (machine base leading outer s)) :
    (PantheonCall.returned (machine base leading outer s) h.scope h.game h.function h.world.god).heap=
      (machine base leading outer h.called).heap := by
  simp only [PantheonCall.returned,PantheonCall.state,PantheonLocals.start,PantheonLocals.heap,
    Inputs.called,machine,PriceLocals.start,PriceLocals.heap,Array.append_empty,Array.push_append]

theorem Inputs.native_call {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs (machine base leading outer s)) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (205+fuel) {machine base leading outer s with control:=.expression godExpression,continuation}=
      Builtins.run fuel {machine base leading outer h.called with
        control:=.expressionResult (.value (.boolean false)),continuation} := by
  simp only [godExpression]
  rw [PantheonCall.source_call {machine base leading outer s with continuation} h.scope h.game h.function
    (h.world.extend (HeapExtension.same_objects rfl)) h.capture h.source h.gameObject h.functionObject
    h.gamePresent h.gameKind h.method h.functionPresent h.functionKind h.gameRead]
  congr 1
  have layout:=h.layout
  simp only [PantheonCall.returned,machine,PriceLocals.start] at layout ⊢
  congr 1

theorem god_reference (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (control : Control) (continuation : List Frame) :
    identifierReference {machine base leading outer s with control,continuation} "godLvl"=
      .ok (godReference leading) := by
  simp [identifierReference,resolveName,machine,PriceLocals.start,godReference,
    PriceLocals.checked_local,PriceLocals.bindings,bind,Except.bind,pure,Except.pure]

attribute [local cbv_opaque] machine identifierReference
attribute [local cbv_eval] god_reference

theorem Inputs.native_prefix {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs (machine base leading outer s)) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (11+fuel) {machine base leading outer s with control:=.statement (statement 11),continuation}=
      Builtins.run fuel {machine base leading outer s with
        control:=.expression godExpression,
        continuation:=godFrames leading continuation} := by
  have methodRead : Reads (machine base leading outer s) (.member (.identifier "Game") (.identifier "hasGod") false)
      (.object h.function) 7 := dot _ _ h.game "hasGod" (.object h.function) h.gameObject 3 h.gameRead
        h.gamePresent (Or.inl h.gameKind) h.method
  rw [show 11+fuel=1+(7+(3+fuel)) by omega,Nat.add_comm 1 (7+(3+fuel))]
  change Builtins.run (7+(3+fuel)) {machine base leading outer s with
    control:=.expression (.member (.identifier "Game") (.identifier "hasGod") false),
    continuation:=.ifTest (.block [.variable [("godLvl",some godExpression)],godCondition]) none::continuation}=_
  rw [methodRead _ (by rfl),show 3+fuel=2+(1+fuel) by omega,Nat.add_comm 2 (1+fuel)]
  change Builtins.run (1+fuel) {machine base leading outer s with
    control:=.statement (.variable [("godLvl",some godExpression)])
    continuation:=.statementList [godCondition] none::continuation}=_
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {variables {machine base leading outer s with
    control:=.statement (.variable [("godLvl",some godExpression)])
    continuation:=.statementList [godCondition] none::continuation}
    [("godLvl",some godExpression)] with elapsed:=base.elapsed}=_
  simp only [variables,god_reference,checked,nameFrames,godExpression,MemberCall.expression,List.nil_append]
  rfl

theorem god_identified (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : PriceLocals.Values) (suffix : Array LexicalEnvironment)
    (control : Control) (continuation : List Frame) :
    Environment.identifier {PriceLocals.start base objects leading outer values suffix with control,continuation} "godLvl"=
      {PriceLocals.start base objects leading outer values suffix with
        control:=.expressionResult (.reference (godReference leading)),continuation} := by
  exact Environment.resolve_declared _ _ _ "godLvl" false (PriceLocals.bindings values) (some outer)
    (PriceLocals.checked_local objects leading outer values suffix) (PriceLocals.has_godLvl values)

attribute [local cbv_eval] god_identified
attribute [local cbv_opaque] PriceLocals.heap PriceLocals.slotIndex
  checkedEnvironment readBinding setBinding
attribute [local cbv_eval] PriceLocals.checked_local PriceLocals.set_godLvl PriceLocals.read_godLvl

private theorem equal_one : Number.equal 0 4607182418800017408=false := by decide +kernel
private theorem equal_two : Number.equal 0 4611686018427387904=false := by decide +kernel
private theorem equal_three : Number.equal 0 4613937818241073152=false := by decide +kernel
attribute [local cbv_opaque] Number.equal
attribute [local cbv_eval] equal_one equal_two equal_three

theorem native_suffix (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (32+fuel) {machine base leading outer s with
      control:=.expressionResult (.value (.boolean false)),continuation:=godFrames leading continuation}=
      Builtins.run fuel {machine base leading outer {s with values:={s.values with godLvl:=.boolean false}} with
        control:=.completion (.normal none),continuation} := by
  rw [Nat.add_comm 32 fuel]
  unfold machine
  cbv

theorem Inputs.native_statement {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs (machine base leading outer s)) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (248+fuel) {machine base leading outer s with control:=.statement (statement 11),continuation}=
      Builtins.run fuel {machine base leading outer h.after with control:=.completion (.normal none),continuation} := by
  rw [show 248+fuel=11+(205+(32+fuel)) by omega,h.native_prefix,h.native_call,native_suffix]
  rfl

end CookieClicker.JavaScript.PriceGod

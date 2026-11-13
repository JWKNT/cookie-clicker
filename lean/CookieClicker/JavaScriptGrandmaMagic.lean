import CookieClicker.JavaScriptGrandmaTiered

namespace CookieClicker.JavaScript.GrandmaMagic
open SourceRead TieredRead GrandmaTiered
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def nameExpression : Expr := .member (.identifier "me") (.identifier "name") false
def statement : Stmt := (GrandmaSource.body.drop 16).headD .empty
def caller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=GrandmaBody.callContinuation old.environments Number.one base.continuation }

structure Inputs (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  game : ObjectId
  me : ObjectId
  function : ObjectId
  scope : EnvId
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject (machine base old state).heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  property : lookupProperty (machine base old state).heap game (JSString.ofString "magicCpS")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (ProductionLeaf.magicClosure scope source)
  name : JSString
  nameEdge : DataEdge (machine base old state) me (JSString.ofString "name") (.string name)
  meValue : state.values.me=.object me
  mult : state.values.mult=.number Number.one
  gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3

def Inputs.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=state.objects.push (HasInvocation.argumentObject (callee:=some input.function)
    (caller base old state) (.string input.name))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (HasInvocation.locals
    (caller base old state) (.string input.name)),some input.scope⟩ }

theorem Inputs.returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (ProductionLeaf.magicReturned (callee:=some input.function)
      (caller base old state) input.scope (.string input.name)).heap=(machine base old input.after).heap :=
  GrandmaAllocation.actual_allocated_heap _ state.objects old.environments old.closureScope
    state.values state.suffix input.scope (.string input.name)
    (HasInvocation.locals (caller base old state) (.string input.name)) (some input.function) rfl

theorem Inputs.after_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (machine base old state).heap (machine base old input.after).heap :=
  HeapExtension.trans (HeapExtension.append_object (machine base old state).heap
    (HasInvocation.argumentObject (callee:=some input.function) (caller base old state) (.string input.name)))
    (HeapExtension.same_objects rfl)

theorem Inputs.native_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (27+fuel) {caller base old state with
      control:=.expression (MemberCall.expression "magicCpS" nameExpression)}=
      Builtins.run fuel {machine base old input.after with
        control:=.expressionResult (.value (.number Number.one)),continuation:=(caller base old state).continuation} := by
  have meRead : Reads (caller base old state) (.identifier "me") (.object input.me) 3 := by
    simpa only [input.meValue,caller,machine,Reads,GrandmaLocals.start] using
      GrandmaBody.local_me {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        state.objects old.environments old.closureScope state.values state.suffix
  have nameRead : Reads (caller base old state) nameExpression (.string input.name) 7 :=
    input.nameEdge.dot _ 3 meRead
  have call := MemberCall.source_magic (caller base old state) nameExpression (.string input.name)
    input.game input.function input.scope input.source input.gameObject input.functionObject
    7 input.gamePresent input.gameKind input.property input.functionPresent input.functionKind input.gameRead nameRead fuel
  rw [call]
  congr 1
  have heap:=input.returned_layout
  simp only [ProductionLeaf.magicReturned,caller,machine,GrandmaLocals.start]
  congr 1

theorem Inputs.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (37+fuel) {machine base old state with control:=.statement statement}=
      Builtins.run fuel {machine base old input.after with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show 37+fuel=6+(27+(4+fuel)) by omega]
  rw [show statement=GrandmaBody.multiplyStatement
    (MemberCall.expression "magicCpS" nameExpression) from GrandmaBody.magic_statement_source]
  have entered := GrandmaBody.multiply_prefix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix Number.one input.mult
    (MemberCall.expression "magicCpS" nameExpression) (27+(4+fuel))
  refine entered.trans ?_
  refine (input.native_call (4+fuel)).trans ?_
  have suffix := GrandmaBody.multiply_suffix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    input.after.objects old.environments old.closureScope input.after.values input.after.suffix Number.one Number.one fuel
  have values:=GrandmaTiered.values_mult_same input.after.values input.mult
  simpa only [GrandmaTiered.one_mul_one,values,machine,caller,GrandmaLocals.start] using suffix

end CookieClicker.JavaScript.GrandmaMagic

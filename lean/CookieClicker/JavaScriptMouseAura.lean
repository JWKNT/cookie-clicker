import CookieClicker.JavaScriptMouseMachine
import CookieClicker.JavaScriptAuraCall

namespace CookieClicker.JavaScript.MouseAura
open SourceRead TieredRead MouseMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def name : JSString := JSString.ofString "Dragon Cursor"
def callExpression : Expr := MemberCall.expression "auraMult" (.literal (.string name))
def fraction : UInt64 := 4587366580439587226
def expression : Expr := .binary .add (.literal (.number Number.one))
  (.binary .multiply callExpression (.literal (.number fraction)))
def statement : Stmt := (MouseSource.body.drop 43).headD .empty

theorem source_statement : statement=MouseBody.multiplyStatement expression := rfl

def arithmeticContinuation (continuation : List Frame) : List Frame :=
  .binaryLeft .multiply (.literal (.number fraction))::
  .binaryRight .add (.number Number.one)::continuation

def caller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=arithmeticContinuation (MouseBody.callContinuation old.environments Number.one base.continuation) }

theorem arithmetic_prefix (base : Machine) (fuel : Nat) :
    Builtins.run (4+fuel) {base with control:=.expression expression}=
      Builtins.run fuel {base with
        control:=.expression callExpression
        continuation:=arithmeticContinuation base.continuation} := by
  rw [Nat.add_comm 4 fuel]
  cbv

structure Inputs (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  world : AuraRead.World (caller base old state)
  function : ObjectId
  scopes : HasEnvironment.Scopes window
  environments : scopes.environments=(machine base old state).heap.environments
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  windowObject : JSObject
  gamePresent : checkedObject (machine base old state).heap world.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  property : lookupProperty (machine base old state).heap world.game (JSString.ofString "auraMult")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (AuraSource.closure scopes.closureScope source)
  windowPresent : checkedObject (machine base old state).heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty (machine base old state).heap window (JSString.ofString "Game")=
    .ok (some (.data (.object world.game) true true false))
  mult : state.values.mult=.number Number.one
  gameRead : Reads (machine base old state) (.identifier "Game") (.object world.game) 3

def Inputs.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=state.objects.push (AuraSource.argumentObject (caller base old state) (.string name) (some input.function))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (AuraLocals.bindings
    (AuraCall.values (caller base old state) name (.number 0))),some input.scopes.closureScope⟩ }

theorem Inputs.returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (AuraCall.returned (caller base old state) input.scopes.closureScope input.world.game name input.function).heap=
      (machine base old input.after).heap := by
  simp only [AuraCall.returned,AuraCall.state,AuraLocals.start,AuraLocals.heap,
    caller,machine,MouseLocals.start,MouseLocals.heap,Inputs.after,Array.append_empty,Array.push_append]

theorem Inputs.after_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (machine base old state).heap (machine base old input.after).heap := by
  rw [←input.returned_layout]
  exact AuraCall.returned_extends (caller base old state) input.scopes.closureScope input.world.game name input.function

theorem Inputs.native_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (161+fuel) {caller base old state with control:=.expression callExpression}=
      Builtins.run fuel {machine base old input.after with
        control:=.expressionResult (.value (.number 0)),continuation:=(caller base old state).continuation} := by
  have calleeGame := AuraCall.callee_game (caller base old state) input.scopes input.world.game
    name input.function (.number 0) input.windowObject input.environments input.windowPresent
    input.windowKind true true false input.windowGame rfl
  have call := AuraCall.source_call (caller base old state) input.scopes.closureScope input.world name
    input.function input.source input.gameObject input.functionObject (by decide)
    input.gamePresent input.gameKind input.property input.functionPresent input.functionKind input.gameRead calleeGame fuel
  change Builtins.run (161+fuel) {caller base old state with
    control:=.expression (MemberCall.expression "auraMult" (.literal (.string name)))}=_
  rw [call]
  congr 1
  have heap:=input.returned_layout
  simp only [AuraCall.returned,caller,machine,MouseLocals.start]
  congr 1

theorem zero_fraction : Number.mul Number.positiveZero fraction=Number.positiveZero := by decide +kernel
theorem add_zero_one : Number.add Number.one Number.positiveZero=Number.one := by decide +kernel

attribute [local cbv_opaque] Number.mul Number.add

theorem arithmetic_suffix (base : Machine) (fuel : Nat) :
    Builtins.run (4+fuel) {base with
      control:=.expressionResult (.value (.number Number.positiveZero))
      continuation:=arithmeticContinuation base.continuation}=
      Builtins.run fuel {base with control:=.expressionResult (.value (.number Number.one))} := by
  rw [Nat.add_comm 4 fuel]
  change Builtins.run fuel {base with
    control:=.expressionResult (.value (.number (Number.add Number.one (Number.mul Number.positiveZero fraction))))}=_
  rw [zero_fraction,add_zero_one]

theorem Inputs.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (179+fuel) {machine base old state with control:=.statement statement}=
      Builtins.run fuel {machine base old input.after with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show 179+fuel=6+(4+(161+(4+(4+fuel)))) by omega,source_statement]
  have entered:=MouseBody.multiply_prefix {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix Number.one input.mult expression
    (4+(161+(4+(4+fuel))))
  refine entered.trans ?_
  refine (arithmetic_prefix {machine base old state with
    continuation:=MouseBody.callContinuation old.environments Number.one base.continuation}
    (161+(4+(4+fuel)))).trans ?_
  refine (input.native_call (4+(4+fuel))).trans ?_
  have tail:=arithmetic_suffix {machine base old input.after with
    continuation:=MouseBody.callContinuation old.environments Number.one base.continuation} (4+fuel)
  refine tail.trans ?_
  have suffix:=MouseBody.multiply_suffix {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    input.after.objects old.environments old.closureScope input.after.values input.after.suffix Number.one Number.one fuel
  have values:=MouseMachine.values_mult_same input.after.values input.mult
  simpa only [MouseMachine.one_mul_one,values,machine,caller,MouseLocals.start] using suffix

end CookieClicker.JavaScript.MouseAura

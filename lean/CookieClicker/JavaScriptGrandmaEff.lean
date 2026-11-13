import CookieClicker.JavaScriptGrandmaTiered
import CookieClicker.JavaScriptAllocatedGameRead

namespace CookieClicker.JavaScript.GrandmaEff
open SourceRead TieredRead GrandmaTiered
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def name : JSString := JSString.ofString "grandmaCps"
def statement : Stmt := (GrandmaSource.body.drop 6).headD .empty
def caller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=GrandmaBody.callContinuation old.environments Number.one base.continuation }

structure Inputs (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  game : ObjectId
  effects : ObjectId
  function : ObjectId
  scopes : HasEnvironment.Scopes window
  environments : scopes.environments=(machine base old state).heap.environments
  source : Option JSString
  gameObject : JSObject
  effectsObject : JSObject
  functionObject : JSObject
  windowObject : JSObject
  gamePresent : checkedObject (machine base old state).heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  property : lookupProperty (machine base old state).heap game (JSString.ofString "eff")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (EffCall.closure scopes.closureScope source)
  effectsProperty : lookupProperty (machine base old state).heap game (JSString.ofString "effs")=
    .ok (some (.data (.object effects) true true true))
  effectsPresent : checkedObject (machine base old state).heap effects=.ok effectsObject
  effectsKind : effectsObject.kind=.ordinary
  missing : lookupProperty (machine base old state).heap effects name=.ok none
  windowPresent : checkedObject (machine base old state).heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty (machine base old state).heap window (JSString.ofString "Game")=
    .ok (some (.data (.object game) true true false))
  mult : state.values.mult=.number Number.one
  gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3

def Inputs.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=state.objects.push (EffCall.argumentObject (caller base old state) name (some input.function))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (EffCall.locals (caller base old state) name),some input.scopes.closureScope⟩ }

theorem Inputs.returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (EffCall.returned (caller base old state) input.scopes.closureScope name (some input.function)).heap=
      (machine base old input.after).heap := by
  simp only [EffCall.returned,EffCall.allocatedHeap,caller,machine,GrandmaLocals.start,GrandmaLocals.heap,
    Inputs.after,Array.push_append]

theorem Inputs.after_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (machine base old state).heap (machine base old input.after).heap := by
  rw [←input.returned_layout]
  exact EffCall.allocated_extends (caller base old state) input.scopes.closureScope name (some input.function)

theorem Inputs.native_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (58+fuel) {caller base old state with
      control:=.expression (MemberCall.expression "eff" (.literal (.string name)))}=
      Builtins.run fuel {machine base old input.after with
        control:=.expressionResult (.value (.number Number.one)),continuation:=(caller base old state).continuation} := by
  have calleeGame := AllocatedGameRead.eff_callee (caller base old state) input.scopes
    input.game name input.function input.windowObject input.environments input.windowPresent
    input.windowKind true true false input.windowGame rfl
  have call := EffCall.source_call (caller base old state) input.scopes.closureScope input.game input.effects
    input.function name input.source input.gameObject input.effectsObject input.functionObject input.gamePresent
    input.gameKind input.property input.functionPresent input.functionKind input.effectsProperty input.effectsPresent
    input.effectsKind input.missing input.gameRead calleeGame fuel
  rw [call]
  congr 1
  have heap:=input.returned_layout
  simp only [EffCall.returned,caller,machine,GrandmaLocals.start]
  congr 1

theorem Inputs.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (68+fuel) {machine base old state with control:=.statement statement}=
      Builtins.run fuel {machine base old input.after with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show 68+fuel=6+(58+(4+fuel)) by omega]
  rw [show statement=GrandmaBody.multiplyStatement
    (MemberCall.expression "eff" (.literal (.string name))) from GrandmaBody.eff_statement_source]
  have entered := GrandmaBody.multiply_prefix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix Number.one input.mult
    (MemberCall.expression "eff" (.literal (.string name))) (58+(4+fuel))
  refine entered.trans ?_
  refine (input.native_call (4+fuel)).trans ?_
  have suffix := GrandmaBody.multiply_suffix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    input.after.objects old.environments old.closureScope input.after.values input.after.suffix Number.one Number.one fuel
  have values:=GrandmaTiered.values_mult_same input.after.values input.mult
  simpa only [GrandmaTiered.one_mul_one,values,machine,caller,GrandmaLocals.start] using suffix

end CookieClicker.JavaScript.GrandmaEff

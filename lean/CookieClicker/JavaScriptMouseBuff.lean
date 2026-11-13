import CookieClicker.JavaScriptMouseMachine
import CookieClicker.JavaScriptHasBuffCall

namespace CookieClicker.JavaScript.MouseBuff
open SourceRead TieredRead MouseMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def name : JSString := JSString.ofString "Cursed finger"
def statement : Stmt := (MouseSource.body.drop 46).headD .empty
def consequent : Stmt := match statement with | .ifThenElse _ consequent _ => consequent | _ => .empty

def caller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=.ifTest consequent none::base.continuation }

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
  property : lookupProperty (machine base old state).heap game (JSString.ofString "hasBuff")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (HasBuffCall.closure scopes.closureScope source)
  effectsProperty : lookupProperty (machine base old state).heap game (JSString.ofString "buffs")=
    .ok (some (.data (.object effects) true true true))
  effectsPresent : checkedObject (machine base old state).heap effects=.ok effectsObject
  effectsKind : effectsObject.kind=.ordinary
  missing : lookupProperty (machine base old state).heap effects name=.ok none
  windowPresent : checkedObject (machine base old state).heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty (machine base old state).heap window (JSString.ofString "Game")=
    .ok (some (.data (.object game) true true false))
  gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3

def Inputs.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=state.objects.push (HasBuffCall.argumentObject (caller base old state) name (some input.function))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (HasBuffCall.locals (caller base old state) name),some input.scopes.closureScope⟩ }

theorem Inputs.returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (HasBuffCall.returned (caller base old state) input.scopes.closureScope name (some input.function)).heap=
      (machine base old input.after).heap := by
  simp only [HasBuffCall.returned,HasBuffCall.allocatedHeap,caller,machine,MouseLocals.start,MouseLocals.heap,
    Inputs.after,Array.push_append]

theorem Inputs.after_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (machine base old state).heap (machine base old input.after).heap := by
  rw [←input.returned_layout]
  exact HasBuffCall.allocated_extends (caller base old state) input.scopes.closureScope name (some input.function)

theorem Inputs.native_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (42+fuel) {caller base old state with
      control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))}=
      Builtins.run fuel {machine base old input.after with
        control:=.expressionResult (.value (.number Number.positiveZero)),continuation:=(caller base old state).continuation} := by
  have calleeGame := HasBuffCall.callee_game (caller base old state) input.scopes
    input.game name input.function input.windowObject input.environments input.windowPresent
    input.windowKind true true false input.windowGame rfl
  have call := HasBuffCall.source_call (caller base old state) input.scopes.closureScope input.game input.effects
    input.function name input.source input.gameObject input.effectsObject input.functionObject input.gamePresent
    input.gameKind input.property input.functionPresent input.functionKind input.effectsProperty input.effectsPresent
    input.effectsKind input.missing input.gameRead calleeGame fuel
  rw [call]
  congr 1
  have heap:=input.returned_layout
  simp only [HasBuffCall.returned,caller,machine,MouseLocals.start]
  congr 1

theorem source_statement : statement=.ifThenElse
    (MemberCall.expression "hasBuff" (.literal (.string name))) consequent none := rfl

theorem Inputs.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (44+fuel) {machine base old state with control:=.statement statement}=
      Builtins.run fuel {machine base old input.after with control:=.completion (.normal none)} := by
  rw [show 44+fuel=1+(42+(1+fuel)) by omega,source_statement,Nat.add_comm 1 (42+(1+fuel))]
  change Builtins.run (42+(1+fuel)) {caller base old state with
    control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))}=_
  rw [input.native_call,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.MouseBuff

import CookieClicker.JavaScriptCursorLeafCalls

namespace CookieClicker.JavaScript.CursorLeafInputs
open CursorTierCall CursorLeafCalls SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure Magic (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  scope : EnvId
  game : ObjectId
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject (machine base old state).heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  property : lookupProperty (machine base old state).heap game (JSString.ofString "magicCpS")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (ProductionLeaf.magicClosure scope source)
  gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3
  mult : state.values.mult=.number Number.one

def Magic.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Magic base old state) : State := afterMagic base old state input.scope input.function

theorem Magic.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Magic base old state) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (31+fuel) {callBase base old state continuation with control:=.statement magicStatement}=
      Builtins.run fuel {callBase base old input.after continuation with
        control:=.completion (.normal (some (.number Number.one)))} :=
  native_magic_statement base old state input.scope input.game input.function input.source
    input.gameObject input.functionObject input.gamePresent input.gameKind input.property
    input.functionPresent input.functionKind input.gameRead input.mult continuation fuel

structure Eff (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  scope : EnvId
  game : ObjectId
  effects : ObjectId
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  effectsObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject (machine base old state).heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  property : lookupProperty (machine base old state).heap game (JSString.ofString "eff")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (EffCall.closure scope source)
  effectsProperty : lookupProperty (machine base old state).heap game (JSString.ofString "effs")=
    .ok (some (.data (.object effects) true true true))
  effectsPresent : checkedObject (machine base old state).heap effects=.ok effectsObject
  effectsKind : effectsObject.kind=.ordinary
  missing : lookupProperty (machine base old state).heap effects effName=.ok none
  callerGame : Reads (machine base old state) (.identifier "Game") (.object game) 3
  calleeGame : Reads (EffCall.started (machine base old state) scope game effName (some function))
    (.identifier "Game") (.object game) 3
  mult : state.values.mult=.number Number.one

def Eff.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Eff base old state) : State := afterEff base old state input.scope input.function

theorem Eff.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Eff base old state) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (68+fuel) {callBase base old state continuation with control:=.statement effStatement}=
      Builtins.run fuel {callBase base old input.after continuation with
        control:=.completion (.normal (some (.number Number.one)))} :=
  native_eff_statement base old state input.scope input.game input.effects input.function input.source
    input.gameObject input.effectsObject input.functionObject input.gamePresent input.gameKind input.property
    input.functionPresent input.functionKind input.effectsProperty input.effectsPresent input.effectsKind
    input.missing input.callerGame input.calleeGame input.mult continuation fuel

end CookieClicker.JavaScript.CursorLeafInputs

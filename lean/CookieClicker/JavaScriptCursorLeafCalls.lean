import CookieClicker.JavaScriptCursorTierCall
import CookieClicker.JavaScriptEffCall

namespace CookieClicker.JavaScript.CursorLeafCalls
open CursorTierCall SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def magicName : JSString := JSString.ofString "Cursor"
def effName : JSString := JSString.ofString "cursorCps"

def callBase (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (continuation : List Frame) : Machine := {machine base old state with continuation}

def afterMagic (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope function : ObjectId) : State := {
  objects:=state.objects.push (HasInvocation.argumentObject (callee:=some function)
    (machine base old state) (.string magicName))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (HasInvocation.locals (machine base old state) (.string magicName)),some scope⟩ }

theorem magic_layout (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope function : ObjectId) (continuation : List Frame) :
    ProductionLeaf.magicReturned (callee:=some function) (callBase base old state continuation)
      scope (.string magicName)=
      {callBase base old (afterMagic base old state scope function) continuation with
        control:=.expressionResult (.value (.number Number.one))} := by
  simp only [ProductionLeaf.magicReturned,callBase,machine,CursorLocals.start,CursorLocals.heap,
    afterMagic,HasInvocation.allocatedHeap,HasInvocation.argumentObject,HasInvocation.localIndex,
    HasInvocation.argumentIndex,HasInvocation.locals,argumentsCalleeProperties,argumentsCalleeUnknown,Array.push_append]

theorem native_magic (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope game function : ObjectId) (source : Option JSString) (gameObject functionObject : JSObject)
    (gamePresent : checkedObject (machine base old state).heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty (machine base old state).heap game (JSString.ofString "magicCpS")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject (machine base old state).heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (ProductionLeaf.magicClosure scope source))
    (gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (21+fuel) {callBase base old state continuation with
      control:=.expression (MemberCall.expression "magicCpS" (.literal (.string magicName)))}=
      Builtins.run fuel {callBase base old (afterMagic base old state scope function) continuation with
        control:=.expressionResult (.value (.number Number.one))} := by
  rw [show 21+fuel=1+20+fuel by omega,
    MemberCall.source_magic (callBase base old state continuation) (.literal (.string magicName))
      (.string magicName) game function scope source gameObject functionObject 1 gamePresent gameKind
      property functionPresent functionKind gameRead (literal _ (.string magicName)),magic_layout]

def afterEff (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope function : ObjectId) : State := {
  objects:=state.objects.push (EffCall.argumentObject (machine base old state) effName (some function))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (EffCall.locals (machine base old state) effName),some scope⟩ }

theorem eff_layout (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope function : ObjectId) (continuation : List Frame) :
    EffCall.returned (callBase base old state continuation) scope effName (some function)=
      {callBase base old (afterEff base old state scope function) continuation with
        control:=.expressionResult (.value (.number Number.one))} := by
  simp only [EffCall.returned,callBase,machine,CursorLocals.start,CursorLocals.heap,
    afterEff,EffCall.allocatedHeap,EffCall.argumentObject,EffCall.localIndex,
    EffCall.argumentIndex,EffCall.locals,argumentsCalleeProperties,argumentsCalleeUnknown,Array.push_append]

theorem native_eff (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope game effects function : ObjectId) (source : Option JSString)
    (gameObject effectsObject functionObject : JSObject)
    (gamePresent : checkedObject (machine base old state).heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty (machine base old state).heap game (JSString.ofString "eff")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject (machine base old state).heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (EffCall.closure scope source))
    (effectsProperty : lookupProperty (machine base old state).heap game (JSString.ofString "effs")=
      .ok (some (.data (.object effects) true true true)))
    (effectsPresent : checkedObject (machine base old state).heap effects=.ok effectsObject)
    (effectsKind : effectsObject.kind=.ordinary)
    (missing : lookupProperty (machine base old state).heap effects effName=.ok none)
    (callerGame : Reads (machine base old state) (.identifier "Game") (.object game) 3)
    (calleeGame : Reads (EffCall.started (machine base old state) scope game effName (some function))
      (.identifier "Game") (.object game) 3)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (58+fuel) {callBase base old state continuation with
      control:=.expression (MemberCall.expression "eff" (.literal (.string effName)))}=
      Builtins.run fuel {callBase base old (afterEff base old state scope function) continuation with
        control:=.expressionResult (.value (.number Number.one))} := by
  rw [EffCall.source_call (callBase base old state continuation) scope game effects function effName source
    gameObject effectsObject functionObject gamePresent gameKind property functionPresent functionKind
    effectsProperty effectsPresent effectsKind missing callerGame calleeGame,eff_layout]

theorem native_magic_statement (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope game function : ObjectId) (source : Option JSString) (gameObject functionObject : JSObject)
    (gamePresent : checkedObject (machine base old state).heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty (machine base old state).heap game (JSString.ofString "magicCpS")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject (machine base old state).heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (ProductionLeaf.magicClosure scope source))
    (gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3)
    (mult : state.values.mult=.number Number.one)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (31+fuel) {callBase base old state continuation with
      control:=.statement magicStatement}=
      Builtins.run fuel {callBase base old (afterMagic base old state scope function) continuation with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show 31+fuel=6+(21+(4+fuel)) by omega]
  rw [show magicStatement=CursorHelpersBody.multiplyStatement
    (MemberCall.expression "magicCpS" (.literal (.string magicName))) from CursorHelpersBody.magic_statement_source]
  have entered:=CursorHelpersBody.multiply_prefix
    {base with globalObject:=window,objectEnvironmentExclusions:=[],continuation}
    state.objects old.environments old.closureScope state.values state.suffix Number.one mult
    (MemberCall.expression "magicCpS" (.literal (.string magicName))) (21+(4+fuel))
  refine entered.trans ?_
  refine (native_magic base old state scope game function source
    gameObject functionObject gamePresent gameKind property functionPresent functionKind
    gameRead
    (CursorHelpersBody.callContinuation old.environments Number.one continuation) (4+fuel)).trans ?_
  have suffix:=CursorHelpersBody.multiply_suffix
    {base with globalObject:=window,objectEnvironmentExclusions:=[],continuation}
    (afterMagic base old state scope function).objects old.environments old.closureScope
    state.values (afterMagic base old state scope function).suffix Number.one Number.one fuel
  simpa only [one_mul_one,values_mult_same state.values mult,callBase,machine,CursorLocals.start,
    afterMagic] using suffix

theorem native_eff_statement (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (scope game effects function : ObjectId) (source : Option JSString)
    (gameObject effectsObject functionObject : JSObject)
    (gamePresent : checkedObject (machine base old state).heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty (machine base old state).heap game (JSString.ofString "eff")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject (machine base old state).heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (EffCall.closure scope source))
    (effectsProperty : lookupProperty (machine base old state).heap game (JSString.ofString "effs")=
      .ok (some (.data (.object effects) true true true)))
    (effectsPresent : checkedObject (machine base old state).heap effects=.ok effectsObject)
    (effectsKind : effectsObject.kind=.ordinary)
    (missing : lookupProperty (machine base old state).heap effects effName=.ok none)
    (callerGame : Reads (machine base old state) (.identifier "Game") (.object game) 3)
    (calleeGame : Reads (EffCall.started (machine base old state) scope game effName (some function))
      (.identifier "Game") (.object game) 3)
    (mult : state.values.mult=.number Number.one)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (68+fuel) {callBase base old state continuation with
      control:=.statement effStatement}=
      Builtins.run fuel {callBase base old (afterEff base old state scope function) continuation with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show 68+fuel=6+(58+(4+fuel)) by omega]
  rw [show effStatement=CursorHelpersBody.multiplyStatement
    (MemberCall.expression "eff" (.literal (.string effName))) from CursorHelpersBody.eff_statement_source]
  have entered:=CursorHelpersBody.multiply_prefix
    {base with globalObject:=window,objectEnvironmentExclusions:=[],continuation}
    state.objects old.environments old.closureScope state.values state.suffix Number.one mult
    (MemberCall.expression "eff" (.literal (.string effName))) (58+(4+fuel))
  refine entered.trans ?_
  refine (native_eff base old state scope game effects function source
    gameObject effectsObject functionObject gamePresent gameKind property functionPresent functionKind
    effectsProperty effectsPresent effectsKind missing callerGame calleeGame
    (CursorHelpersBody.callContinuation old.environments Number.one continuation) (4+fuel)).trans ?_
  have suffix:=CursorHelpersBody.multiply_suffix
    {base with globalObject:=window,objectEnvironmentExclusions:=[],continuation}
    (afterEff base old state scope function).objects old.environments old.closureScope
    state.values (afterEff base old state scope function).suffix Number.one Number.one fuel
  simpa only [one_mul_one,values_mult_same state.values mult,callBase,machine,CursorLocals.start,
    afterEff] using suffix

end CookieClicker.JavaScript.CursorLeafCalls

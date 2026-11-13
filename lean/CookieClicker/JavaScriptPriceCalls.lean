import CookieClicker.JavaScriptPriceStages
import CookieClicker.JavaScriptPriceArithmetic

/-! Actual nested source calls made by modifyBuildingPrice. No returned value
is an input: the source closure and concrete property reads determine it. -/
namespace CookieClicker.JavaScript.PriceCalls
open SourceRead TieredRead PriceStages
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure Buff (base : Machine) (name : JSString) where
  scope : EnvId
  game : ObjectId
  effects : ObjectId
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  effectsObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject base.heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap game (JSString.ofString "hasBuff")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (HasBuffCall.closure scope source)
  effectsProperty : lookupProperty base.heap game (JSString.ofString "buffs")=
    .ok (some (.data (.object effects) true true true))
  effectsPresent : checkedObject base.heap effects=.ok effectsObject
  effectsKind : effectsObject.kind=.ordinary
  missing : lookupProperty base.heap effects name=.ok none
  callerGame : Reads base (.identifier "Game") (.object game) 3
  calleeGame : Reads (HasBuffCall.started base scope game name (some function))
    (.identifier "Game") (.object game) 3

def Buff.after {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Buff (machine base leading outer s) name) : State := {
  objects:=s.objects.push (HasBuffCall.argumentObject (machine base leading outer s) name (some h.function))
  values:=s.values
  suffix:=s.suffix.push ⟨.declarative (HasBuffCall.locals (machine base leading outer s) name),some h.scope⟩ }

theorem Buff.layout {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Buff (machine base leading outer s) name) :
    (HasBuffCall.returned (machine base leading outer s) h.scope name (some h.function)).heap=
      (machine base leading outer h.after).heap := by
  simp only [HasBuffCall.returned,HasBuffCall.allocatedHeap,Buff.after,machine,
    PriceLocals.start,PriceLocals.heap,Array.push_append]

theorem Buff.native_call {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Buff (machine base leading outer s) name)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (42+fuel) {machine base leading outer s with
      control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name))),continuation}=
      Builtins.run fuel {machine base leading outer h.after with
        control:=.expressionResult (.value (.number 0)),continuation} := by
  rw [HasBuffCall.source_call {machine base leading outer s with continuation} h.scope h.game h.effects h.function
    name h.source h.gameObject h.effectsObject h.functionObject h.gamePresent h.gameKind h.method
    h.functionPresent h.functionKind h.effectsProperty h.effectsPresent h.effectsKind h.missing
    h.callerGame h.calleeGame]
  congr 1
  have layout:=h.layout
  simp only [HasBuffCall.returned,machine,PriceLocals.start] at layout ⊢
  congr 1

structure Effect (base : Machine) (name : JSString) where
  scope : EnvId
  game : ObjectId
  effects : ObjectId
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  effectsObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject base.heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap game (JSString.ofString "eff")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (EffCall.closure scope source)
  effectsProperty : lookupProperty base.heap game (JSString.ofString "effs")=
    .ok (some (.data (.object effects) true true true))
  effectsPresent : checkedObject base.heap effects=.ok effectsObject
  effectsKind : effectsObject.kind=.ordinary
  missing : lookupProperty base.heap effects name=.ok none
  callerGame : Reads base (.identifier "Game") (.object game) 3
  calleeGame : Reads (EffCall.started base scope game name (some function))
    (.identifier "Game") (.object game) 3

def Effect.after {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Effect (machine base leading outer s) name) : State := {
  objects:=s.objects.push (EffCall.argumentObject (machine base leading outer s) name (some h.function))
  values:=s.values
  suffix:=s.suffix.push ⟨.declarative (EffCall.locals (machine base leading outer s) name),some h.scope⟩ }

theorem Effect.layout {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Effect (machine base leading outer s) name) :
    (EffCall.returned (machine base leading outer s) h.scope name (some h.function)).heap=
      (machine base leading outer h.after).heap := by
  simp only [EffCall.returned,EffCall.allocatedHeap,Effect.after,machine,
    PriceLocals.start,PriceLocals.heap,Array.push_append]

theorem Effect.native_call {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {name : JSString} (h : Effect (machine base leading outer s) name)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (58+fuel) {machine base leading outer s with
      control:=.expression (MemberCall.expression "eff" (.literal (.string name))),continuation}=
      Builtins.run fuel {machine base leading outer h.after with
        control:=.expressionResult (.value (.number Number.one)),continuation} := by
  rw [EffCall.source_call {machine base leading outer s with continuation} h.scope h.game h.effects h.function
    name h.source h.gameObject h.effectsObject h.functionObject h.gamePresent h.gameKind h.method
    h.functionPresent h.functionKind h.effectsProperty h.effectsPresent h.effectsKind h.missing
    h.callerGame h.calleeGame]
  congr 1
  have layout:=h.layout
  simp only [EffCall.returned,machine,PriceLocals.start] at layout ⊢
  congr 1

structure Aura (base : Machine) (what : JSString) where
  scope : EnvId
  world : AuraRead.World base
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  other : AuraRead.noAura ≠ what
  gamePresent : checkedObject base.heap world.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap world.game (JSString.ofString "auraMult")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (AuraSource.closure scope source)
  callerGame : Reads base (.identifier "Game") (.object world.game) 3
  calleeGame : Reads (AuraCall.state base scope world.game what function (.number 0))
    (.identifier "Game") (.object world.game) 3

def Aura.after {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : Aura (machine base leading outer s) what) : State := {
  objects:=s.objects.push (AuraSource.argumentObject (machine base leading outer s) (.string what) (some h.function))
  values:=s.values
  suffix:=s.suffix.push ⟨.declarative (AuraLocals.bindings (AuraCall.values (machine base leading outer s) what (.number 0))),some h.scope⟩ }

theorem Aura.layout {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : Aura (machine base leading outer s) what) :
    (AuraCall.returned (machine base leading outer s) h.scope h.world.game what h.function).heap=
      (machine base leading outer h.after).heap := by
  simp only [AuraCall.returned,AuraCall.state,AuraLocals.start,AuraLocals.heap,
    Aura.after,machine,PriceLocals.start,PriceLocals.heap,Array.append_empty,Array.push_append]

theorem Aura.native_call {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : Aura (machine base leading outer s) what)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (161+fuel) {machine base leading outer s with
      control:=.expression (MemberCall.expression "auraMult" (.literal (.string what))),continuation}=
      Builtins.run fuel {machine base leading outer h.after with
        control:=.expressionResult (.value (.number 0)),continuation} := by
  rw [AuraCall.source_call {machine base leading outer s with continuation} h.scope (AuraCall.extendWorld h.world (HeapExtension.same_objects rfl))
    what h.function h.source h.gameObject h.functionObject h.other h.gamePresent h.gameKind h.method
    h.functionPresent h.functionKind h.callerGame h.calleeGame]
  congr 1
  have layout:=h.layout
  simp only [AuraCall.returned,machine,PriceLocals.start] at layout ⊢
  congr 1

end CookieClicker.JavaScript.PriceCalls

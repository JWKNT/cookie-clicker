import CookieClicker.JavaScriptPantheonRuinPreservation

/-! A constructed original entry witnesses the diamond/no-aura premises.
It is not a browser capture or a proof of complete game startup. -/
namespace CookieClicker.JavaScript.PantheonRuinFixture
open PantheonRuinOriginal OriginalGamePath SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def property (name : String) (value : Value) : OwnProperty :=
  ⟨JSString.ofString name,.data value true true true⟩
def windowObject : JSObject := {
  properties:=[⟨JSString.ofString "Game",.data (.object 1) true true false⟩] }
def gameObject : JSObject := {
  properties:=[property "hasGod" (.object 2),property "hasAura" (.object 3),
    property "dragonAuras" (.object 8),property "dragonAura" (.number 0),property "dragonAura2" (.number 0)] }
def godFunction : JSObject := {kind:=.function (PantheonSource.closure 1 none)}
def auraFunction : JSObject := {kind:=.function (HasAuraCall.closure 2 none)}
def minigame : JSObject := {properties:=[property "gods" (.object 5),property "slot" (.object 6)]}
def gods : JSObject := {properties:=[property "ruin" (.object 7)]}
def slots : JSObject := {
  kind:=.array
  properties:=[property "0" (.number 4611686018427387904),
    property "1" (.number 13830554455654793216),property "2" (.number 13830554455654793216),
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 3)) true false false⟩] }
def ruinGod : JSObject := {properties:=[property "id" (.number 4611686018427387904)]}
def auras : JSObject := {
  kind:=.array
  properties:=[property "0" (.object 9),⟨JSString.ofString "length",.data (.number Number.one) true false false⟩] }
def emptyAura : JSObject := {properties:=[property "name" (.string AuraRead.noAura)]}
def objects : Array JSObject := #[windowObject,gameObject,godFunction,auraFunction,minigame,gods,slots,ruinGod,auras,emptyAura]
def capturedBindings : List Binding := [{name:="M",value:=.object 4}]
def environments : Array LexicalEnvironment := #[
  ⟨.object 0 false,none⟩,⟨.declarative capturedBindings,some 0⟩,
  ⟨.declarative [],some 0⟩,⟨.declarative [],some 0⟩]
def machine (base : Machine) : Machine := {
  base with
  heap:=⟨objects,environments⟩,context:=⟨3,3,.object 0,false⟩,
  globalObject:=0,objectEnvironmentExclusions:=[] }

private def edge (base : Machine) (id : ObjectId) (object : JSObject) (name : String) (value : Value)
    (read : checkedObject (machine base).heap id=.ok object)
    (kind : object.kind=.ordinary ∨ object.kind=.array)
    (known : object.unresolvedOwnNames=[])
    (own : ownProperty object (JSString.ofString name)=some (.data value true true true)) :
    DataEdge (machine base) id (JSString.ofString name) value := {
  object,present:=read,kind
  property:=by simp [lookupProperty,findProperty,read,known,own,Except.bind,Except.pure,bind,pure] }

def entry (base : Machine) : Entry (machine base) 1 1 2 := {
  world:={
    m:=4,gods:=5,slots:=6,god:=7
    godsRead:=edge base 4 minigame "gods" (.object 5) rfl (Or.inl rfl) rfl rfl
    slotsRead:=edge base 4 minigame "slot" (.object 6) rfl (Or.inl rfl) rfl rfl
    selectedRead:=edge base 5 gods "ruin" (.object 7) rfl (Or.inl rfl) rfl rfl
    first:=edge base 6 slots "0" (.number 4611686018427387904) rfl (Or.inr rfl) rfl rfl
    idRead:=edge base 7 ruinGod "id" (.number 4611686018427387904) rfl (Or.inl rfl) rfl rfl }
  capturedM:={
    target:=1,depth:=0,bindings:=capturedBindings,following:=some 0
    chain:=.done 1,room:=by change 0≤4;decide
    present:=rfl,binding:={name:="M",value:=.object 4},found:=rfl,initialized:=rfl,value:=rfl }
  window:={
    id:=0,object:=windowObject,present:=rfl,kind:=Or.inl rfl
    writable:=true,enumerable:=true,configurable:=false,property:=rfl }
  callerPath:={
    target:=0,depth:=1,chain:=.next 3 0 0 0 [] rfl rfl (.done 0)
    room:=by change 1≤4;decide
    globalRead:=rfl }
  pantheonPath:={
    target:=0,depth:=1,chain:=.next 1 0 0 0 capturedBindings rfl (by decide) (.done 0)
    room:=by change 1≤4;decide
    globalRead:=rfl }
  auraScope:=2
  auraPath:={
    target:=0,depth:=1,chain:=.next 2 0 0 0 [] rfl rfl (.done 0)
    room:=by change 1≤4;decide
    globalRead:=rfl }
  auraWorld:={
    game:=1,auras:=8,emptyAura:=9
    table:=edge base 1 gameObject "dragonAuras" (.object 8) rfl (Or.inl rfl) rfl rfl
    first:=edge base 1 gameObject "dragonAura" (.number 0) rfl (Or.inl rfl) rfl rfl
    second:=edge base 1 gameObject "dragonAura2" (.number 0) rfl (Or.inl rfl) rfl rfl
    zeroEntry:=edge base 8 auras "0" (.object 9) rfl (Or.inr rfl) rfl rfl
    name:=edge base 9 emptyAura "name" (.string AuraRead.noAura) rfl (Or.inl rfl) rfl rfl }
  auraGame:=rfl,source:=none,auraFunction:=3,auraSource:=none
  gameObject:=gameObject,functionObject:=godFunction,auraObject:=auraFunction
  gamePresent:=rfl,gameKind:=rfl,method:=rfl,auraMethod:=rfl
  functionPresent:=rfl,functionKind:=rfl,auraPresent:=rfl,auraKind:=rfl,exclusions:=rfl }

theorem actual_source_call (base : Machine) (fuel : Nat) :
    Builtins.run (192+fuel) {machine base with
      control:=.expression (MemberCall.expression "hasGod" (.literal (.string PantheonRuinCall.ruin)))}=
      Builtins.run fuel (entry base).returned := (entry base).actual_source_call fuel

end CookieClicker.JavaScript.PantheonRuinFixture

import CookieClicker.JavaScriptSaleOrbsPreservation

/-! A symbolic no-aura sale-guard fixture with distinct original caller and
closure environments. This is a constructed heap, not a runtime capture. -/
namespace CookieClicker.JavaScript.SaleOrbsFixture
open SaleOrbsNoAura
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def windowObject : JSObject := {properties:=[⟨JSString.ofString "Game",.data (.object 3) true true false⟩]}
def gameObject : JSObject := {properties:=[
  ⟨JSString.ofString "dragonAuras",.data (.object 4) true true true⟩,
  ⟨JSString.ofString "dragonAura",.data (.number 0) true true true⟩,
  ⟨JSString.ofString "dragonAura2",.data (.number 0) true true true⟩,
  ⟨JSString.ofString "auraMult",.data (.object 7) true true true⟩,
  ⟨JSString.ofString "shimmerTypes",.data (.object 8) true true true⟩]}
def auraTable : JSObject := {properties:=[⟨JSString.ofString "0",.data (.object 5) true true true⟩]}
def emptyAura : JSObject := {properties:=[⟨JSString.ofString "name",.data (.string AuraRead.noAura) true true true⟩]}
def auraFunction : JSObject := {kind:=.function (AuraSource.closure 2 none)}
def shimmerTypes : JSObject := {properties:=[⟨JSString.ofString "golden",.data (.object 9) true true true⟩]}
def golden (count : UInt64) : JSObject := {properties:=[⟨JSString.ofString "n",.data (.number count) true true true⟩]}
def callerBindings : List Binding := [{name:="success",value:=.number Number.one}]
def closureBindings : List Binding := [{name:="retained",value:=.boolean true}]
def environments : Array LexicalEnvironment := #[
  ⟨.object 1 false,none⟩,⟨.declarative callerBindings,some 0⟩,⟨.declarative closureBindings,some 0⟩]
def machine (base : Machine) (count : UInt64) : Machine := {base with
  heap:=⟨#[{},windowObject,{},gameObject,auraTable,emptyAura,{},auraFunction,shimmerTypes,golden count],environments⟩
  context:=⟨1,1,.object 3,false⟩
  globalObject:=1
  objectEnvironmentExclusions:=[]}

def aura (base : Machine) (count : UInt64) : AuraOriginal.Entry (machine base count) := {
  world:={
    game:=3,auras:=4,emptyAura:=5
    table:={object:=gameObject,present:=rfl,kind:=Or.inl rfl,property:=rfl}
    first:={object:=gameObject,present:=rfl,kind:=Or.inl rfl,property:=rfl}
    second:={object:=gameObject,present:=rfl,kind:=Or.inl rfl,property:=rfl}
    zeroEntry:={object:=auraTable,present:=rfl,kind:=Or.inl rfl,property:=rfl}
    name:={object:=emptyAura,present:=rfl,kind:=Or.inl rfl,property:=rfl}}
  scope:=2,function:=7,source:=none,gameObject:=gameObject,functionObject:=auraFunction
  gamePresent:=rfl,gameKind:=rfl,method:=rfl,functionPresent:=rfl,functionKind:=rfl
  window:={id:=1,object:=windowObject,present:=rfl,kind:=Or.inl rfl,writable:=true,enumerable:=true,configurable:=false,property:=rfl}
  callerPath:={
    target:=0,depth:=1,chain:=.next 1 0 0 0 callerBindings rfl rfl (.done 0)
    room:=by change 1≤3;decide
    globalRead:=rfl}
  closurePath:={
    target:=0,depth:=1,chain:=.next 2 0 0 0 closureBindings rfl rfl (.done 0)
    room:=by change 1≤3;decide
    globalRead:=rfl}
  exclusions:=rfl }

def entry (base : Machine) (count : UInt64) : Entry (machine base count) := {
  aura:=aura base count
  successValue:=.number Number.one
  success:={bindings:=callerBindings,outer:=some 0,environment:=rfl,found:=rfl,read:=rfl}
  successful:=rfl
  shimmerTypes:=8,golden:=9,count:=count
  table:={object:=gameObject,present:=rfl,kind:=Or.inl rfl,property:=rfl}
  goldenEdge:={object:=shimmerTypes,present:=rfl,kind:=Or.inl rfl,property:=rfl}
  countEdge:={object:=golden count,present:=rfl,kind:=Or.inl rfl,property:=rfl} }

theorem source_guard (base : Machine) (count : UInt64) (fuel : Nat) :
    Builtins.run ((entry base count).steps+fuel) {machine base count with control:=.statement branch}=
      Builtins.run fuel (entry base count).changed := (entry base count).actual_guard fuel

theorem zero_count_steps (base : Machine) : (entry base 0).steps=197 := by
  change (if Number.lessEqual 0 0 then 197 else 31)=197
  decide +kernel

theorem positive_count_steps (base : Machine) : (entry base Number.one).steps=31 := by
  change (if Number.lessEqual Number.one 0 then 197 else 31)=31
  decide +kernel

end CookieClicker.JavaScript.SaleOrbsFixture

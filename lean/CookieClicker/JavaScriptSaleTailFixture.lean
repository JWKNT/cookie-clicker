import CookieClicker.JavaScriptSaleTailPreservation

/-! A symbolic original heap witnesses both native null and false callback
properties. The surrounding caller continuation is arbitrary. -/
namespace CookieClicker.JavaScript.SaleTailFixture
open SaleTailFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Values where
  price : UInt64
  oldPrice : UInt64
  amount : UInt64
  owned : UInt64

def disabled (isNull : Bool) : Value := if isNull then .null else .boolean false
def windowObject : JSObject := {properties:=[⟨JSString.ofString "Game",.data (.object 3) true true false⟩]}
def gameObject (values : Values) : JSObject := {properties:=[
  ⟨JSString.ofString "recalculateGains",.data (.number 0) true true true⟩,
  ⟨JSString.ofString "BuildingsOwned",.data (.number values.owned) true true true⟩]}
def buildingObject (values : Values) (isNull : Bool) : JSObject := {properties:=[
  ⟨JSString.ofString "price",.data (.number values.oldPrice) true true true⟩,
  ⟨JSString.ofString "sellFunction",.data (disabled isNull) true true true⟩,
  ⟨JSString.ofString "amount",.data (.number values.amount) true true true⟩,
  ⟨JSString.ofString "id",.data (.number 0) true true true⟩]}
def bindings (values : Values) : List Binding := [
  {name:="retained",value:=.boolean true},
  {name:="success",value:=.undefined},
  {name:="price",value:=.number values.price}]
def environments (values : Values) : Array LexicalEnvironment := #[
  ⟨.object 1 false,none⟩,⟨.declarative [],some 0⟩,⟨.declarative (bindings values),some 1⟩]
def machine (base : Machine) (values : Values) (isNull : Bool) : Machine := {base with
  heap:=⟨#[{},windowObject,{},gameObject values,buildingObject values isNull],environments values⟩
  context:=⟨2,2,.object 4,false⟩
  globalObject:=1
  objectEnvironmentExclusions:=[]}

def entry (base : Machine) (values : Values) (isNull : Bool) : Entry (machine base values isNull) := {
  price:=values.price,amount:=values.amount,owned:=values.owned,game:=3
  priceLocal:={bindings:=bindings values,outer:=some 1,environment:=rfl,found:=rfl,read:=rfl}
  priceSlot:={
    id:=4,object:=buildingObject values isNull,oldValue:=.number values.oldPrice,
    enumerable:=true,configurable:=true,present:=rfl,kind:=rfl,own:=rfl,lookup:=rfl}
  receiver:=rfl
  recalculate:={
    id:=3,object:=gameObject values,oldValue:=.number 0,
    enumerable:=true,configurable:=true,present:=rfl,kind:=rfl,own:=rfl,lookup:=rfl}
  recalculateId:=rfl
  buildingsOwned:={
    id:=3,object:=gameObject values,oldValue:=.number values.owned,
    enumerable:=true,configurable:=true,present:=rfl,kind:=rfl,own:=rfl,lookup:=rfl}
  ownedId:=rfl,ownedValue:=rfl
  successSlot:={
    bindings:=bindings values,outer:=some 1,binding:={name:="success",value:=.undefined},
    present:=rfl,found:=rfl,mutable:=rfl}
  gameWindow:={id:=1,object:=windowObject,present:=rfl,kind:=Or.inl rfl,writable:=true,enumerable:=true,configurable:=false,property:=rfl}
  gamePath:={
    target:=0,depth:=2,
    chain:=.next 2 1 0 1 (bindings values) rfl rfl (.next 1 0 0 0 [] rfl rfl (.done 0)),
    room:=by change 2≤3;decide
    globalRead:=rfl}
  exclusions:=rfl
  sellFunctionValue:=disabled isNull
  sellFunction:={object:=buildingObject values isNull,present:=rfl,kind:=Or.inl rfl,property:=rfl}
  noSellFunction:=by cases isNull <;> rfl
  amountEdge:={object:=buildingObject values isNull,present:=rfl,kind:=Or.inl rfl,property:=rfl}
  idEdge:={object:=buildingObject values isNull,present:=rfl,kind:=Or.inl rfl,property:=rfl} }

theorem actual_source_suffix (base : Machine) (values : Values) (isNull : Bool) (previous : Option Value) (fuel : Nat) :
    Builtins.run ((entry base values isNull).rowTicks+60+fuel)
      (SaleTailSource.atPriceWrite (entry base values isNull) previous)=
    Builtins.run fuel (entry base values isNull).changed :=
  SaleTailSource.actual_suffix (entry base values isNull) previous fuel

end CookieClicker.JavaScript.SaleTailFixture

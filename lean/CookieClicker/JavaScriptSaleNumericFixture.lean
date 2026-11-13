import CookieClicker.JavaScriptSaleNumericPreservation

/-! A symbolic original layout inhabits the entry premises. This fixture uses
nonzero object IDs and a two-link lexical path. It is not a runtime capture. -/
namespace CookieClicker.JavaScript.SaleNumericFixture
open SaleNumericFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Values where
  sold : UInt64
  moni : UInt64
  price : UInt64
  cookies : UInt64
  earned : UInt64
  amount : UInt64

def windowObject : JSObject := {properties:=[
  ⟨JSString.ofString "Game",.data (.object 5) true true false⟩,
  ⟨JSString.ofString "Math",.data (.object 2) true false true⟩]}
def mathObject : JSObject := {properties:=[⟨JSString.ofString "max",.data (.object 3) true false true⟩]}
def functionObject : JSObject := {kind:=.builtin ⟨"Math","max"⟩}
def gameObject (values : Values) : JSObject := {properties:=[
  ⟨JSString.ofString "cookies",.data (.number values.cookies) true true true⟩,
  ⟨JSString.ofString "cookiesEarned",.data (.number values.earned) true true true⟩]}
def buildingObject (values : Values) : JSObject := {properties:=[
  ⟨JSString.ofString "amount",.data (.number values.amount) true true true⟩,
  ⟨JSString.ofString "sentry",.data (.boolean true) false false false⟩]}
def bindings (values : Values) : List Binding := [
  {name:="sentry",value:=.boolean true},
  {name:="sold",value:=.number values.sold},
  {name:="price",value:=.number values.price},
  {name:="moni",value:=.number values.moni}]
def inherited : List Binding := [{name:="retained",value:=.boolean false}]
def environments (values : Values) : Array LexicalEnvironment := #[
  ⟨.object 1 false,none⟩,⟨.declarative inherited,some 0⟩,⟨.declarative (bindings values),some 1⟩]
def objects (values : Values) : Array JSObject := #[{},windowObject,mathObject,functionObject,{},gameObject values,buildingObject values]
def machine (base : Machine) (values : Values) : Machine := {base with
  heap:=⟨objects values,environments values⟩
  context:=⟨2,2,.object 6,false⟩
  globalObject:=1
  objectEnvironmentExclusions:=[]}
def counter (values : Values) : CounterObjects.Frame values.cookies values.earned := {
  objects:=objects values,game:=5,window:=1,gameObject:=gameObject values,windowObject:=windowObject
  distinct:=by decide
  gameRead:=rfl,windowRead:=rfl,gameKind:=rfl,windowKind:=Or.inl rfl
  gameKnown:=rfl,windowKnown:=rfl,gameBinding:=rfl,cookiesOwn:=rfl,earnedOwn:=rfl}

def path (values : Values) (name : String) (absent : (bindings values).any (fun b=>b.name==name)=false)
    (inheritedAbsent : inherited.any (fun b=>b.name==name)=false) :
    OriginalNamePath.Path name (environments values) 2 1 := {
  target:=0,depth:=2
  chain:=.next 2 1 0 1 (bindings values) rfl absent (.next 1 0 0 0 inherited rfl inheritedAbsent (.done 0))
  room:=by change 2≤3;decide
  globalRead:=rfl}

def maximum (base : Machine) (values : Values) : BuildingMathRead.Binding (machine base values) "max" := {
  math:=2,function:=3,mathObject:=mathObject,functionObject:=functionObject
  mathRead:=by
    let window : OriginalNamePath.Window (machine base values) "Math" (.object 2) := {
      id:=1,object:=windowObject,present:=rfl,kind:=Or.inl rfl
      writable:=true,enumerable:=false,configurable:=true,property:=rfl}
    exact window.read _ (HeapExtension.refl _) (path values "Math" rfl rfl) rfl
  mathPresent:=rfl,mathKind:=rfl,property:=rfl,functionPresent:=rfl,functionKind:=rfl}

def entry (base : Machine) (values : Values) : Entry (machine base values) := {
  sold:=values.sold,moni:=values.moni,price:=values.price,cookies:=values.cookies,earned:=values.earned,amount:=values.amount
  soldSlot:={bindings:=bindings values,outer:=some 1,binding:={name:="sold",value:=.number values.sold},present:=rfl,found:=rfl,mutable:=rfl}
  moniSlot:={bindings:=bindings values,outer:=some 1,binding:={name:="moni",value:=.number values.moni},present:=rfl,found:=rfl,mutable:=rfl}
  soldRead:={bindings:=bindings values,outer:=some 1,environment:=rfl,found:=rfl,read:=rfl}
  moniRead:={bindings:=bindings values,outer:=some 1,environment:=rfl,found:=rfl,read:=rfl}
  priceRead:={bindings:=bindings values,outer:=some 1,environment:=rfl,found:=rfl,read:=rfl}
  counter:=counter values,objects:=rfl
  gamePath:=path values "Game" rfl rfl,mathPath:=path values "Math" rfl rfl,exclusions:=rfl
  maximum:=maximum base values
  mathWritable:=true,mathEnumerable:=false,mathConfigurable:=true,mathProperty:=rfl
  mathDistinct:=by change 2≠5;decide
  functionDistinct:=by change 3≠5;decide
  building:=6,buildingObject:=buildingObject values,receiver:=rfl
  buildingDistinct:=by change 6≠5;decide
  buildingPresent:=rfl,buildingKind:=rfl,amountOwn:=rfl,amountLookup:=rfl}

theorem actual_source_prefix (base : Machine) (values : Values) (fuel : Nat) :
    Builtins.run (94+fuel) {machine base values with control:=.statement (.block SaleNumericSource.successBody)}=
    Builtins.run fuel (SaleNumericSource.atNextPrice (entry base values)) :=
  SaleNumericSource.actual_block_prefix (entry base values) fuel

end CookieClicker.JavaScript.SaleNumericFixture

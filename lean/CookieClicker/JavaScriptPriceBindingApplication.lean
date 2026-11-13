import CookieClicker.JavaScriptPriceRegistryBinding

namespace CookieClicker.JavaScript.PriceBindingApplication
open PriceRegistry PriceRegistryComplete PriceRegistryBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem modifier_body_after_binding {base : Machine} {name : String}
    (slot : SourceBinding.Slot base name) (value : Value) (different : name≠"M")
    (original : World base) (originalProfile : Profile original) (state : PriceStages.State)
    (extension : HeapExtension.Extends (slot.after value).heap (current (world slot value original) state).heap)
    (building : state.values.building=.object originalProfile.building)
    (price : UInt64) (priceValue : state.values.price=.number price)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1152+fuel) (current (world slot value original) state)=
      Builtins.run fuel {current (world slot value original)
        (construct (world slot value original) (profile slot value different originalProfile) state extension building).final with
        control:=.completion (.return (.number price))} :=
  native_body (world slot value original) (profile slot value different originalProfile) state extension building price priceValue stable fuel

theorem actual_binding_write {base : Machine} {name : String} (slot : SourceBinding.Slot base name) (value : Value) :
    setBinding base.heap base.context.lexicalEnvironment name value base.context.strict=.ok (slot.after value).heap := slot.write value

namespace Fixture

def capturedBindings (old : Value) : List Binding := [
  {name:="M",value:=.object 7},{name:="price",value:=old}]
def callerBindings (old : Value) : List Binding := [{name:="price",value:=old}]
def environments (old : Value) : Array LexicalEnvironment := #[
  ⟨.declarative (capturedBindings old),none⟩,⟨.declarative (callerBindings old),some 0⟩]
def machine (base : Machine) (old : Value) (same : Bool) : Machine := {base with
  heap:={base.heap with environments:=environments old}
  context:={base.context with lexicalEnvironment:=if same then 0 else 1} }

def slot (base : Machine) (old : Value) (same : Bool) : SourceBinding.Slot (machine base old same) "price" := by
  cases same with
  | false => exact {
      bindings:=callerBindings old,outer:=some 0,binding:={name:="price",value:=old}
      present:=rfl,found:=rfl,mutable:=rfl}
  | true => exact {
      bindings:=capturedBindings old,outer:=none,binding:={name:="price",value:=old}
      present:=rfl,found:=rfl,mutable:=rfl}

def capture (old : Value) : PantheonRead.CapturedM (environments old) 0 7 := {
  target:=0,depth:=0,bindings:=capturedBindings old,following:=none,chain:=.done 0
  room:=by change 0≤2;decide
  present:=rfl,binding:={name:="M",value:=.object 7},found:=rfl,initialized:=rfl,value:=rfl }

def retained (base : Machine) (old next : Value) (same : Bool) :
    PantheonRead.CapturedM ((slot base old same).after next).heap.environments 0 7 :=
  CapturedBindingWrite.capturedM (slot base old same) next (by decide) (capture old)

theorem original_m_retained (base : Machine) (old next : Value) (same : Bool) :
    (retained base old next same).target=0 ∧
    (retained base old next same).binding={name:="M",value:=.object 7} :=
  ⟨CapturedBindingWrite.target_preserved _ _ _ _,CapturedBindingWrite.binding_preserved _ _ _ _⟩

theorem actual_m_read_after_write (base : Machine) (old next : Value) (same : Bool)
    (objects : Array JSObject) (values : PantheonLocals.Values) :
    SourceRead.Reads (PantheonLocals.start base objects ((slot base old same).after next).heap.environments 0 values #[])
      (.identifier "M") (.object 7) 3 :=
  (retained base old next same).native_read base objects values

end Fixture
end CookieClicker.JavaScript.PriceBindingApplication

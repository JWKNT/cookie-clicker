import CookieClicker.JavaScriptBuildingStore
import CookieClicker.JavaScriptOriginalNamePath
import CookieClicker.JavaScriptGodzamokLocalTransport

namespace CookieClicker.JavaScript.OriginalPropertyWrite
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {base : Machine} {changed key : JSString}

theorem original_present (slot : BuildingStore.Slot base changed) : base.heap.object? slot.id=some slot.object := by
  have read:=slot.present
  cases found:base.heap.object? slot.id with
  | none => simp [checkedObject,found] at read
  | some object => have same:=slot.present;simpa [checkedObject,found] using same

def otherSlot (written : BuildingStore.Slot base changed) (value : Value)
    (slot : BuildingStore.Slot base key) (different : changed≠key) : BuildingStore.Slot (written.after value) key := {
  id:=slot.id,object:=PropertyFrame.transformed written.id slot.id slot.object changed
    (.data value true written.enumerable written.configurable)
  oldValue:=slot.oldValue,enumerable:=slot.enumerable,configurable:=slot.configurable
  present:=PropertyFrame.transformed_checked _ _ _ _ _ (original_present written) _ _ slot.present
  kind:=by rw [PropertyFrame.transformed_kind];exact slot.kind
  own:=by rw [PropertyFrame.transformed_own _ _ _ _ _ _ different];exact slot.own
  lookup:=(PropertyFrame.lookup_other _ _ _ _ _ _ (original_present written) different _).trans slot.lookup }

def window (written : BuildingStore.Slot base changed) (value : Value)
    {name : String} {old : Value} (frame : OriginalNamePath.Window base name old)
    (different : changed≠JSString.ofString name) : OriginalNamePath.Window (written.after value) name old := {
  id:=frame.id,object:=PropertyFrame.transformed written.id frame.id frame.object changed
    (.data value true written.enumerable written.configurable)
  present:=PropertyFrame.transformed_checked _ _ _ _ _ (original_present written) _ _ frame.present
  kind:=by simpa only [PropertyFrame.transformed_kind] using frame.kind
  writable:=frame.writable,enumerable:=frame.enumerable,configurable:=frame.configurable
  property:=(PropertyFrame.lookup_other _ _ _ _ _ _ (original_present written) different _).trans frame.property }

def edge (written : BuildingStore.Slot base changed) (value : Value)
    {id : ObjectId} {old : Value} (frame : TieredRead.DataEdge base id key old)
    (different : changed≠key) : TieredRead.DataEdge (written.after value) id key old :=
  PropertyFrame.edge frame written.id written.object changed (.data value true written.enumerable written.configurable)
    (original_present written) different

def localFrame (written : BuildingStore.Slot base changed) (value : Value)
    {name : String} {old : Value} (frame : DevastationWrite.Local base name old) :
    DevastationWrite.Local (written.after value) name old := {
  bindings:=frame.bindings,outer:=frame.outer,environment:=frame.environment,found:=frame.found
  read:=by
    have env : checkedEnvironment (written.after value).heap base.context.lexicalEnvironment=
      .ok ⟨.declarative frame.bindings,frame.outer⟩:=frame.environment
    change readBinding (written.after value).heap base.context.lexicalEnvironment name=.ok old
    simpa only [readBinding,env,frame.environment] using frame.read }

def localSlot (written : BuildingStore.Slot base changed) (value : Value)
    {name : String} (slot : SourceBinding.Slot base name) : SourceBinding.Slot (written.after value) name := {
  bindings:=slot.bindings,outer:=slot.outer,binding:=slot.binding,present:=slot.present,found:=slot.found,mutable:=slot.mutable }

theorem lookup_other (written : BuildingStore.Slot base changed) (value : Value)
    (id : ObjectId) (different : changed≠key) :
    lookupProperty (written.after value).heap id key=lookupProperty base.heap id key :=
  PropertyFrame.lookup_other _ _ _ _ _ _ (original_present written) different id

theorem lookup_written (slot : BuildingStore.Slot base key) (value : Value) :
    lookupProperty (slot.after value).heap slot.id key=.ok (some (.data value true slot.enumerable slot.configurable)) := by
  have known : slot.object.unresolvedOwnNames.contains key=false := by
    have original:=slot.lookup
    cases status:slot.object.unresolvedOwnNames.contains key with
    | false => rfl
    | true => simp only [lookupProperty,findProperty,slot.present,Except.bind,bind,status,ite_true] at original
              cases original
  simp only [lookupProperty,findProperty,slot.updated_present,BuildingStore.Slot.updated,
    PropertyFrame.set_unresolved,known,PropertyFrame.own_set,Except.bind,bind,pure,Except.pure,Bool.false_eq_true,ite_false]

end CookieClicker.JavaScript.OriginalPropertyWrite

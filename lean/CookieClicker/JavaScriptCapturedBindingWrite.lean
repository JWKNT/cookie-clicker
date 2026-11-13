import CookieClicker.JavaScriptOriginalNamePath
import CookieClicker.JavaScriptPantheonRead

namespace CookieClicker.JavaScript.CapturedBindingWrite
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def capturedM {base : Machine} {name : String} (slot : SourceBinding.Slot base name) (value : Value)
    (different : name≠"M") {outer : EnvId} {m : ObjectId}
    (capture : PantheonRead.CapturedM base.heap.environments outer m) :
    PantheonRead.CapturedM (slot.after value).heap.environments outer m := by
  have chain := BindingWrite.changed_path base.heap base.context.lexicalEnvironment slot.bindings slot.outer
    name "M" value slot.present outer capture.target capture.depth capture.chain
  have room : capture.depth≤(slot.after value).heap.environments.size := by
    simpa [SourceBinding.Slot.after,BindingWrite.changedHeap] using capture.room
  have checked : checkedEnvironment base.heap capture.target=.ok ⟨.declarative capture.bindings,capture.following⟩ := by
    simp [checkedEnvironment,Heap.environment?,capture.present]
  by_cases same : base.context.lexicalEnvironment=capture.target
  · have pair : slot.bindings=capture.bindings ∧ slot.outer=capture.following := by
      have equal:=slot.present
      rw [same,checked] at equal
      simpa using equal.symm
    have updated : checkedEnvironment (slot.after value).heap capture.target=
        .ok ⟨.declarative (BindingWrite.changedBindings name value capture.bindings),capture.following⟩ := by
      have read:=slot.updated_present value
      simpa only [same,pair.1,pair.2] using read
    exact {
      target:=capture.target,depth:=capture.depth
      bindings:=BindingWrite.changedBindings name value capture.bindings,following:=capture.following
      chain:=chain,room:=room
      present:=BindingWrite.local_read _ _ _ _ updated
      binding:=capture.binding
      found:=by rw [BindingWrite.changed_find_other name "M" value capture.bindings (Ne.symm different)];exact capture.found
      initialized:=capture.initialized,value:=capture.value }
  · exact {
      target:=capture.target,depth:=capture.depth,bindings:=capture.bindings,following:=capture.following
      chain:=chain,room:=room
      present:=BindingWrite.local_read _ _ _ _ ((slot.other_environment value capture.target same).trans checked)
      binding:=capture.binding,found:=capture.found,initialized:=capture.initialized,value:=capture.value }

theorem target_preserved {base : Machine} {name : String} (slot : SourceBinding.Slot base name) (value : Value)
    (different : name≠"M") {outer : EnvId} {m : ObjectId}
    (capture : PantheonRead.CapturedM base.heap.environments outer m) :
    (capturedM slot value different capture).target=capture.target := by
  unfold capturedM
  split <;> rfl

theorem binding_preserved {base : Machine} {name : String} (slot : SourceBinding.Slot base name) (value : Value)
    (different : name≠"M") {outer : EnvId} {m : ObjectId}
    (capture : PantheonRead.CapturedM base.heap.environments outer m) :
    (capturedM slot value different capture).binding=capture.binding := by
  unfold capturedM
  split <;> rfl

end CookieClicker.JavaScript.CapturedBindingWrite

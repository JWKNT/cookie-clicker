import CookieClicker.JavaScriptArc4ConstructorRetained

/-! The instance frame obtained from the actual constructor initializers
and both native key-normalization branches. -/
namespace CookieClicker.JavaScript.Arc4ConstructorInstance
open Arc4Initializers Arc4Initialized Arc4ConstructorSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

theorem s_present (q : Setup) :
    checkedObject (objectHeap q.source (sObjects q)) q.receiver=.ok (sObject q.prototype (sIndex q)) := by
  have bound : q.receiver<(allocatedObjects q).size := by
    simpa [Arc4Initializers.allocatedObjects,Arc4Initializers.iObjects,Arc4Initializers.jObjects] using
      Nat.lt_trans (Arc4Initializers.receiver_bound q) (Nat.lt_succ_self q.objects.size)
  simp [checkedObject,Heap.object?,objectHeap,sObjects,bound]

theorem s_shape (q : Setup) : Arc4Instance.Shape (sObject q.prototype (sIndex q)) 0 0 (sIndex q) := by
  refine ⟨rfl,rfl,?_,?_,?_⟩ <;> rfl

theorem s_missing_g (q : Setup)
    (missing : lookupProperty (objectHeap q.source q.objects) q.receiver (JSString.ofString "g")=.ok none) :
    lookupProperty (objectHeap q.source (sObjects q)) q.receiver (JSString.ofString "g")=.ok none := by
  have first := PropertyFrame.lookup_other (objectHeap q.source q.objects) q.receiver (freshObject q.prototype)
    (JSString.ofString "j") (JSString.ofString "g") (.data (.number 0) true true true) q.fresh (by decide) q.receiver
  have firstRead : lookupProperty (objectHeap q.source (jObjects q)) q.receiver (JSString.ofString "g")=.ok none := by
    exact first.trans missing
  have second := PropertyFrame.lookup_other (objectHeap q.source (jObjects q)) q.receiver (jObject q.prototype)
    (JSString.ofString "i") (JSString.ofString "g") (.data (.number 0) true true true) (j_present q) (by decide) q.receiver
  have secondRead : lookupProperty (objectHeap q.source (iObjects q)) q.receiver (JSString.ofString "g")=.ok none := by
    exact second.trans firstRead
  have ext : HeapExtension.Extends (objectHeap q.source (iObjects q)) (objectHeap q.source (allocatedObjects q)) :=
    HeapExtension.trans (HeapExtension.append_object _ (emptyArray (Arc4Locals.base q.source).arrayPrototype))
      (HeapExtension.same_objects rfl)
  have allocatedRead := HeapExtension.lookup_property ext q.receiver (JSString.ofString "g") none secondRead
  have found := HeapExtension.checked_object ext _ _ (show checkedObject (objectHeap q.source (iObjects q)) q.receiver=.ok (iObject q.prototype) from by
    simp [checkedObject,Heap.object?,objectHeap,Arc4Initializers.iObjects,Arc4Initializers.jObjects,Arc4Initializers.receiver_bound q])
  have third := PropertyFrame.lookup_other (objectHeap q.source (allocatedObjects q)) q.receiver (iObject q.prototype)
    (JSString.ofString "S") (JSString.ofString "g") (.data (.object (sIndex q)) true true true)
    (Arc4Initialized.checked_present found) (by decide) q.receiver
  exact third.trans allocatedRead

def nativeObject (i : Arc4ConstructorSetup.Inputs) := sObject i.prototype (sIndex (setup i))

theorem loop_source (i : Arc4ConstructorSetup.Inputs) : (Arc4ConstructorPrefix.loops i).source=(setup i).source := by
  unfold Arc4ConstructorPrefix.loops
  split <;> rfl

theorem loop_receiver (i : Arc4ConstructorSetup.Inputs) : (Arc4ConstructorPrefix.loops i).receiver=.object (receiver i) := by
  unfold Arc4ConstructorPrefix.loops
  split <;> rfl

theorem loop_array (i : Arc4ConstructorSetup.Inputs) : (Arc4ConstructorPrefix.loops i).array=sIndex (setup i) := by
  unfold Arc4ConstructorPrefix.loops
  split <;> rfl

theorem loop_read (i : Arc4ConstructorSetup.Inputs) :
    checkedObject (Arc4Schedule.objectHeap (Arc4ConstructorPrefix.loops i).source (Arc4ConstructorPrefix.loops i).objects)
      (receiver i)=.ok (nativeObject i) := by
  unfold Arc4ConstructorPrefix.loops
  split
  · exact HeapExtension.checked_object
      (HeapExtension.append_object (objectHeap (setup i).source (sObjects (setup i))) (Arc4EmptyKey.keyObject (setup i)))
      _ _ (s_present (setup i))
  · exact s_present (setup i)

theorem loop_shape (i : Arc4ConstructorSetup.Inputs) :
    Arc4Instance.Shape (nativeObject i) 0 0 (Arc4ConstructorPrefix.loops i).array := by
  rw [loop_array]
  exact s_shape (setup i)

theorem loop_lookup (i : Arc4ConstructorSetup.Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    lookupProperty (Arc4Schedule.objectHeap (Arc4ConstructorPrefix.loops i).source (Arc4ConstructorPrefix.loops i).objects)
      (receiver i) (JSString.ofString "g")=.ok none := by
  have original := s_missing_g (setup i) (fresh_lookup i _ missing)
  unfold Arc4ConstructorPrefix.loops
  split
  · exact HeapExtension.lookup_property
      (HeapExtension.append_object (objectHeap (setup i).source (sObjects (setup i))) (Arc4EmptyKey.keyObject (setup i)))
      _ _ _ original
  · exact original

end CookieClicker.JavaScript.Arc4ConstructorInstance

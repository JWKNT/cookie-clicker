import CookieClicker.JavaScriptArc4GenerateComplete

/-! The actual generator instance fields are ordinary writable data
properties. Native reads and writes retain the stored function and all
unrelated metadata on the same object. -/
namespace CookieClicker.JavaScript.Arc4Instance
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Shape (object : JSObject) (f g : UInt8) (array : ObjectId) : Prop where
  kind : object.kind=.ordinary
  unresolved : object.unresolvedOwnNames=[]
  indexI : ownProperty object (JSString.ofString "i")=some (.data (.number (Number.ofNat f.toNat)) true true true)
  indexJ : ownProperty object (JSString.ofString "j")=some (.data (.number (Number.ofNat g.toNat)) true true true)
  stateS : ownProperty object (JSString.ofString "S")=some (.data (.object array) true true true)

theorem lookup_field (heap : Heap) (id : ObjectId) (object : JSObject) (name : JSString) (value : Value)
    (present : checkedObject heap id=.ok object) (unresolved : object.unresolvedOwnNames=[])
    (own : ownProperty object name=some (.data value true true true)) :
    lookupProperty heap id name=.ok (some (.data value true true true)) := by
  simp [lookupProperty,findProperty,present,unresolved,own,Except.bind,bind,Except.pure,pure]

theorem read_field (machine : Machine) (id : ObjectId) (object : JSObject) (name : JSString) (value : Value)
    (present : checkedObject machine.heap id=.ok object) (unresolved : object.unresolvedOwnNames=[])
    (ordinary : object.kind=.ordinary) (own : ownProperty object name=some (.data value true true true)) :
    readProperty machine (.object id) name=result machine value :=
  SourceRead.read_data_property machine id name value object present (Or.inl ordinary)
    (lookup_field _ _ _ _ _ present unresolved own)

def withI (object : JSObject) (f : UInt8) :=
  setOwnProperty object (JSString.ofString "i") (.data (.number (Number.ofNat f.toNat)) true true true)
def withJ (object : JSObject) (g : UInt8) :=
  setOwnProperty object (JSString.ofString "j") (.data (.number (Number.ofNat g.toNat)) true true true)

theorem shape_i {object : JSObject} {f g : UInt8} {array : ObjectId} (shape : Shape object f g array)
    (changed : UInt8) : Shape (withI object changed) changed g array := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [withI,PropertyFrame.set_kind] using shape.kind
  · simpa [withI,PropertyFrame.set_unresolved] using shape.unresolved
  · exact PropertyFrame.own_set _ _ _
  · rw [withI,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact shape.indexJ
  · rw [withI,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact shape.stateS

theorem shape_j {object : JSObject} {f g : UInt8} {array : ObjectId} (shape : Shape object f g array)
    (changed : UInt8) : Shape (withJ object changed) f changed array := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [withJ,PropertyFrame.set_kind] using shape.kind
  · simpa [withJ,PropertyFrame.set_unresolved] using shape.unresolved
  · rw [withJ,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact shape.indexI
  · exact PropertyFrame.own_set _ _ _
  · rw [withJ,PropertyFrame.own_other _ _ _ _ (by decide)]
    exact shape.stateS

theorem native_write_i (machine : Machine) (id : ObjectId) (object : JSObject) (f g : UInt8) (array : ObjectId)
    (shape : Shape object f g array) (present : checkedObject machine.heap id=.ok object) (changed : UInt8) :
    writeProperty machine (.object id) (JSString.ofString "i") (.number (Number.ofNat changed.toNat)) false=
      result {machine with heap := PropertyFrame.replace machine.heap id (withI object changed)}
        (.number (Number.ofNat changed.toNat)) :=
  PropertyFrame.native_write machine id object (JSString.ofString "i")
    (.number (Number.ofNat f.toNat)) (.number (Number.ofNat changed.toNat)) true true false
    (Arc4Initialized.checked_present present) shape.kind shape.indexI
    (lookup_field _ _ _ _ _ present shape.unresolved shape.indexI)

theorem native_write_j (machine : Machine) (id : ObjectId) (object : JSObject) (f g : UInt8) (array : ObjectId)
    (shape : Shape object f g array) (present : checkedObject machine.heap id=.ok object) (changed : UInt8) :
    writeProperty machine (.object id) (JSString.ofString "j") (.number (Number.ofNat changed.toNat)) false=
      result {machine with heap := PropertyFrame.replace machine.heap id (withJ object changed)}
        (.number (Number.ofNat changed.toNat)) :=
  PropertyFrame.native_write machine id object (JSString.ofString "j")
    (.number (Number.ofNat g.toNat)) (.number (Number.ofNat changed.toNat)) true true false
    (Arc4Initialized.checked_present present) shape.kind shape.indexJ
    (lookup_field _ _ _ _ _ present shape.unresolved shape.indexJ)

end CookieClicker.JavaScript.Arc4Instance

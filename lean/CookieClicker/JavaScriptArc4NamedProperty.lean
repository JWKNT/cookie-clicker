import CookieClicker.JavaScriptArc4GeneratorInstalledFrame

/-! Numeric permutation writes preserve the named generator-field lookup,
including any prototype traversal through a changed array object. -/
namespace CookieClicker.JavaScript.Arc4NamedProperty
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

theorem key_not_g (index : Nat) (small : index<256) : MixkeyIndex.key index≠JSString.ofString "g" := by
  intro same
  have encoded := MixkeyIndex.index_key index small
  rw [same] at encoded
  contradiction

theorem replaced_twice (heap : Heap) (id : ObjectId) (first second : JSObject) :
    PropertyFrame.replace (PropertyFrame.replace heap id first) id second=PropertyFrame.replace heap id second := by
  simp only [PropertyFrame.replace,Array.set!_eq_setIfInBounds]
  by_cases bound : id<heap.objects.size
  · simp [Array.setIfInBounds,bound,Array.set_set]
  · simp [Array.setIfInBounds,bound]

theorem dense_lookup (heap : Heap) (id observed : ObjectId) (object : JSObject)
    (length index : Nat) (value : Value) (small : index<256)
    (present : heap.object? id=some object) :
    lookupProperty (DenseArray.writtenHeap heap id object length index value) observed (JSString.ofString "g")=
      lookupProperty heap observed (JSString.ofString "g") := by
  have first := PropertyFrame.lookup_other heap id object (MixkeyIndex.key index) (JSString.ofString "g")
    (DenseArray.descriptor value) present (key_not_g index small) observed
  by_cases grows : length≤index
  · let changed := setOwnProperty object (MixkeyIndex.key index) (DenseArray.descriptor value)
    have bounded : id<heap.objects.size := (Array.getElem?_eq_some_iff.mp present).1
    have read := PropertyFrame.replaced_read heap id changed bounded
    have second := PropertyFrame.lookup_other (PropertyFrame.replace heap id changed) id changed
      (JSString.ofString "length") (JSString.ofString "g")
      (.data (.number (Number.ofNat (index+1))) true false false) read (by decide) observed
    rw [replaced_twice] at second
    simpa only [DenseArray.writtenHeap,DenseArray.written,grows,↓reduceIte,setArrayLength,PropertyFrame.replace,changed]
      using second.trans first
  · simpa only [DenseArray.writtenHeap,DenseArray.written,grows,↓reduceIte,PropertyFrame.replace] using first

theorem byte_lookup (heap : Heap) (id observed : ObjectId) (object : JSObject)
    (length index : Nat) (byte : UInt8) (small : index<256)
    (present : heap.object? id=some object) :
    lookupProperty (MixkeyArray.writtenHeap heap id object length index byte) observed (JSString.ofString "g")=
      lookupProperty heap observed (JSString.ofString "g") :=
  dense_lookup heap id observed object length index (MixkeyArray.byteValue byte) small present

end CookieClicker.JavaScript.Arc4NamedProperty

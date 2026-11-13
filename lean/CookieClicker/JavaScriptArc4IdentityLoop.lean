import CookieClicker.JavaScriptArc4Identity

/-! Complete execution of the source identity-permutation loop. The final
array is obtained from every native descriptor write, not supplied separately. -/
namespace CookieClicker.JavaScript.Arc4IdentityLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals Arc4Identity

def transport {before after : Heap} {array : ObjectId} (frame : DenseArrayState.Frame before array)
    (same : after.objects = before.objects) : DenseArrayState.Frame after array := {
  object := frame.object, length := frame.length, values := frame.values, shape := frame.shape
  present := by simpa only [checkedObject,Heap.object?,same] using frame.present
  prototype := frame.prototype.transport rfl
    (by simpa only [checkedObject,Heap.object?,same] using frame.prototype.arrayRead)
    (by simpa only [checkedObject,Heap.object?,same] using frame.prototype.rootRead)
  room := by simpa only [same] using frame.room
  bound := by simpa only [same] using frame.bound
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

structure Cursor (i : Inputs) (argument array : Nat) (v : Values) where
  objects : Array JSObject
  index : Nat
  small : index≤256
  frame : DenseArrayState.Frame (heap i objects argument (values v array index)) array
  length : frame.length = index
  initialized : ∀ slot, slot<index → frame.values slot = .number (Number.ofNat slot)

def counterFrame {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v) :
    DenseArrayState.Frame (heap i cursor.objects argument (values v array (cursor.index+1))) array :=
  transport cursor.frame rfl

def written {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v) :=
  cursor.objects.set! array (DenseArray.written cursor.frame.object cursor.frame.length cursor.index (.number (Number.ofNat cursor.index)))

def nextFrame {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (small : cursor.index<256) : DenseArrayState.Frame (heap i (written cursor) argument (values v array (cursor.index+1))) array :=
  DenseArrayState.write (counterFrame cursor) cursor.index (.number (Number.ofNat cursor.index)) small
    (by simpa only [counterFrame,transport] using Nat.le_of_eq cursor.length.symm)

def next {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (small : cursor.index<256) : Cursor i argument array v where
  objects := written cursor
  index := cursor.index+1
  small := by omega
  frame := nextFrame cursor small
  length := by simp [nextFrame,DenseArrayState.write,counterFrame,transport,cursor.length,DenseArray.nextLength]
  initialized := by
    intro slot below
    change DenseArray.nextValues cursor.frame.values cursor.index (.number (Number.ofNat cursor.index)) slot = _
    by_cases same : slot=cursor.index
    · simp [DenseArray.nextValues,same]
    · simp only [DenseArray.nextValues,same,↓reduceIte]
      exact cursor.initialized slot (by omega)


def start {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (previous : Option Value) (tail : List Frame) :=
  guard i cursor.objects argument array cursor.index v previous tail

def afterWrite {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (previous : Option Value) (tail : List Frame) : Machine :=
  result (machine i (written cursor) argument (values v array (cursor.index+1))
    (.putValue ⟨.property (.object array) (MixkeyIndex.key cursor.index),false⟩ (.number (Number.ofNat cursor.index)))
    (.expressionStatement :: .forBody (some test) none body [] previous :: tail)) (.number (Number.ofNat cursor.index))

theorem actual_array_write {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (previous : Option Value) (tail : List Frame) (small : cursor.index<256) :
    Builtins.builtinStep (atWrite i cursor.objects argument array cursor.index v previous tail) = afterWrite cursor previous tail := by
  change {writeProperty (atWrite i cursor.objects argument array cursor.index v previous tail) (.object array)
    (MixkeyIndex.key cursor.index) (.number (Number.ofNat cursor.index)) false with elapsed := (base i).elapsed} = _
  rw [DenseArray.native_write _ array cursor.frame.object cursor.frame.length cursor.frame.values cursor.frame.shape
    (counterFrame cursor).present (counterFrame cursor).prototype cursor.index small (.number (Number.ofNat cursor.index))
    (counterFrame cursor).room (counterFrame cursor).bound false]
  rfl

attribute [local cbv_opaque] base scope localIndex heap written Number.ofNat MixkeyIndex.key Array.size List.length

theorem actual_continue {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (previous : Option Value) (tail : List Frame) (small : cursor.index<256) (fuel : Nat) :
    Builtins.run (2+fuel) (afterWrite cursor previous tail) =
      Builtins.run fuel (start (next cursor small) (some (.number (Number.ofNat cursor.index))) tail) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem actual_iteration {i : Inputs} {argument array : Nat} {v : Values} (cursor : Cursor i argument array v)
    (previous : Option Value) (tail : List Frame) (small : cursor.index<256) (fuel : Nat) :
    Builtins.run (33+fuel) (start cursor previous tail) =
      Builtins.run fuel (start (next cursor small) (some (.number (Number.ofNat cursor.index))) tail) := by
  unfold start
  rw [show 33+fuel=10+(20+(1+(2+fuel))) by omega,actual_guard _ _ _ _ _ _ _ _ cursor.small]
  simp only [small,↓reduceIte]
  rw [actual_body_prefix _ _ _ _ _ _ _ _ small,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) (Builtins.builtinStep (atWrite i cursor.objects argument array cursor.index v previous tail)) = _
  rw [actual_array_write cursor previous tail small,actual_continue cursor previous tail small]
  rfl

end CookieClicker.JavaScript.Arc4IdentityLoop

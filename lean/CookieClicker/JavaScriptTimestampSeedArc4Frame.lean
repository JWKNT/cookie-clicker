import CookieClicker.JavaScriptTimestampSeedArc4Prelude

/-! Actual mixed-key descriptors and retained caller objects supply the
ARC4 constructor frame. The key contents are obtained from the source loop. -/
namespace CookieClicker.JavaScript.TimestampSeedArc4Frame
open TimestampSeedArc4Prelude
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

abbrev mixed (i : Inputs) := TimestampSeedMixing.mixing (mixing i)
abbrev data (i : Inputs) := TimestampMixkeyComplete.arrayData (mixed i)
abbrev codes (i : Inputs) := TimestampMixkeyComplete.toStringInput (mixed i)

theorem extension (i : Inputs) : HeapExtension.Extends (mixing i).globals.base.heap (beforeCall i).heap := by
  have retained := TimestampMixkeyComplete.retained_objects (mixed i)
  refine ⟨Nat.le_trans (TimestampSeedMixing.extension (mixing i)).size retained.size,?_⟩
  intro id object found
  have checked : checkedObject (mixing i).globals.base.heap id=.ok object := by simp [checkedObject,found]
  have next := retained.read id object
    (TimestampSeedMixingFrame.key_different (TimestampSeedMixing.setup (mixing i)) id object checked)
    (HeapExtension.checked_object (TimestampSeedMixing.extension (mixing i)) id object checked)
  exact Arc4Initialized.checked_present next

theorem key_read (i : Inputs) : checkedObject (beforeCall i).heap (key i)=.ok (data i).object :=
  TimestampMixkeyComplete.returned_key (mixed i)

theorem prototypes (source : TimestampMixkeyLoop.Inputs) (count : Nat)
    (state : TimestampMixkeyTraversal.State source) (fits : state.index+count≤(TimestampMixkeyLoop.seed source).size) :
    (TimestampMixkeyTraversal.traverse source count state fits).frame.prototype.arrayId=state.frame.prototype.arrayId ∧
    (TimestampMixkeyTraversal.traverse source count state fits).frame.prototype.rootId=state.frame.prototype.rootId := by
  induction count generalizing state with
  | zero => exact ⟨rfl,rfl⟩
  | succ count induction =>
    simp only [TimestampMixkeyTraversal.traverse]
    exact induction _ _

theorem array_id (i : Inputs) : (data i).prototype.arrayId=(mixing i).arrayPrototype.arrayId := by
  change (TimestampMixkeyTraversal.traverse (TimestampMixkeyComplete.loop (mixed i))
    (TimestampMixkeyLoop.seed (TimestampMixkeyComplete.loop (mixed i))).size
    (TimestampMixkeyTraversal.initial (TimestampMixkeyComplete.loop (mixed i)) (mixed i).frame (mixed i).empty (mixed i).callee)
    _).frame.prototype.arrayId=_
  rw [(prototypes _ _ _ _).1]
  rfl

theorem root_id (i : Inputs) : (data i).prototype.rootId=(mixing i).arrayPrototype.rootId := by
  change (TimestampMixkeyTraversal.traverse (TimestampMixkeyComplete.loop (mixed i))
    (TimestampMixkeyLoop.seed (TimestampMixkeyComplete.loop (mixed i))).size
    (TimestampMixkeyTraversal.initial (TimestampMixkeyComplete.loop (mixed i)) (mixed i).frame (mixed i).empty (mixed i).callee)
    _).frame.prototype.rootId=_
  rw [(prototypes _ _ _ _).2]
  rfl

def keyFrame (i : Inputs) : Arc4Bytes.Frame (beforeCall i).heap (key i) := {
  object := (data i).object, length := (data i).length, bytes := (data i).bytes, shape := (data i).shape
  present := key_read i
  prototype := (data i).prototype.transport rfl
    (HeapExtension.checked_object (MixkeyToString.allocation_extends (codes i)) _ _ (data i).prototype.arrayRead)
    (HeapExtension.checked_object (MixkeyToString.allocation_extends (codes i)) _ _ (data i).prototype.rootRead)
  room := Nat.le_trans (data i).room (MixkeyToString.allocation_extends (codes i)).size
  bound := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present (key_read i))).1
  arrayDifferent := by
    change key i≠(data i).prototype.arrayId
    rw [array_id]
    exact TimestampSeedMixingFrame.key_different (TimestampSeedMixing.setup (mixing i)) _ _ (mixing i).arrayPrototype.arrayRead
  rootDifferent := by
    change key i≠(data i).prototype.rootId
    rw [root_id]
    exact TimestampSeedMixingFrame.key_different (TimestampSeedMixing.setup (mixing i)) _ _ (mixing i).arrayPrototype.rootRead }

theorem array_prototype (i : Inputs) : (beforeCall i).arrayPrototype=some (keyFrame i).prototype.arrayId := by
  change (mixing i).globals.base.arrayPrototype=some (data i).prototype.arrayId
  rw [array_id]
  exact (mixing i).arrayPrototype.parent

end CookieClicker.JavaScript.TimestampSeedArc4Frame

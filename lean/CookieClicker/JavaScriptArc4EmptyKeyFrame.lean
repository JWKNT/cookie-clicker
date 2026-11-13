import CookieClicker.JavaScriptArc4EmptyKey

/-! The normalized one-byte key and retained empty permutation array are
read directly from the source fallback's allocation. -/
namespace CookieClicker.JavaScript.Arc4EmptyKeyFrame
open Arc4Locals Arc4Initializers Arc4Initialized Arc4EmptyKey
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem native_shape (q : Setup) : MixkeyArray.Shape (keyObject q) 1 (fun _ => 0) := by
  refine ⟨rfl,rfl,rfl,rfl,by decide,rfl,?_⟩
  intro index small
  have lengthDifferent := MixkeyArray.length_not_key index small
  by_cases zero : index=0
  · subst index; rfl
  · have zeroDifferent : JSString.ofString "0"≠MixkeyIndex.key index := by
      intro same
      have equals := MixkeyIndex.key_injective (a := 0) (b := index) (by decide) small same
      exact zero equals.symm
    have outside : ¬index<1 := by omega
    simp [keyObject,ownProperty,lengthDifferent,zeroDifferent,outside]

attribute [local irreducible] jObjects iObjects sObjects sIndex allocatedObjects

def extension (q : Setup) : HeapExtension.Extends (objectHeap q.source (sObjects q))
    (objectHeap q.source (objects q)) :=
  HeapExtension.append_object (objectHeap q.source (sObjects q)) (keyObject q)

def keyFrame (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId) :
    Arc4Bytes.Frame (objectHeap q.source (objects q)) (keyIndex q) := {
  object := keyObject q, length := 1, bytes := fun _ => 0, shape := native_shape q
  present := by simp [checkedObject,Heap.object?,objectHeap,objects,keyIndex]
  prototype := q.keyFrame.prototype.transport (matching.trans q.keyFrame.prototype.parent.symm)
    (HeapExtension.checked_object (extension q) _ _
      (retained_checked q _ _ (receiver_array q) q.keyFrame.prototype.arrayRead))
    (HeapExtension.checked_object (extension q) _ _
      (retained_checked q _ _ (receiver_root q) q.keyFrame.prototype.rootRead))
  room := by
    change 2≤(objects q).size
    have bound : 2≤q.objects.size := q.keyFrame.room
    rw [objects,Array.size_push,(sizes q).2.2.2]
    omega
  bound := by simp [objectHeap,objects,keyIndex]
  arrayDifferent := by
    change (sObjects q).size≠q.keyFrame.prototype.arrayId
    have bounded := prototype_bound q _ _ q.keyFrame.prototype.arrayRead
    rw [(sizes q).2.2.2]
    exact Nat.ne_of_gt (Nat.lt_trans bounded (Nat.lt_succ_self _))
  rootDifferent := by
    change (sObjects q).size≠q.keyFrame.prototype.rootId
    have bounded := prototype_bound q _ _ q.keyFrame.prototype.rootRead
    rw [(sizes q).2.2.2]
    exact Nat.ne_of_gt (Nat.lt_trans bounded (Nat.lt_succ_self _)) }

def arrayFrame (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId) :
    DenseArrayState.Frame (heap q.source (objects q) q.argument (values q)) (sIndex q) := by
  have ext : HeapExtension.Extends (objectHeap q.source (sObjects q))
      (heap q.source (objects q) q.argument (values q)) :=
    HeapExtension.trans (extension q)
      (HeapExtension.same_objects (before := objectHeap q.source (objects q))
        (after := heap q.source (objects q) q.argument (values q)) rfl)
  exact {
    object := emptyArray (base q.source).arrayPrototype
    length := 0, values := fun _ => .undefined, shape := empty_shape _
    present := HeapExtension.checked_object ext _ _ (empty_present q)
    prototype := q.keyFrame.prototype.transport (matching.trans q.keyFrame.prototype.parent.symm)
      (HeapExtension.checked_object ext _ _ (retained_checked q _ _ (receiver_array q) q.keyFrame.prototype.arrayRead))
      (HeapExtension.checked_object ext _ _ (retained_checked q _ _ (receiver_root q) q.keyFrame.prototype.rootRead))
    room := by
      change 2≤(objects q).size
      have bound : 2≤q.objects.size := q.keyFrame.room
      rw [objects,Array.size_push,(sizes q).2.2.2]
      omega
    bound := by
      change sIndex q<(objects q).size
      rw [objects,Array.size_push,(sizes q).2.2.1,(sizes q).2.2.2]
      omega
    arrayDifferent := by
      change sIndex q≠q.keyFrame.prototype.arrayId
      rw [(sizes q).2.2.1]
      exact Nat.ne_of_gt (prototype_bound q _ _ q.keyFrame.prototype.arrayRead)
    rootDifferent := by
      change sIndex q≠q.keyFrame.prototype.rootId
      rw [(sizes q).2.2.1]
      exact Nat.ne_of_gt (prototype_bound q _ _ q.keyFrame.prototype.rootRead) }

def normalized (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId) :
    Arc4ConstructorLoops.Inputs := {
  source := q.source, objects := objects q, argument := q.argument, key := keyIndex q, array := sIndex q
  receiver := .object q.receiver
  keyFrame := keyFrame q matching, nonempty := by change 0<1; exact Nat.zero_lt_succ 0
  arrayFrame := Arc4IdentityLoop.transport
    (before := heap q.source (objects q) q.argument (values q))
    (after := heap q.source (objects q) q.argument
      (Arc4ConstructorLoops.locals (keyIndex q) 1 (sIndex q) (.object q.receiver)))
    (arrayFrame q matching) rfl
  empty := rfl
  different := by
    change sIndex q≠(sObjects q).size
    rw [(sizes q).2.2.1,(sizes q).2.2.2]
    exact Nat.ne_of_lt (Nat.lt_succ_self _)
  keyArrayDifferent := (emptyFrame q matching).arrayDifferent
  keyRootDifferent := (emptyFrame q matching).rootDifferent }

theorem loop_start (i : Arc4ConstructorLoops.Inputs) (tail : List Frame) :
    Arc4ConstructorLoops.start i tail=
      Arc4Locals.machine i.source i.objects i.argument
        (Arc4ConstructorLoops.locals i.key i.keyFrame.length i.array i.receiver)
        (.expression Arc4Identity.test)
        (.forTest (some Arc4Identity.test) none Arc4Identity.body [] none ::
          Arc4ConstructorLoops.beforeTail tail) := rfl

theorem final_values (q : Setup) :
    values q=Arc4ConstructorLoops.locals (keyIndex q) 1 (sIndex q) (.object q.receiver) := rfl

theorem same_start (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId)
    (tail : List Frame) :
    Arc4EmptyKey.finish q tail=Arc4ConstructorLoops.start (normalized q matching) tail := by
  rw [loop_start]
  change machineAt q.source (objects q) q.argument q.receiver (values q) _ _=
    Arc4Locals.machine q.source (objects q) q.argument
      (Arc4ConstructorLoops.locals (keyIndex q) 1 (sIndex q) (.object q.receiver)) _ _
  rw [final_values]
  rfl

theorem actual_normalized (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId)
    (empty : q.keyFrame.length=0) (tail : List Frame) (fuel : Nat) :
    Builtins.run (23+fuel) (Arc4Normalize.start q tail)=
      Builtins.run fuel (Arc4ConstructorLoops.start (normalized q matching) tail) := by
  rw [actual_empty q empty,same_start q matching]

end CookieClicker.JavaScript.Arc4EmptyKeyFrame

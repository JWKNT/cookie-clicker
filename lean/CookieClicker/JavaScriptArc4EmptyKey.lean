import CookieClicker.JavaScriptArc4Normalize

/-! The actual source fallback for a zero-length key. Its array literal,
postfix update, local assignment and native descriptor order are retained. -/
namespace CookieClicker.JavaScript.Arc4EmptyKey
open Arc4Locals Arc4Initializers Arc4Initialized
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def keyIndex (q : Setup) := (sObjects q).size
def keyObject (q : Setup) : JSObject := {
  kind := .array, prototype := (base q.source).arrayPrototype
  properties := [⟨JSString.ofString "length",.data (.number Number.one) true false false⟩,
    ⟨JSString.ofString "0",.data (.number 0) true true true⟩] }
def objects (q : Setup) := (sObjects q).push (keyObject q)
def values (q : Setup) : Values := {finalValues q with a := .object (keyIndex q), c := .number Number.one}
def finish (q : Setup) (tail : List Frame) :=
  machineAt q.source (objects q) q.argument q.receiver (values q) (.expression Arc4Identity.test)
    (.forTest (some Arc4Identity.test) none Arc4Identity.body [] none ::
      Arc4ConstructorLoops.beforeTail tail)

theorem checked_pushed (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (object : JSObject) :
    checkedObject (heap i (objects.push object) argument v) objects.size=.ok object := by
  simp [checkedObject,Heap.object?,heap]

theorem replace_pushed (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (before after : JSObject) :
    replaceObject (heap i (objects.push before) argument v) objects.size after=
      .ok (heap i (objects.push after) argument v) := by
  simp [replaceObject,Heap.writeObject,heap,Array.setIfInBounds,Array.set_push]

theorem native_increment_zero : Number.add 0 Number.one=Number.one := rfl

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  sObjects sIndex Heap.allocateObject Array.push checkedObject replaceObject
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_c
  allocate_local number_zero List.length_nil List.length_cons checked_pushed replace_pushed native_increment_zero

theorem actual_empty_tail (q : Setup) (empty : q.keyFrame.length=0) (tail : List Frame) (fuel : Nat) :
    Builtins.run (17+fuel) (Arc4Normalize.atLogical q tail)=Builtins.run fuel (finish q tail) := by
  rw [Nat.add_comm 17 fuel]
  simp only [Arc4Normalize.atLogical,finalValues,gValues,readyValues,empty]
  cbv

theorem actual_empty (q : Setup) (empty : q.keyFrame.length=0) (tail : List Frame) (fuel : Nat) :
    Builtins.run (23+fuel) (Arc4Normalize.start q tail)=Builtins.run fuel (finish q tail) := by
  rw [show 23+fuel=6+(17+fuel) by omega,Arc4Normalize.actual_before_logical,actual_empty_tail q empty]

end CookieClicker.JavaScript.Arc4EmptyKey

import CookieClicker.JavaScriptTimestampMixkeyLoop
import CookieClicker.JavaScriptMixkeyString

/-! The actual charCodeAt(e++) expression retained in the seed mixing loop. -/
namespace CookieClicker.JavaScript.TimestampMixkeyCode
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open TimestampMixkey TimestampMixkeyLoop

def startCode (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value) : Machine := {
  start i objects (.number d) index previous with
  control := .expressionResult (.value (.number d))
  continuation := .binaryLeft .add codeExpr :: .binaryRight .bitAnd (.number (Number.ofNat 255)) ::
    .assignmentRight .assign ⟨.property (.object (key i)) (MixkeyIndex.key (Nat.mod index 256)),false⟩ none ::
    .expressionStatement :: (start i objects (.number d) index previous).continuation }

def codeTail (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value) :=
  .binaryRight .add (.number d) :: (startCode i objects d index previous).continuation.tail

def atMethod (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value) : Machine := {
  startCode i objects d index previous with
  control := .getValue ⟨.property (.timestampText (seed i)) MixkeyString.methodName,false⟩
  continuation := .callResolved (.timestampText (seed i)) [.update .increment (.identifier "e") false] false ::
    codeTail i objects d index previous }

def afterMethod (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) : Machine := {
  atMethod i (objects.push (stringWrapper (base i) (seed i))) d index previous with
  control := .expressionResult (.value (.object method)) }

attribute [local cbv_opaque] base scope seed key libraryBindings libraryOuter heap localIndex bodyHeap
  checkedEnvironment binary toJSString readBinding MixkeyIndex.key Nat.mod Number.ofNat Array.size List.length readProperty
attribute [local cbv_eval] checked_library checked_local environment_size contains_mask read_mask
  local_read_a local_read_b local_read_c local_read_d local_read_e slot_ofNat key_mod

theorem actual_method_prefix (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (fuel : Nat) :
    Builtins.run (8+fuel) (startCode i objects d index previous) =
      Builtins.run fuel (atMethod i objects d index previous) := by
  change Builtins.run (8+fuel) {startCode i objects d index previous with heap := heap i objects (.number d) index} = _
  rw [Nat.add_comm 8 fuel]
  cbv

theorem actual_method_lookup (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (frame : MixkeyString.PrototypeFrame (atMethod i objects d index previous)) :
    Builtins.builtinStep (atMethod i objects d index previous) =
      afterMethod i objects d index previous frame.method := by
  change {readProperty (atMethod i objects d index previous) (.timestampText (seed i)) MixkeyString.methodName
    with elapsed := (base i).elapsed} = _
  rw [MixkeyString.actual_lookup (atMethod i objects d index previous) (seed i) frame]
  rfl

def atInvoke (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) : Machine := {
  start i objects (.number d) (index+1) previous with
  control := .invoke (.object method) (.timestampText (seed i)) [.textIndex (Int.ofNat index)] false
  continuation := codeTail i objects d index previous }

theorem write_index (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    setBinding (heap i objects d index) (localIndex (base i)) "e" (.textIndex (Int.ofNat index + 1)) false =
      .ok (heap i objects d (index+1)) := by
  simpa only [heap,Int.ofNat_eq_natCast,Int.natCast_add,Int.natCast_one] using
    TimestampMixkey.write_e (base i) (scope i) (seed i) (key i) objects d (.timestampText (seed i))
      (.textIndex index) (.textIndex (Int.ofNat index+1))

theorem write_index_succ (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    setBinding (heap i objects d index) (localIndex (base i)) "e" (.textIndex (Int.ofNat (Nat.succ index))) false =
      .ok (heap i objects d (Nat.succ index)) := by
  simpa only [Int.ofNat_eq_natCast,Int.natCast_add,Int.natCast_one,Nat.succ_eq_add_one] using write_index i objects d index

attribute [local cbv_opaque] setBinding
attribute [local cbv_eval] write_index write_index_succ

theorem actual_postincrement (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (fuel : Nat) :
    Builtins.run (9+fuel) {atMethod i objects d index previous with control := .expressionResult (.value (.object method))} =
      Builtins.run fuel (atInvoke i objects d index previous method) := by
  change Builtins.run (9+fuel) {atMethod i objects d index previous with
    heap := heap i objects (.number d) index, control := .expressionResult (.value (.object method))} = _
  rw [Nat.add_comm 9 fuel]
  cbv
  all_goals (try simp only [write_index_succ]; cbv)
  all_goals rfl

def atBuiltin (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) : Machine := {
  atInvoke i objects d index previous method with
  control := .unresolved (.builtin MixkeyString.methodId (.timestampText (seed i)) [.textIndex (Int.ofNat index)] false) }

def afterCode (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) (bound : index < (seed i).size) : Machine :=
  result (atInvoke i objects d index previous method) (.number (Number.ofNat (seed i)[index].toNat))

theorem actual_builtin_request (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (object : JSObject)
    (present : checkedObject (heap i objects (.number d) (index+1)) method = .ok object)
    (kind : object.kind = .builtin MixkeyString.methodId) :
    Builtins.builtinStep (atInvoke i objects d index previous method) = atBuiltin i objects d index previous method := by
  change {invoke (atInvoke i objects d index previous method) (.object method) (.timestampText (seed i))
    [.textIndex (Int.ofNat index)] false with elapsed := (base i).elapsed} = _
  have nativePresent : checkedObject (atInvoke i objects d index previous method).heap method = .ok object := present
  simp only [invoke,nativePresent,kind,checked,fail]
  rfl

theorem actual_builtin_response (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size) :
    Builtins.builtinStep (atBuiltin i objects d index previous method) =
      afterCode i objects d index previous method bound := by
  change Builtins.dispatch (atBuiltin i objects d index previous method) MixkeyString.methodId
    (.timestampText (seed i)) [.textIndex (Int.ofNat index)] false = _
  rw [MixkeyString.native_call (atBuiltin i objects d index previous method) (seed i) index bound]
  rfl

theorem actual_builtin_call (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (object : JSObject)
    (present : checkedObject (heap i objects (.number d) (index+1)) method = .ok object)
    (kind : object.kind = .builtin MixkeyString.methodId) (bound : index < (seed i).size) (fuel : Nat) :
    Builtins.run (2+fuel) (atInvoke i objects d index previous method) =
      Builtins.run fuel (afterCode i objects d index previous method bound) := by
  rw [show 2+fuel=(fuel+1)+1 by omega]
  change Builtins.run (fuel+1) (Builtins.builtinStep (atInvoke i objects d index previous method)) = _
  rw [actual_builtin_request i objects d index previous method object present kind]
  simp only [Builtins.run]
  change (match status (Builtins.builtinStep (atBuiltin i objects d index previous method)) with
    | .unresolved _ | .fault _ => Builtins.builtinStep (atBuiltin i objects d index previous method)
    | _ => Builtins.run fuel (Builtins.builtinStep (atBuiltin i objects d index previous method))) = _
  rw [actual_builtin_response i objects d index previous method bound]
  rfl

end CookieClicker.JavaScript.TimestampMixkeyCode

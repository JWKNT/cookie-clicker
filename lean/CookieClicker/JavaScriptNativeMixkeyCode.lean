import CookieClicker.JavaScriptNativeMixkeyLoop
import CookieClicker.JavaScriptNativeMixkeyString

/-! The actual charCodeAt(e++) expression retained in the seed mixing loop. -/
namespace CookieClicker.JavaScript.NativeMixkeyCode
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open NativeMixkey NativeMixkeyLoop

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
  control := .getValue ⟨.property (.string (seed i).toList) NativeMixkeyString.methodName,false⟩
  continuation := .callResolved (.string (seed i).toList) [.update .increment (.identifier "e") false] false ::
    codeTail i objects d index previous }

def afterMethod (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) : Machine := {
  atMethod i (objects.push (stringWrapper (base i) (seed i))) d index previous with
  control := .expressionResult (.value (.object method)) }

attribute [local cbv_opaque] base scope seed key libraryBindings libraryOuter heap localIndex bodyHeap
  checkedEnvironment binary toJSString readBinding MixkeyIndex.key Nat.mod Number.ofNat Array.size List.length readProperty
attribute [local cbv_eval] checked_library checked_local environment_size contains_mask read_mask
  local_read_a local_read_b local_read_c local_read_d local_read_e key_mod

theorem actual_method_prefix (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (fuel : Nat) :
    Builtins.run (8+fuel) (startCode i objects d index previous) =
      Builtins.run fuel (atMethod i objects d index previous) := by
  change Builtins.run (8+fuel) {startCode i objects d index previous with heap := heap i objects (.number d) index} = _
  rw [Nat.add_comm 8 fuel]
  cbv

theorem actual_method_lookup (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (frame : NativeMixkeyString.PrototypeFrame (atMethod i objects d index previous)) :
    Builtins.builtinStep (atMethod i objects d index previous) =
      afterMethod i objects d index previous frame.method := by
  change {readProperty (atMethod i objects d index previous) (.string (seed i).toList) NativeMixkeyString.methodName
    with elapsed := (base i).elapsed} = _
  rw [NativeMixkeyString.actual_lookup (atMethod i objects d index previous) (seed i) frame]
  rfl

def atInvoke (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) : Machine := {
  start i objects (.number d) (index+1) previous with
  control := .invoke (.object method) (.string (seed i).toList) [.number (Number.ofNat index)] false
  continuation := codeTail i objects d index previous }

theorem write_index (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    setBinding (heap i objects d index) (localIndex (base i)) "e" (.number (Number.ofNat (index+1))) false =
      .ok (heap i objects d (index+1)) :=
    NativeMixkey.write_e (base i) (scope i) (seed i) (key i) objects d (.string (seed i).toList)
      (.number (Number.ofNat index)) (.number (Number.ofNat (index+1)))

theorem write_index_succ (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    setBinding (heap i objects d index) (localIndex (base i)) "e" (.number (Number.ofNat (Nat.succ index))) false =
      .ok (heap i objects d (Nat.succ index)) := write_index i objects d index

attribute [local cbv_opaque] setBinding
attribute [local cbv_eval] write_index write_index_succ

def atIncrement (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) : Machine := {
  atMethod i objects d index previous with
  control := .expressionResult (.value (.number (Number.ofNat index)))
  continuation := .updateRead .increment ⟨.environment (localIndex (base i)) "e",false⟩ false ::
    .callArguments (.object method) (.string (seed i).toList) [] [] false :: codeTail i objects d index previous }

def atCounterWrite (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) : Machine := {
  atIncrement i objects d index previous method with
  control := .putValue ⟨.environment (localIndex (base i)) "e",false⟩ (.number (Number.ofNat (index+1)))
  continuation := .putResult (.number (Number.ofNat index)) ::
    .callArguments (.object method) (.string (seed i).toList) [] [] false :: codeTail i objects d index previous }

theorem actual_before_increment (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (fuel : Nat) :
    Builtins.run (5+fuel) {atMethod i objects d index previous with control := .expressionResult (.value (.object method))} =
      Builtins.run fuel (atIncrement i objects d index previous method) := by
  change Builtins.run (5+fuel) {atMethod i objects d index previous with
    heap := heap i objects (.number d) index, control := .expressionResult (.value (.object method))} = _
  rw [Nat.add_comm 5 fuel]
  cbv

theorem actual_increment (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (small : index<256) :
    Builtins.builtinStep (atIncrement i objects d index previous method)=
      atCounterWrite i objects d index previous method := by
  change {atCounterWrite i objects d index previous method with control := .putValue ⟨.environment (localIndex (base i)) "e",false⟩ (.number (Number.add (Number.ofNat index) (Number.ofNat 1)))} = _
  rw [NaturalArithmetic.native_add_small index 1 (by omega) (by decide)]
  rfl

theorem actual_after_increment (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (fuel : Nat) :
    Builtins.run (3+fuel) (atCounterWrite i objects d index previous method)=
      Builtins.run fuel (atInvoke i objects d index previous method) := by
  change Builtins.run (3+fuel) {atCounterWrite i objects d index previous method with heap := heap i objects (.number d) index} = _
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_postincrement (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (small : index<256) (fuel : Nat) :
    Builtins.run (9+fuel) {atMethod i objects d index previous with control := .expressionResult (.value (.object method))} =
      Builtins.run fuel (atInvoke i objects d index previous method) := by
  rw [show 9+fuel=5+((3+fuel)+1) by omega,actual_before_increment]
  change Builtins.run (3+fuel) (Builtins.builtinStep (atIncrement i objects d index previous method))=_
  rw [actual_increment _ _ _ _ _ _ small,actual_after_increment]

def atBuiltin (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) : Machine := {
  atInvoke i objects d index previous method with
  control := .unresolved (.builtin NativeMixkeyString.methodId (.string (seed i).toList) [.number (Number.ofNat index)] false) }

def afterCode (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat) (previous : Option Value)
    (method : ObjectId) (bound : index < (seed i).size) : Machine :=
  result (atInvoke i objects d index previous method) (.number (Number.ofNat (seed i)[index].toNat))

theorem actual_builtin_request (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (object : JSObject)
    (present : checkedObject (heap i objects (.number d) (index+1)) method = .ok object)
    (kind : object.kind = .builtin NativeMixkeyString.methodId) :
    Builtins.builtinStep (atInvoke i objects d index previous method) = atBuiltin i objects d index previous method := by
  change {invoke (atInvoke i objects d index previous method) (.object method) (.string (seed i).toList)
    [.number (Number.ofNat index)] false with elapsed := (base i).elapsed} = _
  have nativePresent : checkedObject (atInvoke i objects d index previous method).heap method = .ok object := present
  simp only [invoke,nativePresent,kind,checked,fail]
  rfl

theorem actual_builtin_response (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (bound : index < (seed i).size) :
    Builtins.builtinStep (atBuiltin i objects d index previous method) =
      afterCode i objects d index previous method bound := by
  change Builtins.dispatch (atBuiltin i objects d index previous method) NativeMixkeyString.methodId
    (.string (seed i).toList) [.number (Number.ofNat index)] false = _
  rw [NativeMixkeyString.native_call (atBuiltin i objects d index previous method) (seed i) index bound (by have h := i.seedSize; change (seed i).size=256 at h; omega)]
  rfl

theorem actual_builtin_call (i : Inputs) (objects : Array JSObject) (d : UInt64) (index : Nat)
    (previous : Option Value) (method : ObjectId) (object : JSObject)
    (present : checkedObject (heap i objects (.number d) (index+1)) method = .ok object)
    (kind : object.kind = .builtin NativeMixkeyString.methodId) (bound : index < (seed i).size) (fuel : Nat) :
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

end CookieClicker.JavaScript.NativeMixkeyCode

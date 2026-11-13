import CookieClicker.JavaScriptMixkeyArray
import CookieClicker.JavaScriptBuiltins

/-! Native Function.apply over the fully populated, bounded seed-key array. -/
namespace CookieClicker.JavaScript.MixkeyApply
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  base : Machine
  array : ObjectId
  object : JSObject
  length : Nat
  bytes : Nat → UInt8
  shape : MixkeyArray.Shape object length bytes
  present : checkedObject base.heap array = .ok object
  prototype : MixkeyArray.PrototypeFrame base.heap object
  room : 2 ≤ base.heap.objects.size
  function : ObjectId
  functionObject : JSObject
  functionPresent : checkedObject base.heap function = .ok functionObject
  functionKind : functionObject.kind = .builtin ⟨"String","fromCharCode"⟩

def applyId : BuiltinId := ⟨"Function.prototype","apply"⟩
def arguments (i : Inputs) : List Value := [.number Number.positiveZero,.object i.array]
def continuation (i : Inputs) (index : Nat) (done : List Value) : BuiltinContinuation := {
  id := applyId, phase := "element", thisValue := .object i.function,
  arguments := arguments i, locals := .object i.array :: done, indices := [i.length,index] }

def selected (i : Inputs) (index : Nat) : Value := MixkeyArray.byteValue (i.bytes index)
def values (i : Inputs) (start count : Nat) := (List.range' start count).map (selected i)

def invoked (i : Inputs) (done : List Value) : Machine := {
  i.base with control := .invoke (.object i.function) (.number Number.positiveZero) done false }

def atElement (i : Inputs) (index : Nat) (done : List Value) : Machine :=
  result {i.base with continuation := .builtin (continuation i index done) :: i.base.continuation} (selected i index)

def atResponse (i : Inputs) (index : Nat) (done : List Value) : Machine := {
  i.base with control := .resumeBuiltin (continuation i index done) (selected i index) }

theorem next_before (i : Inputs) (index : Nat) (done : List Value) (before : index < i.length) :
    Builtins.applyNext i.base (continuation i index done) = atElement i index done := by
  have small : index < 256 := by have := i.shape.bound; omega
  have read := MixkeyArray.native_read
    {i.base with continuation := .builtin (continuation i index done) :: i.base.continuation}
    i.array i.object i.length i.bytes i.shape i.present i.prototype index small i.room
  simp only [MixkeyArray.readByte,before,↓reduceIte] at read
  simpa [Builtins.applyNext,continuation,applyId,Builtins.suspendGet,Builtins.indexKey,MixkeyIndex.key,
    atElement,selected,show ¬index≥i.length by omega] using read

theorem next_end (i : Inputs) (index : Nat) (done : List Value) (atEnd : index = i.length) :
    Builtins.applyNext i.base (continuation i index done) = invoked i done := by
  simp [Builtins.applyNext,continuation,atEnd,invoked,Builtins.argument,arguments]

theorem consume_element (i : Inputs) (index : Nat) (done : List Value) :
    Builtins.builtinStep (atElement i index done) = atResponse i index done := rfl

theorem resume_element (i : Inputs) (index : Nat) (done : List Value) :
    Builtins.builtinStep (atResponse i index done) =
      Builtins.applyNext i.base (continuation i (index+1) (done ++ [selected i index])) := by
  simp [Builtins.builtinStep,atResponse,Builtins.resume,continuation,applyId]
  rfl

def next (i : Inputs) (index : Nat) (done : List Value) :=
  if index < i.length then atElement i index done else invoked i done

theorem apply_next (i : Inputs) (index : Nat) (done : List Value) (within : index ≤ i.length) :
    Builtins.applyNext i.base (continuation i index done) = next i index done := by
  by_cases before : index < i.length
  · rw [next_before i index done before]; simp [next,before]
  · rw [next_end i index done (by omega)]; simp [next,before]

theorem actual_element (i : Inputs) (index : Nat) (done : List Value) (before : index < i.length) (fuel : Nat) :
    Builtins.run (2+fuel) (next i index done) =
      Builtins.run fuel (next i (index+1) (done ++ [selected i index])) := by
  simp only [next,before,↓reduceIte]
  rw [show 2+fuel=(fuel+1)+1 by omega]
  change Builtins.run fuel (Builtins.builtinStep (Builtins.builtinStep (atElement i index done))) = _
  rw [consume_element,resume_element,apply_next i (index+1) _ (by omega)]
  rfl

theorem actual_elements (i : Inputs) (count index : Nat) (done : List Value) (remaining : index+count=i.length) (fuel : Nat) :
    Builtins.run (2*count+fuel) (next i index done) =
      Builtins.run fuel (invoked i (done ++ values i index count)) := by
  induction count generalizing index done with
  | zero => simp [next,show index=i.length by omega,values]
  | succ count ih =>
    rw [show 2*(count+1)+fuel=2+(2*count+fuel) by omega,actual_element i index done (by omega)]
    rw [ih (index+1) _ (by omega)]
    simp [values,List.range'_succ,List.map_cons,List.append_assoc]

theorem length_conversion (length : Fin 257) :
    Builtins.toLength (.number (Number.ofNat length.val)) = .ok length.val := by
  have small : length.val < 2^52 := by have := length.isLt; omega
  obtain ⟨finite,sign,value⟩ := IndexBits.ofNat_represents length.val small
  have exponent : Number.exponentField (Number.ofNat length.val) ≠ 2047 := by
    simpa only [Number.isFinite,bne_iff_ne,ne_eq] using finite
  have bound : length.val ≤ 2^53-1 := by have := length.isLt; omega
  simp [Builtins.toLength,toNumber,Number.isNaN,Number.isInfinite,exponent,sign,
    IndexBits.truncate_ofNat length.val small,Nat.min_eq_right bound,Except.bind,bind,Except.pure,pure]

theorem native_read_length (i : Inputs) (machine : Machine) (same : machine.heap = i.base.heap) :
    readProperty machine (.object i.array) (JSString.ofString "length") =
      result machine (.number (Number.ofNat i.length)) := by
  have present : checkedObject machine.heap i.array = .ok i.object := same ▸ i.present
  have lookup : lookupProperty machine.heap i.array (JSString.ofString "length") =
      .ok (some (.data (.number (Number.ofNat i.length)) true false false)) := by
    simp [lookupProperty,findProperty,present,i.shape.unresolved,i.shape.size,Except.bind,bind,Except.pure,pure]
  simp [readProperty,toObject,readObjectProperty,checked,present,i.shape.kind,lookup,Except.bind,bind,Except.pure,pure]

def lengthContinuation (i : Inputs) : BuiltinContinuation := {
  id := applyId, phase := "length", thisValue := .object i.function,
  arguments := arguments i, locals := [.object i.array] }

def atLength (i : Inputs) : Machine :=
  result {i.base with continuation := .builtin (lengthContinuation i) :: i.base.continuation}
    (.number (Number.ofNat i.length))

def lengthResponse (i : Inputs) : Machine := {
  i.base with control := .resumeBuiltin (lengthContinuation i) (.number (Number.ofNat i.length)) }

theorem native_apply_call (i : Inputs) :
    Builtins.dispatch i.base applyId (.object i.function) (arguments i) false = atLength i := by
  have read := native_read_length i
    {i.base with continuation := .builtin (lengthContinuation i) :: i.base.continuation} rfl
  simpa [Builtins.dispatch,applyId,Builtins.applyCall,arguments,Builtins.argument,i.functionPresent,
    i.functionKind,checked,Builtins.suspendGet,lengthContinuation,atLength] using read

theorem consume_length (i : Inputs) : Builtins.builtinStep (atLength i) = lengthResponse i := rfl

theorem phase_irrelevant (i : Inputs) (index : Nat) (done : List Value) (phase : String) :
    Builtins.applyNext i.base {continuation i index done with phase := phase} =
      Builtins.applyNext i.base (continuation i index done) := by
  simp [Builtins.applyNext,continuation]

theorem resume_length (i : Inputs) :
    Builtins.builtinStep (lengthResponse i) = next i 0 [] := by
  have conversion := length_conversion ⟨i.length,by have := i.shape.bound; omega⟩
  simp only [Builtins.builtinStep,lengthResponse]
  simp [Builtins.resume,lengthContinuation,applyId,conversion,checked]
  change Builtins.applyNext i.base {continuation i 0 [] with phase := "length"} = _
  rw [phase_irrelevant,apply_next i 0 [] (Nat.zero_le _)]

theorem actual_apply (i : Inputs) (fuel : Nat) :
    Builtins.run (2+2*i.length+fuel) (atLength i) =
      Builtins.run fuel (invoked i (values i 0 i.length)) := by
  rw [show 2+2*i.length+fuel=(2*i.length+fuel+1)+1 by omega]
  change Builtins.run (2*i.length+fuel) (Builtins.builtinStep (Builtins.builtinStep (atLength i))) = _
  rw [consume_length,resume_length,actual_elements i i.length 0 [] (by omega)]
  rfl

theorem byte_conversion (value : UInt8) :
    UInt16.ofNat (Number.toUInt32 (Number.ofNat value.toNat)).toNat = UInt16.ofNat value.toNat := by
  have small : value.toNat < 4294967296 := by have := value.toNat_lt; omega
  rw [IndexBits.toUInt32_ofNat _ small]
  simp [UInt32.toNat_ofNat,Nat.mod_eq_of_lt small]

def text (i : Inputs) := (List.range i.length).map fun index => UInt16.ofNat (i.bytes index).toNat

theorem numbers (i : Inputs) (indices : List Nat) :
    (indices.map (selected i)).mapM toNumber =
      .ok (indices.map fun index => Number.ofNat (i.bytes index).toNat) := by
  induction indices with
  | nil => rfl
  | cons first rest ih => simp [List.mapM_cons,selected,MixkeyArray.byteValue,toNumber,ih]; rfl

theorem native_from_codes (i : Inputs) (machine : Machine) :
    Builtins.dispatch machine ⟨"String","fromCharCode"⟩ (.number Number.positiveZero) (values i 0 i.length) false =
      result machine (.string (text i)) := by
  have call : Builtins.primitiveCall machine ⟨"String","fromCharCode"⟩ (.number Number.positiveZero)
      (values i 0 i.length) false = .ok (.string (text i)) := by
    change (do
      let values ← ((List.range' 0 i.length).map (selected i)).mapM toNumber
      pure (Value.string (values.map fun bits => UInt16.ofNat (Number.toUInt32 bits).toNat)) : Checked Value) = _
    rw [numbers]
    simp only [Except.bind,bind,Except.pure,pure,List.map_map,Function.comp_def,byte_conversion]
    simp only [text,List.range_eq_range']
  simp [Builtins.dispatch,call,checked]

def codesRequest (i : Inputs) : Machine := {
  i.base with control := .unresolved (.builtin ⟨"String","fromCharCode"⟩ (.number Number.positiveZero)
    (values i 0 i.length) false) }

def returned (i : Inputs) := result i.base (.string (text i))

theorem invoke_codes (i : Inputs) :
    Builtins.builtinStep (invoked i (values i 0 i.length)) = codesRequest i := by
  change {invoke (invoked i (values i 0 i.length)) (.object i.function) (.number Number.positiveZero)
    (values i 0 i.length) false with elapsed := i.base.elapsed} = _
  have present : checkedObject (invoked i (values i 0 i.length)).heap i.function = .ok i.functionObject := i.functionPresent
  simp only [invoke,present,i.functionKind,checked,fail]
  rfl

theorem respond_codes (i : Inputs) : Builtins.builtinStep (codesRequest i) = returned i := by
  change Builtins.dispatch (codesRequest i) ⟨"String","fromCharCode"⟩ (.number Number.positiveZero)
    (values i 0 i.length) false = _
  rw [native_from_codes]
  rfl

theorem actual_codes (i : Inputs) (fuel : Nat) :
    Builtins.run (2+fuel) (invoked i (values i 0 i.length)) = Builtins.run fuel (returned i) := by
  rw [show 2+fuel=(fuel+1)+1 by omega]
  change Builtins.run (fuel+1) (Builtins.builtinStep (invoked i (values i 0 i.length))) = _
  rw [invoke_codes]
  simp only [Builtins.run]
  change (match status (Builtins.builtinStep (codesRequest i)) with
    | .unresolved _ | .fault _ => Builtins.builtinStep (codesRequest i)
    | _ => Builtins.run fuel (Builtins.builtinStep (codesRequest i))) = _
  rw [respond_codes]
  cases remaining : i.base.continuation <;> simp [returned,result,status,remaining]

theorem complete_native_apply (i : Inputs) (fuel : Nat) :
    Builtins.run (4+2*i.length+fuel) (atLength i) = Builtins.run fuel (returned i) := by
  rw [show 4+2*i.length+fuel=2+2*i.length+(2+fuel) by omega,actual_apply,actual_codes]

theorem actual_apply_request (i : Inputs)
    (control : i.base.control = .unresolved (.builtin applyId (.object i.function) (arguments i) false)) (fuel : Nat) :
    Builtins.run (5+2*i.length+fuel) i.base = Builtins.run fuel (returned i) := by
  rw [show 5+2*i.length+fuel=(4+2*i.length+fuel)+1 by omega]
  simp only [Builtins.run,status,control]
  have response : Builtins.builtinStep i.base = atLength i := by
    simp only [Builtins.builtinStep,control]
    exact native_apply_call i
  rw [response]
  change Builtins.run (4+2*i.length+fuel) (atLength i) = _
  exact complete_native_apply i fuel

end CookieClicker.JavaScript.MixkeyApply

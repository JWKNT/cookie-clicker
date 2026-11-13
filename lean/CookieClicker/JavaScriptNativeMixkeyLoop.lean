import CookieClicker.JavaScriptNativeMixkey
import CookieClicker.JavaScriptMixkeyArray

/-! The native mixkey loop body, including its actual bindings and array.
All arithmetic on smear and key bytes remains the retained binary64 operations. -/
namespace CookieClicker.JavaScript.NativeMixkeyLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open NativeMixkey

structure Inputs where
  base : Machine
  scope : EnvId
  seed : Array UInt16
  seedSize : seed.size=256
  key : ObjectId
  bindings : List Binding
  outer : Option EnvId
  scopeRead : checkedEnvironment base.heap scope = .ok ⟨.declarative bindings,outer⟩
  maskDeclared : bindings.any (fun b => b.name == "j") = true
  maskRead : readBinding base.heap scope "j" = .ok (.number (Number.ofNat 255))

def base (i : Inputs) := i.base
def scope (i : Inputs) := i.scope
def seed (i : Inputs) := i.seed
def key (i : Inputs) := i.key
def libraryBindings (i : Inputs) := i.bindings
def libraryOuter (i : Inputs) := i.outer

def heap (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :=
  bodyHeap (base i) (scope i) (seed i) (key i) objects d (.string (seed i).toList) (.number (Number.ofNat index))
def start (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) :=
  atBody (base i) (scope i) (seed i) (key i) objects d index previous

theorem scope_bound (i : Inputs) : scope i < (base i).heap.environments.size := by
  have present := i.scopeRead
  unfold checkedEnvironment Heap.environment? at present
  cases h : i.base.heap.environments[i.scope]? with
  | none => simp [h] at present
  | some environment => exact Array.getElem?_eq_some_iff.mp h |>.1

theorem checked_library (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    checkedEnvironment (heap i objects d index) (scope i) =
      .ok ⟨.declarative (libraryBindings i),libraryOuter i⟩ := by
  have different : i.scope ≠ i.base.heap.environments.size := Nat.ne_of_lt (scope_bound i)
  simpa only [heap,bodyHeap,checkedEnvironment,Heap.environment?,Array.getElem?_push,
    if_neg different,base,scope,libraryBindings,libraryOuter] using i.scopeRead

theorem contains_mask (i : Inputs) : (libraryBindings i).any (fun b => b.name == "j") = true := i.maskDeclared

theorem read_mask (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    readBinding (heap i objects d index) (scope i) "j" = .ok (.number (Number.ofNat 255)) := by
  have original := i.maskRead
  unfold readBinding at original ⊢
  rw [i.scopeRead] at original
  rw [checked_library]
  exact original

theorem checked_local (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    checkedEnvironment (heap i objects d index) (localIndex (base i)) =
      .ok ⟨.declarative (scopeLocals (base i) (seed i) (key i) d (.string (seed i).toList) (.number (Number.ofNat index))),some (scope i)⟩ :=
  checked_body_local _ _ _ _ _ _ _ _

theorem environment_size (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    (heap i objects d index).environments.size = (base i).heap.environments.size+1 := by simp [heap,bodyHeap]

def codeExpr : Expr := .call (.member (.identifier "c") (.identifier "charCodeAt") false)
  [.update .increment (.identifier "e") false]

def atOldByte (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) (previous : Option Value) : Machine := {
  start i objects d index previous with
  control := .getValue ⟨.property (.object (key i)) (MixkeyIndex.key (Nat.mod index 256)),false⟩
  continuation := .binaryRight .multiply (.number (Number.ofNat 19)) ::
    .assignmentRight .bitXor ⟨.environment (localIndex (base i)) "d",false⟩ (some d) ::
    .binaryLeft .add codeExpr :: .binaryRight .bitAnd (.number (Number.ofNat 255)) ::
    .assignmentRight .assign ⟨.property (.object (key i)) (MixkeyIndex.key (Nat.mod index 256)),false⟩ none ::
    .expressionStatement :: (start i objects d index previous).continuation }

attribute [local cbv_opaque] base scope seed key libraryBindings libraryOuter heap localIndex bodyHeap
  checkedEnvironment binary toJSString readBinding MixkeyIndex.key Nat.mod Number.ofNat Array.size List.length readProperty
attribute [local cbv_eval] checked_library checked_local environment_size contains_mask read_mask
  MixkeyIndex.source_slot MixkeyIndex.source_key

theorem local_read_a (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    readBinding (heap i objects d index) (localIndex (base i)) "a" = .ok (.string (seed i).toList) := by
  simp [readBinding,checked_local,scopeLocals,initialLocals,Except.bind,bind,Except.pure,pure]

theorem local_read_b (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    readBinding (heap i objects d index) (localIndex (base i)) "b" = .ok (.object (key i)) := by
  simp [readBinding,checked_local,scopeLocals,initialLocals,Except.bind,bind,Except.pure,pure]

theorem local_read_c (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    readBinding (heap i objects d index) (localIndex (base i)) "c" = .ok (.string (seed i).toList) := by
  simp [readBinding,checked_local,scopeLocals,initialLocals,Except.bind,bind,Except.pure,pure]

theorem local_read_d (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    readBinding (heap i objects d index) (localIndex (base i)) "d" = .ok d := by
  simp [readBinding,checked_local,scopeLocals,initialLocals,Except.bind,bind,Except.pure,pure]

theorem local_read_e (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat) :
    readBinding (heap i objects d index) (localIndex (base i)) "e" = .ok (.number (Number.ofNat index)) := by
  simp [readBinding,checked_local,scopeLocals,initialLocals,Except.bind,bind,Except.pure,pure]

theorem slot_ofNat (index : Nat) (small : index < 256) :
    binary .bitAnd (.number (Number.ofNat 255)) (.number (Number.ofNat index)) =
      .ok (.number (Number.ofNat (Nat.mod index 256))) := by
  change (Except.ok (.number (Number.bitAnd (Number.ofNat 255) (Number.ofNat index))) : Checked Value)=_
  rw [IndexBits.native_low_byte index (by omega)]
  rfl

theorem key_mod (index : Nat) :
    toJSString (.number (Number.ofNat (Nat.mod index 256))) =
      .ok (MixkeyIndex.key (Nat.mod index 256)) := MixkeyIndex.source_key index

attribute [local cbv_eval] local_read_a local_read_b local_read_c local_read_d local_read_e key_mod

theorem actual_before_old_byte (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat)
    (previous : Option Value) (small : index<256) (fuel : Nat) :
    Builtins.run (48+fuel) (start i objects d index previous) =
      Builtins.run fuel (atOldByte i objects d index previous) := by
  change Builtins.run (48+fuel) {start i objects d index previous with heap := heap i objects d index} = _
  rw [Nat.add_comm 48 fuel]
  cbv
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals (try simp only [environment_size,slot_ofNat index small,key_mod]; cbv)
  all_goals rw [slot_ofNat index small]
  all_goals cbv

def smearValue : Option UInt64 → Value
  | none => .undefined
  | some bits => .number bits

def oldBits (length : Nat) (bytes : Nat → UInt8) (index : Nat) : UInt64 :=
  if Nat.mod index 256 < length then Number.ofNat (bytes (Nat.mod index 256)).toNat else Number.nan

def multiplied (length : Nat) (bytes : Nat → UInt8) (index : Nat) : UInt64 :=
  Number.mul (Number.ofNat 19) (oldBits length bytes index)

def nextSmear (smear : Option UInt64) (length : Nat) (bytes : Nat → UInt8) (index : Nat) : UInt64 :=
  Number.bitXor (smear.getD Number.nan) (multiplied length bytes index)

def afterOldByte (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat)
    (previous : Option Value) (length : Nat) (bytes : Nat → UInt8) : Machine :=
  result (atOldByte i objects d index previous) (MixkeyArray.readByte length bytes (Nat.mod index 256))

theorem actual_read_old_byte (i : Inputs) (objects : Array JSObject) (d : Value) (index : Nat)
    (previous : Option Value) (object : JSObject) (length : Nat) (bytes : Nat → UInt8)
    (shape : MixkeyArray.Shape object length bytes)
    (present : checkedObject (heap i objects d index) (key i) = .ok object)
    (prototype : MixkeyArray.PrototypeFrame (heap i objects d index) object)
    (room : 2 ≤ objects.size) :
    Builtins.builtinStep (atOldByte i objects d index previous) =
      afterOldByte i objects d index previous length bytes := by
  change {readProperty (atOldByte i objects d index previous) (.object (key i)) (MixkeyIndex.key (Nat.mod index 256))
    with elapsed := (base i).elapsed} = _
  rw [MixkeyArray.native_read _ _ object length bytes shape present prototype (Nat.mod index 256)
    (show Nat.mod index 256 < 256 from Nat.mod_lt index (by decide)) room]
  rfl

theorem native_multiply (length : Nat) (bytes : Nat → UInt8) (index : Nat) :
    binary .multiply (.number 4626041242239631360) (MixkeyArray.readByte length bytes (Nat.mod index 256)) =
      .ok (.number (multiplied length bytes index)) := by
  change binary .multiply (.number 4626041242239631360)
    (if Nat.mod index 256 < length then .number (Number.ofNat (bytes (Nat.mod index 256)).toNat) else .undefined) =
    .ok (.number (Number.mul (Number.ofNat 19)
      (if Nat.mod index 256 < length then Number.ofNat (bytes (Nat.mod index 256)).toNat else Number.nan)))
  by_cases occupied : Nat.mod index 256 < length <;>
    simp only [occupied,↓reduceIte,binary,numericBinary,toNumber,Except.bind,bind,Except.pure,pure]
  all_goals rfl

theorem native_smear (smear : Option UInt64) (length : Nat) (bytes : Nat → UInt8) (index : Nat) :
    binary .bitXor (smearValue smear) (.number (multiplied length bytes index)) =
      .ok (.number (nextSmear smear length bytes index)) := by
  cases smear <;> simp [binary,numericBinary,smearValue,nextSmear,toNumber,Except.bind,bind,Except.pure,pure]

theorem write_d (i : Inputs) (objects : Array JSObject) (d value : Value) (index : Nat) :
    setBinding (heap i objects d index) (localIndex (base i)) "d" value false =
      .ok (heap i objects value index) := by
  simp [heap,bodyHeap,setBinding,checkedEnvironment,Heap.environment?,scopeLocals,initialLocals,
    localIndex,replaceEnvironment,Heap.writeEnvironment,Array.setIfInBounds,Array.set_push,
    Except.bind,bind,Except.pure,pure]

def afterSmear (i : Inputs) (objects : Array JSObject) (smear : Option UInt64) (index : Nat)
    (previous : Option Value) (length : Nat) (bytes : Nat → UInt8) : Machine := {
  start i objects (.number (nextSmear smear length bytes index)) index previous with
  control := .expressionResult (.value (.number (nextSmear smear length bytes index)))
  continuation := .binaryLeft .add codeExpr :: .binaryRight .bitAnd (.number (Number.ofNat 255)) ::
    .assignmentRight .assign ⟨.property (.object (key i)) (MixkeyIndex.key (Nat.mod index 256)),false⟩ none ::
    .expressionStatement :: (start i objects (.number (nextSmear smear length bytes index)) index previous).continuation }

theorem multiply_numbers (a b : UInt64) : binary .multiply (.number a) (.number b) =
    .ok (.number (Number.mul a b)) := rfl

theorem multiply_undefined (a : UInt64) : binary .multiply (.number a) .undefined =
    .ok (.number (Number.mul a Number.nan)) := rfl

theorem xor_numbers (a b : UInt64) : binary .bitXor (.number a) (.number b) =
    .ok (.number (Number.bitXor a b)) := rfl

theorem xor_undefined (b : UInt64) : binary .bitXor .undefined (.number b) =
    .ok (.number (Number.bitXor Number.nan b)) := rfl

attribute [local cbv_opaque] multiplied nextSmear MixkeyArray.readByte setBinding Number.mul Number.bitXor
attribute [local cbv_eval] native_multiply native_smear write_d multiply_numbers multiply_undefined xor_numbers xor_undefined

theorem actual_smear (i : Inputs) (objects : Array JSObject) (smear : Option UInt64) (index : Nat)
    (previous : Option Value) (length : Nat) (bytes : Nat → UInt8) (fuel : Nat) :
    Builtins.run (4+fuel) (afterOldByte i objects (smearValue smear) index previous length bytes) =
      Builtins.run fuel (afterSmear i objects smear index previous length bytes) := by
  change Builtins.run (4+fuel) {afterOldByte i objects (smearValue smear) index previous length bytes with
    heap := heap i objects (smearValue smear) index} = _
  rw [Nat.add_comm 4 fuel]
  by_cases occupied : Nat.mod index 256 < length
  · have read : MixkeyArray.readByte length bytes (Nat.mod index 256) =
        .number (Number.ofNat (bytes (Nat.mod index 256)).toNat) := by simp [MixkeyArray.readByte,occupied,MixkeyArray.byteValue]
    cases smear <;> cbv
    all_goals (simp only [read]; cbv)
    all_goals simp only [heap,nextSmear,multiplied,oldBits,occupied,↓reduceIte,Option.getD]
    all_goals rfl
  · have read : MixkeyArray.readByte length bytes (Nat.mod index 256) = .undefined := by simp [MixkeyArray.readByte,occupied]
    cases smear <;> cbv
    all_goals (simp only [read]; cbv)
    all_goals simp only [heap,nextSmear,multiplied,oldBits,occupied,↓reduceIte,Option.getD]
    all_goals rfl

end CookieClicker.JavaScript.NativeMixkeyLoop

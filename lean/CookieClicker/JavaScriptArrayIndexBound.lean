import CookieClicker.JavaScriptDenseArrayState

/-! A native array has no indexed own property outside its stored length.
These source-heap conditions are preserved by each represented queue write. -/
namespace CookieClicker.JavaScript.ArrayIndexBound
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def Holds (object : JSObject) (length : Nat) : Prop :=
  ∀ property ∈ object.properties, ∀ index, arrayIndex property.name = some index → index < length

theorem canonical {name : JSString} {index : Nat} (parsed : arrayIndex name = some index) : name = MixkeyIndex.key index := by
  unfold arrayIndex at parsed
  cases digits : name.foldlM (fun current unit =>
    if 48 ≤ unit.toNat && unit.toNat ≤ 57 then some (10*current+unit.toNat-48) else none) 0 with
  | none => simp only [digits,bind,Option.bind] at parsed; contradiction
  | some value =>
    simp only [digits,bind,Option.bind] at parsed
    split at parsed
    next yes =>
      have eq : value=index := Option.some.inj parsed
      subst value
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at yes
      exact yes.2
    next no => contradiction

theorem monotone {object : JSObject} {old next : Nat} (bound : Holds object old) (larger : old ≤ next) : Holds object next := by
  intro property member index parsed
  exact Nat.lt_of_lt_of_le (bound property member index parsed) larger

theorem changed {object : JSObject} {length : Nat} (bound : Holds object length) (name : JSString) (descriptor : PropertyDescriptor)
    (nameBound : ∀ index, arrayIndex name = some index → index < length) : Holds (setOwnProperty object name descriptor) length := by
  intro property member index parsed
  simp only [setOwnProperty] at member
  split at member
  · obtain ⟨previous,inside,equal⟩ := List.mem_map.mp member
    subst property
    have same : (if previous.name == name then {previous with descriptor} else previous).name = previous.name := by split <;> rfl
    rw [same] at parsed
    exact bound previous inside index parsed
  · cases List.mem_append.mp member with
    | inl inside => exact bound property inside index parsed
    | inr added =>
      have equal : property = ⟨name,descriptor⟩ := by simpa only [List.mem_singleton] using added
      subst property
      exact nameBound index parsed

theorem length_changed {object : JSObject} {boundLength : Nat} (bound : Holds object boundLength)
    (length : Nat) (writable : Bool) : Holds (setArrayLength object length writable) boundLength := by
  apply changed bound
  intro index parsed
  have impossible : arrayIndex (JSString.ofString "length") = none := rfl
  rw [impossible] at parsed
  contradiction

theorem written {object : JSObject} {length : Nat} (bound : Holds object length)
    (index : Nat) (value : Value) (small : index < 256) :
    Holds (DenseArray.written object length index value) (DenseArray.nextLength length index) := by
  have grows : length ≤ DenseArray.nextLength length index := by unfold DenseArray.nextLength; split <;> omega
  have inside : index < DenseArray.nextLength length index := by unfold DenseArray.nextLength; split <;> omega
  have first := changed (monotone bound grows) (MixkeyIndex.key index) (DenseArray.descriptor value) (by
    intro other parsed
    rw [MixkeyIndex.index_key index small] at parsed
    cases Option.some.inj parsed
    exact inside)
  unfold DenseArray.written
  split
  · exact length_changed first _ _
  · exact first

end CookieClicker.JavaScript.ArrayIndexBound

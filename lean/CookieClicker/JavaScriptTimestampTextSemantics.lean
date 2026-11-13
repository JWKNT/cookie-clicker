import CookieClicker.JavaScriptTimestampText
import CookieClicker.JavaScriptBuiltins

/-! Exact timestamp-text representation and traversal steps. These statements
connect the selected index carrier to the real evaluator and string builtin.
They do not assert completion of the entire seeded-library source loop. -/
namespace CookieClicker.JavaScript.TimestampTextSemantics

 theorem tagged_type (heap : Heap) (text : Array UInt16) :
    valueType heap (.timestampText text) = .ok "string" := rfl

 theorem tagged_content (text : Array UInt16) :
    toJSString (.timestampText text) = .ok text.toList := rfl

 theorem tagged_equal_native (text : JSString) :
    strictEqual (.timestampText text.toArray) (.string text) = true := by
  simp [strictEqual]

 theorem index_type (heap : Heap) (index : Int) :
    valueType heap (.textIndex index) = .ok "number" := rfl

 theorem index_to_string (index : Int) :
    toJSString (.textIndex index) = .ok (JSString.ofString (toString index)) := rfl

 theorem index_low_bits (index : Int) :
    bitwiseNumber (.textIndex index) = .ok (Number.ofInt (index % 4294967296)) := rfl

 theorem index_low_bits_periodic (index multiple : Int) :
    bitwiseNumber (.textIndex (index + 4294967296 * multiple)) =
      bitwiseNumber (.textIndex index) := by
  simp [bitwiseNumber, Int.add_emod]

 theorem exact_sequence_length (index : Int) :
    Builtins.toLength (.textIndex index) = .ok index.toNat := rfl

 theorem postfix_increment (base : Machine) (reference : Reference) (tail : List Frame)
    (index : Int) :
    consumeValue {base with continuation := .updateRead .increment reference false :: tail} (.textIndex index) =
      {base with
        control := .putValue reference (.textIndex (index + 1))
        continuation := .putResult (.textIndex index) :: tail} := rfl

 theorem prefix_increment (base : Machine) (reference : Reference) (tail : List Frame)
    (index : Int) :
    consumeValue {base with continuation := .updateRead .increment reference true :: tail} (.textIndex index) =
      {base with
        control := .putValue reference (.textIndex (index + 1))
        continuation := .putResult (.textIndex (index + 1)) :: tail} := rfl

 theorem increment_never_stagnates (index : Int) : index < index + 1 := by omega

 theorem exact_loop_guard (length index : Int) :
    binary .greater (.textIndex length) (.textIndex index) =
      .ok (.boolean (index < length)) := by
  simp [binary, indexBinary, exactNumeric, Rat.intCast_lt_intCast, pure, Except.pure]

 theorem exact_loop_exit (length : Int) :
    binary .greater (.textIndex length) (.textIndex length) = .ok (.boolean false) := by
  rw [exact_loop_guard]
  simp

 theorem exact_loop_remaining (length index : Nat) (before : index < length) :
    length - (index + 1) < length - index := by omega

 theorem char_code_at (heap : Heap) (text : Array UInt16) (index : Int) :
    Builtins.stringCall heap ⟨"String.prototype","charCodeAt"⟩ (.timestampText text) [.textIndex index] =
      .ok (.number (((if index < 0 then none else text[index.toNat]?).map
        (fun unit => Number.ofNat unit.toNat)).getD Number.nan)) := by
  simp [Builtins.stringCall, Builtins.textProvenance, Builtins.exactStringIndex,
    Builtins.argument, Except.bind, bind, Except.pure, pure]

 theorem same_value_native_text (text : JSString) :
    sameValuePrimitive (.timestampText text.toArray) (.string text) = true := by
  simp [sameValuePrimitive, strictEqual]

 theorem index_zero_is_positive_zero :
    sameValuePrimitive (.textIndex 0) (.number Number.positiveZero) = true := by decide +kernel

 theorem index_zero_is_not_negative_zero :
    sameValuePrimitive (.textIndex 0) (.number Number.negativeZero) = false := by decide +kernel

end CookieClicker.JavaScript.TimestampTextSemantics

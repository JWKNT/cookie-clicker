import CookieClicker.JavaScriptIndexBits
import CookieClicker.JavaScriptEval

/-! The native seed helper uses exactly 256 key slots. These lemmas connect
its exact traversal index to native low-byte arithmetic and property keys. -/
namespace CookieClicker.JavaScript.MixkeyIndex
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def key (index : Nat) := JSString.ofString (toString index)

theorem source_slot (index : Nat) :
    binary .bitAnd (.number (Number.ofNat 255)) (.textIndex index) =
      .ok (.number (Number.ofNat (index % 256))) := by
  simp [binary,indexBinary,bitwiseNumber,toNumber,numericBinary,Except.bind,bind,Except.pure,pure,
    IndexBits.extended_index_low_byte _ (Int.natCast_nonneg _)]

theorem decimal_table : ∀ index : Fin 256,
    NumberString.toDecimal (Number.ofNat index.val) = some (key index.val) := by
  decide +kernel

theorem array_index_table : ∀ index : Fin 256,
    arrayIndex (key index.val) = some index.val := by
  decide +kernel

theorem source_key (index : Nat) :
    toJSString (.number (Number.ofNat (index % 256))) = .ok (key (index % 256)) := by
  simp [toJSString,decimal_table ⟨index%256,Nat.mod_lt _ (by decide)⟩]

theorem index_key (index : Nat) (small : index < 256) :
    arrayIndex (key index) = some index := array_index_table ⟨index,small⟩

theorem key_injective {a b : Nat} (smallA : a < 256) (smallB : b < 256)
    (same : key a = key b) : a = b := by
  have first := index_key a smallA
  rw [same,index_key b smallB] at first
  exact (Option.some.inj first).symm

end CookieClicker.JavaScript.MixkeyIndex

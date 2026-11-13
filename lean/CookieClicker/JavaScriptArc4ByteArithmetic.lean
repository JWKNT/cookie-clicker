import CookieClicker.JavaScriptArc4Permutation

/-! Exact binary64 addition and byte masking on the complete byte domain. -/
namespace CookieClicker.JavaScript.Arc4ByteArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem add_mask_fin : ∀ a b : Fin 256,
    MixkeyArray.maskedByte (Number.add (Number.ofNat a.val) (Number.ofNat b.val)) =
      UInt8.ofNat a.val + UInt8.ofNat b.val := by
  intro a b
  have aSmall := a.isLt
  have bSmall := b.isLt
  rw [NaturalArithmetic.native_add_small a.val b.val (by omega) (by omega)]
  unfold MixkeyArray.maskedByte
  rw [IndexBits.toUInt32_ofNat (a.val+b.val) (by omega),UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (show a.val+b.val<4294967296 by omega)]
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofNat',UInt8.toNat_add,Nat.mod_mod]
  omega

theorem add_mask (a b : UInt8) :
    MixkeyArray.maskedByte (Number.add (Number.ofNat a.toNat) (Number.ofNat b.toNat)) = a+b := by
  simpa only [UInt8.ofNat_toNat] using add_mask_fin ⟨a.toNat,a.toNat_lt⟩ ⟨b.toNat,b.toNat_lt⟩

end CookieClicker.JavaScript.Arc4ByteArithmetic

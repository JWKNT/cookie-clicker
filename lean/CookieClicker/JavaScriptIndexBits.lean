import CookieClicker.JavaScriptNaturalArithmetic

/-! Exact native integer and low-byte conversions used by source seed mixing.
The statements cover every bounded integer, without enumerating its values. -/
namespace CookieClicker.JavaScript.IndexBits
open Float.Model Float.Model.UnpackedFloat RoundingBridge NaturalArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096

theorem magnitude_denominator_positive (bits : UInt64) :
    0 < (Number.magnitudeFraction bits).2 := by
  unfold Number.magnitudeFraction
  split
  split <;> simp [Nat.two_pow_pos]

theorem ofNat_represents (n : Nat) (small : n < 2^52) :
    RepresentsNatBits (Number.ofNat n) n := by
  by_cases zero : n=0
  · subst n
    exact zero_pack_represents
  · obtain ⟨m,e,p,lo,hi,el,eu,shape,rep⟩ := native_small_integer_round_shape n (by omega) small
    rw [ofNat_encoding,shape]
    exact normal_pack_represents m n e p lo hi el (by omega) rep

theorem truncate_represented (bits : UInt64) (n : Nat) (represented : RepresentsNatBits bits n) :
    Number.truncateInt bits=(n : Int) := by
  obtain ⟨finite,sign,value⟩ := represented
  simp only [Number.truncateInt,finite,sign,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [value,Int.natCast_mul,Int.mul_ediv_cancel]
  have := magnitude_denominator_positive bits
  omega

theorem truncate_ofNat (n : Nat) (small : n < 2^52) :
    Number.truncateInt (Number.ofNat n)=(n : Int) :=
  truncate_represented _ n (ofNat_represents n small)

theorem toUInt32_ofNat (n : Nat) (small : n < 2^32) :
    Number.toUInt32 (Number.ofNat n)=UInt32.ofNat n := by
  rw [Number.toUInt32,truncate_ofNat n (by omega)]
  have bound : (n : Int) < 2^32 := by omega
  rw [Int.emod_eq_of_lt (by omega) bound,Int.toNat_natCast]

theorem ofInt_nonnegative (n : Nat) : Number.ofInt (n : Int)=Number.ofNat n := by
  simp [Number.ofInt,Number.ofNat,Float.Model.ofInt,Float.Model.ofNat,
    UnpackedFloat.ofInt,UnpackedFloat.ofNat]

theorem toUInt32_nonnegative (n : Int) (positive : 0≤n) (small : n<2^32) :
    Number.toUInt32 (Number.ofInt n)=UInt32.ofNat n.toNat := by
  have same : n=(n.toNat : Int) := (Int.toNat_of_nonneg positive).symm
  calc
    Number.toUInt32 (Number.ofInt n)=Number.toUInt32 (Number.ofNat n.toNat) := by
      rw [same,ofInt_nonnegative,Int.toNat_natCast]
    _=UInt32.ofNat n.toNat := toUInt32_ofNat _ (by omega)

theorem word_low_byte (n : Nat) :
    ((UInt32.ofNat 255) &&& UInt32.ofNat n).toNat=n%256 := by
  rw [UInt32.toNat_and]
  change 255 &&& (n%4294967296)=n%256
  rw [Nat.and_comm]
  change (n%2^32) &&& (2^8-1)=n%2^8
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_mod_of_dvd n (by decide : 2^8 ∣ 2^32)]

theorem signed_low_byte (n : Nat) :
    Number.signed32 ((UInt32.ofNat 255) &&& UInt32.ofNat n)=(n%256 : Nat) := by
  rw [Number.signed32,word_low_byte,if_pos]
  have := Nat.mod_lt n (by decide : 0<256)
  omega

theorem native_low_byte (n : Nat) (small : n<2^32) :
    Number.bitAnd (Number.ofNat 255) (Number.ofNat n)=Number.ofNat (n%256) := by
  rw [Number.bitAnd,toUInt32_ofNat 255 (by decide),toUInt32_ofNat n small,
    signed_low_byte,ofInt_nonnegative]

theorem mask_byte (bits : UInt64) :
    Number.bitAnd (Number.ofNat 255) bits=
      Number.ofNat ((Number.toUInt32 bits).toNat%256) := by
  rw [Number.bitAnd,toUInt32_ofNat 255 (by decide)]
  have word : Number.toUInt32 bits=UInt32.ofNat (Number.toUInt32 bits).toNat := by simp
  conv => lhs; rw [word]
  rw [signed_low_byte,ofInt_nonnegative]

theorem masked_byte_represented (bits : UInt64) :
    RepresentsNatBits (Number.bitAnd (Number.ofNat 255) bits)
      ((Number.toUInt32 bits).toNat%256) := by
  rw [mask_byte]
  apply ofNat_represents
  have := Nat.mod_lt (Number.toUInt32 bits).toNat (by decide : 0<256)
  omega

theorem extended_index_low_byte (index : Int) (positive : 0≤index) :
    Number.bitAnd (Number.ofNat 255) (Number.ofInt (index%4294967296))=
      Number.ofNat (index.toNat%256) := by
  have remainderPositive : 0≤index%4294967296 := Int.emod_nonneg _ (by decide)
  have remainderSmall : index%4294967296<2^32 := Int.emod_lt_of_pos _ (by decide)
  rw [Number.bitAnd,toUInt32_ofNat 255 (by decide),
    toUInt32_nonnegative _ remainderPositive remainderSmall,signed_low_byte,ofInt_nonnegative]
  congr 1
  have same : index=(index.toNat : Int) := (Int.toNat_of_nonneg positive).symm
  rw [same]
  simp only [Int.natCast_emod,Int.toNat_natCast]
  exact Nat.mod_mod_of_dvd _ (by decide : 256∣4294967296)

end CookieClicker.JavaScript.IndexBits

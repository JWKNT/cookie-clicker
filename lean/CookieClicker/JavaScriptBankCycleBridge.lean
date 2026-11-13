import CookieClicker.JavaScriptNaturalArithmetic
import CookieClicker.JavaScriptScaledArithmeticBridge
import CookieClicker.JavaScriptMath

/-! Binary64 bank identities for the proposed Cursor sale/rebuy route.
Every canonical bank with exponent6..970 absorbs integer refunds0..4 and
debits0..15, including the lower-binade boundary below a power of two.
The repeated arithmetic follows the actual refund-then-debit order and does
not reset the bank between cycles. The Cursor price formulas use the pinned
V8 pow translation; whole-callback, host and installed-engine refinement
remain separate. This file does not prove legal full-game reachability. -/
namespace CookieClicker.JavaScript.BankCycleBridge
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge NaturalArithmetic
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxHeartbeats 2000000

theorem normal_nat_pair_unique (m₁ m₂ e₁ e₂ : Nat)
    (lower₁ : 2^52 ≤ m₁) (upper₁ : m₁ < 2^53)
    (lower₂ : 2^52 ≤ m₂) (upper₂ : m₂ < 2^53)
    (sameValue : m₁*2^e₁ = m₂*2^e₂) : m₁ = m₂ ∧ e₁ = e₂ := by
  have log₁ : m₁.log2 = 52 := (Nat.log2_eq_iff (by omega : m₁ ≠ 0)).mpr ⟨lower₁,upper₁⟩
  have log₂ : m₂.log2 = 52 := (Nat.log2_eq_iff (by omega : m₂ ≠ 0)).mpr ⟨lower₂,upper₂⟩
  have logarithms := congrArg Nat.log2 sameValue
  rw [log2_scaled m₁ e₁ (by omega),log2_scaled m₂ e₂ (by omega),log₁,log₂] at logarithms
  have exponents : e₁ = e₂ := by omega
  rw [exponents] at sameValue
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) sameValue,exponents⟩

theorem packed_integer_round_equals_normal (n m e : Nat) (positive : 0 < m)
    (large : 2^52 ≤ n) (bounded : n < 2^1023)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (_finite : e ≤ 971)
    (rounded : roundedInteger n = m*2^e) :
    (Float.Model.pack (round Format.binary64 .positive n 0)).toBits =
      (Float.Model.pack (.finite .positive m e positive)).toBits := by
  obtain ⟨m',e',positive',lower',upper',finite',shape⟩ := native_integer_round_shape n large bounded
  have projection := native_normal_integer_round n large
  rw [shape] at projection
  have value : m'*2^e' = roundedInteger n := by simpa [RepresentsNat] using projection
  have sameValue : m'*2^e' = m*2^e := value.trans rounded
  obtain ⟨sameM,sameE⟩ := normal_nat_pair_unique m' m e' e lower' upper' lower upper sameValue
  subst m'; subst e'; rw [shape]

theorem round_above_multiple (spacing quotient credit : Nat) (positive : 0 < spacing)
    (small : 2*credit < spacing) :
    roundMultiple spacing (quotient*spacing+credit) = quotient*spacing := by
  have creditSmall : credit < spacing := by omega
  have division : (quotient*spacing+credit)/spacing = quotient := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt creditSmall]
    simp
  have remainder : (quotient*spacing+credit)%spacing = credit := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt creditSmall]
  simp only [roundMultiple,division,remainder]
  have notAbove : ¬spacing < 2*credit := by omega
  have notEqual : spacing ≠ 2*credit := by omega
  simp [notAbove,notEqual]

theorem round_below_multiple (spacing quotient debit : Nat) (positive : 0 < spacing)
    (qPositive : 0 < quotient) (debitPositive : 0 < debit) (small : 2*debit < spacing) :
    roundMultiple spacing (quotient*spacing-debit) = quotient*spacing := by
  have debitSmall : debit < spacing := by omega
  have expression : quotient*spacing-debit = (quotient-1)*spacing+(spacing-debit) := by
    have product : (quotient-1)*spacing = quotient*spacing-spacing := by rw [Nat.sub_mul,Nat.one_mul]
    have lower := Nat.le_mul_of_pos_left spacing qPositive
    omega
  have remainderSmall : spacing-debit < spacing := by omega
  have division : (quotient*spacing-debit)/spacing = quotient-1 := by
    rw [expression,Nat.add_comm,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt remainderSmall]
    simp
  have remainder : (quotient*spacing-debit)%spacing = spacing-debit := by
    rw [expression]
    simp [Nat.add_mod,Nat.mod_eq_of_lt remainderSmall]
  have above : spacing < 2*(spacing-debit) := by omega
  simp [roundMultiple,division,remainder,above,show quotient-1+1 = quotient by omega]

theorem canonical_log_after_refund (m e credit : Nat) (lower : 2^52 ≤ m) (upper : m < 2^53)
    (expLower : 6 ≤ e) (creditBound : credit ≤ 4) : (m*2^e+credit).log2 = 52+e := by
  have valueLower : 2^(52+e) ≤ m*2^e+credit := by
    rw [Nat.pow_add]
    have h := Nat.mul_le_mul_right (2^e) lower
    omega
  have margin : credit < 2^e := Nat.lt_of_lt_of_le (by omega : credit < 2^6)
    (Nat.pow_le_pow_right (by decide) expLower)
  have valueUpper : m*2^e+credit < 2^(52+e+1) := by
    have h := Nat.mul_le_mul_right (2^e) (show m+1 ≤ 2^53 by omega)
    rw [Nat.add_mul,Nat.one_mul] at h
    have power : 2^(52+e+1) = 2^53*2^e := by rw [← Nat.pow_add]; congr 1; omega
    rw [power]; omega
  exact (Nat.log2_eq_iff (by omega : m*2^e+credit ≠ 0)).mpr ⟨valueLower,valueUpper⟩

theorem rounded_refund_fixed (m e credit : Nat) (lower : 2^52 ≤ m) (upper : m < 2^53)
    (expLower : 6 ≤ e) (creditBound : credit ≤ 4) : roundedInteger (m*2^e+credit) = m*2^e := by
  have log := canonical_log_after_refund m e credit lower upper expLower creditBound
  rw [roundedInteger,integer_spacing_matches_native,log,show 52+e-52=e by omega]
  exact round_above_multiple _ _ _ (Nat.two_pow_pos _)
    (Nat.lt_of_lt_of_le (by omega : 2*credit < 2^6) (Nat.pow_le_pow_right (by decide) expLower))

theorem canonical_log_after_debit (m e debit : Nat) (lower : 2^52 < m) (upper : m < 2^53)
    (expLower : 6 ≤ e) (debitPositive : 0 < debit) (debitBound : debit ≤ 15) : (m*2^e-debit).log2 = 52+e := by
  have margin : debit < 2^e := Nat.lt_of_lt_of_le (by omega : debit < 2^6)
    (Nat.pow_le_pow_right (by decide) expLower)
  have valueLower : 2^(52+e) ≤ m*2^e-debit := by
    have h := Nat.mul_le_mul_right (2^e) (show 2^52+1 ≤ m by omega)
    rw [Nat.add_mul,Nat.one_mul] at h
    rw [Nat.pow_add]
    omega
  have valueUpper : m*2^e-debit < 2^(52+e+1) := by
    have h := Nat.mul_lt_mul_of_pos_right upper (Nat.two_pow_pos e)
    have power : 2^(52+e+1) = 2^53*2^e := by rw [← Nat.pow_add]; congr 1; omega
    rw [power]; omega
  exact (Nat.log2_eq_iff (by have := Nat.two_pow_pos (52+e); omega : m*2^e-debit ≠ 0)).mpr
    ⟨valueLower,valueUpper⟩

theorem boundary_log_after_debit (e debit : Nat) (expLower : 6 ≤ e) (debitPositive : 0 < debit) (debitBound : debit ≤ 15) :
    (2^52*2^e-debit).log2 = 51+e := by
  have power : 2^52*2^e = 2^(51+e)*2 := by rw [← Nat.pow_succ,← Nat.pow_add]; congr 1; omega
  have margin : debit < 2^(51+e) := Nat.lt_of_lt_of_le (by omega : debit < 2^57)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have valueLower : 2^(51+e) ≤ 2^52*2^e-debit := by rw [power]; omega
  have valueUpper : 2^52*2^e-debit < 2^(51+e+1) := by rw [Nat.pow_succ,power]; omega
  exact (Nat.log2_eq_iff (by omega : 2^52*2^e-debit ≠ 0)).mpr ⟨valueLower,valueUpper⟩

theorem rounded_debit_fixed (m e debit : Nat) (lower : 2^52 ≤ m) (upper : m < 2^53)
    (expLower : 6 ≤ e) (debitPositive : 0 < debit) (debitBound : debit ≤ 15) : roundedInteger (m*2^e-debit) = m*2^e := by
  by_cases boundary : m = 2^52
  · subst m
    have log := boundary_log_after_debit e debit expLower debitPositive debitBound
    rw [roundedInteger,integer_spacing_matches_native,log,show 51+e-52=e-1 by omega]
    have value : 2^52*2^e = 2^53*2^(e-1) := by rw [← Nat.pow_add,← Nat.pow_add]; congr 1; omega
    rw [value]
    exact round_below_multiple _ _ _ (Nat.two_pow_pos _) (by decide) debitPositive
      (Nat.lt_of_lt_of_le (by omega : 2*debit < 2^5) (Nat.pow_le_pow_right (by decide) (by omega)))
  · have log := canonical_log_after_debit m e debit (by omega) upper expLower debitPositive debitBound
    rw [roundedInteger,integer_spacing_matches_native,log,show 52+e-52=e by omega]
    exact round_below_multiple _ _ _ (Nat.two_pow_pos _) (by omega) debitPositive
      (Nat.lt_of_lt_of_le (by omega : 2*debit < 2^6) (Nat.pow_le_pow_right (by decide) expLower))

theorem bank_value_lower (m e : Nat) (lower : 2^52 ≤ m) (expLower : 6 ≤ e) :
    2^58 ≤ m*2^e := by
  have h := Nat.mul_le_mul lower (Nat.pow_le_pow_right (by decide : 0 < 2) expLower)
  exact h

theorem bank_refund_bounded (m e : Nat) (lower : 2^52 ≤ m) (upper : m < 2^53)
    (expLower : 6 ≤ e) (expUpper : e ≤ 970) : m*2^e+4 < 2^1023 := by
  have logarithm := canonical_log_after_refund m e 4 lower upper expLower (Nat.le_refl _)
  have bound := ((Nat.log2_eq_iff (by omega : m*2^e+4 ≠ 0)).mp logarithm).2
  exact Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))

/-- Every native refund from0 through4 is absorbed in these canonical binades. -/
theorem native_refund_fixed (m e credit : Nat) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : 6 ≤ e) (expUpper : e ≤ 970)
    (creditBound : credit ≤ 4) :
    let bank := (Float.Model.pack (.finite .positive m e positive)).toBits
    Number.add bank (Number.ofNat credit) = bank := by
  by_cases zero : credit = 0
  · subst credit
    exact FractionalArithmeticBridge.number_add_zero_right m (e:Int) positive lower upper (by omega) (by omega)
  · have large := bank_value_lower m e lower expLower
    obtain ⟨mc,ec,pc,lc,uc,elc,euc,shape,represented⟩ :=
      native_small_integer_round_shape credit (by omega) (by omega)
    have bounded := bank_refund_bounded m e lower upper expLower expUpper
    dsimp only
    rw [ofNat_encoding credit,shape]
    simp only [Number.add,Float.Model.add,
      normal_model_unpack m (e:Int) positive lower upper (by omega) (by omega),
      normal_model_unpack mc ec pc lc uc elc (by omega)]
    rw [native_integer_add_is_round m mc (m*2^e) credit (e:Int) ec lower lc
      (by simp [RepresentsNat]) represented (by omega)]
    exact packed_integer_round_equals_normal _ m e positive (by omega) (by omega)
      lower upper (by omega) (rounded_refund_fixed m e credit lower upper expLower creditBound)

/-- At a power-of-two bank, subtraction enters the lower binade. Every
integer debit through15 is strictly below its half-ulp16 boundary. -/
theorem native_debit_fixed (m e debit : Nat) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : 6 ≤ e) (expUpper : e ≤ 970)
    (debitBound : debit ≤ 15) :
    let bank := (Float.Model.pack (.finite .positive m e positive)).toBits
    Number.sub bank (Number.ofNat debit) = bank := by
  by_cases zero : debit = 0
  · subst debit
    exact FractionalArithmeticBridge.number_sub_zero_right m (e:Int) positive lower upper (by omega) (by omega)
  · have large := bank_value_lower m e lower expLower
    have bounded := bank_refund_bounded m e lower upper expLower expUpper
    obtain ⟨md,ed,pd,ld,ud,eld,eud,shape,represented⟩ :=
      native_small_integer_round_shape debit (by omega) (by omega)
    dsimp only
    rw [ofNat_encoding debit,shape]
    simp only [Number.sub,Float.Model.sub,
      normal_model_unpack m (e:Int) positive lower upper (by omega) (by omega),
      normal_model_unpack md ed pd ld ud eld (by omega)]
    rw [native_integer_sub_is_round m md (m*2^e) debit (e:Int) ed
      positive pd (by simp [RepresentsNat]) represented (by omega)]
    exact packed_integer_round_equals_normal _ m e positive (by omega) (by omega)
      lower upper (by omega) (rounded_debit_fixed m e debit lower upper expLower (by omega) debitBound)

/-- Native source arithmetic with no building-price modifier and free=0. -/
theorem fresh_cursor_buy_price :
    Number.ceil (Number.mul (Number.ofNat 15)
      (Math.pow (Number.ofScientific 115 (-2)) Number.positiveZero)) = Number.ofNat 15 := by
  decide +kernel

theorem fresh_cursor_sale_refund :
    Number.floor (Number.mul
      (Number.ceil (Number.mul (Number.ofNat 15)
        (Math.pow (Number.ofScientific 115 (-2)) Number.one)))
      (Number.ofScientific 25 (-2))) = Number.ofNat 4 := by
  decide +kernel

/-- If Starter kit leaves free>=1 while amount=1, the price exponent is zero. -/
theorem starter_cursor_sale_refund :
    Number.floor (Number.mul
      (Number.ceil (Number.mul (Number.ofNat 15)
        (Math.pow (Number.ofScientific 115 (-2)) Number.positiveZero)))
      (Number.ofScientific 25 (-2))) = Number.ofNat 3 := by
  decide +kernel

def cycle (refund debit : Nat) (bank : UInt64) : UInt64 :=
  Number.sub (Number.add bank (Number.ofNat refund)) (Number.ofNat debit)

theorem native_cycle_fixed (m e refund debit : Nat) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : 6 ≤ e) (expUpper : e ≤ 970)
    (refundBound : refund ≤ 4) (debitBound : debit ≤ 15) :
    let bank := (Float.Model.pack (.finite .positive m e positive)).toBits
    cycle refund debit bank = bank := by
  dsimp only [cycle]
  rw [native_refund_fixed m e refund positive lower upper expLower expUpper refundBound,
    native_debit_fixed m e debit positive lower upper expLower expUpper debitBound]

theorem every_finite_cycle_prefix_preserves_bank (m e refund debit count : Nat) (positive : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : 6 ≤ e) (expUpper : e ≤ 970)
    (refundBound : refund ≤ 4) (debitBound : debit ≤ 15) :
    let bank := (Float.Model.pack (.finite .positive m e positive)).toBits
    Nat.repeat (cycle refund debit) count bank = bank := by
  induction count with
  | zero => rfl
  | succ count ih =>
    dsimp only at ih ⊢
    simp only [Nat.repeat]
    rw [ih]
    exact native_cycle_fixed m e refund debit positive lower upper expLower expUpper refundBound debitBound

end CookieClicker.JavaScript.BankCycleBridge

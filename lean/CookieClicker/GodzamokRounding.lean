import Std

/-! Integer-input binary64 round-to-nearest, ties-to-even projections.
This covers the native unit-increment Godzamok recurrence and exact integer
cookie debits/refunds at a power-of-two bank. It is not a full native callback
refinement. Other sale batch sizes can have different increments and fixed points.
-/
namespace CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 2048

/-- Binary64 has 53 significant bits, counting the implicit leading bit.
Integer inputs below 2^53 have unit spacing. There are no fractional/subnormal
inputs in this projection. -/
def integerSpacing (n : Nat) : Nat :=
  if n < 2 ^ 53 then 1 else 2 ^ (n.log2 - 52)

/-- Nearest multiple, with an exact halfway remainder going to an even quotient. -/
def roundMultiple (spacing n : Nat) : Nat :=
  let quotient := n / spacing
  let remainder := n % spacing
  let up := spacing < 2 * remainder || (spacing == 2 * remainder && quotient % 2 == 1)
  (quotient + if up then 1 else 0) * spacing

def roundedInteger (n : Nat) : Nat := roundMultiple (integerSpacing n) n

/-- None denotes positive infinity after exponent overflow. An integer whose
rounded normalized exponent is at most 1023 has its exact rounded Nat value. -/
def roundBinary64Integer (n : Nat) : Option Nat :=
  let rounded := roundedInteger n
  if rounded < 2 ^ 1024 then some rounded else none

def unitCap : Nat := 2 ^ 53
def bank : Nat := 2 ^ 90

/-- The native literal 0.01 has significand fraction 5764607523034235 / 2^59.
Scaling its exact product by 100 to an integer preserves this normal binade's
significand rounding: the numerator is 2^59 + 12 and rounds to 2^59.
The corresponding rounded multiplier increment is therefore exactly one. -/
theorem hundred_times_cent_scaled :
    5764607523034235 * 100 = 2 ^ 59 + 12 ∧
    roundedInteger (5764607523034235 * 100) = 2 ^ 59 := by decide +kernel

theorem unit_spacing_exact (n : Nat) : roundMultiple 1 n = n := by
  simp [roundMultiple, Nat.mod_one]

theorem integer_exact_through_cap (n : Nat) (within : n ≤ unitCap) : roundedInteger n = n := by
  by_cases below : n < 2 ^ 53
  · simp [roundedInteger, integerSpacing, below, unit_spacing_exact]
  · have equality : n = unitCap := by unfold unitCap at *; omega
    subst n
    decide +kernel

theorem unit_cap_halfway_rounds_down : roundedInteger (unitCap + 1) = unitCap := by decide +kernel

theorem increment_one (n : Nat) (within : n ≤ unitCap) :
    roundedInteger (n + 1) = min (n + 1) unitCap := by
  by_cases below : n < unitCap
  · have successor : n + 1 ≤ unitCap := by omega
    rw [integer_exact_through_cap _ successor, Nat.min_eq_left successor]
  · have equality : n = unitCap := by omega
    subst n
    rw [unit_cap_halfway_rounds_down, Nat.min_eq_right (by omega)]

def unitIterations : Nat → Nat
  | 0 => 1
  | n + 1 => roundedInteger (unitIterations n + 1)

theorem unit_iterations_exact (n : Nat) : unitIterations n = min (n + 1) unitCap := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    simp only [unitIterations, ih]
    rw [increment_one _ (Nat.min_le_right _ _)]
    omega

theorem unit_fixed_point : roundedInteger (unitCap + 1) = unitCap := unit_cap_halfway_rounds_down

theorem unit_prefix_finite_reaches_cap : unitIterations (unitCap - 1) = unitCap := by
  rw [unit_iterations_exact]
  decide +kernel

theorem unit_iterations_binary64 (n : Nat) :
    roundBinary64Integer (unitIterations n + 1) = some (min (n + 2) unitCap) := by
  have within : unitIterations n ≤ unitCap := by rw [unit_iterations_exact]; exact Nat.min_le_right _ _
  have rounded : roundedInteger (unitIterations n + 1) = min (n + 2) unitCap := by
    rw [increment_one _ within, unit_iterations_exact]
    omega
  have capFinite : unitCap < 2 ^ 1024 := by decide +kernel
  have finite : min (n + 2) unitCap < 2 ^ 1024 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) capFinite
  simp [roundBinary64Integer, rounded, finite]

theorem upper_bank_spacing (amount : Nat) (small : amount ≤ 2 ^ 37) :
    integerSpacing (bank + amount) = 2 ^ 38 := by
  have lower : 2 ^ 90 ≤ bank + amount := by unfold bank; omega
  have upper : bank + amount < 2 ^ (90 + 1) := by unfold bank at *; omega
  have positive : bank + amount ≠ 0 := by unfold bank; omega
  have logarithm : (bank + amount).log2 = 90 := (Nat.log2_eq_iff positive).mpr ⟨lower, upper⟩
  have notSmall : ¬bank + amount < 2 ^ 53 := by unfold bank; omega
  simp [integerSpacing, notSmall, logarithm]

theorem lower_bank_spacing (amount : Nat) (positive : 0 < amount) (small : amount ≤ 2 ^ 36) :
    integerSpacing (bank - amount) = 2 ^ 37 := by
  have lower : 2 ^ 89 ≤ bank - amount := by unfold bank at *; omega
  have upper : bank - amount < 2 ^ (89 + 1) := by unfold bank at *; omega
  have nonzero : bank - amount ≠ 0 := by omega
  have logarithm : (bank - amount).log2 = 89 := (Nat.log2_eq_iff nonzero).mpr ⟨lower, upper⟩
  have notSmall : ¬bank - amount < 2 ^ 53 := by unfold bank at *; omega
  simp [integerSpacing, notSmall, logarithm]

theorem refund_rounds_away (amount : Nat) (small : amount ≤ 2 ^ 37) :
    roundedInteger (bank + amount) = bank := by
  unfold roundedInteger
  rw [upper_bank_spacing amount small]
  have quotient : (bank + amount) / 2 ^ 38 = 2 ^ 52 := by unfold bank at *; omega
  have remainder : (bank + amount) % 2 ^ 38 = amount := by unfold bank at *; omega
  simp only [roundMultiple, quotient, remainder]
  have notAbove : ¬2 ^ 38 < 2 * amount := by omega
  simp [notAbove, bank]

theorem debit_rounds_away (amount : Nat) (small : amount ≤ 2 ^ 36) :
    roundedInteger (bank - amount) = bank := by
  by_cases zero : amount = 0
  · subst amount
    decide +kernel
  · have positive : 0 < amount := by omega
    unfold roundedInteger
    rw [lower_bank_spacing amount positive small]
    have quotient : (bank - amount) / 2 ^ 37 = 2 ^ 53 - 1 := by unfold bank at *; omega
    have remainder : (bank - amount) % 2 ^ 37 = 2 ^ 37 - amount := by unfold bank at *; omega
    simp only [roundMultiple, quotient, remainder]
    have up : (decide (2 ^ 37 < 2 * (2 ^ 37 - amount)) ||
        ((2 ^ 37 == 2 * (2 ^ 37 - amount)) && (((2 ^ 53 - 1) % 2) == 1))) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
      simp only [Nat.reducePow, Nat.reduceSub, and_true] at *
      omega
    rw [up]
    decide +kernel

theorem bank_finite : bank < 2 ^ 1024 := by decide +kernel

theorem binary64_refund_rounds_away (amount : Nat) (small : amount ≤ 2 ^ 37) :
    roundBinary64Integer (bank + amount) = some bank := by
  unfold roundBinary64Integer
  rw [refund_rounds_away amount small, if_pos bank_finite]

theorem binary64_debit_rounds_away (amount : Nat) (small : amount ≤ 2 ^ 36) :
    roundBinary64Integer (bank - amount) = some bank := by
  unfold roundBinary64Integer
  rw [debit_rounds_away amount small, if_pos bank_finite]

inductive Transaction where
  | refund (amount : Nat)
  | debit (amount : Nat)
  deriving DecidableEq

def Transaction.small : Transaction → Prop
  | .refund amount => amount ≤ 2 ^ 37
  | .debit amount => amount ≤ 2 ^ 36

def Transaction.apply (transaction : Transaction) (cookies : Nat) : Option Nat :=
  match transaction with
  | .refund amount => roundBinary64Integer (cookies + amount)
  | .debit amount => if amount ≤ cookies then roundBinary64Integer (cookies - amount) else none

theorem small_transaction_preserves_bank (transaction : Transaction) (small : transaction.small) :
    transaction.apply bank = some bank := by
  cases transaction with
  | refund amount => exact binary64_refund_rounds_away amount small
  | debit amount =>
    have affordable : amount ≤ bank := by dsimp [Transaction.small] at small; unfold bank; omega
    simp only [Transaction.apply, if_pos affordable]
    exact binary64_debit_rounds_away amount small

def transact : List Transaction → Nat → Option Nat
  | [], cookies => some cookies
  | first :: rest, cookies => (first.apply cookies).bind (transact rest)

theorem transactions_preserve_bank (transactions : List Transaction)
    (small : ∀ transaction ∈ transactions, transaction.small) :
    transact transactions bank = some bank := by
  induction transactions with
  | nil => rfl
  | cons first rest ih =>
    have firstSmall : first.small := small first (by simp)
    have restSmall : ∀ transaction ∈ rest, transaction.small := by
      intro transaction member
      exact small transaction (by simp [member])
    simp only [transact, small_transaction_preserves_bank first firstSmall, Option.bind_some]
    exact ih restSmall

/-- This is a projection of bounded per-copy transactions, not a claim that
every native sale/rebuy preserves all other game state or uses these bounds. -/
def transactionCycles (transactions : Nat → List Transaction) : Nat → Option Nat
  | 0 => some bank
  | n + 1 => (transactionCycles transactions n).bind (transact (transactions n))

theorem arbitrarily_many_finite_cycles (transactions : Nat → List Transaction)
    (small : ∀ n transaction, transaction ∈ transactions n → transaction.small) (cycles : Nat) :
    transactionCycles transactions cycles = some bank ∧
      unitIterations cycles = min (cycles + 1) unitCap := by
  constructor
  · induction cycles with
    | zero => rfl
    | succ n ih =>
      simp only [transactionCycles, ih, Option.bind_some]
      exact transactions_preserve_bank _ (small n)
  · exact unit_iterations_exact cycles

/-- The unit-increment fixed point is not a cap for larger sale increments. -/
theorem increment_two_passes_unit_cap : roundedInteger (unitCap + 2) = unitCap + 2 := by decide +kernel

/-- The halfway bank bounds are exact for these integer inputs. -/
theorem bank_next_debit_changes : roundedInteger (bank - (2 ^ 36 + 1)) = bank - 2 ^ 37 := by decide +kernel

theorem bank_next_refund_changes : roundedInteger (bank + (2 ^ 37 + 1)) = bank + 2 ^ 38 := by decide +kernel

end CookieClicker.FullGame.GodzamokRounding

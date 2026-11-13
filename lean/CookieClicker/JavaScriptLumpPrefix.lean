import CookieClicker.JavaScriptNaturalArithmetic
import CookieClicker.JavaScriptLumpSource
/-! A bounded early-lump arithmetic envelope tied to the extracted source choices.
The range theorem covers every sequence of136 supported credits with actual
binary64 addition, plus the level-cost and ripe-time budgets. It does not prove
the initialized whole-game heap, seedrandom range, callback frame invariants,
or legal timing of every harvest. Those remain source-composition obligations.
-/
namespace CookieClicker.JavaScript.LumpPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

theorem native_small_adds_exact (bank : Fin 953) (credit : Fin 8) :
    Number.add (Number.ofNat bank.val) (Number.ofNat credit.val) =
      Number.ofNat (bank.val + credit.val) :=
  NaturalArithmetic.native_add_small bank.val credit.val (by omega) (by omega)

theorem native_small_spends_exact (bank : Fin 953) (cost : Fin 13)
    (affordable : cost.val ≤ bank.val) :
    Number.sub (Number.ofNat bank.val) (Number.ofNat cost.val) =
      Number.ofNat (bank.val - cost.val) :=
  NaturalArithmetic.native_sub_small bank.val cost.val (by omega) (by omega) affordable

theorem native_ripe_multiply_floor_exact : ∀ (choice : Fin 7),
    Number.floor (Number.mul Number.one (Number.ofNat (choice.val + 1))) =
      Number.ofNat (choice.val + 1) := by
  decide +kernel

def naturalTotal (choices : Nat → Fin 7) : Nat → Nat
  | 0 => 0
  | n + 1 => naturalTotal choices n + (choices n).val + 1

def nativeTotal (choices : Nat → Fin 7) : Nat → UInt64
  | 0 => Number.positiveZero
  | n + 1 => Number.add (nativeTotal choices n) (Number.ofNat ((choices n).val + 1))

theorem total_bounds (choices : Nat → Fin 7) (n : Nat) :
    n ≤ naturalTotal choices n ∧ naturalTotal choices n ≤ 7 * n := by
  induction n with
  | zero => simp [naturalTotal]
  | succ n ih =>
    have range := (choices n).isLt
    simp only [naturalTotal]
    omega

/-- Every sequence of136 allowed yields, including the all-one worst case.
This arithmetic theorem is conditional on the source callback credit contract;
it does not declare that the full-game heap invariant is proved. -/
theorem native_total_exact (choices : Nat → Fin 7) (n : Nat) (bound : n ≤ 136) :
    nativeTotal choices n = Number.ofNat (naturalTotal choices n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have range := (choices n).isLt
    have previous := total_bounds choices n
    have exactAdd := native_small_adds_exact
      ⟨naturalTotal choices n, by omega⟩ ⟨(choices n).val + 1, by omega⟩
    simp only [nativeTotal, naturalTotal, ih (by omega)]
    simpa [Nat.add_assoc] using exactAdd

theorem all_136_yields_supply_136 (choices : Nat → Fin 7) :
    nativeTotal choices 136 = Number.ofNat (naturalTotal choices 136) ∧
      136 ≤ naturalTotal choices 136 ∧ naturalTotal choices 136 ≤ 952 := by
  exact ⟨native_total_exact choices 136 (by decide), total_bounds choices 136⟩

def levelCost (level : Nat) : Nat := level * (level + 1) / 2

theorem target_level_cost :
    levelCost 12 + levelCost 10 + 3 * levelCost 1 = 136 := by decide +kernel

theorem ripe_click_window :
    Number.lessThan (Number.ofNat 82800001) (Number.ofNat 72000000) = false ∧
    Number.lessThan (Number.ofNat 82800001) (Number.ofNat 82800000) = false ∧
    Number.lessThan (Number.ofNat 82800001) (Number.ofNat 86400000) = true := by
  decide +kernel

theorem bounded_collection_time :
    136 * (82800000 + 1) = 11260800136 ∧
    136 * (82800000 + 1) < 2 ^ 34 ∧
    2 ^ 40 + (136 * (82800000 + 1) + 32) / 33 < 2 ^ 41 ∧
    2 ^ 41 < 2 ^ 53 := by
  decide +kernel

/-- The credit set is read from the intact native harvest syntax. -/
theorem source_option_has_integer_index (value : UInt64)
    (supported : value ∈ LumpSource.nonmeatyOptions) :
    ∃ choice : Fin 7, value = Number.ofNat (choice.val + 1) := by
  have all := LumpSource.source_nonmeaty_options_are_one_through_seven
  have existsIndex := (List.all_eq_true.mp all) value supported
  obtain ⟨index, member, equal⟩ := List.any_eq_true.mp existsIndex
  exact ⟨⟨index, List.mem_range.mp member⟩, eq_of_beq equal⟩

/-- Every finite source-supported sequence uses exact native additions, in its
original order. This is an operand-level theorem; the callback frame invariant
must establish that these are the actual credits of an execution. -/
theorem source_credits_exact (credits : List UInt64) (start : Nat)
    (bounded : start + 7 * credits.length ≤ 952)
    (supported : ∀ value ∈ credits, value ∈ LumpSource.nonmeatyOptions) :
    ∃ added : Nat, credits.length ≤ added ∧ added ≤ 7 * credits.length ∧
      credits.foldl Number.add (Number.ofNat start) = Number.ofNat (start + added) := by
  induction credits generalizing start with
  | nil => exact ⟨0, by simp, by simp, by simp⟩
  | cons credit credits ih =>
    obtain ⟨choice, creditEq⟩ := source_option_has_integer_index credit (supported credit (by simp))
    have range := choice.isLt
    have tailSupport : ∀ value ∈ credits, value ∈ LumpSource.nonmeatyOptions := by
      intro value member; exact supported value (by simp [member])
    have tailBound : start + (choice.val + 1) + 7 * credits.length ≤ 952 := by
      simp only [List.length_cons] at bounded; omega
    obtain ⟨added,low,high,exactTail⟩ := ih (start + (choice.val + 1)) tailBound tailSupport
    refine ⟨choice.val + 1 + added, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.foldl_cons, creditEq]
      rw [NaturalArithmetic.native_add_small start (choice.val + 1) (by omega) (by omega), exactTail]
      simp only [Nat.add_assoc]

theorem source_136_credits_suffice (credits : List UInt64) (count : credits.length = 136)
    (supported : ∀ value ∈ credits, value ∈ LumpSource.nonmeatyOptions) :
    ∃ total : Nat, 136 ≤ total ∧ total ≤ 952 ∧
      credits.foldl Number.add Number.positiveZero = Number.ofNat total := by
  obtain ⟨total,low,high,value⟩ := source_credits_exact credits 0 (by omega) supported
  refine ⟨total, by omega, by omega, ?_⟩
  change credits.foldl Number.add (Number.ofNat 0) = Number.ofNat total
  simpa only [Nat.zero_add] using value

theorem first_temple_leaves_remaining_level_cost (total : Nat) (enough : 136 ≤ total) :
    levelCost 12 + levelCost 10 + 2 * levelCost 1 = 135 ∧
      135 ≤ total - 1 := by
  constructor
  · decide +kernel
  · omega

end CookieClicker.JavaScript.LumpPrefix

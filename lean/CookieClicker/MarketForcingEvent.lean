import CookieClicker.MarketRecurrence

/-! Finite IID53 draw words used by the native market forcing event.
The words depend on the pre-tick mode and aura branch. They describe a positive
probability event conditional on state, not information or controls given to a
trading policy. Source interpretation of the draw order is tested separately.
-/
namespace CookieClicker.FullGame.MarketForcingEvent

open UniformRandom MarketRecurrence

def zero : Draw 53 := ⟨0, by decide +kernel⟩
def half : Draw 53 := ⟨4503599627370496, by decide +kernel⟩
def halfPlus : Draw 53 := ⟨4503599627370497, by decide +kernel⟩
def highest : Draw 53 := ⟨9007199254740991, by decide +kernel⟩
def modeAtom : Direction → Draw 53
  | .rise => ⟨6192449487634432, by decide +kernel⟩
  | .fall => ⟨7318349394477056, by decide +kernel⟩

def modeDraws : Mode → List (Draw 53)
  | .fastRise | .fastFall => [highest, highest]
  | _ => [highest]

def skippedOptional : Mode → List (Draw 53)
  | .chaotic | .fastRise => [half, half]
  | .fastFall => [half]
  | _ => []

def goodWord (direction : Direction) (mode : Mode) (extraAuraBranch : Bool) : List (Draw 53) :=
  modeDraws mode ++ [zero, zero, zero, zero] ++
  (match direction with | .rise => [highest, highest] | .fall => [zero, zero]) ++
  [half, half, half] ++ skippedOptional mode ++ [zero, highest] ++
  (if extraAuraBranch then [highest] else []) ++ [highest, modeAtom direction]

def tickWord (direction : Direction) (modes : List Mode) (extraAuraBranch : Bool) : List (Draw 53) :=
  [half, zero, halfPlus] ++ modes.flatMap (fun mode => goodWord direction mode extraAuraBranch)

theorem mode_atom_index (direction : Direction) :
    (modeAtom direction).val * 8 / size 53 = (match direction with | .rise => 5 | .fall => 6) := by
  cases direction <;> decide +kernel

theorem atom_values : value highest = MarketRecurrence.top ∧
    2 * (value halfPlus - 1 / 2) = globalShock ∧ value half = 1 / 2 := by
  decide +kernel

theorem good_word_length (direction : Direction) (mode : Mode) (extraAuraBranch : Bool) :
    (goodWord direction mode extraAuraBranch).length ≤ 18 := by
  cases direction <;> cases mode <;> cases extraAuraBranch <;> decide +kernel

theorem flattened_length_bound (direction : Direction) (modes : List Mode) (extraAuraBranch : Bool) :
    (modes.flatMap (fun mode => goodWord direction mode extraAuraBranch)).length ≤ 18 * modes.length := by
  induction modes with
  | nil => simp
  | cons mode rest ih =>
    have head := good_word_length direction mode extraAuraBranch
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem tick_word_length (direction : Direction) (modes : List Mode) (extraAuraBranch : Bool)
    (goods : modes.length = 18) : (tickWord direction modes extraAuraBranch).length ≤ 327 := by
  have bound := flattened_length_bound direction modes extraAuraBranch
  simp only [tickWord, List.length_append, List.length_cons, List.length_nil]
  omega

def atomMass : Rat := 1 / (size 53 : Rat)

theorem singleton_mass (draw : Draw 53) : eventMass 53 (interval draw.val (draw.val + 1)) = atomMass := by
  rw [interval_mass _ _ _ (by omega) (by have h := draw.isLt; omega)]
  simp only [Nat.add_sub_cancel_left, atomMass, Rat.natCast_ofNat]

def atomPower : Nat → Rat
  | 0 => 1
  | n + 1 => atomMass * atomPower n

def wordMass (word : List (Draw 53)) : Rat :=
  cylinderMass 53 (word.map (fun draw => interval draw.val (draw.val + 1)))

theorem word_mass_exact (word : List (Draw 53)) : wordMass word = atomPower word.length := by
  induction word with
  | nil => rfl
  | cons draw rest ih =>
    simp only [wordMass, List.map_cons, cylinderMass, singleton_mass, List.length_cons, atomPower]
    exact congrArg (fun x => atomMass * x) ih

theorem atom_mass_bounds : 0 < atomMass ∧ atomMass ≤ 1 := by decide +kernel

theorem atom_power_positive (n : Nat) : 0 < atomPower n := by
  induction n with
  | zero => decide +kernel
  | succ n ih => exact Rat.mul_pos atom_mass_bounds.1 ih

theorem atom_power_decreasing {earlier later : Nat} (ordered : earlier ≤ later) :
    atomPower later ≤ atomPower earlier := by
  induction later generalizing earlier with
  | zero =>
    have same : earlier = 0 := by omega
    subst earlier
    exact Rat.le_refl
  | succ later ih =>
    by_cases same : earlier = later + 1
    · subst earlier; exact Rat.le_refl
    · have step := Rat.mul_le_mul_of_nonneg_right atom_mass_bounds.2 (Rat.le_of_lt (atom_power_positive later))
      simp only [Rat.one_mul] at step
      exact Rat.le_trans step (ih (by omega))

theorem tick_word_uniform_lower (direction : Direction) (modes : List Mode) (extraAuraBranch : Bool)
    (goods : modes.length = 18) :
    atomPower 327 ≤ wordMass (tickWord direction modes extraAuraBranch) := by
  rw [word_mass_exact]
  exact atom_power_decreasing (tick_word_length direction modes extraAuraBranch goods)

theorem block_word_positive (word : List (Draw 53)) (bounded : word.length ≤ 337464) :
    0 < atomPower 337464 ∧ atomPower 337464 ≤ wordMass word := by
  rw [word_mass_exact]
  exact ⟨atom_power_positive _, atom_power_decreasing bounded⟩

theorem block_bit_budget : (53 * 337464 : Nat) = 17885592 := by decide +kernel

end CookieClicker.FullGame.MarketForcingEvent

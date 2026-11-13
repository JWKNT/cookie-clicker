import CookieClicker.JavaScriptExecution

/-! A finite successful source branch has a positive probability under IID53.
The supplied word describes an environment event. It is not a policy input or
an action which selects future randomness. Uniform retry bounds still require
a common draw bound and a source invariant for all retry entry states.
-/
namespace CookieClicker.JavaScript.Execution

open CookieClicker.FullGame UniformRandom AdaptiveHandPicked

/-- A finite word records exactly the free draws on one source-prefix branch. -/
inductive Cylinder {X : Type} : RandomProgram X → List Draw → X → Prop where
  | returned (result : X) : Cylinder (.pure result) [] result
  | draw {next : Draw → RandomProgram X} {word : List Draw} {result : X}
      (chosen : Draw) (after : Cylinder (next chosen) word result) :
      Cylinder (.draw next) (chosen :: word) result

def wordMass : Nat → Rat
  | 0 => 1
  | draws + 1 => wordMass draws / (size 53 : Rat)

theorem wordMass_positive (draws : Nat) : 0 < wordMass draws := by
  induction draws with
  | zero => decide
  | succ draws ih =>
    have positive : (0 : Rat) < (size 53 : Rat) := Rat.natCast_pos.mpr (size_positive 53)
    exact (Rat.lt_div_iff positive).mpr (by simpa [Rat.zero_mul] using ih)

private theorem sum_nonnegative (f : Nat → Rat) (count : Nat)
    (nonnegative : ∀ i, i < count → 0 ≤ f i) : 0 ≤ sumRange f count := by
  have bound := sum_mono (fun _ => 0) f count nonnegative
  simpa [constant_sum, Rat.mul_zero] using bound

private theorem sum_member (f : Nat → Rat) (count index : Nat)
    (member : index < count) (nonnegative : ∀ i, i < count → 0 ≤ f i) :
    f index ≤ sumRange f count := by
  induction count with
  | zero => omega
  | succ count ih =>
    have prefixPositive := sum_nonnegative f count (fun i hi => nonnegative i (by omega))
    have lastPositive := nonnegative count (by omega)
    by_cases last : index = count
    · subst index
      simp only [sumRange]
      grind
    · have before := ih (by omega) (fun i hi => nonnegative i (by omega))
      simp only [sumRange]
      grind

private theorem divide_mono (a b : Rat) (ordered : a ≤ b) :
    a / (size 53 : Rat) ≤ b / (size 53 : Rat) := by
  have positive : (0 : Rat) < (size 53 : Rat) := Rat.natCast_pos.mpr (size_positive 53)
  apply Rat.le_of_mul_le_mul_right (c := (size 53 : Rat)) _ positive
  simpa only [Rat.div_mul_cancel (by grind : (size 53 : Rat) ≠ 0)] using ordered

private theorem mean_member (f : Nat → Rat) (chosen : Draw)
    (nonnegative : ∀ i, i < size 53 → 0 ≤ f i) :
    f chosen.val / (size 53 : Rat) ≤ mean 53 f :=
  divide_mono _ _ (sum_member f _ chosen.val chosen.isLt nonnegative)

def eventValue {X : Type} (event : X → Bool) (result : X) : Rat :=
  if event result then 1 else 0

theorem eventValue_bounds {X : Type} (event : X → Bool) (result : X) :
    0 ≤ eventValue event result ∧ eventValue event result ≤ 1 := by
  unfold eventValue
  split <;> decide

/-- This lower bound retains all other branches. Their nonnegative probability
contribution cannot reduce the mass of the supplied successful finite word. -/
theorem cylinder_event_lower {X : Type} {program : RandomProgram X}
    {word : List Draw} {result : X} (cylinder : Cylinder program word result)
    (event : X → Bool) (success : event result = true) :
    wordMass word.length ≤ program.expect (eventValue event) := by
  induction cylinder with
  | returned result => simp [wordMass, HittingTime.Program.expect, eventValue, success]
  | @draw next word result chosen after ih =>
    have represented : rangeDraw chosen.val = chosen := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt chosen.isLt
    have nonnegative : ∀ i, i < size 53 →
        0 ≤ (next (rangeDraw i)).expect (eventValue event) := by
      intro i _
      exact (HittingTime.program_bounds _ _ 0 1 (eventValue_bounds event)).1
    have oneBranch := mean_member
      (fun i => (next (rangeDraw i)).expect (eventValue event)) chosen nonnegative
    rw [represented] at oneBranch
    exact Rat.le_trans (divide_mono _ _ (ih success)) oneBranch

theorem cylinder_event_positive {X : Type} {program : RandomProgram X}
    {word : List Draw} {result : X} (cylinder : Cylinder program word result)
    (event : X → Bool) (success : event result = true) :
    0 < program.expect (eventValue event) := by
  have positive := wordMass_positive word.length
  have lower := cylinder_event_lower cylinder event success
  grind

theorem wordMass_denominator (draws : Nat) :
    wordMass draws * ((size 53 ^ draws : Nat) : Rat) = 1 := by
  induction draws with
  | zero => simp [wordMass, Rat.mul_one]
  | succ draws ih =>
    have positive : (0 : Rat) < (size 53 : Rat) := Rat.natCast_pos.mpr (size_positive 53)
    have cancelled := Rat.div_mul_cancel (a := wordMass draws)
      (b := (size 53 : Rat)) (by grind)
    simp only [wordMass, Nat.pow_succ, Rat.natCast_mul]
    calc
      wordMass draws / (size 53 : Rat) * ((size 53 ^ draws : Nat) * (size 53 : Rat)) =
          (wordMass draws / (size 53 : Rat) * (size 53 : Rat)) * (size 53 ^ draws : Nat) := by grind
      _ = 1 := by rw [cancelled, ih]

theorem wordMass_exact (draws : Nat) :
    wordMass draws = 1 / ((2 ^ (53 * draws) : Nat) : Rat) := by
  have powers : size 53 ^ draws = 2 ^ (53 * draws) := (Nat.pow_mul 2 53 draws).symm
  have multiplied := wordMass_denominator draws
  rw [powers] at multiplied
  have positive : (0 : Rat) < ((2 ^ (53 * draws) : Nat) : Rat) :=
    Rat.natCast_pos.mpr (Nat.pow_pos (by decide))
  have cancelled := Rat.div_mul_cancel (a := 1)
    (b := ((2 ^ (53 * draws) : Nat) : Rat)) (by grind)
  grind

/-- The theorem applies to the concrete interpreter prefix, not just to a
separately stipulated transition probability. A full native trace must still
be represented as this Cylinder before a diagnostic tape is a Lean witness. -/
theorem source_cylinder_event_lower (fuel : Nat) (state : Browser.State)
    (word : List Draw) (outcome : Outcome)
    (cylinder : Cylinder (runPrefix fuel state) word outcome)
    (event : Outcome → Bool) (success : event outcome = true) :
    wordMass word.length ≤ (runPrefix fuel state).expect (eventValue event) :=
  cylinder_event_lower cylinder event success

end CookieClicker.JavaScript.Execution

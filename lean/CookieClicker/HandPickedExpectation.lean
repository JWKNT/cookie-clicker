import CookieClicker.HandPicked

/-! Conditional expected hitting-time lower bound for the required Hand-picked goal.
The rational survival values are certified lower bounds for P(completion time > t)
in integer game-clock milliseconds, including paths that never complete. They
may equal the true tails when those tails are rational. An explicit finite-sum
soundness bridge transfers the certificate to an arbitrary expectation lower cut;
the true tails need not be rational. This is not a sum of action costs.
The source clock/reset and conditional-fairness correspondence remain explicit
hypotheses. No full-game optimal strategy or probability law is asserted.
-/
namespace CookieClicker.FullGame.HandPickedExpectation

/-- Rational lower-tail envelope, not a restriction that actual probabilities be rational. -/
structure RationalTailCertificate where
  survival : Nat → Rat
  nonnegative : ∀ t, 0 ≤ survival t
  at_most_one : ∀ t, survival t ≤ 1
  decreasing : ∀ a b, a ≤ b → survival b ≤ survival a

def sumFrom (f : Nat → Rat) (start : Nat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumFrom f start n + f (start + n)

/-- Lower cut obtained from all finite sums of the rational tail certificate. -/
def ExpectedAbove (law : RationalTailCertificate) (bound : Rat) : Prop :=
  ∃ horizon, bound < sumFrom law.survival 0 horizon

/-- The certificate proves every strict rational lower bound below this value. -/
def ExpectedAtLeast (law : RationalTailCertificate) (bound : Rat) : Prop :=
  ∀ lower : Rat, lower < bound → ExpectedAbove law lower

/-- Every finite certificate sum gives valid strict bounds on the actual expectation.
`actual q` means q is strictly below that expectation. Its true survival values
can be irrational. This source/probability correspondence must be established
separately; no measure-theoretic engine semantics is asserted here.
-/
def FiniteTailsSound (law : RationalTailCertificate) (actual : Rat → Prop) : Prop :=
  ∀ horizon lower, lower < sumFrom law.survival 0 horizon → actual lower

theorem certificate_cut_refines {law : RationalTailCertificate} {actual : Rat → Prop}
    (sound : FiniteTailsSound law actual) {lower : Rat}
    (certified : ExpectedAbove law lower) : actual lower := by
  obtain ⟨horizon, below⟩ := certified
  exact sound horizon lower below

theorem certificate_bound_transfers {law : RationalTailCertificate} {actual : Rat → Prop}
    (sound : FiniteTailsSound law actual) {bound : Rat}
    (certified : ExpectedAtLeast law bound) :
    ∀ lower, lower < bound → actual lower := by
  intro lower below
  exact certificate_cut_refines sound (certified lower below)

def halfSurvival : Nat → Rat
  | 0 => 1
  | n + 1 => halfSurvival n / 2

/-- Stochastic and native-clock obligations for a rational tail certificate.
The attempt sequence bounds P(N > n), where N is the first successful attempt
index. Histories with no next attempt have N = infinity and remain unsuccessful.
-/
structure HandPickedBridge (law : RationalTailCertificate) (spacing : Nat) where
  attemptSurvival : Nat → Rat
  initially_missing : attemptSurvival 0 = 1
  conditional_failure : ∀ n, attemptSurvival n / 2 ≤ attemptSurvival (n + 1)
  clock_and_required_goal : ∀ n k, k < spacing →
    attemptSurvival n ≤ law.survival (n * spacing + k)

private theorem half_mono {a b : Rat} (h : a ≤ b) : a / 2 ≤ b / 2 := by
  apply Rat.le_of_mul_le_mul_right (c := 2) _ (by decide +kernel)
  rw [Rat.div_mul_cancel (by decide +kernel), Rat.div_mul_cancel (by decide +kernel)]
  exact h

private theorem half_nonnegative (n : Nat) : 0 ≤ halfSurvival n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have h := half_mono ih
    have zero : (0 : Rat) / 2 = 0 := by decide +kernel
    simpa [halfSurvival, zero] using h

theorem attempt_survival_lower {law : RationalTailCertificate} {spacing : Nat}
    (bridge : HandPickedBridge law spacing) (n : Nat) :
    halfSurvival n ≤ bridge.attemptSurvival n := by
  induction n with
  | zero => simp [halfSurvival, bridge.initially_missing]
  | succ n ih => exact Rat.le_trans (half_mono ih) (bridge.conditional_failure n)

private theorem sumFrom_add (f : Nat → Rat) (start a b : Nat) :
    sumFrom f start (a + b) = sumFrom f start a + sumFrom f (start + a) b := by
  induction b with
  | zero => simp [sumFrom, Rat.add_zero]
  | succ b ih =>
    change sumFrom f start (a + b) + f (start + (a + b)) =
      sumFrom f start a + (sumFrom f (start + a) b + f ((start + a) + b))
    rw [ih]
    rw [show start + (a + b) = start + a + b from by omega]
    exact Rat.add_assoc _ _ _

private theorem sumFrom_lower (f : Nat → Rat) (start length : Nat) (lower : Rat)
    (bounded : ∀ k, k < length → lower ≤ f (start + k)) :
    (length : Rat) * lower ≤ sumFrom f start length := by
  induction length with
  | zero => simp [sumFrom, Rat.zero_mul]
  | succ n ih =>
    have hp := ih (fun k hk => bounded k (by omega))
    have hl := bounded n (by omega)
    simp only [sumFrom, Rat.natCast_add, Rat.natCast_ofNat]
    have expand : ((n : Rat) + 1) * lower = (n : Rat) * lower + lower := by grind
    rw [expand]
    grind

/-- A pointwise larger rational envelope preserves all certified expectation bounds. -/
theorem certificate_monotone {lower upper : RationalTailCertificate}
    (pointwise : ∀ t, lower.survival t ≤ upper.survival t) {bound : Rat}
    (certified : ExpectedAbove lower bound) : ExpectedAbove upper bound := by
  obtain ⟨horizon, below⟩ := certified
  have sums : ∀ n, sumFrom lower.survival 0 n ≤ sumFrom upper.survival 0 n := by
    intro n
    induction n with
    | zero => exact Rat.le_refl
    | succ n ih =>
      have step := pointwise (0 + n)
      simp only [sumFrom]
      grind
  have larger := sums horizon
  exact ⟨horizon, by grind⟩

/-- Every finite set of attempt intervals gives a rigorous expected-time lower bound. -/
theorem finite_tail_lower_bound {law : RationalTailCertificate} {spacing : Nat}
    (bridge : HandPickedBridge law spacing) (attempts : Nat) :
    (spacing : Rat) * sumFrom halfSurvival 0 attempts ≤
      sumFrom law.survival 0 (attempts * spacing) := by
  induction attempts with
  | zero => simp [sumFrom, Rat.mul_zero]
  | succ n ih =>
    have block := sumFrom_lower law.survival (n * spacing) spacing (halfSurvival n)
      (fun k hk => Rat.le_trans (attempt_survival_lower bridge n) (bridge.clock_and_required_goal n k hk))
    change (spacing : Rat) * (sumFrom halfSurvival 0 n + halfSurvival (0 + n)) ≤
      sumFrom law.survival 0 ((n + 1) * spacing)
    rw [Nat.add_mul, Nat.one_mul, sumFrom_add law.survival 0 (n * spacing) spacing]
    simp only [Nat.zero_add]
    have expand : (spacing : Rat) * (sumFrom halfSurvival 0 n + halfSurvival n) =
        (spacing : Rat) * sumFrom halfSurvival 0 n + (spacing : Rat) * halfSurvival n := by grind
    rw [expand]
    grind

private theorem geometric_sum (n : Nat) :
    sumFrom halfSurvival 0 n = 2 * (1 - halfSurvival n) := by
  induction n with
  | zero => simp [sumFrom, halfSurvival]; decide +kernel
  | succ n ih =>
    have cancel : halfSurvival n / 2 * 2 = halfSurvival n :=
      Rat.div_mul_cancel (by decide +kernel)
    simp only [sumFrom, Nat.zero_add, halfSurvival]
    rw [ih]
    grind

private theorem exists_nat_above (q : Rat) : ∃ n : Nat, q < (n : Rat) := by
  let z := q.ceil + 1
  have hceil : q ≤ (q.ceil : Rat) := Rat.le_ceil
  have hz : (q.ceil : Rat) < (z : Rat) := Rat.intCast_lt_intCast.mpr (by dsimp [z]; omega)
  have hnat : (z : Rat) ≤ (z.toNat : Rat) := Rat.intCast_le_intCast.mpr (Int.self_le_toNat z)
  exact ⟨z.toNat, by grind⟩

private theorem one_le_power_gap (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem geometric_reciprocal (n : Nat) : halfSurvival n * ((2 ^ n : Nat) : Rat) = 1 := by
  induction n with
  | zero => simp [halfSurvival]
  | succ n ih =>
    have cancel : halfSurvival n / 2 * 2 = halfSurvival n := Rat.div_mul_cancel (by decide +kernel)
    simp only [halfSurvival, Nat.pow_succ, Rat.natCast_mul, Rat.natCast_ofNat]
    grind

private theorem geometric_times_n (n : Nat) : halfSurvival n * ((n + 1 : Nat) : Rat) ≤ 1 := by
  have power := Rat.natCast_le_natCast.mpr (one_le_power_gap n)
  have multiplied := Rat.mul_le_mul_of_nonneg_left power (half_nonnegative n)
  rw [geometric_reciprocal] at multiplied
  exact multiplied

private theorem geometric_arbitrarily_small (epsilon : Rat) (positive : 0 < epsilon) :
    ∃ n, halfSurvival n < epsilon := by
  obtain ⟨n, above⟩ := exists_nat_above (1 / epsilon)
  have large : 1 < (n : Rat) * epsilon := (Rat.div_lt_iff positive).mp above
  have larger : 1 < ((n + 1 : Nat) : Rat) * epsilon := by
    rw [Rat.natCast_add, Rat.natCast_ofNat]
    have expand : ((n : Rat) + 1) * epsilon = (n : Rat) * epsilon + epsilon := by grind
    rw [expand]
    grind
  refine ⟨n, ?_⟩
  apply Rat.not_le.mp
  intro too_large
  have multiplied := Rat.mul_le_mul_of_nonneg_right too_large (Rat.natCast_nonneg (a := n + 1))
  have cap := geometric_times_n n
  have commute : ((n + 1 : Nat) : Rat) * epsilon = epsilon * ((n + 1 : Nat) : Rat) := Rat.mul_comm _ _
  grind

/-- The rational certificate proves an unrestricted lower bound of twice the spacing. -/
theorem expected_hitting_time_lower_bound {law : RationalTailCertificate} {spacing : Nat}
    (bridge : HandPickedBridge law spacing) (positive : 0 < spacing) :
    ExpectedAtLeast law (2 * (spacing : Rat)) := by
  intro lower below
  have denominator_positive : (0 : Rat) < 2 * (spacing : Rat) := by
    have hp := Rat.natCast_pos.mpr positive
    grind
  let epsilon := (2 * (spacing : Rat) - lower) / (2 * (spacing : Rat))
  have epsilon_positive : 0 < epsilon := by
    apply (Rat.lt_div_iff denominator_positive).mpr
    simp only [Rat.zero_mul]
    grind
  obtain ⟨n, small⟩ := geometric_arbitrarily_small epsilon epsilon_positive
  have product_small := (Rat.lt_div_iff denominator_positive).mp small
  have bound := finite_tail_lower_bound bridge n
  rw [geometric_sum] at bound
  have expand : (spacing : Rat) * (2 * (1 - halfSurvival n)) =
      2 * (spacing : Rat) - halfSurvival n * (2 * (spacing : Rat)) := by grind
  rw [expand] at bound
  exact ⟨n * spacing, by grind⟩

/-- The source-audited spacing gives this conditional rational-tail bound. -/
theorem conditional_hand_picked_bound {law : RationalTailCertificate}
    (bridge : HandPickedBridge law 64436019) : ExpectedAtLeast law 128872038 := by
  have h := expected_hitting_time_lower_bound bridge (by decide)
  have value : (2 : Rat) * (64436019 : Nat) = 128872038 := by decide +kernel
  simpa only [value] using h

/-- The same numerical lower bound transfers without rational actual-tail assumptions. -/
theorem certified_hand_picked_bound {law : RationalTailCertificate} {actual : Rat → Prop}
    (sound : FiniteTailsSound law actual) (bridge : HandPickedBridge law 64436019) :
    ∀ lower, lower < 128872038 → actual lower :=
  certificate_bound_transfers sound (conditional_hand_picked_bound bridge)

/-- A positive probability of never completing gives infinite expected hitting time. -/
theorem positive_noncompletion_mass_infinite {law : RationalTailCertificate} {mass : Rat}
    (positive : 0 < mass) (persists : ∀ t, mass ≤ law.survival t) :
    ∀ bound : Rat, ExpectedAbove law bound := by
  intro bound
  obtain ⟨n, above⟩ := exists_nat_above (bound / mass)
  have large := (Rat.div_lt_iff positive).mp above
  have lower := sumFrom_lower law.survival 0 n mass (fun k _ => persists (0 + k))
  exact ⟨n, by grind⟩

/-- An outcome that never completes has survival probability one at every time. -/
def neverCompletes : RationalTailCertificate where
  survival := fun _ => 1
  nonnegative := fun _ => by decide +kernel
  at_most_one := fun _ => Rat.le_refl
  decreasing := fun _ _ _ => Rat.le_refl

private theorem constant_one_sum (n : Nat) : sumFrom (fun _ => (1 : Rat)) 0 n = (n : Rat) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFrom, ih, Rat.natCast_add]

/-- Unsuccessful paths have infinite hitting time, rather than zero action cost. -/
theorem never_completion_has_infinite_expectation :
    ∀ bound : Rat, ExpectedAbove neverCompletes bound := by
  intro bound
  obtain ⟨n, above⟩ := exists_nat_above bound
  exact ⟨n, by simpa only [neverCompletes, constant_one_sum] using above⟩

end CookieClicker.FullGame.HandPickedExpectation

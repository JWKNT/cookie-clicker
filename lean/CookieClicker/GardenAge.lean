import CookieClicker.JavaScriptNumber

/-! Finite age projection for the pinned Garden. Ages use exact quarter units.
The native cap constants are checked below. The growth argument is a natural
number because the source uses randomFloor; its full source execution and the
finite arithmetic bounds still need separate refinement. This module proves
the projection and current-save truncation laws, not full-game reachability or
equality of rendered tooltip observations. -/
namespace CookieClicker.FullGame.GardenAge

inductive Kind where
  | mortal | elderwort | everdaisy
  deriving DecidableEq, Repr

def immortal : Kind → Bool
  | .mortal => false
  | _ => true

def maturity (kind : Kind) (seedless : Bool) : Nat :=
  match kind, seedless with
  | .elderwort, false => 360
  | .elderwort, true => 342
  | .everdaisy, false => 300
  | .everdaisy, true => 285
  | .mortal, _ => 0

def cap (kind : Kind) (seedless : Bool) : Nat := maturity kind seedless + 4

/-- The two fractional caps are the only noninteger ages in this domain.
Both require the persistent Seedless achievement. -/
def Valid (kind : Kind) (seedless : Bool) (age : Nat) : Prop :=
  age < 400 ∧ (age % 4 = 0 ∨
    (seedless = true ∧
      ((kind = .elderwort ∧ age = 346) ∨ (kind = .everdaisy ∧ age = 289))))

instance (kind : Kind) (seedless : Bool) (age : Nat) : Decidable (Valid kind seedless age) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whole native age after growth, immortal clamp, or mortal death. Any native
onDie replacement is a separate age-zero transition. -/
def grow (kind : Kind) (seedless : Bool) (age increment : Nat) : Nat :=
  let next := age + 4 * increment
  if immortal kind then min (cap kind seedless) next
  else if next < 400 then next else 0

def saved (age : Nat) : Nat := 4 * (age / 4)

inductive EconomicAge where
  | integer (age : Nat)
  | matureImmortal
  deriving DecidableEq, Repr

def project (kind : Kind) (seedless : Bool) (age : Nat) : EconomicAge :=
  if immortal kind && decide (maturity kind seedless ≤ age) then .matureImmortal
  else .integer (age / 4)

theorem zero_valid (kind : Kind) (seedless : Bool) : Valid kind seedless 0 := by
  exact ⟨by decide, Or.inl rfl⟩

theorem cap_valid (kind : Kind) (seedless : Bool) (isImmortal : immortal kind = true) :
    Valid kind seedless (cap kind seedless) := by
  cases kind <;> cases seedless <;> simp_all [immortal, cap, maturity, Valid]

theorem fractional_age_mature (kind : Kind) (seedless : Bool) (age : Nat)
    (valid : Valid kind seedless age) (fractional : age % 4 ≠ 0) :
    immortal kind = true ∧ maturity kind seedless ≤ saved age ∧
      maturity kind seedless ≤ age := by
  rcases valid.2 with integer | ⟨rfl, alternatives⟩
  · contradiction
  · rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide

theorem seedless_preserves_valid (kind : Kind) (age : Nat)
    (valid : Valid kind false age) : Valid kind true age := by
  refine ⟨valid.1, Or.inl ?_⟩
  rcases valid.2 with integer | ⟨impossible, _⟩
  · exact integer
  · cases impossible

theorem grow_valid (kind : Kind) (seedless : Bool) (age increment : Nat)
    (valid : Valid kind seedless age) : Valid kind seedless (grow kind seedless age increment) := by
  unfold grow
  by_cases isImmortal : immortal kind = true
  · rw [if_pos isImmortal]
    by_cases limited : cap kind seedless ≤ age + 4 * increment
    · rw [Nat.min_eq_left limited]
      exact cap_valid kind seedless isImmortal
    · rw [Nat.min_eq_right (by omega)]
      have capBound := (cap_valid kind seedless isImmortal).1
      refine ⟨by omega, ?_⟩
      rcases valid.2 with integer | ⟨rfl, alternatives⟩
      · exact Or.inl (by omega)
      · rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [cap, maturity] at limited <;> omega
  · rw [if_neg isImmortal]
    split
    · next below =>
        refine ⟨below, Or.inl ?_⟩
        rcases valid.2 with integer | ⟨_, alternatives⟩
        · omega
        · rcases alternatives with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [immortal] at isImmortal
    · exact zero_valid kind seedless

theorem saved_valid (kind : Kind) (seedless : Bool) (age : Nat)
    (valid : Valid kind seedless age) : Valid kind seedless (saved age) := by
  have bound := valid.1
  unfold saved
  exact ⟨by omega, Or.inl (by omega)⟩

theorem save_preserves_projection (kind : Kind) (seedless : Bool) (age : Nat)
    (valid : Valid kind seedless age) :
    project kind seedless (saved age) = project kind seedless age := by
  by_cases integer : age % 4 = 0
  · have same : saved age = age := by unfold saved; omega
    rw [same]
  · obtain ⟨isImmortal, savedMature, ageMature⟩ :=
      fractional_age_mature kind seedless age valid integer
    simp [project, isImmortal, savedMature, ageMature]

theorem mature_stays_mature (kind : Kind) (seedless : Bool) (age increment : Nat)
    (isImmortal : immortal kind = true) (isMature : maturity kind seedless ≤ age) :
    project kind seedless (grow kind seedless age increment) = .matureImmortal := by
  have after : maturity kind seedless ≤ grow kind seedless age increment := by
    simp only [grow, isImmortal, ↓reduceIte, cap]
    omega
  simp [project, isImmortal, after]

theorem nonmature_integral (kind : Kind) (seedless : Bool) (age : Nat)
    (valid : Valid kind seedless age)
    (notMature : project kind seedless age ≠ .matureImmortal) : age % 4 = 0 := by
  by_cases integer : age % 4 = 0
  · exact integer
  · obtain ⟨isImmortal, _, isMature⟩ := fractional_age_mature kind seedless age valid integer
    simp [project, isImmortal, isMature] at notMature

/-- Equal economic ages remain equal after the same integer growth outcome.
No distributional independence or hidden age observation is assumed. -/
theorem growth_projection_congruent (kind : Kind) (seedless : Bool) (left right increment : Nat)
    (leftValid : Valid kind seedless left) (rightValid : Valid kind seedless right)
    (same : project kind seedless left = project kind seedless right) :
    project kind seedless (grow kind seedless left increment) =
      project kind seedless (grow kind seedless right increment) := by
  by_cases matureLeft : project kind seedless left = .matureImmortal
  · have matureRight : project kind seedless right = .matureImmortal := same ▸ matureLeft
    have decode : ∀ age, project kind seedless age = .matureImmortal →
        immortal kind = true ∧ maturity kind seedless ≤ age := by
      intro age equal
      unfold project at equal
      split at equal
      · next condition => simpa using condition
      · contradiction
    obtain ⟨immortalLeft, ageLeft⟩ := decode left matureLeft
    obtain ⟨immortalRight, ageRight⟩ := decode right matureRight
    rw [mature_stays_mature kind seedless left increment immortalLeft ageLeft,
      mature_stays_mature kind seedless right increment immortalRight ageRight]
  · have matureRight : project kind seedless right ≠ .matureImmortal := by
      intro wrong; exact matureLeft (same.trans wrong)
    have leftIntegral := nonmature_integral kind seedless left leftValid matureLeft
    have rightIntegral := nonmature_integral kind seedless right rightValid matureRight
    have leftProjection : project kind seedless left = .integer (left / 4) := by
      unfold project at matureLeft ⊢; split <;> simp_all
    have rightProjection : project kind seedless right = .integer (right / 4) := by
      unfold project at matureRight ⊢; split <;> simp_all
    rw [leftProjection, rightProjection] at same
    have values : left / 4 = right / 4 := EconomicAge.integer.inj same
    have equal : left = right := by omega
    rw [equal]

def nativeMaturity (kind : Kind) (seedless : Bool) : UInt64 :=
  JavaScript.Number.mul (JavaScript.Number.ofNat (if kind = .elderwort then 90 else 75))
    (if seedless then 4606732058837280358 else JavaScript.Number.one)

/-- These constants use the actual logical binary64 multiplication and addition.
They justify the quarter-unit caps, without a real-arithmetic replacement. -/
theorem native_immortal_constants :
    nativeMaturity .elderwort false = JavaScript.Number.ofNat 90 ∧
    nativeMaturity .everdaisy false = JavaScript.Number.ofNat 75 ∧
    nativeMaturity .elderwort true = JavaScript.Number.div (JavaScript.Number.ofNat 342) (JavaScript.Number.ofNat 4) ∧
    nativeMaturity .everdaisy true = JavaScript.Number.div (JavaScript.Number.ofNat 285) (JavaScript.Number.ofNat 4) ∧
    JavaScript.Number.add (nativeMaturity .elderwort true) JavaScript.Number.one =
      JavaScript.Number.div (JavaScript.Number.ofNat 346) (JavaScript.Number.ofNat 4) ∧
    JavaScript.Number.add (nativeMaturity .everdaisy true) JavaScript.Number.one =
      JavaScript.Number.div (JavaScript.Number.ofNat 289) (JavaScript.Number.ofNat 4) := by
  decide +kernel

def candidateAges : List Nat := (List.range 100).map (4 * ·) ++ [346, 289]

theorem valid_in_finite_domain (kind : Kind) (seedless : Bool) (age : Nat)
    (valid : Valid kind seedless age) : age ∈ candidateAges := by
  have bound := valid.1
  rcases valid.2 with integer | ⟨_, alternatives⟩
  · apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨age / 4, List.mem_range.mpr (by omega), ?_⟩
    omega
  · rcases alternatives with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [candidateAges]

theorem candidate_age_count : candidateAges.length = 102 := by decide +kernel

def nativeGrowthIndicator (quarterAge : Nat) : UInt64 :=
  let age := JavaScript.Number.div (JavaScript.Number.ofNat quarterAge) (JavaScript.Number.ofNat 4)
  JavaScript.Number.floor (JavaScript.Number.mul
    (JavaScript.Number.div age (JavaScript.Number.ofNat 100)) (JavaScript.Number.ofNat 256))

/-- The economic quotient must not be advertised as identical DOM output. -/
theorem elderwort_bar_distinguishes_truncation :
    nativeGrowthIndicator 346 = JavaScript.Number.ofNat 221 ∧
    nativeGrowthIndicator (saved 346) = JavaScript.Number.ofNat 220 := by
  decide +kernel

end CookieClicker.FullGame.GardenAge

import CookieClicker.AdaptiveHandPicked
import CookieClicker.PetRetry

/-! Completion-time semantics from finite execution prefixes.
The depth limit is taken at each fixed elapsed-time cap before the cap grows.
An unfinished prefix costs the whole cap, including a permanent zero-time stall.
Native seeded operations are deterministic transition code; only free draws use
`draw`. Programs here terminate. A native refinement must prove termination of
each represented callback or add internal divergence semantics without exposing
internal step counts to the policy. Full native refinement is still needed.
-/
namespace CookieClicker.FullGame.HittingTime
open UniformRandom AdaptiveHandPicked

/-- A finite native transition can consume an adaptive number of free draws. -/
inductive Program (Result : Type) where
  | pure (result : Result) : Program Result
  | draw (continuation : Draw 53 → Program Result) : Program Result

def Program.expect {Result : Type} (value : Result → Rat) : Program Result → Rat
  | .pure result => value result
  | .draw next => mean 53 (fun index => Program.expect value (next (rangeDraw index)))

def Program.bind {X Y : Type} (next : X → Program Y) : Program X → Program Y
  | .pure result => next result
  | .draw continuation => .draw (fun draw => Program.bind next (continuation draw))

/-- Every reachable leaf satisfies the supplied predicate. -/
def Program.All {X : Type} (predicate : X → Prop) : Program X → Prop
  | .pure result => predicate result
  | .draw continuation => ∀ draw, Program.All predicate (continuation draw)

/-- Every free outcome has positive mass. This relation records a finite
program leaf without exposing its draw indices to the controller. -/
inductive Program.Reaches {X : Type} (result : X) : Program X → Prop where
  | pure : Reaches result (.pure result)
  | draw {next : Draw 53 → Program X} (outcome : Draw 53)
      (after : Reaches result (next outcome)) : Reaches result (.draw next)

theorem program_all_reaches {X : Type} (program : Program X) (predicate : X → Prop)
    (all : program.All predicate) (result : X) (reaches : program.Reaches result) : predicate result := by
  induction reaches with
  | pure => exact all
  | draw outcome after ih => exact ih (all outcome)

/-- Composed native callbacks use one continuing free draw law. Deterministic
seeded computations do not create or resample an independent seeded outcome. -/
theorem program_bind_expect {X Y : Type} (program : Program X)
    (next : X → Program Y) (value : Y → Rat) :
    (program.bind next).expect value = program.expect (fun result => (next result).expect value) := by
  induction program with
  | pure result => rfl
  | draw continuation ih => simp only [Program.bind, Program.expect, ih]

theorem program_constant {Result : Type} (program : Program Result) (constant : Rat) :
    program.expect (fun _ => constant) = constant := by
  induction program with
  | pure result => rfl
  | draw next ih => simp only [Program.expect, ih, mean_constant]

theorem program_mono {Result : Type} (program : Program Result) (left right : Result → Rat)
    (ordered : ∀ result, left result ≤ right result) :
    program.expect left ≤ program.expect right := by
  induction program with
  | pure result => exact ordered result
  | draw next ih => exact mean_mono 53 _ _ (fun i _ => ih (rangeDraw i))

theorem program_bounds {Result : Type} (program : Program Result) (value : Result → Rat)
    (lower upper : Rat) (bounded : ∀ result, lower ≤ value result ∧ value result ≤ upper) :
    lower ≤ program.expect value ∧ program.expect value ≤ upper := by
  have lo := program_mono program (fun _ => lower) value (fun result => (bounded result).1)
  have hi := program_mono program value (fun _ => upper) (fun result => (bounded result).2)
  rw [program_constant] at lo hi
  exact ⟨lo, hi⟩

theorem program_support_lower {X : Type} (program : Program X) (value : X → Rat)
    (lower : Rat) (bounded : program.All (fun result => lower ≤ value result)) :
    lower ≤ program.expect value := by
  induction program with
  | pure result => exact bounded
  | draw continuation ih =>
    apply mean_lower
    intro index _
    exact ih (rangeDraw index) (bounded (rangeDraw index))

/-- Private state can contain seeds and pending engine data. The native source
must supply all checkpoints, including transient completion inside an action. -/
structure Environment (State Observation Action : Type) where
  complete : State → Bool
  elapsed : State → Rat
  nonnegative : ∀ state, 0 ≤ elapsed state
  observe : State → Observation
  legal : State → Action → Prop
  step : State → Action → Program State
  monotone : ∀ state action, (step state action).All (fun next => elapsed state ≤ elapsed next)

/-- Full public history is available, including information about hidden seeds
that the policy can infer. Actual private outcomes and state are not arguments. -/
abbrev PublicPolicy (Observation Action : Type) :=
  List (Observation × Action) → Observation → Action

def chosen {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (history : List (O × A)) (state : S) : A := policy history (env.observe state)

theorem public_history_noninterference {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (history : List (O × A)) (left right : S)
    (same : env.observe left = env.observe right) :
    chosen env policy history left = chosen env policy history right := by
  simp only [chosen, same]

/-- Reachability averages over one fixed hidden startup law. The startup draws
are not put in the public history, so a policy is not selected separately per seed. -/
inductive Reachable {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (initial : Program S) : List (O × A) → S → Prop where
  | initial {state : S} (leaf : initial.Reaches state) : Reachable env policy initial [] state
  | step {history : List (O × A)} {state next : S}
      (before : Reachable env policy initial history state)
      (unfinished : env.complete state = false)
      (leaf : (env.step state (chosen env policy history state)).Reaches next) :
      Reachable env policy initial (history ++ [(env.observe state, chosen env policy history state)]) next

/-- A future full-game certificate must restrict competitors to this property,
with the actual action restrictions supplied by the source-refined environment. -/
def Admissible {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (initial : Program S) : Prop :=
  ∀ history state, Reachable env policy initial history state →
    env.complete state = false → env.legal state (chosen env policy history state)


/-- A terminal startup needs no legal control: evaluation stops before choosing.
This also prevents terminal states with an empty action set from being excluded. -/
theorem completed_initial_admissible {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (initial : Program S)
    (completed : initial.All (fun state => env.complete state = true)) : Admissible env policy initial := by
  intro history state reachable unfinished
  have done : env.complete state = true := by
    clear unfinished
    induction reachable with
    | initial leaf => exact program_all_reaches initial _ completed _ leaf
    | step before wasUnfinished leaf ih => simp [ih] at wasUnfinished
  simp [done] at unfinished

/-- Finished prefixes supply capped elapsed time; unfinished prefixes supply
the cap. Prefix length is an approximation parameter, not a strategy limit. -/
def capped {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (horizon : Nat) : Nat → List (O × A) → S → Rat
  | depth, history, state =>
    if env.complete state then min (env.elapsed state) (horizon : Rat)
    else match depth with
      | 0 => (horizon : Rat)
      | depth + 1 =>
        let action := chosen env policy history state
        (env.step state action).expect (fun next =>
          capped env policy horizon depth (history ++ [(env.observe state, action)]) next)

theorem capped_bounds {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (horizon depth : Nat) (history : List (O × A)) (state : S) :
    0 ≤ capped env policy horizon depth history state ∧
      capped env policy horizon depth history state ≤ (horizon : Rat) := by
  induction depth generalizing history state with
  | zero =>
    simp only [capped]
    split
    · have h := env.nonnegative state
      have hH : (0 : Rat) ≤ (horizon : Rat) := Rat.natCast_nonneg
      constructor <;> grind
    · exact ⟨Rat.natCast_nonneg, Rat.le_refl⟩
  | succ depth ih =>
    simp only [capped]
    split
    · have h := env.nonnegative state
      have hH : (0 : Rat) ≤ (horizon : Rat) := Rat.natCast_nonneg
      constructor <;> grind
    · exact program_bounds _ _ _ _ (fun next => ih _ next)

/-- At a fixed cap, deeper prefixes can only remove unfinished penalties. -/
theorem capped_depth_decreasing {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (horizon depth : Nat) (history : List (O × A)) (state : S) :
    capped env policy horizon (depth + 1) history state ≤
      capped env policy horizon depth history state := by
  induction depth generalizing history state with
  | zero =>
    by_cases done : env.complete state = true
    · simp [capped, done]
    · simp only [capped, done, Bool.false_eq_true, ↓reduceIte]
      exact (program_bounds _ _ 0 horizon (fun next => capped_bounds env policy horizon 0
        (history ++ [(env.observe state, chosen env policy history state)]) next)).2
  | succ depth ih =>
    by_cases done : env.complete state = true
    · simp [capped, done]
    · simp only [capped, done, Bool.false_eq_true, ↓reduceIte]
      exact program_mono _ _ _ (fun next => ih _ next)

theorem capped_horizon_increasing {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) {lower upper : Nat} (ordered : lower ≤ upper)
    (depth : Nat) (history : List (O × A)) (state : S) :
    capped env policy lower depth history state ≤ capped env policy upper depth history state := by
  have cast : (lower : Rat) ≤ (upper : Rat) := Rat.natCast_le_natCast.mpr ordered
  induction depth generalizing history state with
  | zero => simp only [capped]; split <;> grind
  | succ depth ih =>
    simp only [capped]
    split
    · grind
    · exact program_mono _ _ _ (fun next => ih _ next)

/-- Rational lower cut of `sup horizon, inf depth, capped horizon depth`.
The positive margin expresses a strict bound on the infimum. A finite-depth
unfinished penalty cannot alone certify a bound on the expectation. -/
def Expected {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (state : S) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧
    ∀ depth, bound + margin ≤ capped env policy horizon depth [] state

/-- The initial private seed is sampled before the first public observation.
All policies in one comparison use this same startup program. -/
def initialCapped {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (initial : Program S) (horizon depth : Nat) : Rat :=
  initial.expect (fun state => capped env policy horizon depth [] state)

def InitialExpected {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A)
    (initial : Program S) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧
    ∀ depth, bound + margin ≤ initialCapped env policy initial horizon depth

theorem initial_capped_bounds {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (initial : Program S) (horizon depth : Nat) :
    0 ≤ initialCapped env policy initial horizon depth ∧
      initialCapped env policy initial horizon depth ≤ (horizon : Rat) :=
  program_bounds initial _ _ _ (fun state => capped_bounds env policy horizon depth [] state)

theorem initial_capped_depth_decreasing {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (initial : Program S) (horizon depth : Nat) :
    initialCapped env policy initial horizon (depth + 1) ≤
      initialCapped env policy initial horizon depth :=
  program_mono initial _ _ (fun state => capped_depth_decreasing env policy horizon depth [] state)

theorem initial_capped_horizon_increasing {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (initial : Program S) {lower upper : Nat} (ordered : lower ≤ upper)
    (depth : Nat) : initialCapped env policy initial lower depth ≤ initialCapped env policy initial upper depth :=
  program_mono initial _ _ (fun state => capped_horizon_increasing env policy ordered depth [] state)

theorem fixed_initial_expected {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (bound : Rat) :
    InitialExpected env policy (.pure state) bound ↔ Expected env policy state bound := Iff.rfl

/-- The startup averaging is performed before either limit. A pointwise choice
of a different policy for each concealed state is absent from this comparison. -/
theorem initial_prefix_dominance {S O A : Type} (env : Environment S O A)
    (fast slow : PublicPolicy O A) (initial : Program S)
    (dominates : ∀ horizon depth,
      initialCapped env fast initial horizon depth ≤ initialCapped env slow initial horizon depth) :
    ∀ bound, InitialExpected env fast initial bound → InitialExpected env slow initial bound := by
  rintro bound ⟨horizon, margin, positive, lower⟩
  exact ⟨horizon, margin, positive, fun depth => Rat.le_trans (lower depth) (dominates horizon depth)⟩

/-- Finite private randomization is sampled independently before the concealed
native startup law. Neither draw history is provided to the other sampler. -/
def mixedCapped {S O A : Type} (env : Environment S O A)
    (policies : Program (PublicPolicy O A)) (initial : Program S) (horizon depth : Nat) : Rat :=
  policies.expect (fun policy => initialCapped env policy initial horizon depth)

def MixedExpected {S O A : Type} (env : Environment S O A)
    (policies : Program (PublicPolicy O A)) (initial : Program S) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧
    ∀ depth, bound + margin ≤ mixedCapped env policies initial horizon depth

/-- All sampled deterministic policies are admissible under the same startup law. -/
def MixedAdmissible {S O A : Type} (env : Environment S O A)
    (policies : Program (PublicPolicy O A)) (initial : Program S) : Prop :=
  policies.All (fun policy => Admissible env policy initial)

/-- A shared finite-cap lower bound survives independent finite randomization.
The shared cap and bound are explicit: separate policy limits are not interchanged.
This does not cover an unrestricted infinite private random tape. -/
theorem uniform_mixture_lower_bound {S O A : Type} (env : Environment S O A)
    (policies : Program (PublicPolicy O A)) (initial : Program S) (horizon : Nat) (value : Rat)
    (lower : ∀ depth, policies.All (fun policy => value ≤ initialCapped env policy initial horizon depth))
    (bound : Rat) (strict : bound < value) : MixedExpected env policies initial bound := by
  refine ⟨horizon, value - bound, by grind, ?_⟩
  intro depth
  have h := program_support_lower policies _ value (lower depth)
  change _ ≤ policies.expect _
  grind

theorem pure_mixed_expected {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (initial : Program S) (bound : Rat) :
    MixedExpected env (.pure policy) initial bound ↔ InitialExpected env policy initial bound := Iff.rfl

theorem expected_downward {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (lower upper : Rat) (ordered : lower ≤ upper)
    (below : Expected env policy state upper) : Expected env policy state lower := by
  obtain ⟨horizon, margin, positive, bounds⟩ := below
  refine ⟨horizon, margin, positive, ?_⟩
  intro depth
  have h := bounds depth
  grind

/-- The cut is open: it contains a larger rational whenever it contains one. -/
theorem expected_rounded {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (bound : Rat) :
    Expected env policy state bound ↔ ∃ larger, bound < larger ∧ Expected env policy state larger := by
  constructor
  · rintro ⟨horizon, margin, positive, lower⟩
    refine ⟨bound + margin / 2, by grind, horizon, margin / 2, by grind, ?_⟩
    intro depth
    have h := lower depth
    grind
  · rintro ⟨larger, strict, below⟩
    exact expected_downward env policy state bound larger (Rat.le_of_lt strict) below

theorem negative_below_expectation {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (bound : Rat) (negative : bound < 0) :
    Expected env policy state bound := by
  refine ⟨0, -bound, by grind, ?_⟩
  intro depth
  have h := (capped_bounds env policy 0 depth [] state).1
  grind

/-- The prefix semantics supplies this link without an external expectation field. -/
theorem prefix_lower_bound {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (horizon : Nat) (value : Rat)
    (lower : ∀ depth, value ≤ capped env policy horizon depth [] state)
    (bound : Rat) (strict : bound < value) : Expected env policy state bound := by
  refine ⟨horizon, value - bound, by grind, ?_⟩
  intro depth
  have h := lower depth
  grind

/-- Per-cap convergence gives an upper bound without requiring every path to
finish or imposing a maximum number of actions. -/
theorem prefix_upper_bound {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (value : Rat)
    (upper : ∀ horizon epsilon, 0 < epsilon →
      ∃ depth, capped env policy horizon depth [] state < value + epsilon)
    (bound : Rat) (below : Expected env policy state bound) : bound < value := by
  obtain ⟨horizon, margin, positive, lower⟩ := below
  obtain ⟨depth, small⟩ := upper horizon margin positive
  have h := lower depth
  grind

private theorem exists_nat_above (q : Rat) : ∃ n : Nat, q < (n : Rat) := by
  let z := q.ceil + 1
  have hc : q ≤ (q.ceil : Rat) := Rat.le_ceil
  have hz : (q.ceil : Rat) < (z : Rat) := Rat.intCast_lt_intCast.mpr (by dsimp [z]; omega)
  have hn : (z : Rat) ≤ (z.toNat : Rat) := Rat.intCast_le_intCast.mpr (Int.self_le_toNat z)
  exact ⟨z.toNat, by grind⟩

/-- A completed checkpoint has exactly its elapsed time, even when that time
exceeds a particular cap. All integer caps are used in the outer supremum. -/
theorem completed_exact {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (done : env.complete state = true) (bound : Rat) :
    Expected env policy state bound ↔ bound < env.elapsed state := by
  have terminal : ∀ horizon depth history,
      capped env policy horizon depth history state = min (env.elapsed state) (horizon : Rat) := by
    intro horizon depth history
    cases depth <;> simp [capped, done]
  constructor
  · rintro ⟨horizon, margin, positive, lower⟩
    have h := lower 0
    rw [terminal] at h
    grind
  · intro strict
    obtain ⟨horizon, large⟩ := exists_nat_above (env.elapsed state)
    apply prefix_lower_bound env policy state horizon (env.elapsed state) _ bound strict
    intro depth
    rw [terminal]
    grind

/-- Positive permanently unfinished mass gives infinite expectation even when
the clocks on all those paths stay at zero. -/
theorem positive_stall_mass_infinite {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (state : S) (mass : Rat) (positive : 0 < mass)
    (survival : ∀ (horizon depth : Nat),
      (horizon : Rat) * mass ≤ capped env policy horizon depth [] state) :
    ∀ bound, Expected env policy state bound := by
  intro bound
  obtain ⟨horizon, large⟩ := exists_nat_above (bound / mass)
  have strict := (Rat.div_lt_iff positive).mp large
  exact prefix_lower_bound env policy state horizon (horizon * mass)
    (survival horizon) bound (by grind)

/-- Prefix dominance is a sufficient expectation comparison, not a claim that
a policy with this property has been found for the full game. -/
theorem prefix_dominance {S O A : Type} (env : Environment S O A)
    (fast slow : PublicPolicy O A) (state : S)
    (dominates : ∀ horizon depth,
      capped env fast horizon depth [] state ≤ capped env slow horizon depth [] state) :
    ∀ bound, Expected env fast state bound → Expected env slow state bound := by
  rintro bound ⟨horizon, margin, positive, lower⟩
  exact ⟨horizon, margin, positive, fun depth => Rat.le_trans (lower depth) (dominates horizon depth)⟩

namespace Stall

def environment : Environment Unit Unit Unit where
  complete := fun _ => false
  elapsed := fun _ => 0
  nonnegative := by intro _; exact Rat.le_refl
  observe := fun _ => ()
  legal := fun _ _ => True
  step := fun _ _ => .pure ()
  monotone := by intro _ _; exact Rat.le_refl

def policy : PublicPolicy Unit Unit := fun _ _ => ()

theorem capped_stall (horizon depth : Nat) (history : List (Unit × Unit)) :
    capped environment policy horizon depth history () = (horizon : Rat) := by
  induction depth generalizing history with
  | zero => rfl
  | succ depth ih => exact ih _

theorem infinite_completion_time : ∀ bound, Expected environment policy () bound := by
  apply positive_stall_mass_infinite environment policy () 1 (by decide +kernel)
  intro horizon depth
  rw [capped_stall, Rat.mul_one]
  exact Rat.le_refl

end Stall


private theorem sum_scale (f : Nat → Rat) (factor : Rat) (count : Nat) :
    sumRange (fun i => f i * factor) count = sumRange f count * factor := by
  induction count with
  | zero => simp [sumRange, Rat.zero_mul]
  | succ count ih => simp only [sumRange, ih]; grind

private theorem mean_scale (bits : Nat) (f : Nat → Rat) (factor : Rat) :
    mean bits (fun i => f i * factor) = mean bits f * factor := by
  have positive : (0 : Rat) < (size bits : Rat) := Rat.natCast_pos.mpr (size_positive bits)
  unfold mean
  rw [sum_scale]
  have cancel1 := Rat.div_mul_cancel (a := sumRange f (size bits) * factor)
    (b := (size bits : Rat)) (by grind)
  have cancel2 := Rat.div_mul_cancel (a := sumRange f (size bits))
    (b := (size bits : Rat)) (by grind)
  grind

private theorem mean_equal (bits : Nat) (f g : Nat → Rat)
    (same : ∀ i, i < size bits → f i = g i) : mean bits f = mean bits g := by
  apply Rat.le_antisymm
  · exact mean_mono bits f g (fun i hi => by rw [same i hi]; exact Rat.le_refl)
  · exact mean_mono bits g f (fun i hi => by rw [same i hi]; exact Rat.le_refl)

namespace NativePet

/-- Only the local known-missing quarter is modeled here. Its seed-selected drop
is fixed. The trigger uses the same exact native threshold as `PetRetry.pet`. -/
def environment : Environment PetRetry.State Bool Unit where
  complete := fun state => !state.missing
  elapsed := fun state => (state.elapsed : Rat)
  nonnegative := by intro _; exact Rat.natCast_nonneg
  observe := fun state => state.missing
  legal := fun _ _ => True
  step := fun state _ => .draw (fun draw => .pure (PetRetry.pet state draw))
  monotone := by intro state action draw; exact Rat.le_refl

def policy : PublicPolicy Bool Unit := fun _ _ => ()
def initial : PetRetry.State := ⟨0, true⟩

private theorem done (horizon depth : Nat) (history : List (Bool × Unit)) :
    capped environment policy horizon depth history ⟨0, false⟩ = 0 := by
  cases depth <;> simp [capped, environment]
  all_goals have h : (0 : Rat) ≤ (horizon : Rat) := Rat.natCast_nonneg; grind

private theorem failure_mean (value : Rat) :
    mean 53 (fun index => if index < PetRetry.successfulIndices then 0 else value) =
      PetRetry.failureProbability * value := by
  have equal := mean_equal 53
    (fun index => if index < PetRetry.successfulIndices then 0 else value)
    (fun index => (if interval PetRetry.successfulIndices (size 53) index then 1 else 0) * value)
    (by
      intro index inside
      by_cases low : index < PetRetry.successfulIndices
      · simp [interval, low, show ¬PetRetry.successfulIndices ≤ index from by omega]
      · simp [interval, low, inside, show PetRetry.successfulIndices ≤ index from by omega])
  rw [equal, mean_scale, mean_indicator, PetRetry.exact_failure_probability]

/-- Each unfinished finite prefix contributes the entire time cap. The prefix
probability is computed by the IID53 program, not supplied as a distribution. -/
theorem capped_retry (horizon depth : Nat) (history : List (Bool × Unit)) :
    capped environment policy horizon depth history initial =
      (horizon : Rat) * PetRetry.failure depth := by
  induction depth generalizing history with
  | zero => simp [capped, environment, initial, PetRetry.failure, Rat.mul_one]
  | succ depth ih =>
    simp only [capped, environment, initial, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      chosen, policy, Program.expect]
    have mask := mean_equal 53
      (fun index => capped environment policy horizon depth
        (history ++ [(true, ())]) (PetRetry.pet ⟨0, true⟩ (rangeDraw index)))
      (fun index => if index < PetRetry.successfulIndices then 0
        else (horizon : Rat) * PetRetry.failure depth)
      (by
        intro index inside
        have mod : index % size 53 = index := Nat.mod_eq_of_lt inside
        by_cases low : index < PetRetry.successfulIndices
        · have pet : PetRetry.pet ⟨0, true⟩ (rangeDraw index) = ⟨0, false⟩ := by
            simp [PetRetry.pet, rangeDraw, mod, show ¬PetRetry.successfulIndices ≤ index from by omega]
          rw [pet, done, if_pos low]
        · have pet : PetRetry.pet ⟨0, true⟩ (rangeDraw index) = initial := by
            simp [PetRetry.pet, rangeDraw, mod, initial, show PetRetry.successfulIndices ≤ index from by omega]
          rw [pet, ih, if_neg low])
    change mean 53 (fun index => capped environment policy horizon depth
      (history ++ [(true, ())]) (PetRetry.pet ⟨0, true⟩ (rangeDraw index))) = _
    rw [mask, failure_mean]
    simp only [PetRetry.failure]
    grind

/-- Zero expected extra elapsed time coexists with positive failure probability
at every finite retry depth. No pathwise termination or time-progress premise. -/
theorem expected_retry_zero (bound : Rat) :
    Expected environment policy initial bound ↔ bound < 0 := by
  constructor
  · intro below
    apply prefix_upper_bound environment policy initial 0 _ bound below
    intro horizon epsilon positive
    by_cases zero : horizon = 0
    · subst horizon
      exact ⟨0, by simp only [capped_retry, Rat.natCast_ofNat, Rat.zero_mul, Rat.zero_add]; exact positive⟩
    · have hpositive : (0 : Rat) < (horizon : Rat) := Rat.natCast_pos.mpr (by omega)
      have epspos : 0 < epsilon / (horizon : Rat) := (Rat.lt_div_iff hpositive).mpr (by simpa only [Rat.zero_mul] using positive)
      obtain ⟨depth, small⟩ := PetRetry.failure_tends_to_zero _ epspos
      refine ⟨depth, ?_⟩
      rw [capped_retry]
      have h := (Rat.lt_div_iff hpositive).mp small
      grind
  · exact negative_below_expectation environment policy initial bound

end NativePet

end CookieClicker.FullGame.HittingTime

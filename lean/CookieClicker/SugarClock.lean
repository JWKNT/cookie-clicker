import CookieClicker.HandPickedExpectation

/-! Concrete rational-clock projection of the native sugar handlers.
No restore operation exists. Every harvest resets the timer, offline processing
advances it, and other lump gains do not move it. Native binary64 refinement and
the probability law remain separate obligations. Seeded type selection is an
external outcome constrained by the native yield support; it is not resampled
as an independent uniform choice by this model.
-/
namespace CookieClicker.FullGame.SugarClock

set_option maxRecDepth 4096

inductive Aura where
  | none | reality | curve | both
  deriving DecidableEq

inductive OrderGod where
  | none | diamond | ruby | jade
  deriving DecidableEq

structure Config where
  diabetica : Bool := false
  ichor : Bool := false
  aura : Aura := .none
  stevia : Bool := false
  sugarAging : Bool := false
  grandmas : Nat := 0
  order : OrderGod := .none

/-- Order is none unless the building-count divisibility condition holds. -/
def orderReduction : OrderGod → Rat
  | .none => 0
  | .diamond => 3600000
  | .ruby => 2400000
  | .jade => 1200000

def auraFactor : Aura → Rat
  | .none => 1
  | .reality => 201 / 200
  | .curve => 21 / 20
  | .both => 211 / 200

def mature (c : Config) : Rat :=
  (72000000 - (if c.diabetica then 3600000 else 0) -
    (if c.ichor then 420000 else 0)) / auraFactor c.aura

def ripe (c : Config) : Rat :=
  (82800000 - (if c.stevia then 3600000 else 0) -
    (if c.sugarAging then 6000 * ((min 600 c.grandmas : Nat) : Rat) else 0) -
    orderReduction c.order) / auraFactor c.aura

def overripe (c : Config) : Rat := ripe c + 3600000

theorem maturity_minimum (c : Config) : Pinned.minimumHandPickedMaturity ≤ mature c := by
  obtain ⟨diabetica, ichor, aura, stevia, aging, grandmas, order⟩ := c
  cases diabetica <;> cases ichor <;> cases aura <;>
    simp only [mature, auraFactor, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem overripe_positive (c : Config) : 0 < overripe c := by
  have capped : ((min 600 c.grandmas : Nat) : Rat) ≤ 600 :=
    Rat.natCast_le_natCast.mpr (Nat.min_le_left _ _)
  have numerator : (0 : Rat) < 82800000 - (if c.stevia then 3600000 else 0) -
      (if c.sugarAging then 6000 * ((min 600 c.grandmas : Nat) : Rat) else 0) -
      orderReduction c.order := by
    cases hs : c.stevia <;> cases ha : c.sugarAging <;> cases ho : c.order <;>
      simp only [orderReduction, Bool.false_eq_true, ↓reduceIte] <;> grind
  have factorPositive : 0 < auraFactor c.aura := by
    cases c.aura <;> decide +kernel
  have ripePositive : 0 < ripe c := by
    apply (Rat.lt_div_iff factorPositive).mpr
    simpa only [Rat.zero_mul] using numerator
  dsimp [overripe]
  grind

inductive Kind where
  | normal | bifurcated | golden | meaty | caramelized
  deriving DecidableEq

def yieldAllowed : Kind → Nat → Prop
  | .normal, factor => factor = 1
  | .bifurcated, factor => factor = 1 ∨ factor = 2
  | .golden, factor => 2 ≤ factor ∧ factor ≤ 7
  | .meaty, factor => factor ≤ 2
  | .caramelized, factor => 1 ≤ factor ∧ factor ≤ 3

instance (kind : Kind) (factor : Nat) : Decidable (yieldAllowed kind factor) := by
  cases kind <;> unfold yieldAllowed <;> infer_instance

structure State where
  clock : Nat
  started : Rat
  attempts : Nat
  handPicked : Bool
  active : Bool
  initialized : Bool
  balance : Nat
  total : Nat
  kind : Kind
  deriving DecidableEq

def fresh : State := ⟨0, 0, 0, false, false, false, 0, 0, .normal⟩

def age (s : State) : Rat := (s.clock : Rat) - s.started

def gain (s : State) (amount : Nat) : State :=
  { s with
    active := true
    initialized := true
    balance := (if s.initialized then s.balance else 0) + amount
    total := (if s.initialized then s.total else 0) + amount }

def harvest (s : State) (amount factor : Nat) (nextKind : Kind) : State :=
  { gain s (amount * factor) with started := s.clock, kind := nextKind }

def unripe (s : State) (success : Bool) (factor : Nat) (nextKind : Kind) : State :=
  { harvest s (if success then 1 else 0) factor nextKind with
    attempts := s.attempts + 1, handPicked := s.handPicked || success }

def offline (s : State) (c : Config) (count factor : Nat) (nextKind : Kind) : State :=
  { gain s (factor + (count - 1)) with
    started := s.started + (count : Rat) * overripe c, kind := nextKind }

/-- Native branch guards and timer assignments; outcomes are not policy inputs. -/
inductive Step : State → State → Prop where
  | wait (s : State) (now : Nat) (monotone : s.clock ≤ now) :
      Step s { s with clock := now }
  | eligibility (s : State) (active : Bool) : Step s { s with active := active }
  | retype (s : State) (kind : Kind) : Step s { s with kind := kind }
  | ordinaryGain (s : State) (amount : Nat) : Step s (gain s amount)
  | spend (s : State) (amount : Nat) (enough : amount ≤ s.balance) :
      Step s { s with balance := s.balance - amount }
  | activate (s : State) (enabled : s.active = true) (first : s.initialized = false)
      (nextKind : Kind) :
      Step s { s with started := s.clock, initialized := true, balance := 0, total := 0, kind := nextKind }
  | immatureClick (s : State) (c : Config) (early : age s < mature c) : Step s s
  | unripeClick (s : State) (c : Config) (enabled : s.active = true)
      (ready : mature c ≤ age s) (notRipe : age s < ripe c)
      (success : Bool) (factor : Nat) (support : yieldAllowed s.kind factor) (nextKind : Kind) :
      Step s (unripe s success factor nextKind)
  | ripeClick (s : State) (c : Config) (enabled : s.active = true)
      (ready : ripe c ≤ age s) (notOverripe : age s < overripe c)
      (factor : Nat) (support : yieldAllowed s.kind factor) (nextKind : Kind) :
      Step s (harvest s 1 factor nextKind)
  | automatic (s : State) (c : Config) (enabled : s.active = true)
      (ready : overripe c < age s) (factor : Nat)
      (support : yieldAllowed s.kind factor) (nextKind : Kind) :
      Step s (harvest s 1 factor nextKind)
  | offlineCatchup (s : State) (c : Config) (enabled : s.active = true)
      (count : Nat) (positive : 0 < count)
      (lower : (count : Rat) * overripe c ≤ age s)
      (upper : age s < ((count + 1 : Nat) : Rat) * overripe c)
      (factor : Nat) (support : yieldAllowed s.kind factor) (nextKind : Kind) :
      Step s (offline s c count factor nextKind)
  | hardReset (s : State) :
      Step s { fresh with clock := s.clock, started := s.clock, attempts := s.attempts }
  | idle (s : State) : Step s s

/-- The ghost attempt count is preserved even if a hard reset clears achievements. -/
def Invariant (s : State) : Prop :=
  ((s.attempts * 64436019 : Nat) : Rat) ≤ s.started ∧ s.started ≤ (s.clock : Rat)

theorem fresh_invariant : Invariant fresh := by
  unfold Invariant fresh
  decide +kernel

/-- Every eligible next attempt is at least one minimum interval after its predecessors. -/
theorem next_attempt_clock (s : State) (c : Config) (inv : Invariant s)
    (ready : mature c ≤ age s) : (s.attempts + 1) * 64436019 ≤ s.clock := by
  have minAge := maturity_minimum c
  have startLower := inv.1
  have startUpper := inv.2
  have baseLe : s.attempts * 64436019 ≤ s.clock := Rat.natCast_le_natCast.mp (by grind)
  have difference : ((s.clock - s.attempts * 64436019 : Nat) : Rat) =
      (s.clock : Rat) - ((s.attempts * 64436019 : Nat) : Rat) := by
    have eq := congrArg (fun n : Nat => (n : Rat)) (Nat.sub_add_cancel baseLe)
    simp only [Rat.natCast_add] at eq
    grind
  have eligible : Pinned.minimumHandPickedMaturity ≤
      ((s.clock - s.attempts * 64436019 : Nat) : Rat) := by
    rw [difference]
    dsimp [age] at ready
    grind
  have gate := Pinned.eligible_integer_clock_difference _ eligible
  have combined := Nat.add_le_add_left gate (s.attempts * 64436019)
  rw [Nat.add_sub_of_le baseLe] at combined
  simpa only [Nat.add_mul, Nat.one_mul] using combined

theorem step_preserves_invariant {s t : State} (inv : Invariant s) (step : Step s t) : Invariant t := by
  have lower := inv.1
  have upper := inv.2
  cases step with
  | wait now monotone =>
    have cast := Rat.natCast_le_natCast.mpr monotone
    exact ⟨lower, by grind⟩
  | eligibility active => exact inv
  | retype kind => exact inv
  | ordinaryGain amount => exact inv
  | spend amount enough => exact inv
  | activate enabled first nextKind => exact ⟨Rat.le_trans lower upper, Rat.le_refl⟩
  | immatureClick c early => exact inv
  | unripeClick c enabled ready notRipe success factor support nextKind =>
    have gate := Rat.natCast_le_natCast.mpr (next_attempt_clock s c inv ready)
    exact ⟨gate, Rat.le_refl⟩
  | ripeClick c enabled ready notOverripe factor support nextKind =>
    exact ⟨Rat.le_trans lower upper, Rat.le_refl⟩
  | automatic c enabled ready factor support nextKind =>
    exact ⟨Rat.le_trans lower upper, Rat.le_refl⟩
  | offlineCatchup c enabled count positive floorLower floorUpper factor support nextKind =>
    have periodNonnegative : 0 ≤ overripe c := by have h := overripe_positive c; grind
    have increment := Rat.mul_nonneg (Rat.natCast_nonneg (a := count)) periodNonnegative
    constructor
    · change ((s.attempts * 64436019 : Nat) : Rat) ≤ s.started + (count : Rat) * overripe c
      grind
    · change s.started + (count : Rat) * overripe c ≤ (s.clock : Rat)
      dsimp [age] at floorLower
      grind
  | hardReset => exact ⟨Rat.le_trans lower upper, Rat.le_refl⟩
  | idle => exact inv

inductive Reachable : State → Prop where
  | initial : Reachable fresh
  | next {s t : State} : Reachable s → Step s t → Reachable t

theorem reachable_invariant {s : State} (reachable : Reachable s) : Invariant s := by
  induction reachable with
  | initial => exact fresh_invariant
  | next _ step ih => exact step_preserves_invariant ih step

theorem attempts_times_spacing_le_clock {s : State} (reachable : Reachable s) :
    s.attempts * 64436019 ≤ s.clock := by
  have inv := reachable_invariant reachable
  exact Rat.natCast_le_natCast.mp (Rat.le_trans inv.1 inv.2)

/-- Before the end of interval n, there can have been at most n eligible attempts. -/
theorem attempts_before_interval_end {s : State} (reachable : Reachable s)
    (n k : Nat) (offset : k < 64436019) (clock : s.clock = n * 64436019 + k) :
    s.attempts ≤ n := by
  have timing := attempts_times_spacing_le_clock reachable
  omega

theorem hand_picked_needs_attempt {s : State} (reachable : Reachable s)
    (won : s.handPicked = true) : 0 < s.attempts := by
  induction reachable with
  | initial => contradiction
  | @next before after reachable step ih =>
    cases step <;> simp_all [unripe, harvest, gain, offline, fresh] <;> omega

theorem hand_picked_not_before_minimum {s : State} (reachable : Reachable s)
    (won : s.handPicked = true) : 64436019 ≤ s.clock := by
  have attempts := hand_picked_needs_attempt reachable won
  have timing := attempts_times_spacing_le_clock reachable
  omega

/-- Ordinary gains, including a Garden lump, do not reset the formation clock. -/
theorem ordinary_gain_preserves_timer (s : State) (amount : Nat) :
    (gain s amount).started = s.started := rfl

/-- Failure resets the formation clock even though its base harvest amount is zero. -/
theorem failed_attempt_resets (s : State) (factor : Nat) (nextKind : Kind) :
    (unripe s false factor nextKind).started = (s.clock : Rat) := rfl

/-- An arbitrary sequence of the concrete transitions, with idle steps permitted. -/
structure Run where
  state : Nat → State
  initial : state 0 = fresh
  next : ∀ i, Step (state i) (state (i + 1))

theorem Run.reachable (run : Run) (i : Nat) : Reachable (run.state i) := by
  induction i with
  | zero => rw [run.initial]; exact .initial
  | succ i ih => exact .next ih (run.next i)

/-- This includes paths that stop before making n attempts. -/
def NoSuccessInFirst (run : Run) (n : Nat) : Prop :=
  ∀ i, (run.state i).attempts ≤ n → (run.state i).handPicked = false

/-- First-hit semantics retain every earlier completion even if later goals are lost. -/
def NoCompletionBy (run : Run) (observations : Nat → Snapshot) (time : Nat) : Prop :=
  ∀ i, (run.state i).clock ≤ time → complete Pinned.requirements (observations i) = false

theorem no_success_initially (run : Run) : NoSuccessInFirst run 0 := by
  intro i count
  cases won : (run.state i).handPicked with
  | false => rfl
  | true =>
    have positive := hand_picked_needs_attempt (run.reachable i) won
    omega

/-- The clock/required-goal event inclusion is derived from transitions, not assumed. -/
theorem no_success_implies_no_completion (run : Run) (observations : Nat → Snapshot)
    (projection : ∀ i, (run.state i).handPicked = (observations i).achievements "Hand-picked")
    (n k : Nat) (offset : k < 64436019) (failed : NoSuccessInFirst run n) :
    NoCompletionBy run observations (n * 64436019 + k) := by
  intro i before
  have timing := attempts_times_spacing_le_clock (run.reachable i)
  have count : (run.state i).attempts ≤ n := by omega
  have absent := failed i count
  cases done : complete Pinned.requirements (observations i) with
  | false => rfl
  | true =>
    have won := Pinned.completion_requires_hand_picked (observations i) done
    rw [projection] at absent
    simp_all

/-- Monotone rational event bounds. Additivity and an engine probability model
are not supplied by this interface. Actual expectation soundness is separate.
-/
structure EventBounds (Ω : Type) where
  value : (Ω → Prop) → Rat
  nonnegative : ∀ event, 0 ≤ value event
  at_most_one : ∀ event, value event ≤ 1
  certain : value (fun _ => True) = 1
  monotone : ∀ event larger, (∀ outcome, event outcome → larger outcome) →
    value event ≤ value larger

def fullTailCertificate {Ω : Type} (bounds : EventBounds Ω) (runs : Ω → Run)
    (observations : Ω → Nat → Snapshot) : HandPickedExpectation.RationalTailCertificate where
  survival := fun time => bounds.value (fun outcome => NoCompletionBy (runs outcome) (observations outcome) time)
  nonnegative := fun _ => bounds.nonnegative _
  at_most_one := fun _ => bounds.at_most_one _
  decreasing := by
    intro earlier later order
    apply bounds.monotone
    intro outcome absent i before
    exact absent i (Nat.le_trans before order)

/-- Concrete clock transitions discharge the prior clock-and-required-goal field.
Only the event bounds, observation projection, and stochastic failure inequality
remain inputs. In particular, no attempt spacing or event inclusion is assumed.
-/
def bridge_from_sugar_runs {Ω : Type} (bounds : EventBounds Ω) (runs : Ω → Run)
    (observations : Ω → Nat → Snapshot)
    (projection : ∀ outcome i, ((runs outcome).state i).handPicked =
      (observations outcome i).achievements "Hand-picked")
    (fairFailure : ∀ n,
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) n) / 2 ≤
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) (n + 1))) :
    HandPickedExpectation.HandPickedBridge (fullTailCertificate bounds runs observations) 64436019 where
  attemptSurvival := fun n => bounds.value (fun outcome => NoSuccessInFirst (runs outcome) n)
  initially_missing := by
    have event : (fun outcome => NoSuccessInFirst (runs outcome) 0) = (fun _ => True) := by
      funext outcome
      exact propext ⟨fun _ => trivial, fun _ => no_success_initially (runs outcome)⟩
    rw [event]
    exact bounds.certain
  conditional_failure := fairFailure
  clock_and_required_goal := by
    intro n k offset
    apply bounds.monotone
    intro outcome failed
    exact no_success_implies_no_completion (runs outcome) (observations outcome)
      (projection outcome) n k offset failed

/-- Conditional lower bound with the clock part now proved from native-style steps. -/
theorem sugar_run_expected_lower_bound {Ω : Type} (bounds : EventBounds Ω) (runs : Ω → Run)
    (observations : Ω → Nat → Snapshot)
    (projection : ∀ outcome i, ((runs outcome).state i).handPicked =
      (observations outcome i).achievements "Hand-picked")
    (fairFailure : ∀ n,
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) n) / 2 ≤
      bounds.value (fun outcome => NoSuccessInFirst (runs outcome) (n + 1)))
    (actual : Rat → Prop)
    (sound : HandPickedExpectation.FiniteTailsSound (fullTailCertificate bounds runs observations) actual) :
    ∀ lower, lower < 128872038 → actual lower :=
  HandPickedExpectation.certified_hand_picked_bound sound
    (bridge_from_sugar_runs bounds runs observations projection fairFailure)

end CookieClicker.FullGame.SugarClock

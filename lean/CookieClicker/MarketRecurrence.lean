import CookieClicker.UniformRandom

/-! Exact-rational projection of a source-audited native market forcing tick.
The draw atoms, branch order, damping, and floor corrections follow the pinned
market source. The selected random event is not a policy-controlled input.
Native binary64 refinement and the invariant under arbitrary non-forced draws
remain separate obligations.
-/
namespace CookieClicker.FullGame.MarketRecurrence

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

inductive Mode where
  | stable | slowRise | slowFall | fastRise | fastFall | chaotic
  deriving DecidableEq

inductive Direction where
  | rise | fall
  deriving DecidableEq

structure State where
  price : Rat
  velocity : Rat
  mode : Mode
  deriving DecidableEq

def top : Rat := 9007199254740991 / 9007199254740992
def globalShock : Rat := 1 / 4503599627370496
def alpha (boost : Rat) : Rat := 97 / 100 + boost / 100
def targetMode : Direction → Mode | .rise => .fastRise | .fall => .fastFall

def modeVelocity (mode : Mode) (d : Rat) : Rat :=
  match mode with
  | .stable => d * (95 / 100) + (1 / 20) * (top - 1 / 2)
  | .slowRise => d * (99 / 100) + (1 / 20) * (top - 1 / 10)
  | .slowFall => d * (99 / 100) - (1 / 20) * (top - 1 / 10)
  | .fastRise => d + (3 / 20) * (top - 1 / 10)
  | .fastFall => d - (3 / 20) * (top - 1 / 10)
  | .chaotic => d + (3 / 10) * (top - 1 / 2)

def modePrice (mode : Mode) (price : Rat) : Rat :=
  match mode with
  | .fastRise => price + top * 5
  | .fastFall => price - top * 5
  | _ => price

def priceNoise : Direction → Rat
  | .fall => -3
  | .rise => ((top - 1 / 2) * 2) ^ 11 * 3

def velocityNoise : Direction → Rat
  | .fall => -1 / 20
  | .rise => (1 / 10) * (top - 1 / 2)

def highDamp (price velocity : Rat) : Rat :=
  if 100 < price ∧ 0 < velocity then velocity * (9 / 10) else velocity

def lowPrice (price : Rat) : Rat := if price < 5 then (price + 5) / 2 else price

def finish (price velocity : Rat) (mode : Mode) : State :=
  let d := highDamp price velocity
  let v := lowPrice (price + d)
  { price := max v 1, velocity := if v < 5 ∧ d < 0 then d * (95 / 100) else d, mode }

/-- The global disturbance is applied with zero size draws, so it subtracts
twice globalShock from price and adds globalShock to velocity. Optional events
are disabled by their audited atoms. Duration zero forces the final mode reset.
-/
def preVelocity (direction : Direction) (boost : Rat) (state : State) : Rat :=
  modeVelocity state.mode (alpha boost * state.velocity) + globalShock + velocityNoise direction

def prePrice (direction : Direction) (resting : Rat) (state : State) : Rat :=
  (99 / 100) * modePrice state.mode state.price + resting / 100 - 2 * globalShock + priceNoise direction

def forcedStep (direction : Direction) (boost resting : Rat) (state : State) : State :=
  finish (prePrice direction resting state) (preVelocity direction boost state) (targetMode direction)

def Box (resting : Rat) (state : State) : Prop :=
  1 ≤ state.price ∧ state.price ≤ resting + 250000 ∧ -300 ≤ state.velocity ∧ state.velocity ≤ 300

theorem forcing_constants :
    0 < top ∧ top < 1 ∧ 0 < globalShock ∧ globalShock < 1 / 1000 ∧
    (3 / 20) * (top - 1 / 10) + 1 / 20 - globalShock ≥ (184 / 1000 : Rat) ∧
    (3 / 20) * (top - 1 / 10) + globalShock + velocityNoise .rise ≥ (184 / 1000 : Rat) ∧
    (99 / 100) * 5 * top + 2 * globalShock + 3 ≥ (79 / 10 : Rat) ∧
    (99 / 100) * 5 * top - 2 * globalShock + priceNoise .rise ≥ (79 / 10 : Rat) := by
  decide +kernel

theorem alpha_bounds {boost : Rat} (low : 0 ≤ boost) (high : boost ≤ 11 / 10) :
    0 ≤ alpha boost ∧ alpha boost ≤ 981 / 1000 := by
  unfold alpha
  grind

theorem finish_velocity_bounds (price velocity : Rat) (mode : Mode) :
    min 0 velocity ≤ (finish price velocity mode).velocity ∧
    (finish price velocity mode).velocity ≤ max 0 velocity := by
  unfold finish highDamp
  split <;> dsimp only <;> grind

theorem finish_price_lower (price velocity : Rat) (mode : Mode) :
    1 ≤ (finish price velocity mode).price := by
  unfold finish
  grind

theorem finish_price_upper (price velocity : Rat) (mode : Mode) (cap : Rat)
    (positive : 0 ≤ cap) (bounded : velocity ≤ cap) :
    (finish price velocity mode).price ≤ max 5 (price + cap) := by
  unfold finish highDamp lowPrice
  split <;> dsimp only <;> grind

theorem finish_falling_price (price velocity : Rat) (mode : Mode) (falling : velocity ≤ 0) :
    (finish price velocity mode).price ≤ max 5 price := by
  have h := finish_price_upper price velocity mode 0 (Rat.le_refl) falling
  simpa only [Rat.add_zero] using h

theorem finish_rising_price (price velocity : Rat) (mode : Mode) (rising : 0 ≤ velocity) :
    price ≤ (finish price velocity mode).price := by
  unfold finish highDamp lowPrice
  split <;> dsimp only <;> grind

theorem forced_mode (direction : Direction) (boost resting : Rat) (state : State) :
    (forcedStep direction boost resting state).mode = targetMode direction := rfl

theorem noise_bounds (direction : Direction) :
    -(3 : Rat) ≤ priceNoise direction ∧ priceNoise direction ≤ 3 ∧
    -(1 / 20 : Rat) ≤ velocityNoise direction ∧ velocityNoise direction ≤ 1 / 20 := by
  cases direction <;> decide +kernel

theorem mode_velocity_bounds (mode : Mode) (velocity : Rat)
    (lo : -(2943 / 10 : Rat) ≤ velocity) (hi : velocity ≤ 2943 / 10) :
    -(5889 / 20 : Rat) ≤ modeVelocity mode velocity ∧ modeVelocity mode velocity ≤ 5889 / 20 := by
  have constants := forcing_constants
  cases mode <;> simp only [modeVelocity] <;> grind

theorem pre_velocity_bounds (direction : Direction) (boost : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (lo : -300 ≤ state.velocity) (hi : state.velocity ≤ 300) :
    -300 ≤ preVelocity direction boost state ∧ preVelocity direction boost state ≤ 300 := by
  have ab := alpha_bounds boostLow boostHigh
  have upper := Rat.mul_le_mul_of_nonneg_left hi ab.1
  have lower := Rat.mul_le_mul_of_nonneg_left lo ab.1
  have scaled : -(2943 / 10 : Rat) ≤ alpha boost * state.velocity ∧
      alpha boost * state.velocity ≤ 2943 / 10 := by grind
  have adjusted := mode_velocity_bounds state.mode _ scaled.1 scaled.2
  have noise := noise_bounds direction
  have constants := forcing_constants
  unfold preVelocity
  grind

theorem pre_price_upper (direction : Direction) (resting : Rat) (state : State) :
    prePrice direction resting state ≤ (99 / 100) * state.price + resting / 100 + 8 := by
  have noise := noise_bounds direction
  have constants := forcing_constants
  have modeBound : modePrice state.mode state.price ≤ state.price + 5 := by
    cases state.mode <;> simp only [modePrice] <;> grind
  unfold prePrice
  grind

theorem forced_preserves_box (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (restLow : 10 ≤ resting) (inside : Box resting state) :
    Box resting (forcedStep direction boost resting state) := by
  have velocity := pre_velocity_bounds direction boost state boostLow boostHigh inside.2.2.1 inside.2.2.2
  have finalVelocity := finish_velocity_bounds (prePrice direction resting state)
    (preVelocity direction boost state) (targetMode direction)
  have low := finish_price_lower (prePrice direction resting state)
    (preVelocity direction boost state) (targetMode direction)
  have high := finish_price_upper (prePrice direction resting state)
    (preVelocity direction boost state) (targetMode direction) 300 (by decide) velocity.2
  have preHigh := pre_price_upper direction resting state
  unfold Box at inside ⊢
  unfold forcedStep
  grind

def signed : Direction → Rat → Rat | .fall, d => d | .rise, d => -d
def distance (direction : Direction) (velocity : Rat) : Rat := max 0 (signed direction velocity)

theorem distance_nonnegative (direction : Direction) (velocity : Rat) : 0 ≤ distance direction velocity := by
  unfold distance
  grind

theorem alpha_distance (boost velocity : Rat) (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) :
    alpha boost * velocity ≤ (981 / 1000) * max 0 velocity := by
  have ab := alpha_bounds boostLow boostHigh
  have self : velocity ≤ max 0 velocity := by grind
  have positive : (0 : Rat) ≤ max 0 velocity := by grind
  have a := Rat.mul_le_mul_of_nonneg_left self ab.1
  have b := Rat.mul_le_mul_of_nonneg_right ab.2 positive
  exact Rat.le_trans a b

theorem pre_velocity_progress (direction : Direction) (boost : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = targetMode direction) :
    signed direction (preVelocity direction boost state) ≤
      (981 / 1000) * distance direction state.velocity - 184 / 1000 := by
  have comparison := alpha_distance boost (signed direction state.velocity) boostLow boostHigh
  have constants := forcing_constants
  cases direction <;> simp only [signed, distance, preVelocity, aligned, targetMode, modeVelocity, velocityNoise] at * <;> grind

theorem finish_distance (direction : Direction) (price velocity : Rat) (mode : Mode) :
    distance direction (finish price velocity mode).velocity ≤ distance direction velocity := by
  have bounds := finish_velocity_bounds price velocity mode
  cases direction <;> simp only [distance, signed] <;> grind

theorem forced_distance_progress (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = targetMode direction) :
    distance direction (forcedStep direction boost resting state).velocity ≤
      max 0 ((981 / 1000) * distance direction state.velocity - 184 / 1000) := by
  have pre := pre_velocity_progress direction boost state boostLow boostHigh aligned
  have final := finish_distance direction (prePrice direction resting state)
    (preVelocity direction boost state) (targetMode direction)
  unfold forcedStep
  unfold distance at final pre ⊢
  grind

def iterate (direction : Direction) (boost resting : Rat) : Nat → State → State
  | 0, state => state
  | n + 1, state => forcedStep direction boost resting (iterate direction boost resting n state)

theorem iterate_aligned (direction : Direction) (boost resting : Rat) (state : State)
    (aligned : state.mode = targetMode direction) (n : Nat) :
    (iterate direction boost resting n state).mode = targetMode direction := by
  cases n with
  | zero => exact aligned
  | succ n => rfl

theorem iterate_box (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (restLow : 10 ≤ resting) (inside : Box resting state) (n : Nat) :
    Box resting (iterate direction boost resting n state) := by
  induction n with
  | zero => exact inside
  | succ n ih => exact forced_preserves_box direction boost resting _ boostLow boostHigh restLow ih

def velocityEnvelope : Nat → Rat
  | 0 => 300
  | n + 1 => (981 / 1000) * velocityEnvelope n - 184 / 1000

def powerRatio (numerator denominator exponent : Nat) : Rat :=
  ((numerator ^ exponent : Nat) : Rat) / ((denominator ^ exponent : Nat) : Rat)

theorem power_ratio_succ (numerator denominator exponent : Nat) (positive : 0 < denominator) :
    powerRatio numerator denominator (exponent + 1) =
      ((numerator : Rat) / (denominator : Rat)) * powerRatio numerator denominator exponent := by
  have dp : (0 : Rat) < (denominator : Rat) := Rat.natCast_pos.mpr positive
  have pp : (0 : Rat) < ((denominator ^ exponent : Nat) : Rat) := Rat.natCast_pos.mpr (Nat.pow_pos positive)
  unfold powerRatio
  rw [Nat.pow_succ, Nat.pow_succ, Rat.natCast_mul, Rat.natCast_mul]
  have one := Rat.div_mul_cancel (a := ((numerator ^ exponent : Nat) : Rat)) (b := ((denominator ^ exponent : Nat) : Rat)) (by grind)
  have two := Rat.div_mul_cancel (a := (numerator : Rat)) (b := (denominator : Rat)) (by grind)
  have three := Rat.div_mul_cancel (a := ((numerator ^ exponent : Nat) : Rat) * numerator)
    (b := ((denominator ^ exponent : Nat) : Rat) * denominator) (by grind)
  grind

theorem velocity_envelope_closed (n : Nat) :
    velocityEnvelope n = (5884 / 19) * powerRatio 981 1000 n - 184 / 19 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [velocityEnvelope, ih, power_ratio_succ _ _ _ (by decide)]
    grind

theorem velocity_clamp (x : Rat) :
    max 0 ((981 / 1000) * max 0 x - 184 / 1000) =
      max 0 ((981 / 1000) * x - 184 / 1000) := by grind

theorem iterate_velocity_bound (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = targetMode direction) (initial : distance direction state.velocity ≤ 300)
    (n : Nat) :
    distance direction (iterate direction boost resting n state).velocity ≤ max 0 (velocityEnvelope n) := by
  induction n with
  | zero => simpa only [iterate, velocityEnvelope, show max (0 : Rat) 300 = 300 by decide] using initial
  | succ n ih =>
    have step := forced_distance_progress direction boost resting (iterate direction boost resting n state)
      boostLow boostHigh (iterate_aligned direction boost resting state aligned n)
    have mul := Rat.mul_le_mul_of_nonneg_left ih (by decide +kernel : (0 : Rat) ≤ 981 / 1000)
    have bound : max 0 ((981 / 1000) * distance direction (iterate direction boost resting n state).velocity - 184 / 1000) ≤
        max 0 ((981 / 1000) * max 0 (velocityEnvelope n) - 184 / 1000) := by grind
    rw [velocity_clamp] at bound
    exact Rat.le_trans step bound

theorem velocity_envelope_200_negative : velocityEnvelope 200 < 0 := by
  rw [velocity_envelope_closed]
  decide +kernel

theorem aligned_sign_after_200 (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = targetMode direction) (initial : distance direction state.velocity ≤ 300) :
    distance direction (iterate direction boost resting 200 state).velocity = 0 := by
  have bound := iterate_velocity_bound direction boost resting state boostLow boostHigh aligned initial 200
  have negative := velocity_envelope_200_negative
  have nonnegative := distance_nonnegative direction (iterate direction boost resting 200 state).velocity
  grind

theorem direction_sign_preserved (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = targetMode direction) (rightSign : distance direction state.velocity = 0) :
    distance direction (forcedStep direction boost resting state).velocity = 0 := by
  have step := forced_distance_progress direction boost resting state boostLow boostHigh aligned
  have nonnegative := distance_nonnegative direction (forcedStep direction boost resting state).velocity
  rw [rightSign] at step
  grind

theorem iterate_sign (direction : Direction) (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = targetMode direction) (rightSign : distance direction state.velocity = 0)
    (n : Nat) : distance direction (iterate direction boost resting n state).velocity = 0 := by
  induction n with
  | zero => exact rightSign
  | succ n ih =>
    exact direction_sign_preserved direction boost resting _ boostLow boostHigh
      (iterate_aligned direction boost resting state aligned n) ih

theorem falling_price_step (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = .fastFall) (rightSign : distance .fall state.velocity = 0) :
    (forcedStep .fall boost resting state).price ≤
      max 5 ((99 / 100) * state.price + resting / 100 - 79 / 10) := by
  have progress := pre_velocity_progress .fall boost state boostLow boostHigh aligned
  rw [rightSign] at progress
  have negative : preVelocity .fall boost state ≤ 0 := by
    simp only [signed] at progress
    grind
  have final := finish_falling_price (prePrice .fall resting state) (preVelocity .fall boost state) .fastFall negative
  have constants := forcing_constants
  have pre : prePrice .fall resting state ≤ (99 / 100) * state.price + resting / 100 - 79 / 10 := by
    simp only [prePrice, aligned, modePrice, priceNoise]
    grind
  unfold forcedStep targetMode
  grind

theorem rising_price_step (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (aligned : state.mode = .fastRise) (rightSign : distance .rise state.velocity = 0) :
    (99 / 100) * state.price + resting / 100 + 79 / 10 ≤
      (forcedStep .rise boost resting state).price := by
  have progress := pre_velocity_progress .rise boost state boostLow boostHigh aligned
  rw [rightSign] at progress
  have positive : 0 ≤ preVelocity .rise boost state := by simp only [signed] at progress; grind
  have final := finish_rising_price (prePrice .rise resting state) (preVelocity .rise boost state) .fastRise positive
  have constants := forcing_constants
  have pre : (99 / 100) * state.price + resting / 100 + 79 / 10 ≤ prePrice .rise resting state := by
    simp only [prePrice, aligned, modePrice]
    grind
  unfold forcedStep
  exact Rat.le_trans pre final

def fallingEnvelope : Nat → Rat
  | 0 => 250180
  | n + 1 => (99 / 100) * fallingEnvelope n - 61 / 10

theorem falling_envelope_closed (n : Nat) :
    fallingEnvelope n = 250790 * powerRatio 99 100 n - 610 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [fallingEnvelope, ih, power_ratio_succ _ _ _ (by decide)]
    grind

theorem price_clamp (x : Rat) :
    max 5 ((99 / 100) * max 5 x - 61 / 10) = max 5 ((99 / 100) * x - 61 / 10) := by grind

theorem iterate_falling_bound (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) (restHigh : resting ≤ 180)
    (aligned : state.mode = .fastFall) (rightSign : distance .fall state.velocity = 0)
    (initial : state.price ≤ 250180) (n : Nat) :
    (iterate .fall boost resting n state).price ≤ max 5 (fallingEnvelope n) := by
  induction n with
  | zero => simpa only [iterate, fallingEnvelope, show max (5 : Rat) 250180 = 250180 by decide] using initial
  | succ n ih =>
    have step := falling_price_step boost resting (iterate .fall boost resting n state) boostLow boostHigh
      (iterate_aligned .fall boost resting state aligned n) (iterate_sign .fall boost resting state boostLow boostHigh aligned rightSign n)
    have bound : max 5 ((99 / 100) * (iterate .fall boost resting n state).price + resting / 100 - 79 / 10) ≤
        max 5 ((99 / 100) * max 5 (fallingEnvelope n) - 61 / 10) := by grind
    rw [price_clamp] at bound
    exact Rat.le_trans step bound

theorem falling_envelope_600_below_floor : fallingEnvelope 600 ≤ 5 := by
  rw [falling_envelope_closed]
  decide +kernel

theorem aligned_fall_after_600 (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) (restHigh : resting ≤ 180)
    (aligned : state.mode = .fastFall) (rightSign : distance .fall state.velocity = 0)
    (initial : state.price ≤ 250180) : (iterate .fall boost resting 600 state).price ≤ 5 := by
  have bound := iterate_falling_bound boost resting state boostLow boostHigh restHigh aligned rightSign initial 600
  have numeric := falling_envelope_600_below_floor
  grind

def saleBand (resting : Rat) : Rat := (21 / 20) * resting

theorem rise_below_band (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) (restHigh : resting ≤ 180)
    (aligned : state.mode = .fastRise) (rightSign : distance .rise state.velocity = 0)
    (below : state.price < saleBand resting) :
    state.price + 781 / 100 ≤ (forcedStep .rise boost resting state).price := by
  have step := rising_price_step boost resting state boostLow boostHigh aligned rightSign
  unfold saleBand at below
  grind

theorem rise_preserves_band (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) (restHigh : resting ≤ 180)
    (aligned : state.mode = .fastRise) (rightSign : distance .rise state.velocity = 0)
    (above : saleBand resting ≤ state.price) :
    saleBand resting ≤ (forcedStep .rise boost resting state).price := by
  have step := rising_price_step boost resting state boostLow boostHigh aligned rightSign
  unfold saleBand at above ⊢
  grind

theorem iterate_rising_bound (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) (restHigh : resting ≤ 180)
    (aligned : state.mode = .fastRise) (rightSign : distance .rise state.velocity = 0)
    (initial : 1 ≤ state.price) (n : Nat) :
    min (saleBand resting) (1 + (n : Rat) * (781 / 100)) ≤ (iterate .rise boost resting n state).price := by
  induction n with
  | zero => change min (saleBand resting) (1 + (0 : Rat) * (781 / 100)) ≤ state.price; grind
  | succ n ih =>
    have am := iterate_aligned .rise boost resting state aligned n
    have ds := iterate_sign .rise boost resting state boostLow boostHigh aligned rightSign n
    simp only [iterate]
    by_cases above : saleBand resting ≤ (iterate .rise boost resting n state).price
    · have step := rise_preserves_band boost resting _ boostLow boostHigh restHigh am ds above
      grind
    · have below : (iterate .rise boost resting n state).price < saleBand resting := by grind
      have step := rise_below_band boost resting _ boostLow boostHigh restHigh am ds below
      simp only [Rat.natCast_add, Rat.natCast_ofNat]
      change min (saleBand resting) (1 + ((n : Rat) + 1) * (781 / 100)) ≤
        (forcedStep .rise boost resting (iterate .rise boost resting n state)).price
      grind

theorem aligned_rise_after_30 (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10) (restHigh : resting ≤ 180)
    (aligned : state.mode = .fastRise) (rightSign : distance .rise state.velocity = 0)
    (initial : 1 ≤ state.price) : saleBand resting ≤ (iterate .rise boost resting 30 state).price := by
  have bound := iterate_rising_bound boost resting state boostLow boostHigh restHigh aligned rightSign initial 30
  unfold saleBand at bound ⊢
  grind

theorem iterate_add (direction : Direction) (boost resting : Rat) (state : State) (first second : Nat) :
    iterate direction boost resting (first + second) state =
      iterate direction boost resting second (iterate direction boost resting first state) := by
  induction second with
  | zero => rfl
  | succ n ih =>
    change forcedStep direction boost resting (iterate direction boost resting (first + n) state) =
      forcedStep direction boost resting (iterate direction boost resting n (iterate direction boost resting first state))
    rw [ih]

theorem box_distance_bound (direction : Direction) (resting : Rat) (state : State)
    (inside : Box resting state) : distance direction state.velocity ≤ 300 := by
  unfold Box at inside
  cases direction <;> unfold distance signed <;> grind

/-- The full falling forcing block, including the first mode-alignment tick. -/
theorem falling_block_low (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (restLow : 10 ≤ resting) (restHigh : resting ≤ 180) (inside : Box resting state) :
    (iterate .fall boost resting 801 state).price ≤ 5 := by
  let first := forcedStep .fall boost resting state
  have firstBox := forced_preserves_box .fall boost resting state boostLow boostHigh restLow inside
  have firstAligned : first.mode = .fastFall := rfl
  have bound := box_distance_bound .fall resting first firstBox
  have sign := aligned_sign_after_200 .fall boost resting first boostLow boostHigh firstAligned bound
  have phaseBox := iterate_box .fall boost resting first boostLow boostHigh restLow firstBox 200
  have aligned := iterate_aligned .fall boost resting first firstAligned 200
  have initialPrice : (iterate .fall boost resting 200 first).price ≤ 250180 := by
    unfold Box at phaseBox
    grind
  have low := aligned_fall_after_600 boost resting (iterate .fall boost resting 200 first)
    boostLow boostHigh restHigh aligned sign initialPrice
  have split1 := iterate_add .fall boost resting state 201 600
  have split2 := iterate_add .fall boost resting state 1 200
  rw [split1, split2]
  exact low

theorem falling_block_buy_band (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (restLow : 10 ≤ resting) (restHigh : resting ≤ 180) (inside : Box resting state) :
    (iterate .fall boost resting 801 state).price ≤ (65 / 100) * resting := by
  have low := falling_block_low boost resting state boostLow boostHigh restLow restHigh inside
  grind

/-- The full rising forcing block, including the first mode-alignment tick. -/
theorem rising_block_sale_band (boost resting : Rat) (state : State)
    (boostLow : 0 ≤ boost) (boostHigh : boost ≤ 11 / 10)
    (restLow : 10 ≤ resting) (restHigh : resting ≤ 180) (inside : Box resting state) :
    saleBand resting ≤ (iterate .rise boost resting 231 state).price := by
  let first := forcedStep .rise boost resting state
  have firstBox := forced_preserves_box .rise boost resting state boostLow boostHigh restLow inside
  have firstAligned : first.mode = .fastRise := rfl
  have bound := box_distance_bound .rise resting first firstBox
  have sign := aligned_sign_after_200 .rise boost resting first boostLow boostHigh firstAligned bound
  have phaseBox := iterate_box .rise boost resting first boostLow boostHigh restLow firstBox 200
  have aligned := iterate_aligned .rise boost resting first firstAligned 200
  have high := aligned_rise_after_30 boost resting (iterate .rise boost resting 200 first)
    boostLow boostHigh restHigh aligned sign phaseBox.1
  have split1 := iterate_add .rise boost resting state 201 30
  have split2 := iterate_add .rise boost resting state 1 200
  rw [split1, split2]
  exact high

theorem forcing_block_draw_budget : (801 + 231) * 327 = (337464 : Nat) := by decide +kernel

end CookieClicker.FullGame.MarketRecurrence

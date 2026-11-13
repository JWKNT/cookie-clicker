import CookieClicker.JavaScriptScaledArithmeticBridge
import CookieClicker.JavaScriptNaturalArithmetic
import CookieClicker.JavaScriptBrowser
/-! Native binary64 latency arithmetic for the one-Cursor waiting prefix.
The stored negative delay has an exact scaled numerator. Actual Float.Model
additions preserve its sign, so the source catch-up guard stays false. The
native minimum with 5000 leaves it unchanged. Pinned timer conversion and
integer Date reads give a 33ms ordinary interval. Complete callback frames,
startup and scheduler composition remain separate obligations.
-/
namespace CookieClicker.JavaScript.LoopArithmeticBridge
open Float.Model Float.Model.UnpackedFloat RoundingBridge ScaledArithmeticBridge NaturalArithmetic
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

theorem negative_normal_pack_components (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    pack Float.Model.Format.binary64 (.finite .negative mantissa exponent positive) =
      packComponents Float.Model.Format.binary64 .negative
        (BitVec.ofNat 11 (exponent + 1075).toNat) (BitVec.ofNat 52 mantissa) := by
  have logarithm : mantissa.log2 = 52 :=
    (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower,upper⟩
  have biased : (exponent + 1023 + 52).toNat = (exponent + 1075).toNat := by omega
  have safe : ¬ 2^11 ≤ (exponent + 1075).toNat + 1 := by omega
  change (if 2^11 ≤ (exponent + 1023 + 52).toNat + 1 then
      packedInfinity Float.Model.Format.binary64 .negative
    else if mantissa.log2+1=53 then
      packComponents Float.Model.Format.binary64 .negative
        (BitVec.ofNat 11 (exponent + 1023 + 52).toNat) (BitVec.ofNat 52 mantissa)
    else packComponents Float.Model.Format.binary64 .negative 0 (BitVec.ofNat 52 mantissa)) = _
  rw [biased, if_neg safe, logarithm]
  rfl

theorem negative_normal_unpack_pack (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    (Float.Model.pack (.finite .negative mantissa exponent positive)).unpack =
      .finite .negative mantissa exponent positive := by
  have biasedBound : (exponent + 1075).toNat < 2^11 := by omega
  have biasedPositive : 0 < (exponent + 1075).toNat := by omega
  have biasedNotAll : (exponent + 1075).toNat ≠ 2047 := by omega
  have exponentNotZero : BitVec.ofNat 11 (exponent + 1075).toNat ≠ 0#11 := by
    intro h
    have v := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt biasedBound] at v
    change (exponent + 1075).toNat = 0 at v
    omega
  have exponentNotAll : BitVec.ofNat 11 (exponent + 1075).toNat ≠ -1#11 := by
    intro h
    have v := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt biasedBound] at v
    have allBits : ((-1#11).toNat) = 2047 := by decide +kernel
    rw [allBits] at v
    exact biasedNotAll v
  have remainder : mantissa % 2^52 = mantissa - 2^52 := by omega
  change UnpackedFloat.unpack Float.Model.Format.binary64
    (pack Float.Model.Format.binary64 (.finite .negative mantissa exponent positive)) = _
  rw [negative_normal_pack_components mantissa exponent positive lower upper expLower expUpper]
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_components, Sign.ofBitVec, Sign.toBitVec, ↓reduceIte,
    exponentNotAll, exponentNotZero, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt biasedBound]
  have expCancel : ((exponent + 1075).toNat : Int) - (1023 + 52) = exponent := by omega
  have mantissaRecover : ((1#1 ++ BitVec.ofNat 52 mantissa) : BitVec 53).toNat = mantissa := by
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat, remainder]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : mantissa - 2^52 < 2^52)]
    simp only [Nat.shiftLeft_eq]
    omega
  simp only [mantissaRecover]
  change Float.Model.UnpackedFloat.finite .negative mantissa
    (((exponent + 1075).toNat : Int) - (1023+52)) _ = _
  simp only [expCancel]

theorem negative_normal_model_pack (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    Number.model (Float.Model.pack (.finite .negative mantissa exponent positive)).toBits =
      Float.Model.pack (.finite .negative mantissa exponent positive) := by
  change Float.Model.pack (Float.Model.pack (.finite .negative mantissa exponent positive)).unpack = _
  rw [negative_normal_unpack_pack mantissa exponent positive lower upper expLower expUpper]

theorem negative_normal_model_unpack (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53)
    (expLower : -1074 ≤ exponent) (expUpper : exponent ≤ 971) :
    (Number.model (Float.Model.pack (.finite .negative mantissa exponent positive)).toBits).unpack =
      .finite .negative mantissa exponent positive := by
  rw [negative_normal_model_pack mantissa exponent positive lower upper expLower expUpper,
    negative_normal_unpack_pack mantissa exponent positive lower upper expLower expUpper]


theorem roundWithAccuracy_negative (n : Nat) (e : Int) (accuracy : Accuracy) :
    roundWithAccuracy Format.binary64 .negative n e accuracy =
      (roundWithAccuracy Format.binary64 .positive n e accuracy).neg := by
  unfold roundWithAccuracy
  split <;> dsimp only <;> split <;> rfl

theorem round_negative (n : Nat) (e : Int) :
    round Format.binary64 .negative n e =
      (round Format.binary64 .positive n e).neg := by
  unfold round
  exact roundWithAccuracy_negative _ _ _

def NegativeScaledNormal (bits : UInt64) (D n : Nat) : Prop :=
  ∃ (m : Nat) (e : Int) (positive : 0 < m),
    2^52 ≤ m ∧ m < 2^53 ∧ -(D:Int) ≤ e ∧ e ≤ 971 ∧
    bits = (Float.Model.pack (.finite .negative m e positive)).toBits ∧
    m*2^(e+D).toNat = n

def NegativeScaledValue (bits : UInt64) (D n : Nat) : Prop :=
  (bits = Number.positiveZero ∧ n = 0) ∨ NegativeScaledNormal bits D n

def negativeIncrementBits (c D : Nat) (positive : 0 < c) : UInt64 :=
  (Float.Model.pack (.finite .negative c (-(D:Int)) positive)).toBits

theorem native_negative_scaled_normal_add (bits : UInt64) (n c D : Nat) (cPositive : 0 < c)
    (value : NegativeScaledNormal bits D n) (cLower : 2^52 ≤ c) (cUpper : c < 2^53)
    (scaleBound : D ≤ 1074) :
    Number.add bits (negativeIncrementBits c D cPositive) =
      (Float.Model.pack (round Format.binary64 .negative (n+c) (-(D:Int)))).toBits := by
  obtain ⟨m,e,positive,lower,upper,scaleLower,expUpper,shape,represented⟩ := value
  rw [shape]
  simp only [negativeIncrementBits,Number.add,Float.Model.add,
    negative_normal_model_unpack m e positive lower upper (by omega) expUpper,
    negative_normal_model_unpack c (-(D:Int)) cPositive cLower cUpper (by omega) (by omega)]
  simp only [UnpackedFloat.add,decreaseExponent,Nat.shiftLeft_eq,Sign.apply]
  have minimum : min e (-(D:Int)) = -(D:Int) := Int.min_eq_right scaleLower
  have otherShift : (-(D:Int)-(-(D:Int))).toNat = 0 := by omega
  have firstShift : e-(-(D:Int)) = e+D := by omega
  rw [minimum,otherShift,firstShift,represented]
  simp only [Nat.pow_zero,Nat.mul_one]
  have comparison : compare (-(n:Int) + -(c:Int)) 0 = .lt := Int.compare_eq_lt.mpr (by omega)
  simp only [normalize,comparison]
  have natValue : (-(-(n:Int) + -(c:Int))).toNat = n+c := by omega
  rw [natValue]

theorem native_negative_scaled_add_value (bits : UInt64) (n c D : Nat) (cPositive : 0 < c)
    (value : NegativeScaledValue bits D n) (cLower : 2^52 ≤ c) (cUpper : c < 2^53)
    (scaleBound : D ≤ 1074) (sumBound : n+c < 2^1023) :
    NegativeScaledNormal (Number.add bits (negativeIncrementBits c D cPositive)) D (roundedInteger (n+c)) := by
  rcases value with ⟨zero,nzero⟩ | normal
  · subst bits; subst n
    have zeroUnpack : (Number.model Number.positiveZero).unpack = .zero .positive := rfl
    simp only [negativeIncrementBits,Number.add,Float.Model.add,zeroUnpack,
      negative_normal_model_unpack c (-(D:Int)) cPositive cLower cUpper (by omega) (by omega),UnpackedFloat.add]
    have smallRound : roundedInteger c = c := by
      simp [roundedInteger,integerSpacing,if_pos cUpper,unit_spacing_exact]
    rw [Nat.zero_add,smallRound]
    exact ⟨c,-(D:Int),cPositive,cLower,cUpper,by omega,by omega,rfl,by
      change c*2^((-(D:Int))+D).toNat = c
      rw [show (-(D:Int)+D).toNat = 0 by omega]; simp⟩
  · rw [native_negative_scaled_normal_add bits n c D cPositive normal cLower cUpper scaleBound]
    obtain ⟨m,e,positive,lower,upper,expLower,expUpper,shape,represented⟩ :=
      scaled_round_shape (n+c) D (by omega) sumBound scaleBound
    rw [round_negative,shape]
    exact ⟨m,e,positive,lower,upper,expLower,expUpper,rfl,represented⟩

theorem native_negative_iterations_scaled (startBits : UInt64) (start c D k : Nat)
    (cPositive : 0 < c) (initial : NegativeScaledValue startBits D start)
    (startBound : start ≤ 2^106) (cLower : 2^52 ≤ c) (cUpper : c < 2^53)
    (scaleBound : D ≤ 1074) :
    NegativeScaledValue (nativeIterations startBits (negativeIncrementBits c D cPositive) k)
      D (numeratorIterations start c k) := by
  induction k with
  | zero => exact initial
  | succ k ih =>
    apply Or.inr
    apply native_negative_scaled_add_value _ _ c D cPositive ih cLower cUpper scaleBound
    have bound := numerator_iterations_bounded start c k startBound cUpper
    omega

theorem negative_scaled_not_positive (bits : UInt64) (D n : Nat)
    (scaleBound : D ≤ 1074) (value : NegativeScaledValue bits D n) :
    Number.lessThan Number.positiveZero bits = false := by
  rcases value with ⟨zero,_⟩ | normal
  · subst bits; decide +kernel
  · obtain ⟨m,e,p,l,u,el,eu,shape,_⟩ := normal
    rw [shape]
    have zeroUnpack : (Number.model Number.positiveZero).unpack = .zero .positive := rfl
    simp only [Number.lessThan,Float.Model.lt,zeroUnpack,
      negative_normal_model_unpack m e p l u (by omega) eu,
      UnpackedFloat.lt,UnpackedFloat.compare]
    rfl

theorem negative_normal_pack_toNat (m : Nat) (e : Int) (p : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    (Float.Model.pack (.finite .negative m e p)).toBits.toNat =
      2^63 + (e+1075).toNat*2^52 + (m-2^52) := by
  have biasedBound : (e+1075).toNat < 2^11 := by omega
  have remainder : m%2^52 = m-2^52 := by omega
  change (pack Format.binary64 (.finite .negative m e p)).toNat = _
  rw [negative_normal_pack_components m e p lower upper expLower expUpper]
  simp only [packComponents, Sign.toBitVec, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt biasedBound, remainder]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : (e+1075).toNat < 2^11)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : m-2^52 < 2^52)]
  simp only [Nat.shiftLeft_eq,Nat.add_mul]

theorem negative_normal_not_nan (m : Nat) (e : Int) (p : 0 < m)
    (lower : 2^52 ≤ m) (upper : m < 2^53) (expLower : -1074 ≤ e) (expUpper : e ≤ 971) :
    Number.isNaN (Float.Model.pack (.finite .negative m e p)).toBits = false := by
  have field : Number.exponentField (Float.Model.pack (.finite .negative m e p)).toBits =
      (e+1075).toNat := by
    rw [Number.exponentField,negative_normal_pack_toNat m e p lower upper expLower expUpper]
    omega
  rw [Number.isNaN,field]
  have notAll : ((e+1075).toNat == 2047) = false := by simp only [beq_eq_false_iff_ne]; omega
  rw [notAll]; rfl

theorem negative_scaled_clamp (bits : UInt64) (D n : Nat)
    (scaleBound : D ≤ 1074) (value : NegativeScaledValue bits D n) :
    Number.minimum bits (Number.ofNat 5000) = bits := by
  rcases value with ⟨zero,_⟩ | normal
  · subst bits; decide +kernel
  · obtain ⟨m,e,p,l,u,el,eu,shape,_⟩ := normal
    rw [shape]
    have noNaN := negative_normal_not_nan m e p l u (by omega) eu
    have rhsNoNaN : Number.isNaN (Number.ofNat 5000) = false := by decide +kernel
    have rhsNotZero : Number.isZero (Number.ofNat 5000) = false := by decide +kernel
    have rhsUnpack : (Number.model (Number.ofNat 5000)).unpack =
        .finite .positive 5497558138880000 (-40) (by decide) := by rfl
    have order : Number.lessThan (Float.Model.pack (.finite .negative m e p)).toBits (Number.ofNat 5000) = true := by
      simp only [Number.lessThan,Float.Model.lt,
        negative_normal_model_unpack m e p l u (by omega) eu,rhsUnpack,
        UnpackedFloat.lt,UnpackedFloat.compare]
      rfl
    simp only [Number.minimum,noNaN,rhsNoNaN,rhsNotZero,Bool.or_false,Bool.and_false,order]
    rfl

theorem negative_scaled_min_infinity (bits : UInt64) (D n : Nat)
    (scaleBound : D ≤ 1074) (value : NegativeScaledValue bits D n) :
    Number.minimum Number.positiveInfinity bits = bits := by
  rcases value with ⟨zero,_⟩ | normal
  · subst bits; decide +kernel
  · obtain ⟨m,e,p,l,u,el,eu,shape,_⟩ := normal
    rw [shape]
    have noNaN := negative_normal_not_nan m e p l u (by omega) eu
    have infNoNaN : Number.isNaN Number.positiveInfinity = false := by decide +kernel
    have infNotZero : Number.isZero Number.positiveInfinity = false := by decide +kernel
    have infUnpack : (Number.model Number.positiveInfinity).unpack = .infinity .positive := rfl
    have order : Number.lessThan Number.positiveInfinity
        (Float.Model.pack (.finite .negative m e p)).toBits = false := by
      simp only [Number.lessThan,Float.Model.lt,infUnpack,
        negative_normal_model_unpack m e p l u (by omega) eu,
        UnpackedFloat.lt,UnpackedFloat.compare]
      rfl
    simp only [Number.minimum,noNaN,infNoNaN,infNotZero,Bool.or_false,Bool.false_and,order]
    rfl

def latencyCredit : UInt64 :=
  Number.sub (Number.ofNat 33) (Number.div (Number.ofNat 1000) (Number.ofNat 30))

theorem native_frame_duration :
    Number.div (Number.ofNat 1000) (Number.ofNat 30) = 4629888066921343659 := by decide +kernel

theorem native_latency_credit :
    latencyCredit = negativeIncrementBits 6004799503160704 54 (by decide) := by decide +kernel

theorem native_initial_delay :
    NegativeScaledNormal
      (Number.sub Number.positiveZero (Number.div (Number.ofNat 1000) (Number.ofNat 30)))
      54 600479950316066176 := by
  exact ⟨4691249611844267,-47,by decide,by decide,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel⟩

theorem accumulated_delay_invariant (initial : UInt64) (n k : Nat)
    (entry : NegativeScaledValue initial 54 n) (bounded : n ≤ 2^106) :
    Number.lessThan Number.positiveZero (nativeIterations initial latencyCredit k) = false ∧
      Number.minimum (nativeIterations initial latencyCredit k) (Number.ofNat 5000) =
        nativeIterations initial latencyCredit k := by
  have represented := native_negative_iterations_scaled initial n 6004799503160704 54 k
    (by decide) entry bounded (by decide) (by decide) (by decide)
  rw [← native_latency_credit] at represented
  exact ⟨negative_scaled_not_positive _ _ _ (by decide) represented,
    negative_scaled_clamp _ _ _ (by decide) represented⟩

theorem native_timestamp_delta (time : Nat) (bounded : time+33 < 2^52) :
    Number.sub (Number.ofNat (time+33)) (Number.ofNat time) = Number.ofNat 33 := by
  rw [native_sub_small (time+33) time bounded (by omega) (by omega)]
  congr 1; omega

theorem native_latency_step (time : Nat) (bounded : time+33 < 2^52) :
    Number.sub (Number.sub (Number.ofNat (time+33)) (Number.ofNat time))
      (Number.div (Number.ofNat 1000) (Number.ofNat 30)) = latencyCredit := by
  rw [native_timestamp_delta time bounded]
  rfl

theorem native_timer_delay (nesting : Option Nat) :
    Browser.timerDelay nesting (Number.div (Number.ofNat 1000) (Number.ofNat 30)) = 33 := by
  unfold Browser.timerDelay
  have converted : Number.toInt32 (Number.div (Number.ofNat 1000) (Number.ofNat 30)) = 33 := by decide +kernel
  rw [converted]
  split <;> rfl

def loopDelays (initial : UInt64) : Nat → UInt64
  | 0 => initial
  | k+1 => Number.minimum (Number.add (loopDelays initial k) latencyCredit) (Number.ofNat 5000)

theorem loop_delays_eq (initial : UInt64) (n k : Nat)
    (entry : NegativeScaledValue initial 54 n) (bounded : n ≤ 2^106) :
    loopDelays initial k = nativeIterations initial latencyCredit k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [loopDelays,ih]
    exact (accumulated_delay_invariant initial n (k+1) entry bounded).2

theorem loop_delay_never_triggers_catchup (initial : UInt64) (n k : Nat)
    (entry : NegativeScaledValue initial 54 n) (bounded : n ≤ 2^106) :
    Number.lessThan Number.positiveZero (loopDelays initial k) = false := by
  rw [loop_delays_eq initial n k entry bounded]
  exact (accumulated_delay_invariant initial n k entry bounded).1

def passiveFrameBudget : Nat := 512000000000+150
def passiveTimeBudget : Nat := 33*passiveFrameBudget

theorem passive_time_budget : passiveTimeBudget = 16896000004950 := by decide +kernel

theorem passive_frame_budget : passiveFrameBudget < 2^40 := by decide +kernel

theorem passive_prefix_calendar_bounds (elapsed initialFrames frame : Nat)
    (initialElapsed : elapsed ≤ 2000) (initialCounter : initialFrames ≤ 100)
    (within : frame ≤ passiveFrameBudget) :
    1793275200000+elapsed+33*frame < 8640000000000000 ∧
      1793275200000+elapsed+33*frame+33 < 2^52 ∧
      initialFrames+frame < 2^40 := by
  unfold passiveFrameBudget at within
  omega

theorem native_calendar_delta_on_prefix (elapsed frame : Nat)
    (initialElapsed : elapsed ≤ 2000) (within : frame ≤ passiveFrameBudget) :
    Number.sub
      (Number.ofNat (1793275200000+elapsed+33*frame+33))
      (Number.ofNat (1793275200000+elapsed+33*frame)) = Number.ofNat 33 := by
  apply native_timestamp_delta
  exact (passive_prefix_calendar_bounds elapsed 0 frame initialElapsed (by decide) within).2.1

theorem native_counter_increment_on_prefix (initial frame : Nat)
    (initialBound : initial ≤ 100) (within : frame ≤ passiveFrameBudget) :
    Number.add (Number.ofNat (initial+frame)) Number.one = Number.ofNat (initial+frame+1) := by
  have counterBound := (passive_prefix_calendar_bounds 0 initial frame (by decide) initialBound within).2.2
  have one : Number.one = Number.ofNat 1 := rfl
  rw [one]
  exact native_add_small (initial+frame) 1 (by omega) (by decide)

end CookieClicker.JavaScript.LoopArithmeticBridge

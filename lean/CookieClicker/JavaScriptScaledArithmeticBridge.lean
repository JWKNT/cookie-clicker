import CookieClicker.JavaScriptFractionalArithmeticBridge

/-! Fixed-scale binary64 recurrences for the proposed new-save funding route.
These theorems use the logical Float.Model round, pack and add operations.
They prove the passive0.1/30 recurrence reaches a billion in finitely many
additions and the cent-increment recurrence reaches its native2^47 cap.
The source production invariant, callback schedule, legal sale/rebuy sequence
and subsequent funding stages remain separate proof obligations.
-/

namespace CookieClicker.JavaScript.ScaledArithmeticBridge
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge DyadicArithmeticBridge FractionalArithmeticBridge
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem normal_carry_shift_int (mantissa : Nat) (exponent : Int)
    (lower : 2^52 ≤ mantissa) (upper : mantissa ≤ 2^53) (expLower : -1074 ≤ exponent) :
    shiftToTargetExponent Format.binary64 mantissa exponent .exact =
      if mantissa = 2^53 then (⟨2^52,false,false⟩, exponent+1)
      else (⟨mantissa,false,false⟩, exponent) := by
  by_cases same : mantissa = 2^53
  · subst mantissa
    have logarithm : (2^53 : Nat).log2 = 53 := by decide +kernel
    have target : Format.binary64.targetExponent (totalExponent (2^53) exponent) = exponent+1 := by
      simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,logarithm]
      omega
    have shift : (exponent+1-exponent).toNat = 1 := by omega
    simp only [shiftToTargetExponent,target,shiftToExponent,shift,↓reduceIte]
    rfl
  · have logarithm : mantissa.log2 = 52 :=
      (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr ⟨lower,by omega⟩
    have target : Format.binary64.targetExponent (totalExponent mantissa exponent) = exponent := by
      simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent,logarithm]
      omega
    simp only [shiftToTargetExponent,target,shiftToExponent,Int.sub_self,Int.toNat_zero,
      Int.ofNat_zero,Int.add_zero,same,↓reduceIte]
    rfl

theorem negative_scaled_shift (n D : Nat) (large : 2^52 ≤ n) (scaleBound : D ≤ 1074) :
    shiftToTargetExponent Format.binary64 n (-(D:Int)) .exact =
      (shifted n (n.log2-52), ((n.log2-52:Nat):Int)-D) := by
  have nonzero : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have target : Format.binary64.targetExponent (totalExponent n (-(D:Int))) =
      (n.log2:Int)-D-52 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : ((n.log2:Int)-D-52-(-(D:Int))).toNat = n.log2-52 := by omega
  unfold shiftToTargetExponent
  rw [target]
  simp only [shiftToExponent,gap]
  change (shifted n (n.log2-52),-(D:Int)+((n.log2-52:Nat):Int)) = _
  congr 1
  omega

theorem scaled_round_shape (n D : Nat) (large : 2^52 ≤ n) (bounded : n < 2^1023)
    (scaleBound : D ≤ 1074) :
    ∃ (m : Nat) (e : Int) (positive : 0 < m),
      2^52 ≤ m ∧ m < 2^53 ∧ -(D:Int) ≤ e ∧ e ≤ 971 ∧
      round Format.binary64 .positive n (-(D:Int)) = .finite .positive m e positive ∧
      m*2^(e+D).toNat = roundedInteger n := by
  have nonzero : n ≠ 0 := by omega
  have logLower : 52 ≤ n.log2 := (Nat.le_log2 nonzero).mpr large
  have logUpper : n.log2 < 1023 := (Nat.log2_lt nonzero).mpr bounded
  let places := n.log2-52
  let outputExponent : Int := (places:Int)-D
  let m := (shifted n places).roundedMantissa
  have lower : 2^52 ≤ m := native_rounded_mantissa_lower n large
  have upper : m ≤ 2^53 := native_rounded_mantissa_bound n
  have firstValue : m*2^places = roundedInteger n := by
    simpa only [m,places,roundedInteger,integer_spacing_matches_native] using shifted_rounding n places
  have target : Format.binary64.targetExponent (totalExponent n (-(D:Int))) =
      (n.log2:Int)-D-52 := by
    simp only [Format.targetExponent,totalExponent,Format.mantissaBits,Format.minExponent]
    omega
  have gap : (-(D:Int)-((n.log2:Int)-D-52)).toNat = 0 := by omega
  have decrease : decreaseExponent n (-(D:Int)) ((n.log2:Int)-D-52) = (n,-(D:Int)) := by
    unfold decreaseExponent
    rw [gap]
    simp
  have sameRound : round Format.binary64 .positive n (-(D:Int)) =
      roundWithAccuracy Format.binary64 .positive n (-(D:Int)) .exact := by
    unfold round
    rw [target]
    dsimp only
    rw [decrease]
  rw [sameRound]
  unfold roundWithAccuracy
  rw [negative_scaled_shift n D large scaleBound]
  change ∃ (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa),
    2^52 ≤ mantissa ∧ mantissa < 2^53 ∧ -(D:Int) ≤ exponent ∧ exponent ≤ 971 ∧
    (let pair := shiftToTargetExponent Format.binary64 m outputExponent .exact
     if h : pair.1.mantissa = 0 then UnpackedFloat.zero .positive
     else UnpackedFloat.finite .positive pair.1.mantissa pair.2 (Nat.pos_of_ne_zero h)) =
      UnpackedFloat.finite .positive mantissa exponent positive ∧
    mantissa*2^(exponent+D).toNat = roundedInteger n
  rw [normal_carry_shift_int m outputExponent lower upper (by dsimp [outputExponent]; omega)]
  by_cases carry : m = 2^53
  · simp only [carry,↓reduceIte]
    refine ⟨2^52,outputExponent+1,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_,?_⟩
    · dsimp [outputExponent]; omega
    · dsimp [outputExponent,places]; omega
    · simp
    · have exponents : (outputExponent+1+D).toNat = places+1 := by dsimp [outputExponent]; omega
      rw [exponents,Nat.pow_succ]
      rw [carry] at firstValue
      omega
  · simp only [carry,↓reduceIte]
    refine ⟨m,outputExponent,by omega,lower,by omega,?_,?_,?_,?_⟩
    · dsimp [outputExponent]; omega
    · dsimp [outputExponent,places]; omega
    · simp [show m ≠ 0 by omega]
    · have exponents : (outputExponent+D).toNat = places := by dsimp [outputExponent]; omega
      rw [exponents]
      exact firstValue

/-- A canonical native normal value, expressed at a fixed binary scale. -/
def ScaledNormal (bits : UInt64) (D n : Nat) : Prop :=
  ∃ (m : Nat) (e : Int) (positive : 0 < m),
    2^52 ≤ m ∧ m < 2^53 ∧ -(D:Int) ≤ e ∧ e ≤ 971 ∧
    bits = (Float.Model.pack (.finite .positive m e positive)).toBits ∧
    m*2^(e+D).toNat = n

def ScaledValue (bits : UInt64) (D n : Nat) : Prop :=
  (bits = Number.positiveZero ∧ n = 0) ∨ ScaledNormal bits D n

def incrementBits (c D : Nat) (positive : 0 < c) : UInt64 :=
  (Float.Model.pack (.finite .positive c (-(D:Int)) positive)).toBits

theorem native_scaled_normal_add (bits : UInt64) (n c D : Nat) (cPositive : 0 < c)
    (value : ScaledNormal bits D n) (cLower : 2^52 ≤ c) (cUpper : c < 2^53)
    (scaleBound : D ≤ 1074) :
    Number.add bits (incrementBits c D cPositive) =
      (Float.Model.pack (round Format.binary64 .positive (n+c) (-(D:Int)))).toBits := by
  obtain ⟨m,e,positive,lower,upper,scaleLower,expUpper,shape,represented⟩ := value
  rw [shape]
  simp only [incrementBits,Number.add,Float.Model.add,
    normal_model_unpack m e positive lower upper (by omega) expUpper,
    normal_model_unpack c (-(D:Int)) cPositive cLower cUpper (by omega) (by omega)]
  rw [native_positive_add_alignment_int]
  have minimum : min e (-(D:Int)) = -(D:Int) := Int.min_eq_right scaleLower
  have otherShift : (-(D:Int)-(-(D:Int))).toNat = 0 := by omega
  have firstShift : e-(-(D:Int)) = e+D := by omega
  rw [minimum,otherShift,firstShift,represented]
  simp only [Nat.pow_zero,Nat.mul_one]
  have comparison : compare ((n+c : Nat) : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp only [normalize,comparison,Int.toNat_natCast]

theorem native_scaled_add_value (bits : UInt64) (n c D : Nat) (cPositive : 0 < c)
    (value : ScaledValue bits D n) (cLower : 2^52 ≤ c) (cUpper : c < 2^53)
    (scaleBound : D ≤ 1074) (sumBound : n+c < 2^1023) :
    ScaledNormal (Number.add bits (incrementBits c D cPositive)) D (roundedInteger (n+c)) := by
  rcases value with ⟨zero,nzero⟩ | normal
  · subst bits; subst n
    rw [incrementBits,number_add_zero_left c (-(D:Int)) cPositive cLower cUpper (by omega) (by omega)]
    have smallRound : roundedInteger c = c := by
      simp [roundedInteger,integerSpacing,if_pos cUpper,unit_spacing_exact]
    rw [Nat.zero_add,smallRound]
    exact ⟨c,-(D:Int),cPositive,cLower,cUpper,by omega,by omega,rfl,by change c*2^((-(D:Int))+D).toNat = c; rw [show (-(D:Int)+D).toNat = 0 by omega]; simp⟩
  · rw [native_scaled_normal_add bits n c D cPositive normal cLower cUpper scaleBound]
    obtain ⟨m,e,positive,lower,upper,expLower,expUpper,shape,represented⟩ :=
      scaled_round_shape (n+c) D (by omega) sumBound scaleBound
    rw [shape]
    exact ⟨m,e,positive,lower,upper,expLower,expUpper,rfl,represented⟩

def numeratorIterations (start c : Nat) : Nat → Nat
  | 0 => start
  | k+1 => roundedInteger (numeratorIterations start c k+c)

def nativeIterations (start credit : UInt64) : Nat → UInt64
  | 0 => start
  | k+1 => Number.add (nativeIterations start credit k) credit

theorem numerator_iterations_bounded (start c k : Nat) (startBound : start ≤ 2^106)
    (creditBound : c < 2^53) : numeratorIterations start c k ≤ 2^106 := by
  induction k with
  | zero => exact startBound
  | succ k ih =>
    exact FractionalRoundingBridge.rounded_power_barrier _ 106 (by decide)
      (by change numeratorIterations start c k+c ≤ 2^106+2^(106-53); omega)

theorem native_iterations_scaled (startBits : UInt64) (start c D k : Nat)
    (cPositive : 0 < c) (initial : ScaledValue startBits D start)
    (startBound : start ≤ 2^106) (cLower : 2^52 ≤ c) (cUpper : c < 2^53)
    (scaleBound : D ≤ 1074) :
    ScaledValue (nativeIterations startBits (incrementBits c D cPositive) k)
      D (numeratorIterations start c k) := by
  induction k with
  | zero => exact initial
  | succ k ih =>
    apply Or.inr
    apply native_scaled_add_value _ _ c D cPositive ih cLower cUpper scaleBound
    have bound := numerator_iterations_bounded start c k startBound cUpper
    omega

theorem normal_scaled_cross_product (bits : UInt64) (D n : Nat)
    (scaleBound : D ≤ 1074) (value : ScaledNormal bits D n) :
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
    (Number.magnitudeFraction bits).1 * 2^D = n*(Number.magnitudeFraction bits).2 := by
  obtain ⟨m,e,positive,lower,upper,scaleLower,expUpper,shape,represented⟩ := value
  rw [shape]
  obtain ⟨finite,sign⟩ := normal_pack_finite_nonnegative_int m e positive lower upper (by omega) expUpper
  refine ⟨finite,sign,?_⟩
  obtain ⟨exponentField,fraction⟩ := normal_pack_fields_int m e positive lower upper (by omega) expUpper
  have nonzero : (e+1075).toNat ≠ 0 := by omega
  have cancel : (((e+1075).toNat:Int)-1075) = e := by omega
  simp only [Number.magnitudeFraction,Number.dyadic,exponentField,fraction,
    beq_iff_eq,nonzero,↓reduceIte,cancel,Nat.add_sub_of_le lower]
  by_cases nonnegative : 0 ≤ e
  · simp only [if_pos nonnegative,Nat.mul_one]
    have gap : e.toNat+D = (e+D).toNat := by omega
    rw [Nat.mul_assoc,← Nat.pow_add,gap]
    exact represented
  · simp only [if_neg nonnegative]
    rw [← represented,Nat.mul_assoc,← Nat.pow_add]
    have gap : (e+D).toNat+(-e).toNat = D := by omega
    rw [gap]

theorem scaled_cross_product (bits : UInt64) (D n : Nat)
    (scaleBound : D ≤ 1074) (value : ScaledValue bits D n) :
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
    (Number.magnitudeFraction bits).1 * 2^D = n*(Number.magnitudeFraction bits).2 := by
  rcases value with ⟨zero,nzero⟩ | normal
  · subst bits; subst n
    simp [Number.isFinite,Number.signBit,Number.magnitudeFraction,Number.dyadic,
      Number.exponentField,Number.fraction,Number.positiveZero]
  · exact normal_scaled_cross_product bits D n scaleBound normal

open CookieClicker.FullGame.BootstrapArithmetic

theorem passive_credit_encoding :
    Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30) =
      incrementBits passiveIncrement 61 (by decide) := by decide +kernel

theorem cent_credit_encoding :
    Number.ofScientific 1 (-2) = incrementBits centNumerator 59 (by decide) := by decide +kernel

theorem native_passive_scaled (k : Nat) :
    ScaledValue (nativeIterations Number.positiveZero
      (Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30)) k)
      61 (numeratorIterations 0 passiveIncrement k) := by
  rw [passive_credit_encoding]
  exact native_iterations_scaled Number.positiveZero 0 passiveIncrement 61 k (by decide)
    (Or.inl ⟨rfl,rfl⟩) (by decide) (by decide) (by decide) (by decide)

theorem passive_numerator_hits_target_from (start : Nat) :
    ∃ k ≤ 512*1000000000, passiveTarget ≤ numeratorIterations start passiveIncrement k := by
  apply Classical.byContradiction
  intro missing
  have below : ∀ k ≤ 512*1000000000, numeratorIterations start passiveIncrement k < passiveTarget := by
    intro k bounded
    by_cases enough : passiveTarget ≤ numeratorIterations start passiveIncrement k
    · exact False.elim (missing ⟨k,bounded,enough⟩)
    · omega
  have progress : ∀ k ≤ 512*1000000000, k*passiveLowerStep ≤ numeratorIterations start passiveIncrement k := by
    intro k
    induction k with
    | zero => intro _; simp [numeratorIterations]
    | succ k ih =>
      intro bound
      have previous := ih (by omega)
      have step := passive_step_progress _ (below k (by omega))
      change (k+1)*passiveLowerStep ≤ roundedInteger (numeratorIterations start passiveIncrement k+passiveIncrement)
      rw [Nat.add_mul,Nat.one_mul]
      omega
  have bound := progress (512*1000000000) (Nat.le_refl _)
  have notEnough := below (512*1000000000) (Nat.le_refl _)
  have exactTarget : 512*1000000000*passiveLowerStep = passiveTarget := by decide +kernel
  rw [exactTarget] at bound
  omega

theorem passive_numerator_hits_target :
    ∃ k ≤ 512*1000000000, passiveTarget ≤ numeratorIterations 0 passiveIncrement k :=
  passive_numerator_hits_target_from 0

theorem native_passive_reaches_billion_from (startBits : UInt64) (start : Nat)
    (initial : ScaledValue startBits 61 start) (bounded : start ≤ 2^106) :
    ∃ k ≤ 512*1000000000,
      let bits := nativeIterations startBits
        (Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30)) k
      Number.isFinite bits = true ∧ Number.signBit bits = false ∧
        1000000000*(Number.magnitudeFraction bits).2 ≤ (Number.magnitudeFraction bits).1 := by
  obtain ⟨k,bound,reached⟩ := passive_numerator_hits_target_from start
  have value := native_iterations_scaled startBits start passiveIncrement 61 k (by decide)
    initial bounded (by decide) (by decide) (by decide)
  rw [← passive_credit_encoding] at value
  obtain ⟨finite,sign,equality⟩ := scaled_cross_product _ 61 _ (by decide) value
  refine ⟨k,bound,finite,sign,?_⟩
  have multiplied := Nat.mul_le_mul_right (Number.magnitudeFraction
    (nativeIterations startBits (Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30)) k)).2 reached
  unfold passiveTarget passiveScale at multiplied
  rw [← equality] at multiplied
  have rearrange : ∀ d : Nat, 1000000000*2^61*d = (1000000000*d)*2^61 := by intro d; omega
  rw [rearrange] at multiplied
  exact Nat.le_of_mul_le_mul_right multiplied (by decide)

theorem native_passive_reaches_billion :
    ∃ k ≤ 512*1000000000,
      let bits := nativeIterations Number.positiveZero
        (Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30)) k
      Number.isFinite bits = true ∧ Number.signBit bits = false ∧
        1000000000*(Number.magnitudeFraction bits).2 ≤ (Number.magnitudeFraction bits).1 :=
  native_passive_reaches_billion_from Number.positiveZero 0 (Or.inl ⟨rfl,rfl⟩) (by decide)

theorem native_fifteen_scaled : ScaledNormal (Number.ofNat 15) 61 (15*2^61) := by
  exact ⟨15*2^49,-49,by decide,by decide,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel⟩

/-- The earned counter after the fifteen initial cookie clicks also reaches
one billion. The Cursor purchase reduces the bank but does not spend earned. -/
theorem native_earned15_reaches_billion :
    ∃ k ≤ 512*1000000000,
      let bits := nativeIterations (Number.ofNat 15)
        (Number.div (Number.ofScientific 1 (-1)) (Number.ofNat 30)) k
      Number.isFinite bits = true ∧ Number.signBit bits = false ∧
        1000000000*(Number.magnitudeFraction bits).2 ≤ (Number.magnitudeFraction bits).1 :=
  native_passive_reaches_billion_from (Number.ofNat 15) (15*2^61)
    (Or.inr native_fifteen_scaled) (by decide)

theorem native_one_scaled : ScaledNormal Number.one 59 multiplierScale := by
  exact ⟨2^52,-52,by decide,by decide,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel⟩

theorem cent_numerators_agree (k : Nat) :
    numeratorIterations multiplierScale centNumerator k = centIterations k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [numeratorIterations,centIterations,ih]

theorem native_cent_scaled (k : Nat) :
    ScaledValue (nativeIterations Number.one (Number.ofScientific 1 (-2)) k)
      59 (centIterations k) := by
  rw [cent_credit_encoding,← cent_numerators_agree]
  exact native_iterations_scaled Number.one multiplierScale centNumerator 59 k (by decide)
    (Or.inr native_one_scaled) (by decide) (by decide) (by decide) (by decide)

theorem scaled_cap_bits (bits : UInt64) (value : ScaledValue bits 59 (2^106)) :
    bits = Number.ofNat (2^47) := by
  rcases value with ⟨_,zero⟩ | normal
  · omega
  · obtain ⟨m,e,positive,lower,upper,scaleLower,expUpper,shape,represented⟩ := normal
    change m*2^(e+59).toNat = 2^106 at represented
    change (-59:Int) ≤ e at scaleLower
    have logM : m.log2 = 52 := (Nat.log2_eq_iff (by omega : m ≠ 0)).mpr ⟨lower,upper⟩
    have logEquality := congrArg Nat.log2 represented
    rw [log2_scaled m (e+59).toNat (by omega),logM] at logEquality
    have logCap : (2^106:Nat).log2 = 106 := by decide +kernel
    rw [logCap] at logEquality
    have gap : (e+59).toNat = 54 := by omega
    have exp : e = -5 := by omega
    rw [gap] at represented
    have mantissa : m = 2^52 := by omega
    subst m; subst e
    rw [shape]
    change (Float.Model.pack (.finite .positive (2^52) (-5) (by decide))).toBits = Number.ofNat (2^47)
    decide +kernel

/-- The actual binary64 cent-increment loop reaches exactly the native cap.
The count is finite. This does not assert zero wall time for a source/UI loop. -/
theorem native_cent_cap_reached :
    nativeIterations Number.one (Number.ofScientific 1 (-2)) (2^56) = Number.ofNat (2^47) := by
  have value := native_cent_scaled (2^56)
  rw [cent_cap_reached_by_finite_prefix] at value
  exact scaled_cap_bits _ value

end CookieClicker.JavaScript.ScaledArithmeticBridge

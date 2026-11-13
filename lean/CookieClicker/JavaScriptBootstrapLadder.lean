import CookieClicker.JavaScriptBoundedBank

/-! Native binary64 credit progress for the fixed no-upgrade purchase ladder.
The source CalculateGains/Logic invariant and native purchase admission are
separate obligations; this module does not assert full-game reachability. -/
namespace CookieClicker.JavaScript.BootstrapLadder
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge ScaledArithmeticBridge FractionalArithmeticBridge BoundedAddition
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure Stage where
  cpsBits : UInt64
  mantissa : Nat
  exponent : Int
  gainExponent : Int
  target : Nat
  budget : Nat
  gainQuanta : Nat
  deriving DecidableEq

def stages : Array Stage := #[
  ⟨4591870180066957722,7686143364045647,-61,-10,100,102400,1⟩,
  ⟨4607632778762754458,5284223562781382,-57,-6,1100,70400,16⟩,
  ⟨4621312462630892339,5464367547876202,-54,-3,12000,96000,128⟩,
  ⟨4633092190406233293,8421731303182828,-52,-1,130000,260000,512⟩,
  ⟨4644268506200250778,5931616009215891,-49,2,1400000,350000,4096⟩,
  ⟨4655262303064057446,8050653458885946,-47,4,20000000,1250000,16384⟩,
  ⟨4666457145629002957,5580300053908903,-44,7,330000000,2578125,131072⟩,
  ⟨4677588010361107251,7845543229763092,-42,9,1000000000,1953125,524288⟩]

def stage (i : Fin 8) : Stage := stages[i.val]'(by have := i.isLt; simpa [stages] using this)

theorem stage_valid : ∀ i : Fin 8,
    0 < (stage i).mantissa ∧ 2^52 ≤ (stage i).mantissa ∧ (stage i).mantissa < 2^53 ∧
    -1074 ≤ (stage i).exponent ∧ (stage i).exponent ≤ -23 ∧
    DyadicLE (stage i).mantissa (stage i).exponent (2^11) ∧
    -10 ≤ (stage i).gainExponent ∧ (stage i).exponent ≤ (stage i).gainExponent+1 ∧
    2^((stage i).gainExponent+1-(stage i).exponent).toNat ≤ (stage i).mantissa ∧
    (stage i).gainQuanta = 2^((stage i).gainExponent+10).toNat ∧
    (stage i).budget*(stage i).gainQuanta = (stage i).target*1024 ∧
    0 < (stage i).target ∧ (stage i).target < 2^30 := by
  unfold DyadicLE
  decide +kernel

def credit (i : Fin 8) : UInt64 := Number.div (stage i).cpsBits (Number.ofNat 30)

theorem credit_encoding : ∀ i : Fin 8,
    credit i = (Float.Model.pack (.finite .positive (stage i).mantissa (stage i).exponent
      (stage_valid i).1)).toBits := by decide +kernel

def quanta (bits : UInt64) : Nat :=
  (Number.magnitudeFraction bits).1*1024 / (Number.magnitudeFraction bits).2

theorem fraction_denominator_positive (bits : UInt64) :
    0 < (Number.magnitudeFraction bits).2 := by
  unfold Number.magnitudeFraction
  split <;> split <;> simp [Nat.two_pow_pos]

theorem quanta_of_cross (bits : UInt64) (n D : Nat) (scale : 10 ≤ D)
    (cross : (Number.magnitudeFraction bits).1*2^D = n*(Number.magnitudeFraction bits).2) :
    quanta bits = n/2^(D-10) := by
  let a := (Number.magnitudeFraction bits).1
  let b := (Number.magnitudeFraction bits).2
  have positive : 0 < b := fraction_denominator_positive bits
  have scaled : (a*1024)*2^(D-10) = n*b := by
    have powers : 1024*2^(D-10) = 2^D := by
      change 2^10*2^(D-10)=2^D
      rw [← Nat.pow_add,show 10+(D-10)=D by omega]
    rw [Nat.mul_assoc,powers]
    exact cross
  change a*1024/b = _
  calc
    a*1024/b = ((a*1024)*2^(D-10))/(b*2^(D-10)) :=
      (Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)).symm
    _ = (n*b)/(2^(D-10)*b) := by rw [scaled,Nat.mul_comm b (2^(D-10))]
    _ = n/2^(D-10) := Nat.mul_div_mul_right _ _ positive

theorem scaled_quanta (bits : UInt64) (D n : Nat) (scaleLower : 10 ≤ D)
    (scaleUpper : D ≤ 1074) (value : ScaledNormal bits D n) :
    quanta bits = n/2^(D-10) :=
  quanta_of_cross bits n D scaleLower (normal_scaled_cross_product bits D n scaleUpper value).2.2

theorem quanta_below (bits : UInt64) (target : Nat) :
    quanta bits < target*1024 ↔
      (Number.magnitudeFraction bits).1 < target*(Number.magnitudeFraction bits).2 := by
  unfold quanta
  rw [Nat.div_lt_iff_lt_mul (fraction_denominator_positive bits)]
  rw [Nat.mul_right_comm target 1024 (Number.magnitudeFraction bits).2]
  exact Nat.mul_lt_mul_right (by decide : 0<1024)


def Normal (bits : UInt64) : Prop :=
  ∃ (m : Nat) (e : Int) (positive : 0<m), 2^52≤m ∧ m<2^53 ∧
    -1074≤e ∧ e≤971 ∧ bits=(Float.Model.pack (.finite .positive m e positive)).toBits

def BankShape (bits : UInt64) : Prop := bits=0 ∨ Normal bits

theorem normal_magnitude (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971) :
    Number.magnitudeFraction (Float.Model.pack (.finite .positive m e positive)).toBits =
      if 0≤e then (m*2^e.toNat,1) else (m,2^(-e).toNat) := by
  obtain ⟨exponentField,fraction⟩ := normal_pack_fields_int m e positive lower upper expLower expUpper
  have nonzero : (e+1075).toNat ≠ 0 := by omega
  have cancel : (((e+1075).toNat:Int)-1075)=e := by omega
  simp only [Number.magnitudeFraction,Number.dyadic,exponentField,fraction,beq_iff_eq,
    nonzero,↓reduceIte,cancel,Nat.add_sub_of_le lower]

theorem normal_bank_bound (i : Fin 8) (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971)
    (below : quanta (Float.Model.pack (.finite .positive m e positive)).toBits < (stage i).target*1024) :
    DyadicLE m e (2^30) := by
  have amount := (quanta_below _ _).mp below
  rw [normal_magnitude m e positive lower upper expLower expUpper] at amount
  have bound := (stage_valid i).2.2.2.2.2.2.2.2.2.2.2.2
  by_cases nonnegative : 0≤e
  · simp only [if_pos nonnegative,Prod.fst,Prod.snd,Nat.mul_one] at amount
    exact (show DyadicLE m e (2^30) from by simp only [DyadicLE,if_pos nonnegative]; omega)
  · simp only [if_neg nonnegative,Prod.fst,Prod.snd] at amount
    have order := Nat.mul_le_mul_right (2^(-e).toNat) (Nat.le_of_lt bound)
    simp only [DyadicLE,if_neg nonnegative]
    omega

theorem scaled_is_normal (bits : UInt64) (D n : Nat) (bound : D≤1074)
    (value : ScaledNormal bits D n) : Normal bits := by
  obtain ⟨m,e,positive,lower,upper,lo,hi,shape,_⟩ := value
  exact ⟨m,e,positive,lower,upper,by omega,hi,shape⟩

theorem native_normal_progress (i : Fin 8) (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971)
    (below : quanta (Float.Model.pack (.finite .positive m e positive)).toBits < (stage i).target*1024) :
    let bank := (Float.Model.pack (.finite .positive m e positive)).toBits
    Normal (Number.add bank (credit i)) ∧
      quanta bank+(stage i).gainQuanta ≤ quanta (Number.add bank (credit i)) := by
  rcases stage_valid i with ⟨cp,clo,chi,ceLo,ceHi,cbound,glo,cg,clower,qeq,_,_,_⟩
  let D := denominatorExponent e (stage i).exponent
  let bankN := m*2^(e-min e (stage i).exponent).toNat
  have dLower : 10≤D := by dsimp [D,denominatorExponent]; omega
  have dUpper : D≤1074 := by dsimp [D,denominatorExponent]; omega
  have common : min e (stage i).exponent = -(D:Int) := by dsimp [D,denominatorExponent]; omega
  have bankScale : ScaledNormal (Float.Model.pack (.finite .positive m e positive)).toBits D bankN := by
    refine ⟨m,e,positive,lower,upper,by omega,expUpper,rfl,?_⟩
    dsimp [bankN]
    rw [common]
    congr 2
    omega
  have progress := native_fixed_credit_progress m (stage i).mantissa e (stage i).exponent (stage i).gainExponent
    positive cp lower upper clo chi expLower expUpper ceLo ceHi
    (normal_bank_bound i m e positive lower upper expLower expUpper below)
    cbound (by omega) cg clower
  dsimp only at progress ⊢
  rw [credit_encoding]
  obtain ⟨n,value,order⟩ := progress
  refine ⟨scaled_is_normal _ D n dUpper value,?_⟩
  rw [scaled_quanta _ D bankN dLower dUpper bankScale,scaled_quanta _ D n dLower dUpper value]
  have power : 2^((D:Int)+(stage i).gainExponent).toNat = (stage i).gainQuanta*2^(D-10) := by
    rw [qeq,← Nat.pow_add]
    congr 1
    omega
  change bankN+2^((D:Int)+(stage i).gainExponent).toNat≤n at order
  rw [power] at order
  have divided := Nat.div_le_div_right (c:=2^(D-10)) order
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)] at divided
  exact divided

theorem zero_quanta : quanta 0=0 := by decide +kernel

theorem credit_quanta : ∀ i : Fin 8, (stage i).gainQuanta ≤ quanta (credit i) := by decide +kernel

theorem native_zero_progress (i : Fin 8) :
    Normal (Number.add 0 (credit i)) ∧
      quanta 0+(stage i).gainQuanta ≤ quanta (Number.add 0 (credit i)) := by
  rcases stage_valid i with ⟨cp,clo,chi,ceLo,ceHi,_,_,_,_,_,_,_,_⟩
  have zero : Number.add 0 (credit i)=credit i := by
    rw [credit_encoding]
    exact number_add_zero_left _ _ cp clo chi ceLo (by omega)
  rw [zero,zero_quanta,Nat.zero_add]
  refine ⟨?_,credit_quanta i⟩
  exact ⟨(stage i).mantissa,(stage i).exponent,cp,clo,chi,ceLo,by omega,credit_encoding i⟩

theorem native_credit_progress (i : Fin 8) (bits : UInt64) (shape : BankShape bits)
    (below : quanta bits < (stage i).target*1024) :
    BankShape (Number.add bits (credit i)) ∧
      quanta bits+(stage i).gainQuanta ≤ quanta (Number.add bits (credit i)) := by
  rcases shape with rfl | ⟨m,e,positive,lower,upper,lo,hi,rfl⟩
  · exact ⟨Or.inr (native_zero_progress i).1,(native_zero_progress i).2⟩
  · obtain ⟨normal,progress⟩ := native_normal_progress i m e positive lower upper lo hi below
    exact ⟨Or.inr normal,progress⟩

theorem native_stage_reaches_target (i : Fin 8) (bits : UInt64) (shape : BankShape bits) :
    ∃ k≤(stage i).budget, (stage i).target*1024≤quanta (nativeIterations bits (credit i) k) := by
  apply Classical.byContradiction
  intro missing
  have below : ∀ k≤(stage i).budget,
      quanta (nativeIterations bits (credit i) k)<(stage i).target*1024 := by
    intro k bound
    by_cases enough : (stage i).target*1024≤quanta (nativeIterations bits (credit i) k)
    · exact False.elim (missing ⟨k,bound,enough⟩)
    · omega
  have progress : ∀ k≤(stage i).budget,
      BankShape (nativeIterations bits (credit i) k) ∧
      k*(stage i).gainQuanta≤quanta (nativeIterations bits (credit i) k) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨shape,by simp [nativeIterations]⟩
    | succ k ih =>
      intro bound
      obtain ⟨oldShape,oldProgress⟩ := ih (by omega)
      obtain ⟨nextShape,nextProgress⟩ := native_credit_progress i _ oldShape (below k (by omega))
      refine ⟨nextShape,?_⟩
      rw [Nat.add_mul,Nat.one_mul]
      change k*(stage i).gainQuanta+(stage i).gainQuanta≤quanta (Number.add _ _)
      omega
  have hit := (progress (stage i).budget (Nat.le_refl _)).2
  have short := below (stage i).budget (Nat.le_refl _)
  have exactBudget := (stage_valid i).2.2.2.2.2.2.2.2.2.2.1
  rw [exactBudget] at hit
  omega


def FractionBound (bits : UInt64) (bound : Nat) : Prop :=
  (Number.magnitudeFraction bits).1 ≤ bound*(Number.magnitudeFraction bits).2

def SafeBank (bits : UInt64) : Prop := BankShape bits ∧ FractionBound bits (2^30)

theorem stage_target_bounds : ∀ i : Fin 8, 64≤(stage i).target ∧ (stage i).target≤1000000000 := by decide +kernel

theorem normal_bound_iff (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971) (bound : Nat) :
    FractionBound (Float.Model.pack (.finite .positive m e positive)).toBits bound ↔ DyadicLE m e bound := by
  unfold FractionBound
  rw [normal_magnitude m e positive lower upper expLower expUpper]
  by_cases sign : 0≤e <;> simp [DyadicLE,sign]

theorem normal_above_iff (m : Nat) (e : Int) (positive : 0<m)
    (lower : 2^52≤m) (upper : m<2^53) (expLower : -1074≤e) (expUpper : e≤971) (bound : Nat) :
    bound*(Number.magnitudeFraction (Float.Model.pack (.finite .positive m e positive)).toBits).2 ≤
      (Number.magnitudeFraction (Float.Model.pack (.finite .positive m e positive)).toBits).1 ↔ DyadicGE m e bound := by
  rw [normal_magnitude m e positive lower upper expLower expUpper]
  by_cases sign : 0≤e <;> simp [DyadicGE,sign]

theorem credit_bounded : ∀ i : Fin 8, FractionBound (credit i) (2^30) := by
  unfold FractionBound
  decide +kernel

theorem native_credit_bound (i : Fin 8) (bits : UInt64) (shape : BankShape bits)
    (below : quanta bits < (stage i).target*1024) :
    FractionBound (Number.add bits (credit i)) (2^30) := by
  rcases shape with rfl | ⟨m,e,positive,lower,upper,lo,hi,rfl⟩
  · have same : Number.add 0 (credit i)=credit i := by
      rw [credit_encoding]
      rcases stage_valid i with ⟨cp,clo,chi,ceLo,ceHi,_⟩
      exact number_add_zero_left _ _ cp clo chi ceLo (by omega)
    rw [same]
    exact credit_bounded i
  · rcases stage_valid i with ⟨cp,clo,chi,ceLo,ceHi,cbound,_⟩
    have amount := (quanta_below _ _).mp below
    have target := (stage_target_bounds i).2
    have order := Nat.mul_le_mul_right (Number.magnitudeFraction (Float.Model.pack (.finite .positive m e positive)).toBits).2 target
    have sourceBound : FractionBound (Float.Model.pack (.finite .positive m e positive)).toBits 1000000000 := by
      unfold FractionBound
      omega
    have bounded := (normal_bound_iff m e positive lower upper lo hi 1000000000).mp sourceBound
    rw [credit_encoding]
    exact BoundedBank.native_add_billion_bound m (stage i).mantissa e (stage i).exponent
      positive cp lower upper clo chi lo hi ceLo (by omega) bounded cbound

def stoppedIterations (i : Fin 8) (bits : UInt64) : Nat → UInt64
  | 0 => bits
  | k+1 => let before := stoppedIterations i bits k
      if quanta before < (stage i).target*1024 then Number.add before (credit i) else before

theorem stopped_safe (i : Fin 8) (bits : UInt64) (initial : SafeBank bits) (n : Nat) :
    SafeBank (stoppedIterations i bits n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    simp only [stoppedIterations]
    split
    · rename_i below
      exact ⟨(native_credit_progress i _ ih.1 below).1,native_credit_bound i _ ih.1 below⟩
    · exact ih

theorem stopped_progress (i : Fin 8) (bits : UInt64) (initial : SafeBank bits) (n : Nat) :
    min (n*(stage i).gainQuanta) ((stage i).target*1024) ≤ quanta (stoppedIterations i bits n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [stoppedIterations]
    split
    · rename_i below
      have shape := (stopped_safe i bits initial n).1
      have next := (native_credit_progress i _ shape below).2
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · rename_i enough
      omega

theorem stopped_native (i : Fin 8) (bits : UInt64) (n : Nat) :
    ∃ k≤n, stoppedIterations i bits n=nativeIterations bits (credit i) k := by
  induction n with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨k,bound,same⟩ := ih
    simp only [stoppedIterations]
    split
    · refine ⟨k+1,by omega,?_⟩
      rw [same,nativeIterations]
    · exact ⟨k,by omega,same⟩

theorem native_safe_stage_reaches (i : Fin 8) (bits : UInt64) (initial : SafeBank bits) :
    ∃ k≤(stage i).budget, SafeBank (nativeIterations bits (credit i) k) ∧
      (stage i).target*1024≤quanta (nativeIterations bits (credit i) k) := by
  obtain ⟨k,bound,same⟩ := stopped_native i bits (stage i).budget
  refine ⟨k,bound,?_,?_⟩
  · rw [← same]
    exact stopped_safe i bits initial (stage i).budget
  · have progress := stopped_progress i bits initial (stage i).budget
    have exactBudget := (stage_valid i).2.2.2.2.2.2.2.2.2.2.1
    rw [exactBudget,Nat.min_self,same] at progress
    exact progress

def costMantissa (i : Fin 8) : Nat := (Number.dyadic (Number.ofNat (stage i).target)).1
def costExponent (i : Fin 8) : Int := (Number.dyadic (Number.ofNat (stage i).target)).2

theorem cost_valid : ∀ i : Fin 8,
    0<costMantissa i ∧ 2^52≤costMantissa i ∧ costMantissa i<2^53 ∧
    -1074≤costExponent i ∧ costExponent i≤0 ∧
    DyadicGE (costMantissa i) (costExponent i) 64 ∧
    DyadicLE (costMantissa i) (costExponent i) (stage i).target := by
  unfold DyadicGE DyadicLE
  decide +kernel

theorem cost_encoding : ∀ i : Fin 8,
    Number.ofNat (stage i).target=(Float.Model.pack
      (.finite .positive (costMantissa i) (costExponent i) (cost_valid i).1)).toBits := by decide +kernel

theorem native_purchase_safe (i : Fin 8) (bits : UInt64) (initial : SafeBank bits)
    (enough : (stage i).target*1024≤quanta bits) :
    SafeBank (Number.sub bits (Number.ofNat (stage i).target)) := by
  have above : (stage i).target*(Number.magnitudeFraction bits).2≤(Number.magnitudeFraction bits).1 := by
    have equivalent := quanta_below bits (stage i).target
    omega
  rcases initial.1 with rfl | ⟨m,e,positive,lower,upper,lo,hi,rfl⟩
  · rw [zero_quanta] at enough
    have positive := (stage_valid i).2.2.2.2.2.2.2.2.2.2.2.1
    omega
  · rcases cost_valid i with ⟨cp,clo,chi,ceLo,ceHi,c64,costUpper⟩
    have bankTarget := (normal_above_iff m e positive lower upper lo hi (stage i).target).mp above
    have bank64 : DyadicGE m e 64 := by
      have target := (stage_target_bounds i).1
      unfold DyadicGE at bankTarget ⊢
      split at bankTarget <;> rename_i sign
      · simp only [if_pos sign]; omega
      · simp only [if_neg sign]
        have order := Nat.mul_le_mul_right (2^(-e).toNat) target
        omega
    have bankBound := (normal_bound_iff m e positive lower upper lo hi (2^30)).mp initial.2
    have nonpositive : min e (costExponent i)≤0 := by omega
    have first := aligned_dyadic_lower m (stage i).target e (min e (costExponent i))
      (Int.min_le_left _ _) nonpositive bankTarget
    have second := aligned_dyadic_upper (costMantissa i) (stage i).target (costExponent i)
      (min e (costExponent i)) (Int.min_le_right _ _) nonpositive costUpper
    have affordable : costMantissa i*2^(costExponent i-min e (costExponent i)).toNat≤
        m*2^(e-min e (costExponent i)).toNat := by omega
    obtain ⟨dBound,value⟩ := BoundedSubtraction.native_bounded_purchase_value m (costMantissa i) e (costExponent i)
      positive cp lower upper clo chi hi ceHi bank64 c64 bankBound affordable
    rw [cost_encoding]
    refine ⟨?_,?_⟩
    · rcases value with ⟨zero,_⟩ | normal
      · exact Or.inl zero
      · exact Or.inr (scaled_is_normal _ _ _ (by omega) normal)
    · exact BoundedBank.native_sub_bank_bound m (costMantissa i) e (costExponent i)
        positive cp lower upper clo chi hi ceHi bank64 c64 bankBound affordable


theorem stopped_first_hit (i : Fin 8) (bits : UInt64) (n : Nat) :
    ∃ k≤n, stoppedIterations i bits n=nativeIterations bits (credit i) k ∧
      ∀ j<k, quanta (nativeIterations bits (credit i) j)<(stage i).target*1024 := by
  induction n with
  | zero => exact ⟨0,by omega,rfl,by intro j h; omega⟩
  | succ n ih =>
    obtain ⟨k,bound,same,first⟩ := ih
    simp only [stoppedIterations]
    split
    · rename_i below
      refine ⟨k+1,by omega,by rw [same,nativeIterations],?_⟩
      intro j hj
      by_cases old : j<k
      · exact first j old
      · have eq : j=k := by omega
        subst j
        simpa only [same] using below
    · exact ⟨k,by omega,same,first⟩

/-- Every fixed stage has a finite first hitting time under the actual binary64
addition, with a safe bank at the hit. No waiting after the first hit is needed. -/
theorem native_safe_first_hit (i : Fin 8) (bits : UInt64) (initial : SafeBank bits) :
    ∃ k≤(stage i).budget, SafeBank (nativeIterations bits (credit i) k) ∧
      (stage i).target*1024≤quanta (nativeIterations bits (credit i) k) ∧
      ∀ j<k, quanta (nativeIterations bits (credit i) j)<(stage i).target*1024 := by
  obtain ⟨k,bound,same,first⟩ := stopped_first_hit i bits (stage i).budget
  refine ⟨k,bound,?_,?_,first⟩
  · rw [← same]
    exact stopped_safe i bits initial (stage i).budget
  · have progress := stopped_progress i bits initial (stage i).budget
    have exactBudget := (stage_valid i).2.2.2.2.2.2.2.2.2.2.1
    rw [exactBudget,Nat.min_self,same] at progress
    exact progress

/-- A purchase-stage transition uses only the actual native addition iterations
and one actual native subtraction at the first affordable credit. -/
def PurchaseStage (i : Fin 8) (before after : UInt64) (ticks : Nat) : Prop :=
  ticks≤(stage i).budget ∧
  (stage i).target*1024≤quanta (nativeIterations before (credit i) ticks) ∧
  (∀ j<ticks, quanta (nativeIterations before (credit i) j)<(stage i).target*1024) ∧
  after=Number.sub (nativeIterations before (credit i) ticks) (Number.ofNat (stage i).target)

theorem native_purchase_stage (i : Fin 8) (before : UInt64) (initial : SafeBank before) :
    ∃ after ticks, PurchaseStage i before after ticks ∧ SafeBank after := by
  obtain ⟨ticks,bound,safe,enough,first⟩ := native_safe_first_hit i before initial
  exact ⟨_,ticks,⟨bound,enough,first,rfl⟩,native_purchase_safe i _ safe enough⟩

inductive PurchaseRoute : List (Fin 8) → UInt64 → UInt64 → Nat → Prop
  | nil (bits : UInt64) : PurchaseRoute [] bits bits 0
  | cons (i : Fin 8) (rest : List (Fin 8)) (before middle after : UInt64) (k n : Nat)
      (step : PurchaseStage i before middle k) (tail : PurchaseRoute rest middle after n) :
      PurchaseRoute (i::rest) before after (k+n)

def routeBudget (indices : List (Fin 8)) : Nat := (indices.map (fun i => (stage i).budget)).sum

theorem native_purchase_route (indices : List (Fin 8)) (before : UInt64) (initial : SafeBank before) :
    ∃ after ticks, PurchaseRoute indices before after ticks ∧ SafeBank after ∧ ticks≤routeBudget indices := by
  induction indices generalizing before with
  | nil => exact ⟨before,0,.nil before,initial,by simp [routeBudget]⟩
  | cons i rest ih =>
    obtain ⟨middle,k,step,safe⟩ := native_purchase_stage i before initial
    obtain ⟨after,n,tail,finalSafe,bound⟩ := ih middle safe
    refine ⟨after,k+n,.cons i rest before middle after k n step tail,finalSafe,?_⟩
    have first := step.1
    simp only [routeBudget,List.map_cons,List.sum_cons] at bound ⊢
    omega

def firstSeven : List (Fin 8) := [0,1,2,3,4,5,6]

theorem first_seven_budget : routeBudget firstSeven=4706925 := by decide +kernel

theorem zero_safe : SafeBank 0 := by
  exact ⟨Or.inl rfl,by unfold FractionBound; decide +kernel⟩

/-- The fixed eight-stage native arithmetic route reaches one billion in the
bank within 6,660,050 production credits. This does not assert source callback
preservation, UI reachability, or elapsed-time refinement. -/
theorem native_ladder_billion :
    ∃ beforeFinal finalBank purchaseTicks finalTicks,
      PurchaseRoute firstSeven 0 beforeFinal purchaseTicks ∧
      finalBank=nativeIterations beforeFinal (credit 7) finalTicks ∧
      (∀ j<finalTicks, quanta (nativeIterations beforeFinal (credit 7) j)<1000000000*1024) ∧
      SafeBank finalBank ∧ 1000000000*1024≤quanta finalBank ∧
      purchaseTicks+finalTicks≤6660050 := by
  obtain ⟨before,purchaseTicks,route,safe,bound⟩ := native_purchase_route firstSeven 0 zero_safe
  obtain ⟨finalTicks,finalBound,finalSafe,enough,first⟩ := native_safe_first_hit 7 before safe
  refine ⟨before,_,purchaseTicks,finalTicks,route,rfl,first,finalSafe,enough,?_⟩
  rw [first_seven_budget] at bound
  have last : (stage 7).budget=1953125 := by decide +kernel
  rw [last] at finalBound
  omega

/-- The arithmetic bound plus the stated scheduler allowance. Source scheduling
and ready-entry hypotheses remain separate source-refinement obligations. -/
theorem elapsed_allowance :
    (6660050+8+150)*33=219786864 ∧
    (6660050+8+150)*33+15*20=219787164 ∧
    200+(6660050+8+150)*33+15*20=219787364 := by decide +kernel

end CookieClicker.JavaScript.BootstrapLadder

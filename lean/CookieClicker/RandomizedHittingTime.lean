import CookieClicker.HittingTime

/-! Public controllers with private memory and fresh independent random choices
at every decision. There is no bound on the total number of decisions or draws.
Each decision sampler and native transition is a terminating `Program`; internal
nontermination still requires a separate transition extension. This is a
competitor semantics, not a completed Cookie Clicker value certificate.
-/
namespace CookieClicker.FullGame.RandomizedHittingTime
open HittingTime

abbrev Controller (Observation Action Memory : Type) :=
  Memory → List (Observation × Action) → Observation → Program (Action × Memory)

def chosen {S O A M : Type} (env : Environment S O A) (policy : Controller O A M)
    (memory : M) (history : List (O × A)) (state : S) : Program (A × M) :=
  policy memory history (env.observe state)

theorem observation_noninterference {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) (memory : M) (history : List (O × A)) (left right : S)
    (same : env.observe left = env.observe right) :
    chosen env policy memory history left = chosen env policy memory history right := by
  simp only [chosen,same]

/-- The private sampler has its own independent draws. Its continuation receives
only public history, observation and remembered private state. Native transition
free draws occur after the action has been selected. -/
def capped {S O A M : Type} (env : Environment S O A) (policy : Controller O A M)
    (horizon : Nat) : Nat → M → List (O × A) → S → Rat
  | depth,memory,history,state =>
    if env.complete state then min (env.elapsed state) (horizon : Rat)
    else match depth with
    | 0 => (horizon : Rat)
    | depth + 1 => (chosen env policy memory history state).expect fun decision =>
      (env.step state decision.1).expect fun next =>
        capped env policy horizon depth decision.2 (history ++ [(env.observe state,decision.1)]) next

/-- Private startup memory is sampled independently of the game's startup state. -/
def initialCapped {S O A M : Type} (env : Environment S O A) (policy : Controller O A M)
    (memory : Program M) (initial : Program S) (horizon depth : Nat) : Rat :=
  memory.expect fun remembered => initial.expect fun state =>
    capped env policy horizon depth remembered [] state

def InitialExpected {S O A M : Type} (env : Environment S O A) (policy : Controller O A M)
    (memory : Program M) (initial : Program S) (bound : Rat) : Prop :=
  ∃ horizon : Nat, ∃ margin : Rat, 0 < margin ∧
    ∀ depth, bound + margin ≤ initialCapped env policy memory initial horizon depth

inductive Reachable {S O A M : Type} (env : Environment S O A) (policy : Controller O A M)
    (memory : Program M) (initial : Program S) : M → List (O × A) → S → Prop where
  | initial {remembered : M} {state : S}
      (privateLeaf : memory.Reaches remembered) (gameLeaf : initial.Reaches state) :
      Reachable env policy memory initial remembered [] state
  | step {remembered nextMemory : M} {history : List (O × A)} {state next : S} {action : A}
      (before : Reachable env policy memory initial remembered history state)
      (unfinished : env.complete state = false)
      (decision : (chosen env policy remembered history state).Reaches (action,nextMemory))
      (gameLeaf : (env.step state action).Reaches next) :
      Reachable env policy memory initial nextMemory (history ++ [(env.observe state,action)]) next

/-- This checks action legality only. The user's ban on seed-targeted decision
rules is an additional policy-level condition; it is not inferred from leaves. -/
def ActionAdmissible {S O A M : Type} (env : Environment S O A) (policy : Controller O A M)
    (memory : Program M) (initial : Program S) : Prop :=
  ∀ remembered history state, Reachable env policy memory initial remembered history state →
    env.complete state = false → (chosen env policy remembered history state).All
      (fun decision => env.legal state decision.1)

theorem program_all_iff_reaches {X : Type} (program : Program X) (predicate : X → Prop) :
    program.All predicate ↔ ∀ result, program.Reaches result → predicate result := by
  constructor
  · exact fun all result reaches => program_all_reaches program predicate all result reaches
  · intro all
    induction program with
    | pure result => exact all result .pure
    | draw next ih => exact fun outcome => ih outcome (fun result reaches => all result (.draw outcome reaches))

theorem program_reachable_mono {X : Type} (program : Program X) (left right : X → Rat)
    (ordered : ∀ result, program.Reaches result → left result ≤ right result) :
    program.expect left ≤ program.expect right := by
  induction program with
  | pure result => exact ordered result .pure
  | draw next ih =>
    apply AdaptiveHandPicked.mean_mono
    intro index _
    exact ih (AdaptiveHandPicked.rangeDraw index) (fun result reaches => ordered result (.draw _ reaches))

theorem capped_bounds {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) (horizon depth : Nat) (memory : M)
    (history : List (O × A)) (state : S) :
    0 ≤ capped env policy horizon depth memory history state ∧
      capped env policy horizon depth memory history state ≤ (horizon : Rat) := by
  induction depth generalizing memory history state with
  | zero =>
    simp only [capped]
    split
    · have := env.nonnegative state
      have : (0 : Rat) ≤ (horizon : Rat) := Rat.natCast_nonneg
      constructor <;> grind
    · exact ⟨Rat.natCast_nonneg,Rat.le_refl⟩
  | succ depth ih =>
    simp only [capped]
    split
    · have := env.nonnegative state
      have : (0 : Rat) ≤ (horizon : Rat) := Rat.natCast_nonneg
      constructor <;> grind
    · exact program_bounds _ _ _ _ (fun decision =>
        program_bounds _ _ _ _ (fun next => ih decision.2 _ next))

theorem capped_depth_decreasing {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) (horizon depth : Nat) (memory : M)
    (history : List (O × A)) (state : S) :
    capped env policy horizon (depth + 1) memory history state ≤
      capped env policy horizon depth memory history state := by
  induction depth generalizing memory history state with
  | zero =>
    by_cases done : env.complete state = true
    · simp [capped,done]
    · simpa only [capped,done,Bool.false_eq_true,↓reduceIte] using
        (capped_bounds env policy horizon 1 memory history state).2
  | succ depth ih =>
    by_cases done : env.complete state = true
    · simp [capped,done]
    · simp only [capped,done,Bool.false_eq_true,↓reduceIte]
      exact program_mono _ _ _ (fun decision => program_mono _ _ _ (fun next => ih decision.2 _ next))

theorem capped_horizon_increasing {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) {lower upper : Nat} (ordered : lower ≤ upper)
    (depth : Nat) (memory : M) (history : List (O × A)) (state : S) :
    capped env policy lower depth memory history state ≤
      capped env policy upper depth memory history state := by
  have : (lower : Rat) ≤ (upper : Rat) := Rat.natCast_le_natCast.mpr ordered
  induction depth generalizing memory history state with
  | zero => simp only [capped]; split <;> grind
  | succ depth ih =>
    simp only [capped]
    split
    · grind
    · exact program_mono _ _ _ (fun decision => program_mono _ _ _ (fun next => ih decision.2 _ next))

/-- A full-state capped lower certificate must hold for every legal action.
This overapproximates observations and may include forbidden timing rules. That
makes a verified lower bound stronger; it does not authorize the attaining rule. -/
structure CappedLower {S O A : Type} (env : Environment S O A)
    (horizon : Nat) (value : S → Rat) : Prop where
  cap : ∀ state, value state ≤ (horizon : Rat)
  terminal : ∀ state, env.complete state = true →
    value state ≤ min (env.elapsed state) (horizon : Rat)
  step : ∀ state action, env.complete state = false → env.legal state action →
    value state ≤ (env.step state action).expect value

theorem lower_all_prefixes {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) (memory : Program M) (initial : Program S)
    (allowed : ActionAdmissible env policy memory initial)
    (horizon : Nat) (value : S → Rat) (certificate : CappedLower env horizon value)
    (depth : Nat) (remembered : M) (history : List (O × A)) (state : S)
    (reachable : Reachable env policy memory initial remembered history state) :
    value state ≤ capped env policy horizon depth remembered history state := by
  induction depth generalizing remembered history state with
  | zero =>
    by_cases done : env.complete state = true
    · simpa [capped,done] using certificate.terminal state done
    · simpa [capped,done] using certificate.cap state
  | succ depth ih =>
    by_cases done : env.complete state = true
    · simpa [capped,done] using certificate.terminal state done
    · have unfinished : env.complete state = false := Bool.eq_false_iff.mpr done
      simp only [capped,unfinished,Bool.false_eq_true,↓reduceIte]
      apply program_support_lower
      apply (program_all_iff_reaches _ _).mpr
      intro decision decisionLeaf
      have legal := program_all_reaches _ _ (allowed remembered history state reachable unfinished) decision decisionLeaf
      apply Rat.le_trans (certificate.step state decision.1 unfinished legal)
      apply program_reachable_mono
      intro next gameLeaf
      exact ih decision.2 _ next (.step reachable unfinished decisionLeaf gameLeaf)

/-- The certificate covers fresh private randomness at each decision, with no
bound on decisions, their total random draws, or the completion time. -/
theorem initial_lower_all_prefixes {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) (memory : Program M) (initial : Program S)
    (allowed : ActionAdmissible env policy memory initial)
    (horizon : Nat) (value : S → Rat) (certificate : CappedLower env horizon value)
    (depth : Nat) : initial.expect value ≤ initialCapped env policy memory initial horizon depth := by
  unfold initialCapped
  apply program_support_lower
  apply (program_all_iff_reaches _ _).mpr
  intro remembered privateLeaf
  apply program_reachable_mono
  intro state gameLeaf
  exact lower_all_prefixes env policy memory initial allowed horizon value certificate depth remembered [] state
    (.initial privateLeaf gameLeaf)

theorem expected_lower {S O A M : Type} (env : Environment S O A)
    (policy : Controller O A M) (memory : Program M) (initial : Program S)
    (allowed : ActionAdmissible env policy memory initial)
    (horizon : Nat) (value : S → Rat) (certificate : CappedLower env horizon value)
    (bound : Rat) (strict : bound < initial.expect value) :
    InitialExpected env policy memory initial bound := by
  refine ⟨horizon,initial.expect value - bound,by grind,?_⟩
  intro depth
  have := initial_lower_all_prefixes env policy memory initial allowed horizon value certificate depth
  grind

/-- Deterministic public controllers are included without changing their values. -/
def deterministic {O A : Type} (policy : PublicPolicy O A) : Controller O A Unit :=
  fun _ history observation => .pure (policy history observation,())

theorem deterministic_capped {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (horizon depth : Nat) (history : List (O × A)) (state : S) :
    capped env (deterministic policy) horizon depth () history state =
      HittingTime.capped env policy horizon depth history state := by
  induction depth generalizing history state with
  | zero => rfl
  | succ depth ih =>
    simp only [capped,HittingTime.capped,chosen,deterministic,HittingTime.chosen,Program.expect]
    split
    · rfl
    · congr 1
      funext next
      exact ih _ next

theorem deterministic_expected {S O A : Type} (env : Environment S O A)
    (policy : PublicPolicy O A) (initial : Program S) (bound : Rat) :
    InitialExpected env (deterministic policy) (.pure ()) initial bound ↔
      HittingTime.InitialExpected env policy initial bound := by
  simp only [InitialExpected,HittingTime.InitialExpected,initialCapped,HittingTime.initialCapped,
    Program.expect,deterministic_capped]


/-- Random private choices cannot turn a permanently unfinished zero-time run
into completion. This includes infinitely many fresh private samples. -/
theorem capped_stall {M : Type} (policy : Controller Unit Unit M)
    (horizon depth : Nat) (memory : M) (history : List (Unit × Unit)) :
    capped HittingTime.Stall.environment policy horizon depth memory history () = (horizon : Rat) := by
  induction depth generalizing memory history with
  | zero => rfl
  | succ depth ih =>
    change (chosen HittingTime.Stall.environment policy memory history ()).expect
      (fun decision => capped HittingTime.Stall.environment policy horizon depth decision.2
        (history ++ [((),decision.1)]) ()) = (horizon : Rat)
    simp only [ih,program_constant]

theorem infinite_stall {M : Type} (policy : Controller Unit Unit M) (memory : Program M)
    (bound : Rat) : InitialExpected HittingTime.Stall.environment policy memory (.pure ()) bound := by
  let integer := bound.ceil + 1
  have ceiling : bound ≤ (bound.ceil : Rat) := Rat.le_ceil
  have greater : (bound.ceil : Rat) < (integer : Rat) := Rat.intCast_lt_intCast.mpr (by dsimp [integer]; omega)
  have natural : (integer : Rat) ≤ (integer.toNat : Rat) := Rat.intCast_le_intCast.mpr (Int.self_le_toNat integer)
  have strict : bound < (integer.toNat : Rat) := by grind
  refine ⟨integer.toNat,(integer.toNat : Rat) - bound,by grind,?_⟩
  intro depth
  simp only [initialCapped,Program.expect,capped_stall,program_constant]
  grind

end CookieClicker.FullGame.RandomizedHittingTime

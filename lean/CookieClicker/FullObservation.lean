import CookieClicker.HittingTime

/-! Transfer expected-time lower bounds from a stronger competitor class.
The stronger player sees the complete current state and may have more legal
actions. The transition law, startup distribution and completion predicate stay
identical. This can remove an observation-refinement obligation from a lower
bound, but supplies neither a bound nor an attaining Cookie Clicker strategy.
-/
namespace CookieClicker.FullGame.FullObservation
open HittingTime

def environment {S O A : Type} (env : Environment S O A)
    (legal : S → A → Prop) : Environment S S A := {
  complete := env.complete
  elapsed := env.elapsed
  nonnegative := env.nonnegative
  observe := id
  legal
  step := env.step
  monotone := env.monotone }

def projectHistory {S O A : Type} (env : Environment S O A)
    (history : List (S × A)) : List (O × A) :=
  history.map (fun (state,action) => (env.observe state,action))

def lift {S O A : Type} (env : Environment S O A) (policy : PublicPolicy O A) : PublicPolicy S A :=
  fun history state => policy (projectHistory env history) (env.observe state)

theorem chosen_lift {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (policy : PublicPolicy O A) (history : List (S × A)) (state : S) :
    chosen (environment env legal) (lift env policy) history state =
      chosen env policy (projectHistory env history) state := rfl

theorem capped_equal {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (policy : PublicPolicy O A) (horizon depth : Nat) (history : List (S × A)) (state : S) :
    capped (environment env legal) (lift env policy) horizon depth history state =
      capped env policy horizon depth (projectHistory env history) state := by
  induction depth generalizing history state with
  | zero => rfl
  | succ depth ih =>
    by_cases done : env.complete state = true
    · simp [capped,environment,done]
    · simp only [capped,environment,done,Bool.false_eq_true,↓reduceIte,chosen,lift,id_eq]
      congr 1
      funext next
      simpa only [projectHistory,List.map_append,List.map_cons,List.map_nil,chosen,environment] using
        ih (history ++ [(state,chosen env policy (projectHistory env history) state)]) next

theorem initial_capped_equal {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (policy : PublicPolicy O A) (initial : Program S) (horizon depth : Nat) :
    initialCapped (environment env legal) (lift env policy) initial horizon depth =
      initialCapped env policy initial horizon depth := by
  simp only [initialCapped,capped_equal,projectHistory,List.map_nil]

theorem expected_equal {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (policy : PublicPolicy O A) (initial : Program S) (bound : Rat) :
    InitialExpected (environment env legal) (lift env policy) initial bound ↔
      InitialExpected env policy initial bound := by
  simp only [InitialExpected,initial_capped_equal]

theorem reachable_projects {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (policy : PublicPolicy O A) (initial : Program S) (history : List (S × A)) (state : S)
    (reachable : Reachable (environment env legal) (lift env policy) initial history state) :
    Reachable env policy initial (projectHistory env history) state := by
  induction reachable with
  | initial leaf => exact .initial leaf
  | step before unfinished leaf ih =>
    simpa only [projectHistory,List.map_append,List.map_cons,List.map_nil,
      environment,chosen,lift,id_eq] using Reachable.step ih unfinished leaf

theorem admissible_lift {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (widen : ∀ state action, env.legal state action → legal state action)
    (policy : PublicPolicy O A) (initial : Program S) (allowed : Admissible env policy initial) :
    Admissible (environment env legal) (lift env policy) initial := by
  intro history state reachable unfinished
  exact widen state _ (allowed _ state
    (reachable_projects env legal policy initial history state reachable) unfinished)

/-- A lower cut valid for every stronger admissible competitor is valid for
every admissible public strategy, including noncompleting paths and all prefix
depths. No bounded action count or hidden-seed-specific policy is inserted. -/
theorem lower_bound_transfers {S O A : Type} (env : Environment S O A) (legal : S → A → Prop)
    (widen : ∀ state action, env.legal state action → legal state action)
    (initial : Program S) (bound : Rat)
    (lower : ∀ policy, Admissible (environment env legal) policy initial →
      InitialExpected (environment env legal) policy initial bound)
    (policy : PublicPolicy O A) (allowed : Admissible env policy initial) :
    InitialExpected env policy initial bound :=
  (expected_equal env legal policy initial bound).mp
    (lower (lift env policy) (admissible_lift env legal widen policy initial allowed))

end CookieClicker.FullGame.FullObservation

import Std

/-! Finite invertible dynamics have a complete bounded predicate check.
The carrier is used in the proof; its length is the execution bound. -/
namespace CookieClicker.FiniteInvertibleOrbit

def run {α : Type} (step : α → α) : Nat → α → α
  | 0, state => state
  | count+1, state => step (run step count state)

theorem run_add {α : Type} (step : α → α) (a b : Nat) (state : α) :
    run step (a+b) state = run step a (run step b state) := by
  induction a with
  | zero => simp [run]
  | succ a induction => simpa only [Nat.succ_add,run] using congrArg step induction

theorem run_succ_start {α : Type} (step : α → α) (count : Nat) (state : α) :
    run step (count+1) state = run step count (step state) := by
  induction count with
  | zero => rfl
  | succ count induction => simpa only [run] using congrArg step induction

theorem run_injective {α : Type} (step : α → α)
    (injective : ∀ a b, step a = step b → a = b) (count : Nat) :
    ∀ a b, run step count a = run step count b → a = b := by
  induction count with
  | zero => intro a b same; exact same
  | succ count induction =>
    intro a b same
    exact induction a b (injective _ _ same)

theorem bounded_period {α : Type} (step : α → α)
    (injective : ∀ a b, step a = step b → a = b)
    (carrier : List α) (covers : ∀ state, state ∈ carrier) (state : α) :
    ∃ period, 0 < period ∧ period ≤ carrier.length ∧ run step period state = state := by
  classical
  apply Classical.byContradiction
  intro absent
  have noReturn : ∀ period, 0 < period → period ≤ carrier.length → run step period state ≠ state := by
    intro period positive bounded same
    exact absent ⟨period,positive,bounded,same⟩
  let visited := (List.range (carrier.length+1)).map (fun n => run step n state)
  have distinct : visited.Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb ordered same
    simp only [visited,List.length_map,List.length_range] at ha hb
    simp only [visited,List.getElem_map,List.getElem_range] at same
    have same' : run step a state = run step a (run step (b-a) state) := by
      rw [←run_add,Nat.add_sub_of_le (Nat.le_of_lt ordered)]
      exact same
    have returned := (run_injective step injective a _ _ same').symm
    exact noReturn (b-a) (by omega) (by omega) returned
  have subset : visited ⊆ carrier := by
    intro candidate _
    exact covers candidate
  have size := distinct.length_le_of_subset subset
  simp only [visited,List.length_map,List.length_range] at size
  omega

theorem run_multiple {α : Type} (step : α → α) (period count : Nat) (state : α)
    (returns : run step period state = state) : run step (count*period) state = state := by
  induction count with
  | zero => simp [run]
  | succ count induction =>
    rw [Nat.succ_mul,run_add,returns,induction]

theorem run_mod {α : Type} (step : α → α) (period count : Nat) (state : α)
    (returns : run step period state = state) :
    run step count state = run step (count%period) state := by
  conv => lhs; rw [←Nat.mod_add_div count period]
  rw [run_add,Nat.mul_comm period,run_multiple step period _ state returns]

def allGood {α : Type} (step : α → α) (good : α → Prop) [DecidablePred good] : Nat → α → Bool
  | 0, _ => true
  | count+1, state => decide (good state) && allGood step good count (step state)

theorem allGood_iff {α : Type} (step : α → α) (good : α → Prop) [DecidablePred good]
    (count : Nat) (state : α) :
    allGood step good count state = true ↔ ∀ n, n < count → good (run step n state) := by
  induction count generalizing state with
  | zero => simp [allGood]
  | succ count induction =>
    simp only [allGood,Bool.and_eq_true,decide_eq_true_eq,induction]
    constructor
    · rintro ⟨first,rest⟩ n bounded
      cases n with
      | zero => exact first
      | succ n =>
        have next := rest n (by omega)
        simpa only [←run_succ_start] using next
    · intro all
      refine ⟨all 0 (by omega),?_⟩
      intro n bounded
      have next := all (n+1) (by omega)
      simpa only [run_succ_start] using next

theorem finite_check_complete {α : Type} (step : α → α)
    (injective : ∀ a b, step a = step b → a = b)
    (carrier : List α) (covers : ∀ state, state ∈ carrier)
    (good : α → Prop) [DecidablePred good] (state : α) :
    allGood step good carrier.length state = true ↔ ∀ n, good (run step n state) := by
  rw [allGood_iff]
  constructor
  · intro bounded n
    rcases bounded_period step injective carrier covers state with ⟨period,positive,small,returns⟩
    rw [run_mod step period n state returns]
    exact bounded (n%period) (Nat.lt_of_lt_of_le (Nat.mod_lt _ positive) small)
  · intro all n _
    exact all n

theorem nonzero_recurs {α : Type} (step : α → α)
    (injective : ∀ a b, step a = step b → a = b)
    (carrier : List α) (covers : ∀ state, state ∈ carrier)
    (good : α → Prop) [DecidablePred good] (state : α)
    (witness : ∃ n, ¬good (run step n state)) (offset : Nat) :
    ∃ n, n < carrier.length ∧ ¬good (run step (offset+n) state) := by
  classical
  rcases bounded_period step injective carrier covers state with ⟨period,positive,small,returns⟩
  rcases witness with ⟨witnessIndex,bad⟩
  let index := (witnessIndex%period + period - offset%period)%period
  have indexSmall : index < period := Nat.mod_lt _ positive
  have modular : (offset+index)%period = witnessIndex%period := by
    have offsetSmall := Nat.mod_lt offset positive
    have sum : offset%period + (witnessIndex%period + period - offset%period) = witnessIndex%period + period := by omega
    unfold index
    rw [Nat.add_mod_mod,←Nat.mod_add_mod offset period,sum,Nat.add_mod_right,Nat.mod_mod]
  refine ⟨index,Nat.lt_of_lt_of_le indexSmall small,?_⟩
  rw [run_mod step period (offset+index) state returns,modular]
  simpa only [run_mod step period witnessIndex state returns] using bad

end CookieClicker.FiniteInvertibleOrbit

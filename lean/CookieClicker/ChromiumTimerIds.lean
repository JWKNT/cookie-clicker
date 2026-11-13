import Std
/-! Local timer-ID conservation for the pinned Chromium87 coordinator.

`dom_timer_coordinator.cc` allocates an unused positive signed32 ID. Clear and
one-shot firing remove its entry. An interval keeps its ID when scheduled again.
The files and licenses are archived in `model/browser-source/chromium-87`.

This proves the resulting finite coordinator invariant without coalescing any
callbacks. It does not refine the C++ compiler or browser scheduler, bound other
host-task queues, establish a finite full-game state quotient, or prove optimality.
-/
namespace CookieClicker.JavaScript.ChromiumTimerIds
set_option exponentiation.threshold 4096

def capacity : Nat := 2 ^ 31 - 1
abbrev TimerId := Fin capacity

def nativeId (id : TimerId) : Nat := id.val + 1

theorem native_id_bounds (id : TimerId) : 1 ≤ nativeId id ∧ nativeId id ≤ capacity := by
  have bounded := id.isLt
  unfold nativeId
  omega

abbrev State := List TimerId

abbrev Valid (state : State) : Prop := state.Nodup

inductive Step : State → State → Prop where
  | install (state : State) (id : TimerId) (fresh : id ∉ state) : Step state (id :: state)
  | clear (state : State) (id : TimerId) : Step state (state.erase id)
  | fireOnce (state : State) (id : TimerId) (active : id ∈ state) : Step state (state.erase id)
  | fireRepeat (state : State) (id : TimerId) (active : id ∈ state) : Step state state

theorem valid_preserved {before after : State} (valid : Valid before) (step : Step before after) : Valid after := by
  cases step with
  | install id fresh => exact List.nodup_cons.mpr ⟨fresh, valid⟩
  | clear id => exact valid.erase id
  | fireOnce id _ => exact valid.erase id
  | fireRepeat _ _ => exact valid

inductive Reachable : State → Prop where
  | initial : Reachable []
  | next {before after : State} : Reachable before → Step before after → Reachable after

theorem reachable_valid {state : State} (reachable : Reachable state) : Valid state := by
  induction reachable with
  | initial => exact List.nodup_nil
  | next _ step ih => exact valid_preserved ih step

theorem valid_capacity {state : State} (valid : Valid state) : state.length ≤ capacity := by
  have bound := valid.length_le_of_subset (fun id _ => List.mem_finRange id)
  simpa only [List.length_finRange] using bound

theorem active_id_cap {state : State} (reachable : Reachable state) : state.length ≤ 2147483647 := by
  have bound := valid_capacity (reachable_valid reachable)
  simpa only [capacity] using bound

theorem install_adds_one (state : State) (id : TimerId) : (id :: state).length = state.length + 1 := rfl

theorem clearing_never_adds (state : State) (id : TimerId) : (state.erase id).length ≤ state.length :=
  List.length_erase_le

theorem one_shot_removes_one (state : State) (id : TimerId) (active : id ∈ state) :
    (state.erase id).length + 1 = state.length := by
  have h := List.length_erase_of_mem active
  have positive := List.length_pos_of_mem active
  omega


theorem full_pool_has_no_fresh_id {state : State} (valid : Valid state)
    (full : state.length = capacity) (id : TimerId) : id ∈ state := by
  by_cases missing : id ∈ state
  · exact missing
  have grown := valid_capacity (List.nodup_cons.mpr ⟨missing, valid⟩)
  simp only [List.length_cons] at grown
  omega

/-- The positive native identifier follows this circular order after subtracting1. -/
def successor (id : TimerId) : TimerId :=
  ⟨(id.val + 1) % capacity, Nat.mod_lt _ (by decide +kernel)⟩

/-- Finite prefix of the native search. `none` means this prefix found no free ID. -/
def scan (state : State) (current : TimerId) : Nat → Option TimerId
  | 0 => none
  | fuel + 1 =>
    let candidate := successor current
    if candidate ∈ state then scan state candidate fuel else some candidate

theorem returned_id_is_fresh (state : State) (current found : TimerId) (fuel : Nat)
    (returned : scan state current fuel = some found) : found ∉ state := by
  induction fuel generalizing current with
  | zero => simp [scan] at returned
  | succ fuel ih =>
    simp only [scan] at returned
    split at returned
    · exact ih _ returned
    · cases returned
      assumption

theorem full_pool_search_never_returns {state : State} (valid : Valid state)
    (full : state.length = capacity) (current : TimerId) (fuel : Nat) :
    scan state current fuel = none := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan, full_pool_has_no_fresh_id valid full, ↓reduceIte]
    exact ih _

end CookieClicker.JavaScript.ChromiumTimerIds

import CookieClicker.Arc4Orbit

/-! A constructor starts its PRGA counters at zero. Invertibility allows a
previous nonzero byte to certify future nonzero output at that entry. -/
namespace CookieClicker.Arc4ConstructorOrbit
open Arc4Orbit FiniteInvertibleOrbit
set_option maxHeartbeats 500000

theorem next_previous (state : State) : next (previous state)=state := by
  cases state
  simp [next,previous,swap_twice]

theorem previous_witness (state : State) (nonzero : output (previous state)≠0) :
    ∃ index, output (run next index state)≠0 := by
  obtain ⟨index,_,later⟩ := nonzero_recurring (previous state) ⟨0,nonzero⟩ 1
  rw [Nat.add_comm 1 index,run_succ_start,next_previous] at later
  exact ⟨index,later⟩

theorem all_zero_previous (state : State) (all : ∀ index, output (run next index state)=0) :
    output (previous state)=0 := by
  by_cases zero : output (previous state)=0
  · exact zero
  · obtain ⟨index,nonzero⟩ := previous_witness state zero
    exact False.elim (nonzero (all index))

theorem initial_previous_output (bytes : UInt8 → UInt8) :
    output (previous ⟨bytes,0,0⟩)=bytes (bytes 0+bytes 0) := by
  unfold output
  rw [next_previous]

theorem initial_previous_witness (bytes : UInt8 → UInt8) (nonzero : bytes (bytes 0+bytes 0)≠0) :
    ∃ index, output (run next index ⟨bytes,0,0⟩)≠0 := by
  apply previous_witness
  rw [initial_previous_output]
  exact nonzero

theorem bad_entry_constraint (bytes : UInt8 → UInt8)
    (all : ∀ index, output (run next index ⟨bytes,0,0⟩)=0) :
    bytes (bytes 0+bytes 0)=0 := by
  rw [←initial_previous_output bytes]
  exact all_zero_previous _ all

end CookieClicker.Arc4ConstructorOrbit

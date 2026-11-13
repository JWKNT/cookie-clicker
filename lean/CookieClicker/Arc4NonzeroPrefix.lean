import CookieClicker.Arc4Orbit

/-! A finite byte-prefix search returns a checked nonzero witness. Failure
only says that this bounded search did not provide a witness. -/
namespace CookieClicker.Arc4NonzeroPrefix
open Arc4Orbit FiniteInvertibleOrbit
set_option maxHeartbeats 500000

structure Witness (state : State) where
  index : Nat
  nonzero : output (run next index state)≠0

def search : Nat → (state : State) → Option (Witness state)
  | 0,_ => none
  | fuel+1,state =>
    if nonzero : output state≠0 then some ⟨0,nonzero⟩
    else match search fuel (next state) with
      | none => none
      | some witness => some ⟨witness.index+1,by
          rw [run_succ_start]
          exact witness.nonzero⟩

theorem sound (state : State) (witness : Witness state) : ∃ index, output (run next index state)≠0 :=
  ⟨witness.index,witness.nonzero⟩

theorem index_bounded (fuel : Nat) (state : State) (witness : Witness state)
    (accepted : search fuel state=some witness) : witness.index<fuel := by
  induction fuel generalizing state with
  | zero => simp [search] at accepted
  | succ fuel ih =>
    rw [search] at accepted
    split at accepted
    · cases Option.some.inj accepted
      simp
    · cases tail : search fuel (next state) with
      | none => simp [tail] at accepted
      | some previous =>
        simp only [tail] at accepted
        cases Option.some.inj accepted
        exact Nat.succ_lt_succ (ih _ previous tail)

end CookieClicker.Arc4NonzeroPrefix

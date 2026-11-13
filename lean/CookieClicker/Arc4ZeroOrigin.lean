import CookieClicker.Arc4ConstructorOrbit

/-! A zero-output permutation orbit cannot contain a table whose zero byte is
at slot zero. This gives a nonzero witness for that structural class. -/
namespace CookieClicker.Arc4ZeroOrigin
open Arc4Orbit FiniteInvertibleOrbit
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def Injective (bytes : UInt8 → UInt8) : Prop :=
  ∀ a b, bytes a = bytes b → a = b

theorem swap_injective (bytes : UInt8 → UInt8) (a b : UInt8)
    (oneToOne : Injective bytes) : Injective (swap bytes a b) := by
  intro x y same
  have hx : swap bytes a b x = bytes (swap id a b x) := by
    by_cases h : x = a
    · simp [swap,h]
    · by_cases k : x = b
      · subst x; simp [swap,h]
      · simp [swap,h,k]
  have hy : swap bytes a b y = bytes (swap id a b y) := by
    by_cases h : y = a
    · simp [swap,h]
    · by_cases k : y = b
      · subst y; simp [swap,h]
      · simp [swap,h,k]
  rw [hx,hy] at same
  have h := oneToOne _ _ same
  have involution (slot : UInt8) : swap id a b (swap id a b slot) = slot := by
    by_cases left : slot = a
    · subst slot
      by_cases equal : a = b
      · subst b; simp [swap]
      · simp [swap,equal,Ne.symm equal]
    · by_cases right : slot = b
      · subst slot; simp [swap,left]
      · simp [swap,left,right]
  simpa only [involution] using congrArg (swap id a b) h

theorem next_injective (state : State) (oneToOne : Injective state.bytes) :
    Injective (next state).bytes := swap_injective _ _ _ oneToOne

theorem run_injective (state : State) (oneToOne : Injective state.bytes) (count : Nat) :
    Injective (run next count state).bytes := by
  induction count with
  | zero => exact oneToOne
  | succ count induction => exact next_injective _ induction

theorem zero_cannot_enter_origin (state : State) (oneToOne : Injective state.bytes)
    (out : output state = 0) (afterZero : (next state).bytes 0 = 0) : state.bytes 0 = 0 := by
  have indexZero : (next state).bytes (next state).i + (next state).bytes (next state).j = 0 :=
    next_injective state oneToOne _ _ (out.trans afterZero.symm)
  let p := state.i+1
  let q := state.j+state.bytes p
  change swap state.bytes p q 0 = 0 at afterZero
  change swap state.bytes p q p + swap state.bytes p q q = 0 at indexZero
  rw [swap_left,swap_right] at indexZero
  by_cases first : p = 0
  · rw [first] at afterZero indexZero
    have zeroQ : state.bytes q = 0 := by simpa only [swap_left] using afterZero
    simpa only [zeroQ,UInt8.zero_add] using indexZero
  · by_cases second : q = 0
    · rw [second] at afterZero indexZero
      have zeroP : state.bytes p = 0 := by simpa only [swap_right] using afterZero
      simpa only [zeroP,UInt8.add_zero] using indexZero
    · simpa [swap,Ne.symm first,Ne.symm second] using afterZero

theorem zero_cannot_enter_run (state : State) (oneToOne : Injective state.bytes)
    (count : Nat) (out : ∀ n, n < count → output (run next n state) = 0)
    (lastZero : (run next count state).bytes 0 = 0) : state.bytes 0 = 0 := by
  induction count with
  | zero => exact lastZero
  | succ count induction =>
    apply induction (fun n bounded => out n (by omega))
    exact zero_cannot_enter_origin _ (run_injective state oneToOne count) (out count (by omega)) lastZero

theorem origin_stays (state : State) (oneToOne : Injective state.bytes)
    (out : ∀ n, output (run next n state) = 0) (origin : state.bytes 0 = 0) :
    (next state).bytes 0 = 0 := by
  obtain ⟨period,positive,_,returns⟩ := bounded_period next Arc4Orbit.next_injective states states_complete state
  apply zero_cannot_enter_run (next state) (next_injective state oneToOne) (period-1)
  · intro n _
    simpa only [←run_succ_start] using out (n+1)
  · rw [←run_succ_start,Nat.sub_add_cancel positive,returns]
    exact origin

theorem origin_at (state : State) (oneToOne : Injective state.bytes)
    (out : ∀ n, output (run next n state) = 0) (origin : state.bytes 0 = 0) (count : Nat) :
    (run next count state).bytes 0 = 0 := by
  induction count with
  | zero => exact origin
  | succ count induction =>
    apply origin_stays _ (run_injective state oneToOne count) _ induction
    intro n
    simpa only [←run_add] using out (n+count)

theorem origin_scan_target (state : State) (oneToOne : Injective state.bytes)
    (origin : state.bytes 0 = 0) (afterOrigin : (next state).bytes 0 = 0) :
    (next state).i = 0 ↔ (next state).j = 0 := by
  let p := state.i+1
  let q := state.j+state.bytes p
  change p = 0 ↔ q = 0
  change swap state.bytes p q 0 = 0 at afterOrigin
  constructor
  · intro scan
    rw [scan,swap_left] at afterOrigin
    exact oneToOne _ _ (afterOrigin.trans origin.symm)
  · intro target
    rw [target,swap_right] at afterOrigin
    exact oneToOne _ _ (afterOrigin.trans origin.symm)

theorem scan_at (state : State) (count : Nat) :
    (run next count state).i = state.i + UInt8.ofNat count := by
  induction count with
  | zero => simp [run]
  | succ count induction =>
    change (run next count state).i+1 = _
    rw [induction,UInt8.ofNat_add,UInt8.ofNat_one,UInt8.add_assoc]

theorem origin_nonzero (state : State) (oneToOne : Injective state.bytes)
    (origin : state.bytes 0 = 0) : ∃ index, output (run next index state) ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro absent
  have out : ∀ n, output (run next n state) = 0 := by
    intro n
    by_cases zero : output (run next n state) = 0
    · exact zero
    · exact False.elim (absent ⟨n,zero⟩)
  let count := (254-state.i).toNat
  let before := run next count state
  have scanBefore : before.i = 254 := by
    rw [show before.i = (run next count state).i from rfl,scan_at]
    simp only [count,UInt8.ofNat_toNat]
    rw [UInt8.add_comm,UInt8.sub_add_cancel]
  have scanNext : (next before).i = 255 := by change before.i+1=255; rw [scanBefore]; rfl
  have scanLast : (next (next before)).i = 0 := by change (next before).i+1=0; rw [scanNext]; rfl
  have originBefore : before.bytes 0 = 0 := origin_at state oneToOne out origin count
  have originNext : (next before).bytes 0 = 0 := origin_at state oneToOne out origin (count+1)
  have originLast : (next (next before)).bytes 0 = 0 := origin_at state oneToOne out origin (count+2)
  have permBefore := run_injective state oneToOne count
  have targetNonzero : (next before).j ≠ 0 := by
    intro zero
    have bad := (origin_scan_target before permBefore originBefore originNext).mpr zero
    rw [scanNext] at bad
    contradiction
  have targetZero := (origin_scan_target (next before) (next_injective before permBefore) originNext originLast).mp scanLast
  have targetSame : (next (next before)).j = (next before).j := by
    change (next before).j + (next before).bytes ((next before).i+1) = _
    rw [scanNext]
    change (next before).j + (next before).bytes 0 = _
    rw [originNext,UInt8.add_zero]
  exact targetNonzero (targetSame.symm.trans targetZero)

theorem at_origin_nonzero (state : State) (oneToOne : Injective state.bytes) (count : Nat)
    (origin : (run next count state).bytes 0 = 0) : ∃ index, output (run next index state) ≠ 0 := by
  obtain ⟨later,nonzero⟩ := origin_nonzero (run next count state) (run_injective state oneToOne count) origin
  exact ⟨later+count,by simpa only [run_add] using nonzero⟩

theorem all_zero_avoids_origin (state : State) (oneToOne : Injective state.bytes)
    (out : ∀ n, output (run next n state) = 0) (count : Nat) :
    (run next count state).bytes 0 ≠ 0 := by
  intro origin
  obtain ⟨index,nonzero⟩ := at_origin_nonzero state oneToOne count origin
  exact nonzero (out index)

theorem origin_nonzero_bounded (state : State) (oneToOne : Injective state.bytes)
    (origin : state.bytes 0 = 0) (offset : Nat) :
    ∃ index, index < bound ∧ output (run next (offset+index) state) ≠ 0 :=
  nonzero_recurring state (origin_nonzero state oneToOne origin) offset

end CookieClicker.Arc4ZeroOrigin

import CookieClicker.FiniteInvertibleOrbit

/-! The byte PRGA is invertible even on arbitrary byte tables. A complete
finite check distinguishes an all-zero orbit from recurring nonzero output. -/
namespace CookieClicker.Arc4Orbit
open FiniteInvertibleOrbit
set_option maxRecDepth 2048
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

structure State where
  bytes : UInt8 → UInt8
  i : UInt8
  j : UInt8

def swap (bytes : UInt8 → UInt8) (a b slot : UInt8) :=
  if slot = a then bytes b else if slot = b then bytes a else bytes slot

theorem swap_left (bytes : UInt8 → UInt8) (a b : UInt8) : swap bytes a b a = bytes b := by simp [swap]

theorem swap_right (bytes : UInt8 → UInt8) (a b : UInt8) : swap bytes a b b = bytes a := by
  by_cases same : a = b
  · subst b; simp [swap]
  · simp [swap,Ne.symm same]

theorem swap_twice (bytes : UInt8 → UInt8) (a b : UInt8) : swap (swap bytes a b) a b = bytes := by
  funext slot
  by_cases first : slot = a
  · subst slot
    by_cases same : a = b
    · subst b; simp [swap]
    · simp [swap,same,Ne.symm same]
  · by_cases second : slot = b
    · subst slot; simp [swap,first]
    · simp [swap,first,second]

def next (state : State) : State :=
  let a := state.i + 1
  let b := state.j + state.bytes a
  ⟨swap state.bytes a b,a,b⟩

def previous (state : State) : State :=
  let bytes := swap state.bytes state.i state.j
  ⟨bytes,state.i-1,state.j-bytes state.i⟩

theorem previous_next (state : State) : previous (next state) = state := by
  cases state
  simp [next,previous,swap_twice]

theorem next_injective (a b : State) (same : next a = next b) : a = b := by
  have h := congrArg previous same
  simpa only [previous_next] using h

def output (state : State) : UInt8 :=
  let after := next state
  after.bytes (after.bytes after.i + after.bytes after.j)

def byteValues : List UInt8 := (List.finRange 256).map (fun slot => UInt8.ofNat slot.val)

theorem byteValues_complete (byte : UInt8) : byte ∈ byteValues := by
  apply List.mem_map.mpr
  exact ⟨⟨byte.toNat,byte.toNat_lt⟩,List.mem_finRange _,UInt8.ofNat_toNat⟩

theorem byteValues_length : byteValues.length = 256 := by simp [byteValues]

def tables : (count : Nat) → List (Fin count → UInt8)
  | 0 => [Fin.elim0]
  | count+1 => byteValues.flatMap fun head => (tables count).map fun tail => Fin.cases head tail

theorem tables_complete (count : Nat) (table : Fin count → UInt8) : table ∈ tables count := by
  induction count with
  | zero =>
    have same : table = Fin.elim0 := by funext index; exact Fin.elim0 index
    simp [tables,same]
  | succ count induction =>
    apply List.mem_flatMap.mpr
    refine ⟨table 0,byteValues_complete _,List.mem_map.mpr ?_⟩
    refine ⟨fun index => table index.succ,induction _,?_⟩
    funext index
    exact Fin.cases rfl (fun _ => rfl) index

theorem flatMap_length {α β : Type} (items : List α) (f : α → List β) (length : Nat)
    (fixed : ∀ item, (f item).length = length) : (items.flatMap f).length = items.length*length := by
  induction items with
  | nil => simp
  | cons item rest induction => simp [fixed,induction,Nat.add_mul,Nat.add_comm]

theorem tables_length (count : Nat) : (tables count).length = 256^count := by
  induction count with
  | zero => rfl
  | succ count induction =>
    rw [tables,flatMap_length _ _ (tables count).length (by intro head; simp),byteValues_length,induction]
    simp [Nat.pow_succ,Nat.mul_comm]

/-- This finite enumeration is used only in proofs. Native initialization must
not attempt to construct all byte tables. -/
noncomputable def byteTables : List (UInt8 → UInt8) := (tables 256).map fun table byte => table ⟨byte.toNat,byte.toNat_lt⟩

theorem byteTables_complete (table : UInt8 → UInt8) : table ∈ byteTables := by
  apply List.mem_map.mpr
  refine ⟨fun index => table (UInt8.ofNat index.val),tables_complete _ _,?_⟩
  funext byte
  simp only [UInt8.ofNat_toNat]

/-- The proof state space is retained as a logical definition. -/
noncomputable def states : List State := byteTables.flatMap fun bytes =>
  byteValues.flatMap fun i => byteValues.map fun j => ⟨bytes,i,j⟩

theorem states_complete (state : State) : state ∈ states := by
  apply List.mem_flatMap.mpr
  refine ⟨state.bytes,byteTables_complete _,List.mem_flatMap.mpr ?_⟩
  refine ⟨state.i,byteValues_complete _,List.mem_map.mpr ?_⟩
  exact ⟨state.j,byteValues_complete _,rfl⟩

def bound : Nat := 256^258

theorem states_length : states.length = bound := by
  rw [states,flatMap_length _ _ (256*256)]
  · simp only [byteTables,List.length_map,tables_length,bound]
  · intro bytes
    rw [flatMap_length _ _ 256 (by intro i; simp [byteValues_length]),byteValues_length]

def allZero (state : State) : Bool := allGood next (fun value => output value = 0) bound state

theorem allZero_iff (state : State) :
    allZero state = true ↔ ∀ n, output (run next n state) = 0 := by
  unfold allZero
  rw [←states_length]
  exact finite_check_complete next next_injective states states_complete _ state

theorem nonzero_recurring (state : State)
    (witness : ∃ n, output (run next n state) ≠ 0) (offset : Nat) :
    ∃ n, n < bound ∧ output (run next (offset+n) state) ≠ 0 := by
  simpa only [states_length] using
    nonzero_recurs next next_injective states states_complete (fun value => output value = 0) state witness offset

end CookieClicker.Arc4Orbit

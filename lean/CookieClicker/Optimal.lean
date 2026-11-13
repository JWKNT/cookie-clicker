import Std

/-! Exact finite purchase planning for a target bank.

All numbers are rational. Each offer can be used once. A purchase waits only
until it is affordable. The goal is a target bank, not cumulative baked cookies.
-/
namespace CookieClicker

structure Offer where
  price : Rat
  gain : Rat
  deriving DecidableEq, Repr

structure State where
  bank : Rat
  rate : Rat
  deriving DecidableEq, Repr

def waitFor (s : State) (amount : Rat) : Rat :=
  if amount ≤ s.bank then 0 else (amount - s.bank) / s.rate

def afterBuy (s : State) (i : Offer) : State :=
  ⟨s.bank + s.rate * waitFor s i.price - i.price, s.rate + i.gain⟩

/-- Every way to remove exactly one occurrence from a list. -/
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (picks rest).map (fun (b, tail) => (b, a :: tail))

structure Result where
  purchases : List Offer
  time : Rat
  deriving DecidableEq, Repr

def bestOf (fallback : Result) : List Result → Result
  | [] => fallback
  | a :: rest =>
    let next := bestOf fallback rest
    if a.time ≤ next.time then a else next

def solve (target : Rat) : Nat → State → List Offer → Result
  | 0, s, _ => ⟨[], waitFor s target⟩
  | n + 1, s, offers =>
    bestOf ⟨[], waitFor s target⟩ ((picks offers).map fun (i, rest) =>
      let tail := solve target n (afterBuy s i) rest
      ⟨i :: tail.purchases, waitFor s i.price + tail.time⟩)

/-- A complete event-time schedule, followed by saving to the target bank. -/
inductive Schedule (target : Rat) : Nat → State → List Offer → Result → Prop
  | stop (n s offers) : Schedule target n s offers ⟨[], waitFor s target⟩
  | buy {n s offers i rest tail}
      (available : (i, rest) ∈ picks offers)
      (continuation : Schedule target n (afterBuy s i) rest tail) :
      Schedule target (n + 1) s offers
        ⟨i :: tail.purchases, waitFor s i.price + tail.time⟩

theorem bestOf_mem (fallback : Result) (xs : List Result) :
    bestOf fallback xs ∈ fallback :: xs := by
  induction xs with
  | nil => simp [bestOf]
  | cons a xs ih =>
    simp only [bestOf]
    split
    · simp
    · simp only [List.mem_cons] at *
      rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem bestOf_le_fallback (fallback : Result) (xs : List Result) :
    (bestOf fallback xs).time ≤ fallback.time := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons a xs ih =>
    simp only [bestOf]
    split
    · exact Rat.le_trans ‹_› ih
    · exact ih

theorem bestOf_le_member (fallback : Result) (xs : List Result) (a : Result)
    (h : a ∈ xs) : (bestOf fallback xs).time ≤ a.time := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    simp only [List.mem_cons] at h
    simp only [bestOf]
    split
    · rename_i hb
      rcases h with rfl | h
      · exact Rat.le_refl
      · exact Rat.le_trans hb (ih h)
    · rename_i hb
      rcases h with rfl | h
      · exact Rat.le_total.resolve_left hb
      · exact ih h

/-- The computed answer is attained by a legal schedule. -/
theorem solve_feasible (target : Rat) (n : Nat) (s : State) (offers : List Offer) :
    Schedule target n s offers (solve target n s offers) := by
  induction n generalizing s offers with
  | zero => exact Schedule.stop 0 s offers
  | succ n ih =>
    unfold solve
    have hm := bestOf_mem (⟨[], waitFor s target⟩ : Result)
      ((picks offers).map fun (i, rest) =>
        let tail := solve target n (afterBuy s i) rest
        (⟨i :: tail.purchases, waitFor s i.price + tail.time⟩ : Result))
    rcases List.mem_cons.mp hm with h | h
    · rw [h]
      exact Schedule.stop (n + 1) s offers
    · obtain ⟨⟨i, rest⟩, hp, heq⟩ := List.mem_map.mp h
      rw [← heq]
      exact Schedule.buy hp (ih (afterBuy s i) rest)

/-- Bellman's recurrence is no slower than every legal schedule. -/
theorem solve_le_schedule {target : Rat} {n : Nat} {s : State}
    {offers : List Offer} {r : Result} (h : Schedule target n s offers r) :
    (solve target n s offers).time ≤ r.time := by
  induction h with
  | stop n s offers =>
    cases n with
    | zero => exact Rat.le_refl
    | succ n => exact bestOf_le_fallback _ _
  | @buy n s offers i rest tail available continuation ih =>
    have hm := bestOf_le_member (⟨[], waitFor s target⟩ : Result)
      ((picks offers).map fun (i, rest) =>
        let tail := solve target n (afterBuy s i) rest
        (⟨i :: tail.purchases, waitFor s i.price + tail.time⟩ : Result))
      ⟨i :: (solve target n (afterBuy s i) rest).purchases,
        waitFor s i.price + (solve target n (afterBuy s i) rest).time⟩
      (List.mem_map.mpr ⟨(i, rest), available, rfl⟩)
    exact Rat.le_trans hm (Rat.add_le_add_left.mpr ih)

/-- The result is a minimum, and not only a lower bound. -/
theorem solve_optimal (target : Rat) (n : Nat) (s : State) (offers : List Offer) :
    Schedule target n s offers (solve target n s offers) ∧
    ∀ r, Schedule target n s offers r → (solve target n s offers).time ≤ r.time :=
  ⟨solve_feasible target n s offers, fun _ h => solve_le_schedule h⟩

end CookieClicker

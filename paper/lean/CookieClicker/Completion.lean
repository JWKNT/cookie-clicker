import CookieClicker.Optimal

namespace CookieClicker

/-- Removing one offer decreases the number of offers by exactly one. -/
theorem picks_length {α : Type} {xs : List α} {x : α} {rest : List α}
    (h : (x, rest) ∈ picks xs) : rest.length + 1 = xs.length := by
  induction xs generalizing rest with
  | nil => simp [picks] at h
  | cons a xs ih =>
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨b, tail⟩, hp, heq⟩
    · cases h
      simp
    · cases heq
      simpa using ih hp

/-- Every selected offer and every remaining offer came from the input list. -/
theorem picks_members {α : Type} {xs : List α} {x : α} {rest : List α}
    (h : (x, rest) ∈ picks xs) : x ∈ xs ∧ ∀ a, a ∈ rest → a ∈ xs := by
  induction xs generalizing rest with
  | nil => simp [picks] at h
  | cons a xs ih =>
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨b, tail⟩, hp, heq⟩
    · cases h
      exact ⟨by simp, fun _ hm => by simp [hm]⟩
    · cases heq
      obtain ⟨hx, hr⟩ := ih hp
      refine ⟨by simp [hx], ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · simp [hr z hz]

/-- Buy every offer. The fuel must be at least the number of offers. -/
def complete : Nat → State → List Offer → Result
  | 0, _, _ => ⟨[], 0⟩
  | _ + 1, _, [] => ⟨[], 0⟩
  | n + 1, s, a :: offers =>
    let first := complete n (afterBuy s a) offers
    bestOf ⟨a :: first.purchases, waitFor s a.price + first.time⟩
      ((picks (a :: offers)).map fun (i, rest) =>
        let tail := complete n (afterBuy s i) rest
        ⟨i :: tail.purchases, waitFor s i.price + tail.time⟩)

/-- All offers are required. The only terminal state has no remaining offers. -/
inductive Completion : State → List Offer → Result → Prop
  | done (s) : Completion s [] ⟨[], 0⟩
  | buy {s offers i rest tail}
      (available : (i, rest) ∈ picks offers)
      (continuation : Completion (afterBuy s i) rest tail) :
      Completion s offers ⟨i :: tail.purchases, waitFor s i.price + tail.time⟩

/-- The exact completion planner produces a valid order of all purchases. -/
theorem complete_feasible (n : Nat) (s : State) (offers : List Offer)
    (enough : offers.length ≤ n) : Completion s offers (complete n s offers) := by
  induction n generalizing s offers with
  | zero =>
    have h : offers = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst offers
    exact Completion.done s
  | succ n ih =>
    cases offers with
    | nil => exact Completion.done s
    | cons a offers =>
      have hfirst : offers.length ≤ n := by simpa using enough
      unfold complete
      have hm := bestOf_mem
        (⟨a :: (complete n (afterBuy s a) offers).purchases,
          waitFor s a.price + (complete n (afterBuy s a) offers).time⟩ : Result)
        ((picks (a :: offers)).map fun (i, rest) =>
          let tail := complete n (afterBuy s i) rest
          (⟨i :: tail.purchases, waitFor s i.price + tail.time⟩ : Result))
      rcases List.mem_cons.mp hm with h | h
      · rw [h]
        exact Completion.buy (by simp [picks]) (ih _ _ hfirst)
      · obtain ⟨⟨i, rest⟩, hp, heq⟩ := List.mem_map.mp h
        rw [← heq]
        have hr := picks_length hp
        exact Completion.buy hp (ih _ _ (by simp at hr; omega))

/-- Every legal completion order takes at least as long as the computed order. -/
theorem complete_le_completion (n : Nat) {s : State} {offers : List Offer} {r : Result}
    (enough : offers.length ≤ n) (h : Completion s offers r) :
    (complete n s offers).time ≤ r.time := by
  induction n generalizing s offers r with
  | zero =>
    have hn : offers = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst offers
    cases h with
    | done => exact Rat.le_refl
    | buy hp _ => simp [picks] at hp
  | succ n ih =>
    cases offers with
    | nil =>
      cases h with
      | done => exact Rat.le_refl
      | buy hp _ => simp [picks] at hp
    | cons a offers =>
      cases h with
      | @buy _ _ i rest tail hp continuation =>
        have hr := picks_length hp
        have hi := ih (by simp at hr; simp at enough; omega) continuation
        have hm := bestOf_le_member
          (⟨a :: (complete n (afterBuy s a) offers).purchases,
            waitFor s a.price + (complete n (afterBuy s a) offers).time⟩ : Result)
          ((picks (a :: offers)).map fun (i, rest) =>
            let tail := complete n (afterBuy s i) rest
            (⟨i :: tail.purchases, waitFor s i.price + tail.time⟩ : Result))
          ⟨i :: (complete n (afterBuy s i) rest).purchases,
            waitFor s i.price + (complete n (afterBuy s i) rest).time⟩
          (List.mem_map.mpr ⟨(i, rest), hp, rfl⟩)
        exact Rat.le_trans hm (Rat.add_le_add_left.mpr hi)

/-- Global minimum over every earliest-affordable order of all one-shot offers. -/
theorem complete_optimal (s : State) (offers : List Offer) :
    Completion s offers (complete offers.length s offers) ∧
    ∀ r, Completion s offers r → (complete offers.length s offers).time ≤ r.time :=
  ⟨complete_feasible _ _ _ (Nat.le_refl _),
    fun _ h => complete_le_completion _ (Nat.le_refl _) h⟩

/-- The exchange-index greedy rule is not an optimal completion policy. -/
def counterexampleOffers : List Offer := [⟨3, 1⟩, ⟨5, 4⟩, ⟨6, 6⟩]

/-- Evaluate a given order using exact earliest-affordable purchases. -/
def orderTime : State → List Offer → Rat
  | _, [] => 0
  | s, i :: rest => waitFor s i.price + orderTime (afterBuy s i) rest

theorem greedy_counterexample :
    orderTime ⟨0, 1⟩ counterexampleOffers = 13 / 2 ∧
    orderTime ⟨0, 1⟩ [⟨5, 4⟩, ⟨6, 6⟩, ⟨3, 1⟩] = 356 / 55 ∧
    (356 / 55 : Rat) < 13 / 2 ∧
    (complete 3 ⟨0, 1⟩ counterexampleOffers).time = 356 / 55 := by
  decide +kernel

end CookieClicker

import CookieClicker.FullCompletionChecks

namespace CookieClicker.FullGame.Pinned

private theorem two_distinct_true {names : List String} {won : String → Bool}
    (distinct : names.Nodup) (count : 2 ≤ names.countP won) :
    ∃ a b, a ∈ names ∧ b ∈ names ∧ a ≠ b ∧ won a = true ∧ won b = true := by
  have filteredDistinct := List.Pairwise.filter won distinct
  rw [List.countP_eq_length_filter] at count
  cases h : names.filter won with
  | nil => simp [h] at count
  | cons a rest =>
    cases rest with
    | nil => simp [h] at count
    | cons b tail =>
      have ha : a ∈ names ∧ won a = true := List.mem_filter.mp (by rw [h]; simp)
      have hb : b ∈ names ∧ won b = true := List.mem_filter.mp (by rw [h]; simp)
      rw [h] at filteredDistinct
      have apart : a ≠ b := by
        intro equal
        have no_a := (List.nodup_cons.mp filteredDistinct).1
        apply no_a
        simp [equal]
      exact ⟨a, b, ha.1, hb.1, apart, ha.2, hb.2⟩

/-- Full completion requires two distinct won names from the 24 sugar exceptions. -/
theorem completion_requires_two_distinct_sugar_achievements (s : Snapshot)
    (done : complete requirements s = true) :
    ∃ a b, a ∈ sugarAchievementNames ∧ b ∈ sugarAchievementNames ∧ a ≠ b ∧
      s.achievements a = true ∧ s.achievements b = true :=
  two_distinct_true sugar_exceptions_distinct (completion_requires_two_sugar_exceptions s done)

end CookieClicker.FullGame.Pinned

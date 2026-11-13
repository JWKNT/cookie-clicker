import CookieClicker.Inventory

/-! First-completion checking on actual normalized event observations.
The input trace must cover every declared native action and timer boundary.
This module verifies its terminal observations and first-hit calculation. It
does not prove that JavaScript produced the trace by legal transitions.
-/
namespace CookieClicker.FullGame.Trace

structure Point where
  elapsedMs : Nat
  observation : Snapshot

def completed (point : Point) : Bool := complete Pinned.requirements point.observation

def firstCompletion (trace : List Point) : Option Point := trace.find? completed

def Chronological (trace : List Point) : Prop :=
  trace.Pairwise (fun a b => a.elapsedMs ≤ b.elapsedMs)

/-- Linear-time chronology check for a normalized event stream. -/
def orderedFrom : Nat → List Point → Bool
  | _, [] => true
  | previous, point :: rest => decide (previous ≤ point.elapsedMs) && orderedFrom point.elapsedMs rest

theorem orderedFrom_sound (previous : Nat) (trace : List Point)
    (checked : orderedFrom previous trace = true) :
    (∀ point, point ∈ trace → previous ≤ point.elapsedMs) ∧ Chronological trace := by
  induction trace generalizing previous with
  | nil => simp [Chronological]
  | cons point rest ih =>
    have first_and_tail : decide (previous ≤ point.elapsedMs) = true ∧
        orderedFrom point.elapsedMs rest = true := by simpa only [orderedFrom, Bool.and_eq_true] using checked
    have first_time : previous ≤ point.elapsedMs := of_decide_eq_true first_and_tail.1
    obtain ⟨tail_times, tail_ordered⟩ := ih point.elapsedMs first_and_tail.2
    constructor
    · intro other member
      rcases List.mem_cons.mp member with same | later
      · subst other; exact first_time
      · exact Nat.le_trans first_time (tail_times other later)
    · exact List.pairwise_cons.mpr ⟨tail_times, tail_ordered⟩

/-- The reported hit completes, and every earlier event observation is incomplete. -/
theorem first_completion_spec {trace : List Point} {hit : Point}
    (found : firstCompletion trace = some hit) :
    completed hit = true ∧ ∃ before after,
      trace = before ++ hit :: after ∧ ∀ earlier, earlier ∈ before → completed earlier = false := by
  obtain ⟨complete_hit, before, after, split, earlier⟩ := List.find?_eq_some_iff_append.mp found
  refine ⟨complete_hit, before, after, split, ?_⟩
  intro point member
  simpa using earlier point member

/-- On a chronological trace, the returned time is the minimum complete checkpoint time. -/
theorem first_completion_minimum_time {trace : List Point} {hit : Point}
    (ordered : Chronological trace) (found : firstCompletion trace = some hit) :
    ∀ point, point ∈ trace → completed point = true → hit.elapsedMs ≤ point.elapsedMs := by
  obtain ⟨_, before, after, split, earlier⟩ := first_completion_spec found
  subst trace
  have tail_ordered := (List.pairwise_append.mp ordered).2.1
  have later := (List.pairwise_cons.mp tail_ordered).1
  intro point member done
  rcases List.mem_append.mp member with prior | following
  · have absent := earlier point prior
    simp [absent] at done
  · rcases List.mem_cons.mp following with same | member
    · subst point
      exact Nat.le_refl _
    · exact later point member

/-- A later ascension or other loss of goals cannot erase a previously observed first hit. -/
theorem first_completion_persists {before : List Point} {hit : Point}
    (found : firstCompletion before = some hit) (later : List Point) :
    firstCompletion (before ++ later) = some hit :=
  (List.IsPrefix.find?_eq_some (by exact ⟨later, rfl⟩)) found

/-- A finite trace without a hit certifies only that its own observations are incomplete. -/
theorem no_hit_iff_incomplete_checkpoints (trace : List Point) :
    firstCompletion trace = none ↔ ∀ point, point ∈ trace → completed point = false := by
  simp [firstCompletion]

/-- Extending a censored trace with a complete observation yields a hit. -/
theorem no_hit_does_not_exclude_future_completion {before : List Point}
    (none_yet : firstCompletion before = none) (next : Point) (done : completed next = true) :
    firstCompletion (before ++ [next]) = some next := by
  simp [firstCompletion, List.find?_append, show before.find? completed = none from none_yet, done]

end CookieClicker.FullGame.Trace

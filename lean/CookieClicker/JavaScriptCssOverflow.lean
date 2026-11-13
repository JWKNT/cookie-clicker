import CookieClicker.JavaScriptCssCascade

/-! A conservative cascade invariant for definite-size box geometry. Unknown
selector matches are over-approximated, never assigned a Boolean value. A set
containing only whole hidden/visible overflow shorthands has identical axis
candidate lists; every possible cascade winner is still hidden or visible.
This does not assert general renderer, scrolling, clipping or hit-test laws. -/
namespace CookieClicker.JavaScript.Css

def isOverflowProperty (name : String) : Bool :=
  ["overflow","overflow-x","overflow-y"].contains name

private def trimOverflow (tokens : List Token) : List Token :=
  (tokens.dropWhile (· == .space)).reverse.dropWhile (· == .space) |>.reverse

def safeOverflowValue (tokens : List Token) : Prop :=
  tokens = [.ident (JSString.ofString "visible")] ∨
  tokens = [.ident (JSString.ofString "hidden")]

def safeOverflowValueB (tokens : List Token) : Bool :=
  tokens == [.ident (JSString.ofString "visible")] ||
  tokens == [.ident (JSString.ofString "hidden")]

private def wholePairedOverflow : Declaration → Bool
  | .invalid _ => true
  | .valid name value _ =>
    if !isOverflowProperty name then true
    else name == "overflow" && safeOverflowValueB (trimOverflow value)

private def validSelector : Selector → Bool
  | .make _ _ valid => valid

/-- Every rule which is not proved irrelevant is checked. In particular, an
unknown hover/focus match is included. Axis-specific declarations, wide keywords,
and mixed values prevent this projection, even if they would lose the cascade. -/
def overflowGeometryIndependent (tree : Tree) (id : Nat) (sheets : List Stylesheet)
    (inline : List Declaration) : Bool :=
  inline.all wholePairedOverflow && sheets.all fun sheet => sheet.rules.all fun rule =>
    match rule with
    | .style selectors declarations =>
      if selectors.any (!validSelector ·) then true
      else if !declarations.any (fun declaration => match declaration with
          | .valid name _ _ => isOverflowProperty name | _ => false) then true
      else if selectors.any (fun selector => matchSelector (tree.size*4+1024) tree id selector != .no) then
        declarations.all wholePairedOverflow
      else true
    | _ => true

/-- The same candidate, including priority and source order, is expanded to both
axes. This is also the actual one-value shorthand expansion used by layout. -/
def pairedOverflowAxes (candidate : Candidate) : List (String × Candidate) :=
  [("overflow-x",candidate),("overflow-y",candidate)]

def overflowAxisCandidates (axis : String) (candidates : List Candidate) : List Candidate :=
  ((candidates.flatMap pairedOverflowAxes).filter (·.1 == axis)).map (·.2)

theorem paired_overflow_x_candidates (candidates : List Candidate) :
    overflowAxisCandidates "overflow-x" candidates = candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates ih =>
    simp [overflowAxisCandidates,pairedOverflowAxes] at ih ⊢
    exact ih

theorem paired_overflow_y_candidates (candidates : List Candidate) :
    overflowAxisCandidates "overflow-y" candidates = candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates ih =>
    simp [overflowAxisCandidates,pairedOverflowAxes] at ih ⊢
    exact ih

theorem paired_overflow_axis_winners (candidates : List Candidate) :
    winner (overflowAxisCandidates "overflow-x" candidates) =
      winner (overflowAxisCandidates "overflow-y" candidates) := by
  rw [paired_overflow_x_candidates,paired_overflow_y_candidates]

private def safeBest (best : Option Candidate) : Prop :=
  ∀ candidate, best = some candidate → safeOverflowValue candidate.value

private def chooseOverflowBest (best : Option Candidate) (candidate : Candidate) : Option Candidate :=
  match best with
  | none => some candidate
  | some old => some (if candidateLE old candidate then candidate else old)

private theorem fold_overflow_safe (values : List Candidate) (best : Option Candidate)
    (hbest : safeBest best)
    (hvalues : ∀ candidate ∈ values, safeOverflowValue candidate.value) :
    safeBest (values.foldl chooseOverflowBest best) := by
  induction values generalizing best with
  | nil => exact hbest
  | cons value values ih =>
    apply ih
    · cases best with
      | none =>
        intro candidate h
        simp [chooseOverflowBest] at h
        subst candidate
        exact hvalues value (by simp)
      | some old =>
        intro candidate h
        simp only [chooseOverflowBest,Option.some.injEq] at h
        split at h
        · subst candidate; exact hvalues value (by simp)
        · subst candidate; exact hbest old rfl
    · intro candidate h
      exact hvalues candidate (by simp [h])

/-- Arbitrary selector resolutions may remove candidates or change their ranks.
Only membership in the checked hidden/visible value class is used here. -/
theorem paired_overflow_winner_safe (values : List Candidate)
    (hvalues : ∀ candidate ∈ values, safeOverflowValue candidate.value) :
    ∀ candidate, winner values = some candidate → safeOverflowValue candidate.value := by
  exact fold_overflow_safe values none (by intro candidate h; cases h) hvalues

theorem paired_overflow_selected_safe (potential selected : List Candidate)
    (hpotential : ∀ candidate ∈ potential, safeOverflowValue candidate.value)
    (hselected : ∀ candidate ∈ selected, candidate ∈ potential) :
    ∀ candidate, winner selected = some candidate → safeOverflowValue candidate.value := by
  apply paired_overflow_winner_safe
  intro candidate h
  exact hpotential candidate (hselected candidate h)

theorem safe_overflow_value_iff (tokens : List Token) :
    safeOverflowValueB tokens = true ↔ safeOverflowValue tokens := by
  simp [safeOverflowValueB,safeOverflowValue]

/-- The executable projection guard establishes the candidate invariant for
inline declarations and excludes all axis-specific overrides. -/
theorem overflow_projection_inline_safe (tree : Tree) (id : Nat) (sheets : List Stylesheet)
    (inline : List Declaration) (name : String) (value : List Token) (important : Bool)
    (hguard : overflowGeometryIndependent tree id sheets inline = true)
    (hproperty : isOverflowProperty name = true)
    (hmember : Declaration.valid name value important ∈ inline) :
    name = "overflow" ∧ safeOverflowValue (trimOverflow value) := by
  unfold overflowGeometryIndependent at hguard
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hguard).1 _ hmember
  simpa [wholePairedOverflow,hproperty,safeOverflowValueB,safeOverflowValue] using h

/-- The same guard covers every rule whose selector may match, including an
unknown dynamic selector. A definite negative selector is the only omission. -/
theorem overflow_projection_rule_safe (tree : Tree) (id : Nat) (sheets : List Stylesheet)
    (inline : List Declaration) (sheet : Stylesheet) (selectors : List Selector)
    (declarations : List Declaration) (name : String) (value : List Token) (important : Bool)
    (hguard : overflowGeometryIndependent tree id sheets inline = true)
    (hsheet : sheet ∈ sheets) (hrule : Rule.style selectors declarations ∈ sheet.rules)
    (hvalid : selectors.any (!validSelector ·) = false)
    (hpossible : selectors.any (fun selector => matchSelector (tree.size*4+1024) tree id selector != .no) = true)
    (hproperty : isOverflowProperty name = true)
    (hmember : Declaration.valid name value important ∈ declarations) :
    name = "overflow" ∧ safeOverflowValue (trimOverflow value) := by
  unfold overflowGeometryIndependent at hguard
  have hsheetAll := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hguard).2 sheet hsheet
  have hruleAll := List.all_eq_true.mp hsheetAll _ hrule
  have relevant : declarations.any (fun declaration => match declaration with
      | .valid name _ _ => isOverflowProperty name | _ => false) = true := by
    apply List.any_eq_true.mpr
    exact ⟨.valid name value important,hmember,hproperty⟩
  simp only [hvalid,Bool.false_eq_true,↓reduceIte,relevant,Bool.not_true,hpossible] at hruleAll
  have h := List.all_eq_true.mp hruleAll _ hmember
  simpa [wholePairedOverflow,hproperty,safeOverflowValueB,safeOverflowValue] using h

end CookieClicker.JavaScript.Css

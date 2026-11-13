import CookieClicker.JavaScriptSyntax

/-! Textarea value and cached selection state from pinned Chromium 87.
This stores UTF-16 code units, including unpaired surrogates. Selection events,
editing, focus, scrolling and layout are separate host transitions.
-/
namespace CookieClicker.JavaScript.TextControl

inductive Direction where
  | none | forward | backward
  deriving Repr, DecidableEq, Inhabited

structure State where
  value : JSString := []
  dirty : Bool := false
  start : Nat := 0
  finish : Nat := 0
  direction : Direction := .none
  revision : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- The JavaScript textarea value setter converts CRLF and lone CR to LF.
The defaultValue getter itself retains the child text without this conversion. -/
def normalize : JSString → JSString
  | [] => []
  | 13 :: 10 :: rest => 10 :: normalize rest
  | 13 :: rest => 10 :: normalize rest
  | unit :: rest => unit :: normalize rest

def setValue (state : State) (text : JSString) : State :=
  let value := normalize text
  if value == state.value then {state with dirty := true}
  else {value, dirty := true, start := value.length, finish := value.length, revision := state.revision + 1}

/-- ChildrenChanged preserves an edited value. Otherwise it updates the value
and clamps both selection endpoints, as SetNonDirtyValue(...,kClamp) does. -/
def childrenChanged (state : State) (text : JSString) : State :=
  if state.dirty then state else
  let value := normalize text
  if value == state.value then state
  else {
    value, dirty := false
    start := min value.length state.start
    finish := min value.length state.finish
    revision := state.revision + 1 }

def setRange (state : State) (start finish : Nat) (direction : Direction) : State :=
  let finish := min finish state.value.length
  {state with start := min start finish, finish, direction}

theorem value_set_dirty (state : State) (text : JSString) :
    (setValue state text).dirty = true := by
  simp [setValue]; split <;> rfl

theorem edited_children_preserve (state : State) (text : JSString)
    (dirty : state.dirty = true) : childrenChanged state text = state := by
  simp [childrenChanged,dirty]

theorem set_range_value (state : State) (start finish : Nat) (direction : Direction) :
    (setRange state start finish direction).value = state.value := rfl

theorem set_range_bounds (state : State) (start finish : Nat) (direction : Direction) :
    (setRange state start finish direction).start ≤ (setRange state start finish direction).finish ∧
    (setRange state start finish direction).finish ≤ state.value.length := by
  exact ⟨Nat.min_le_right _ _, Nat.min_le_right _ _⟩

end CookieClicker.JavaScript.TextControl

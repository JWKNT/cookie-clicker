import CookieClicker.JavaScriptTextControl

/-! The represented FrameSelection is confined to one native textarea's
unchanged internal editor. Arbitrary document/shadow ranges remain unsupported.
Revision distinguishes replacement of the internal editor's text nodes even
when a later assignment restores the same string. -/
namespace CookieClicker.JavaScript.BrowserTextSelectionState

structure Selection where
  owner : Nat
  revision : Nat
  start : Nat
  finish : Nat
  backward : Bool
  directional : Bool
  deriving Repr, DecidableEq, Inhabited

def fromCache (owner : Nat) (state : TextControl.State) : Selection := {
  owner,revision := state.revision,start := state.start,finish := state.finish
  backward := state.direction == .backward && state.start != state.finish
  directional := state.direction != .none }

def direction (selection : Selection) : TextControl.Direction :=
  if !selection.directional then .none
  else if selection.backward then .backward else .forward

theorem normalized_cache_maps_same_selection (owner : Nat) (state : TextControl.State) :
    fromCache owner {state with direction := direction (fromCache owner state)} = fromCache owner state := by
  cases h : state.direction <;> simp [fromCache,direction,h]
  by_cases same : state.start = state.finish <;> simp [same] <;> rfl

theorem from_cache_owner (owner : Nat) (state : TextControl.State) :
    (fromCache owner state).owner = owner := rfl

theorem from_cache_revision (owner : Nat) (state : TextControl.State) :
    (fromCache owner state).revision = state.revision := rfl

structure State where
  current : Option Selection := none
  pending : List Nat := []
  active : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

end CookieClicker.JavaScript.BrowserTextSelectionState

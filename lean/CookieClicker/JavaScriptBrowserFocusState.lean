import CookieClicker.JavaScriptState

/-! Explicit document focus state and nested native focus procedures.
An unset page-focus value is a missing environment assumption, not `false`.
Focusability, scrolling and editable selection are checked by the host model
before a procedure can complete.
-/
namespace CookieClicker.JavaScript.BrowserFocusState

structure Transition where
  oldTarget : Option Nat
  newTarget : Option Nat
  preventScroll : Bool := false
  selectionNone : Bool := false
  phase : Nat := 0
  blocked : Bool := false
  deriving Repr

structure State where
  pageFocused : Option Bool := none
  /-- Pinned Chromium87 defaults. These are host settings, not script data. -/
  spatialNavigationEnabled : Bool := false
  keyboardFocusableScrollers : Bool := false
  element : Option Nat := none
  transitions : List Transition := []
  deriving Repr

end CookieClicker.JavaScript.BrowserFocusState

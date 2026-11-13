import CookieClicker.JavaScriptState

/-! Data for DOM event dispatch. Native registrations retain insertion identity;
source callbacks execute through ordinary source machine frames. No executable
host callback or callback-result oracle is stored here. -/
namespace CookieClicker.JavaScript.BrowserEventState

inductive Target where
  | window
  | node (id : Nat)
  deriving Repr, DecidableEq

inductive HandlerBody where
  | callback (value : Value)
  | inlineText (text : JSString)
  deriving Repr, DecidableEq

/-- A disabled property handler remains recorded even if its content attribute
still contains text. Setting the content attribute again replaces this state. -/
structure Handler where
  eventType : JSString
  body : Option HandlerBody := none
  serial : Option Nat := none
  deriving Repr, DecidableEq

structure Invocation where
  serial : Nat
  callback : Value
  propertyHandler : Bool
  deriving Repr, DecidableEq

structure Visit where
  target : Target
  capture : Bool
  phase : Nat
  deriving Repr, DecidableEq

structure Dispatch where
  event : Nat
  visits : List Visit
  clearTarget : Bool := false
  windowTarget : Bool := false
  requireCanceledMouseClick : Bool := false
  current : Option Visit := none
  pending : List Invocation := []
  deriving Repr

end CookieClicker.JavaScript.BrowserEventState

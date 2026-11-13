import CookieClicker.JavaScriptSyntax

/-! Storage is an explicit environment input. The default is unconfigured;
it does not silently grant file-origin storage or invent a security exception.
Neither area reads a host browser profile or a player save.
-/
namespace CookieClicker.JavaScript.BrowserStorageState

inductive OriginMode where
  | unconfigured | denied | enabled
  deriving Repr, DecidableEq

inductive Quota where
  | unconfigured
  | bytes (limit : Nat)
  | unbounded
  deriving Repr, DecidableEq

structure Area where
  entries : List (JSString × JSString) := []
  object : Option Nat := none
  deriving Repr, DecidableEq

structure State where
  origin : OriginMode := .unconfigured
  quota : Quota := .unconfigured
  localArea : Area := {}
  sessionArea : Area := {}
  deriving Repr, DecidableEq

def byteSize (entries : List (JSString × JSString)) : Nat :=
  entries.foldl (fun total (key,value) => total + 2 * (key.length + value.length)) 0

end CookieClicker.JavaScript.BrowserStorageState

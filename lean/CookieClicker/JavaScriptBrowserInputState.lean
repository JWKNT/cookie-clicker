import CookieClicker.JavaScriptState

/-! Data carried by UI, mouse and keyboard event objects. These are event
records, not a hit-test oracle or a rule for trusted browser input dispatch. -/
namespace CookieClicker.JavaScript.BrowserInputState

structure UI where
  view : Value := .null
  detail : Int := 0
  sourceCapabilities : Value := .null
  deriving Repr

structure Modifiers where
  altKey : Bool := false
  controlKey : Bool := false
  metaKey : Bool := false
  shiftKey : Bool := false
  altGraph : Bool := false
  capsLock : Bool := false
  functionKey : Bool := false
  numLock : Bool := false
  scrollLock : Bool := false
  symbolKey : Bool := false
  deriving Repr

structure Mouse where
  ui : UI
  modifiers : Modifiers
  screenX : UInt64 := 0
  screenY : UInt64 := 0
  clientX : UInt64 := 0
  clientY : UInt64 := 0
  button : Int := 0
  buttons : Nat := 0
  movementX : Int := 0
  movementY : Int := 0
  relatedTarget : Value := .null
  region : Option JSString := none
  /-- Native page coordinates snapshot the view's scroll offset at creation.
  None records the missing scroll model; it is never interpreted as zero. -/
  page : Option (UInt64 × UInt64) := none
  deriving Repr

structure Keyboard where
  ui : UI
  modifiers : Modifiers
  key : JSString := []
  code : JSString := []
  location : Nat := 0
  repeating : Bool := false
  composing : Bool := false
  charCode : Nat := 0
  keyCode : Nat := 0
  deriving Repr

structure Focus where
  ui : UI
  relatedTarget : Value := .null
  deriving Repr

inductive Data where
  | ui (fields : UI)
  | mouse (fields : Mouse)
  | keyboard (fields : Keyboard)
  | focus (fields : Focus)
  deriving Repr

def Data.uiFields : Data → UI
  | .ui fields => fields
  | .mouse fields => fields.ui
  | .keyboard fields => fields.ui
  | .focus fields => fields.ui

def Data.modifiers : Data → Option Modifiers
  | .ui _ => none
  | .mouse fields => some fields.modifiers
  | .keyboard fields => some fields.modifiers
  | .focus _ => none

end CookieClicker.JavaScript.BrowserInputState

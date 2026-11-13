import CookieClicker.JavaScriptPriceRegistryAdvance
import CookieClicker.JavaScriptCursorDomFrame
import CookieClicker.JavaScriptCursorStyleFrame

/-! Actual admitted Cursor DOM operations retain the pricing catalogue.
Fresh text objects remain allocated. These constructors do not assume DOM
operations succeed; their native admission and exact target remain premises. -/
namespace CookieClicker.JavaScript.PriceRegistryDom
open Browser PriceRegistryAdvance PriceRegistry PriceRegistryComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def fromFrame {before after : Browser.State} (frame : CursorDomFrame.Extends before after) :
    Advance before.machine after.machine := {
  heap:=frame.heap,suffix:=#[]
  environments:=by simpa only [Array.append_empty] using frame.environments
  global:=by rw [frame.machine]
  exclusions:=by rw [frame.machine] }

def sameMachine {before after : Browser.State} (same : after.machine=before.machine) :
    Advance before.machine after.machine := fromFrame (CursorDomFrame.same_machine same)

def cursorName (before after : Browser.State) (id : Nat) (node : Browser.Node)
    (present : checkedNode before id=.ok node) (kind : node.kind=.element "div")
    (ran : setInnerHTML before id (JSString.ofString "Cursor")=.ok after) :
    Advance before.machine after.machine :=
  fromFrame (CursorDomFrame.cursor_innerHTML_extends before after id node present kind ran)

def textContent (before after : Browser.State) (id : Nat) (text : JSString)
    (ran : CursorDomFrame.textContentWrite before id text=.ok after) :
    Advance before.machine after.machine :=
  fromFrame (CursorDomFrame.text_content_write_extends before after id text ran)

def nameWorld (before after : Browser.State) (id : Nat) (node : Browser.Node)
    (present : checkedNode before id=.ok node) (kind : node.kind=.element "div")
    (ran : setInnerHTML before id (JSString.ofString "Cursor")=.ok after)
    (world : World before.machine) : World after.machine :=
  (cursorName before after id node present kind ran).world world

def nameProfile (before after : Browser.State) (id : Nat) (node : Browser.Node)
    (present : checkedNode before id=.ok node) (kind : node.kind=.element "div")
    (ran : setInnerHTML before id (JSString.ofString "Cursor")=.ok after)
    (world : World before.machine) (profile : Profile world) :
    Profile (nameWorld before after id node present kind ran world) :=
  (cursorName before after id node present kind ran).profile profile

end CookieClicker.JavaScript.PriceRegistryDom

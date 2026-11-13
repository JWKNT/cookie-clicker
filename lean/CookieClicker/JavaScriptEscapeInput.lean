import CookieClicker.JavaScriptExternalInput
import CookieClicker.JavaScriptBrowserFocus
import CookieClicker.JavaScriptBrowserRuntime
import CookieClicker.JavaScriptBrowserTime

/-! A closed native Escape-release procedure. The request contains only the
physical key identity. Its target comes from the actual document/focus state;
its fields come from retained host keyboard state. This module does not prove
initial reachability of that device state or support general keyboard input.
The Chromium87 source prerequisites are recorded alongside the module.
-/
namespace CookieClicker.JavaScript.EscapeInput
open Browser BrowserInputState
private def key := JSString.ofString
private def missing (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Physical Escape release: " ++ message)))

structure Device where
  escapeHeld : Bool
  modifiers : Modifiers := {}
  composing : Bool := false
  middleClickAutoscroll : Bool := false
  routingToPage : Bool
  javascriptKeysEnabled : Bool
  /-- Captured, cached native FiresTouchEvents(false) capability object. -/
  capabilities : ObjectId
  tooltipVisible : Bool := false

def escapeKey : ExternalInput.PhysicalKey := ⟨7,41⟩

/-- EventTargetNodeForDocument's unfocused ordinary HTML-document branch.
Neither the player request nor a diagnostic fixture supplies a DOM target. -/
def target (state : Browser.State) : Checked Nat := do
  if state.focus.pageFocused != some true then missing "active page focus is not established"
  if (← BrowserFocus.focusedElement state).isSome then missing "focused-control keyboard target/default behavior"
  let document ← checkedNode state state.document
  if document.kind != .document then missing "ordinary HTML document identity"
  let some root ← BrowserDocument.documentElement state state.document | missing "missing document element"
  let html ← checkedNode state root
  if html.kind != .element "html" || html.parent != some state.document then missing "ordinary HTML root"
  let some body ← BrowserDocument.htmlChild state state.document (· == "body") | missing "missing ordinary body target"
  let bodyNode ← checkedNode state body
  if bodyNode.kind != .element "body" || bodyNode.parent != some root then missing "ordinary body path"
  pure body

def fields (state : Browser.State) (device : Device) : Keyboard := {
  ui := {view := .object state.machine.globalObject,sourceCapabilities := .object device.capabilities}
  modifiers := device.modifiers
  key := key "Escape"
  code := key "Escape"
  keyCode := 27 }

/-- Native host admission, before Event construction. A missing capability
object or physical routing state is not replaced by null or assumed focus. -/
def admitted (state : Browser.State) (device : Device) : Checked Unit := do
  if !Execution.atBoundary state then
    .error (.fault (.invalidContinuation "Escape release during unfinished source work"))
  if !device.escapeHeld then missing "no retained physical Escape-down state"
  if !device.routingToPage || !device.javascriptKeysEnabled then missing "native keyboard delivery routing"
  if device.composing then missing "IME composition state"
  if device.middleClickAutoscroll then missing "native middle-click autoscroll consumes keyboard events"
  let capabilities ← checkedObject state.machine.heap device.capabilities
  match capabilities.kind with
  | .host "DOM.InputDeviceCapabilities" 0 => pure ()
  | _ => missing "captured native FiresTouchEvents(false) object identity"
  let some (_,prototype) := state.prototypes.specific.find? (·.1 == "#InputDeviceCapabilities") |
    missing "captured InputDeviceCapabilities prototype"
  if capabilities.prototype != some prototype then missing "native input-capability prototype identity"
  pure ()

structure Started where
  browser : Browser.State
  device : Device

/-- One real trusted key-up Event enters the ordinary source dispatcher. Its
source callbacks, exceptions and return are executed by BrowserRuntime; none
are supplied as results by this adapter. -/
def begin (state : Browser.State) (device : Device) : Checked Started := do
  admitted state device
  let targetNode ← target state
  let receiver ← nodeValue state (some targetNode)
  let (event,next) ← BrowserInput.allocate state "KeyboardEvent" (key "keyup")
    (.keyboard (fields state device)) true true true true
  pure {
    browser := BrowserEvents.dispatchEvent next receiver [event] true
    device := {device with escapeHeld := false,tooltipVisible := false} }

def inject (state : Browser.State) (device : Device) (request : ExternalInput.Input) : Checked Started :=
  match request with
  | .keyUp physical => if physical == escapeKey then begin state device
      else missing "physical key outside Escape-release fragment"
  | _ => missing "input outside Escape-release fragment"

theorem physical_escape_mapping : escapeKey.usagePage = 7 ∧ escapeKey.usage = 41 := by decide +kernel

theorem derived_fields (state : Browser.State) (device : Device) :
    (fields state device).key = key "Escape" ∧ (fields state device).code = key "Escape" ∧
    (fields state device).keyCode = 27 ∧ (fields state device).charCode = 0 ∧
    (fields state device).location = 0 ∧ (fields state device).repeating = false ∧
    (fields state device).composing = false := by exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem retained_modifiers (state : Browser.State) (device : Device) :
    (fields state device).modifiers = device.modifiers := rfl

theorem derived_native_view (state : Browser.State) (device : Device) :
    (fields state device).ui.view = .object state.machine.globalObject ∧
    (fields state device).ui.sourceCapabilities = .object device.capabilities := ⟨rfl,rfl⟩

theorem escape_request (state : Browser.State) (device : Device) :
    inject state device (.keyUp escapeKey) = begin state device := by simp [inject]

theorem released_device (state : Browser.State) (device : Device) (started : Started)
    (success : begin state device = .ok started) :
    started.device = {device with escapeHeld := false,tooltipVisible := false} := by
  unfold begin at success
  simp only [bind,Except.bind,pure,Except.pure] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · split at success
      · contradiction
      · split at success
        · contradiction
        · cases success
          rfl

end CookieClicker.JavaScript.EscapeInput

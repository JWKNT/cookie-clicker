import CookieClicker.JavaScriptEscapePath
import CookieClicker.JavaScriptEscapeHostStep
namespace CookieClicker.JavaScript.EscapeComplete
open Browser BrowserInputState EscapePath
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 3000000

def eventObject : JSObject := {
  kind:=.host "DOM.Event" 0
  prototype:=some 8
  properties := [⟨key "isTrusted",.accessor (some 13) none true false⟩]}
def trustGetter : JSObject := {kind:=.builtin ⟨"Browser.Event","get isTrusted"⟩,propertiesComplete:=false}
def callbackContinuation : BuiltinContinuation := {
  id:=⟨"Browser.Events","dispatch"⟩,thisValue:=.object 0,phase:="callback",indices:=[0,0]}
def liveEvent (elapsed : Rat) : DomEvent := {
  object:=12
  eventType:=key "keyup"
  target:=.object 6
  currentTarget:=.object 0
  time:=elapsed
  bubbles:=true
  cancelable:=true
  composed:=true
  dispatching:=true
  phase:=3}

def entered (gameTime duration : Value) (elapsed : Rat) (draws : List Nat) : Browser.State :=
  let base := state gameTime duration elapsed draws
  {base with
    machine := {base.machine with
      heap := {base.machine.heap with objects := base.machine.heap.objects.push eventObject |>.push trustGetter}
      control := .invoke (.object 3) (.object 0) [.object 12] false
      continuation := [.nativeCallback callbackContinuation base.machine.context]}
    domEvents := #[liveEvent elapsed]
    inputEvents := [(0,.keyboard (EscapeInput.fields base device))]
    eventDispatches := [{event:=0,visits:=[],current:=some ⟨.window,false,3⟩}]}

def firstRequest (a b : Value) (t : Rat) (r : List Nat) : Browser.State :=
  let initial := entered a b t r
  {initial with machine := EscapeSpan.run 47 initial.machine}
def firstValue (a b : Value) (t : Rat) (r : List Nat) : Browser.State :=
  Browser.result (firstRequest a b t r) (.number 4628293042053316608)
def secondRequest (a b : Value) (t : Rat) (r : List Nat) : Browser.State :=
  let initial := firstValue a b t r
  {initial with machine := EscapeSpan.run 79 initial.machine}
def secondValue (a b : Value) (t : Rat) (r : List Nat) : Browser.State :=
  Browser.result (secondRequest a b t r) (.number 4628293042053316608)
def callbackResult (a b : Value) (t : Rat) (r : List Nat) : Browser.State :=
  let initial := secondValue a b t r
  {initial with machine := EscapeSpan.run 9 initial.machine}

attribute [local cbv_opaque] EscapeSyntax.keyUpText closure nodes documentNode htmlNode bodyNode BrowserCanvasState.defaults
attribute [local cbv_eval] nodes_0 nodes_1 nodes_2 nodes_size
attribute [local cbv_eval] document_kind document_object document_parent document_children document_listeners document_handlers
attribute [local cbv_eval] html_kind html_object html_parent html_children html_listeners html_handlers
attribute [local cbv_eval] body_kind body_object body_parent body_children body_listeners body_handlers
attribute [local cbv_eval] closure_name closure_parameters closure_body closure_scope closure_strict closure_text
attribute [local cbv_opaque] BrowserRuntime.step
attribute [local cbv_eval] EscapeHostStep.step_fast
attribute [local cbv_opaque] Number.ofNat Number.ofInt Number.lessThan Number.equal toJSString
attribute [local cbv_eval] number_ofInt_27 number_ofNat_one number_zero_below_one number_27_equal number_27_string

set_option maxHeartbeats 1000000 in
theorem first_certificate (a b : Value) (t : Rat) (r : List Nat) :
    EscapeSpan.certificate 47 (entered a b t r).machine = true := by cbv

set_option maxHeartbeats 1000000 in
theorem second_certificate (a b : Value) (t : Rat) (r : List Nat) :
    EscapeSpan.certificate 79 (firstValue a b t r).machine = true := by cbv

set_option maxHeartbeats 1000000 in
theorem third_certificate (a b : Value) (t : Rat) (r : List Nat) :
    EscapeSpan.certificate 9 (secondValue a b t r).machine = true := by cbv

theorem first_span (a b : Value) (t : Rat) (r : List Nat) (fuel : Nat) :
    BrowserRuntime.run (47+fuel) (entered a b t r) = BrowserRuntime.run fuel (firstRequest a b t r) :=
  EscapeSpan.native_prefix 47 _ fuel rfl rfl (first_certificate a b t r)

theorem second_span (a b : Value) (t : Rat) (r : List Nat) (fuel : Nat) :
    BrowserRuntime.run (79+fuel) (firstValue a b t r) = BrowserRuntime.run fuel (secondRequest a b t r) :=
  EscapeSpan.native_prefix 79 _ fuel rfl rfl (second_certificate a b t r)

theorem third_span (a b : Value) (t : Rat) (r : List Nat) (fuel : Nat) :
    BrowserRuntime.run (9+fuel) (secondValue a b t r) = BrowserRuntime.run fuel (callbackResult a b t r) :=
  EscapeSpan.native_prefix 9 _ fuel rfl rfl (third_certificate a b t r)

theorem first_getter (a b : Value) (t : Rat) (r : List Nat) (fuel : Nat) :
    BrowserRuntime.run (1+fuel) (firstRequest a b t r) = BrowserRuntime.run fuel (firstValue a b t r) := by
  rw [Nat.add_comm 1 fuel]
  cbv

theorem second_getter (a b : Value) (t : Rat) (r : List Nat) (fuel : Nat) :
    BrowserRuntime.run (1+fuel) (secondRequest a b t r) = BrowserRuntime.run fuel (secondValue a b t r) := by
  rw [Nat.add_comm 1 fuel]
  cbv

end CookieClicker.JavaScript.EscapeComplete

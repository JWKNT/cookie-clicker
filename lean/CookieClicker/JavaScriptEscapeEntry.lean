import CookieClicker.JavaScriptEscapeComplete
namespace CookieClicker.JavaScript.EscapeEntry
open Browser BrowserInputState EscapePath EscapeComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option cbv.maxSteps 1000000

def initialEvent (t:Rat) : DomEvent :=
  {liveEvent t with currentTarget:=.null,phase:=0}
def visits : List BrowserEventState.Visit := [
  ⟨.window,true,1⟩,⟨.node 0,true,1⟩,⟨.node 1,true,1⟩,
  ⟨.node 2,false,2⟩,⟨.node 1,false,3⟩,⟨.node 0,false,3⟩,⟨.window,false,3⟩]
def queued (a b:Value)(t:Rat)(r:List Nat) : Browser.State :=
  let base:=state a b t r
  {base with
    machine:={base.machine with
      heap:={base.machine.heap with objects:=base.machine.heap.objects.push eventObject |>.push trustGetter}
      control:=.resumeBuiltin {id:=⟨"Browser.Events","dispatch"⟩,thisValue:=.undefined,phase:="advance"} .undefined}
    domEvents:=#[initialEvent t]
    inputEvents:=[(0,.keyboard (EscapeInput.fields base device))]
    eventDispatches:=[{event:=0,visits}]}
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

def allocated (a b:Value)(t:Rat)(r:List Nat) : Browser.State :=
  let base:=state a b t r
  {base with
    machine:={base.machine with
      heap:={base.machine.heap with objects:=base.machine.heap.objects.push eventObject |>.push trustGetter}}
    domEvents:=#[{initialEvent t with target:=.null,dispatching:=false}]
    inputEvents:=[(0,.keyboard (EscapeInput.fields base device))]}
theorem actual_allocate (a b:Value)(t:Rat)(r:List Nat):
    BrowserInput.allocate (state a b t r) "KeyboardEvent" (key "keyup")
      (.keyboard (EscapeInput.fields (state a b t r) device)) true true true true =
      .ok (.object 12,allocated a b t r) := by cbv

theorem actual_dispatch (a b:Value)(t:Rat)(r:List Nat):
    BrowserEvents.dispatchEvent (allocated a b t r) (.object 6) [.object 12] true=
      queued a b t r := by rfl

theorem actual_started (a b:Value)(t:Rat)(r:List Nat):
    started a b t r=queued a b t r := by
  unfold started EscapeInput.begin
  rw [admission]
  simp only [bind,Except.bind]
  rw [target_is_body]
  change (match BrowserInput.allocate (state a b t r) "KeyboardEvent" (key "keyup")
      (.keyboard (EscapeInput.fields (state a b t r) device)) true true true true with
      | .ok (event,next) => BrowserEvents.dispatchEvent next (.object 6) [event] true
      | .error failure => Browser.fail (state a b t r) failure) = _
  rw [actual_allocate]
  exact actual_dispatch a b t r


theorem dispatch_prefix (a b:Value)(t:Rat)(r:List Nat)(fuel:Nat):
    BrowserRuntime.run (8+fuel) (queued a b t r) =
      BrowserRuntime.run fuel (entered a b t r) := by
  rw [Nat.add_comm 8 fuel]
  cbv

theorem native_entry (a b:Value)(t:Rat)(r:List Nat)(fuel:Nat):
    BrowserRuntime.run (8+fuel) (started a b t r) =
      BrowserRuntime.run fuel (entered a b t r) := by
  rw [actual_started]
  exact dispatch_prefix a b t r fuel

theorem native_input (a b:Value)(t:Rat)(r:List Nat):
    EscapeInput.inject (state a b t r) device (.keyUp EscapeInput.escapeKey)=
      .ok {browser:=queued a b t r,device:={device with escapeHeld:=false,tooltipVisible:=false}} := by
  rw [EscapeInput.escape_request]
  unfold EscapeInput.begin
  rw [admission]
  simp only [bind,Except.bind]
  rw [target_is_body]
  change ((match BrowserInput.allocate (state a b t r) "KeyboardEvent" (key "keyup")
      (.keyboard (EscapeInput.fields (state a b t r) device)) true true true true with
      | .ok (event,next) => .ok ({
          browser:=BrowserEvents.dispatchEvent next (.object 6) [event] true
          device:={device with escapeHeld:=false,tooltipVisible:=false}} : EscapeInput.Started)
      | .error failure => .error failure) : Checked EscapeInput.Started) = _
  rw [actual_allocate]
  simp only [actual_dispatch]
end CookieClicker.JavaScript.EscapeEntry

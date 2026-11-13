import CookieClicker.JavaScriptEscapeEntry
namespace CookieClicker.JavaScript.EscapeReturned
open Browser BrowserInputState EscapePath EscapeComplete EscapeEntry
set_option maxRecDepth 200000
set_option maxHeartbeats 1500000
set_option cbv.maxSteps 3000000

def finished (a b:Value)(t:Rat)(r:List Nat) : Browser.State :=
  Browser.result {callbackResult a b t r with
    domEvents:=#[{liveEvent t with currentTarget:=.null,phase:=0,dispatching:=false}]
    eventDispatches:=[]} (.boolean true)
theorem number_ofNat_28 : Number.ofNat 28=4628574517030027264 := by decide +kernel
theorem number_28_equal : Number.equal 4628574517030027264 4628574517030027264=true := by decide +kernel
attribute [local cbv_eval] number_ofNat_28 number_28_equal
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

theorem finish_prefix (a b:Value)(t:Rat)(r:List Nat)(fuel:Nat):
    BrowserRuntime.run (2+fuel) (callbackResult a b t r)=
      BrowserRuntime.run fuel (finished a b t r) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem source_callback (a b:Value)(t:Rat)(r:List Nat)(fuel:Nat):
    BrowserRuntime.run (147+fuel) (started a b t r)=
      BrowserRuntime.run fuel (finished a b t r) := by
  have count : 147+fuel=8+(47+(1+(79+(1+(9+(2+fuel)))))) := by omega
  rw [count,native_entry,first_span,first_getter,second_span,second_getter,third_span,finish_prefix]

theorem output_exact (a b:Value)(t:Rat)(r:List Nat):
    output a b t r=finished a b t r := source_callback a b t r 0

theorem native_writes (a b:Value)(t:Rat)(r:List Nat):
    propertyValue (finished a b t r) 1 "lastActivity"=some (.data a true true true) ∧
    propertyValue (finished a b t r) 1 "AscendTimer"=some (.data b true true true) ∧
    propertyValue (finished a b t r) 2 "27"=some (.data (.number 0) true true true) := by cbv

theorem native_returned (a b:Value)(t:Rat)(r:List Nat):
    Execution.atBoundary (finished a b t r)=true ∧
    (finished a b t r).machine.elapsed=t ∧
    (finished a b t r).randomInputs=r ∧
    (finished a b t r).machine.context=(state a b t r).machine.context ∧
    (finished a b t r).machine.continuation=[] := by cbv


theorem retained_source_fields (a b:Value)(t:Rat)(r:List Nat):
    propertyValue (finished a b t r) 1 "time"=some (.data a true true true) ∧
    propertyValue (finished a b t r) 1 "AscendDuration"=some (.data b true true true) ∧
    propertyValue (finished a b t r) 1 "promptOn"=some (.data (.number 0) true true true) ∧
    (finished a b t r).machine.heap.objects.size=15 ∧
    (finished a b t r).machine.heap.environments.size=2 := by cbv

theorem released_event (a b:Value)(t:Rat)(r:List Nat):
    (finished a b t r).domEvents[0]?=
      some {liveEvent t with currentTarget:=.null,phase:=0,dispatching:=false} ∧
    (finished a b t r).eventDispatches=[] := by cbv

theorem native_release_outcome (a b:Value)(t:Rat)(r:List Nat):
    propertyValue (output a b t r) 1 "lastActivity"=some (.data a true true true) ∧
    propertyValue (output a b t r) 1 "AscendTimer"=some (.data b true true true) ∧
    propertyValue (output a b t r) 2 "27"=some (.data (.number 0) true true true) ∧
    Execution.atBoundary (output a b t r)=true ∧
    (output a b t r).machine.elapsed=t ∧
    (output a b t r).randomInputs=r := by
  rw [output_exact]
  exact ⟨(native_writes a b t r).1,(native_writes a b t r).2.1,
    (native_writes a b t r).2.2,(native_returned a b t r).1,
    (native_returned a b t r).2.1,(native_returned a b t r).2.2.1⟩
end CookieClicker.JavaScript.EscapeReturned

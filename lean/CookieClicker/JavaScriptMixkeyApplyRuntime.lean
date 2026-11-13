import CookieClicker.JavaScriptMixkeyApply
import CookieClicker.JavaScriptBrowserCoreStep

/-! Native key-array apply and character construction through browser dispatch. -/
namespace CookieClicker.JavaScript.MixkeyApplyRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open MixkeyApply

theorem consume_element (state : Browser.State) (i : Inputs) (index : Nat) (done : List Value) :
    BrowserRuntime.step {state with machine := atElement i index done} =
      {state with machine := atResponse i index done} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,MixkeyApply.consume_element]
  rfl

theorem resume_element (state : Browser.State) (i : Inputs) (index : Nat) (done : List Value)
    (before : index<i.length) :
    BrowserRuntime.step {state with machine := atResponse i index done} =
      {state with machine := next i (index+1) (done++[selected i index])} := by
  have passthrough : BrowserRuntime.step {state with machine := atResponse i index done}=
      {state with machine := {Builtins.builtinStep (atResponse i index done) with elapsed := i.base.elapsed}} :=
    BrowserCoreStep.resume_step state i.base (continuation i index done) (selected i index) (Or.inr (Or.inr rfl))
  rw [passthrough]
  rw [MixkeyApply.resume_element,apply_next i (index+1) _ (by omega)]
  unfold next
  split <;> rfl

theorem actual_element (state : Browser.State) (i : Inputs) (index : Nat) (done : List Value)
    (before : index<i.length) (fuel : Nat) :
    BrowserRuntime.run (2+fuel) {state with machine := next i index done} =
      BrowserRuntime.run fuel {state with machine := next i (index+1) (done++[selected i index])} := by
  simp only [next,before,↓reduceIte]
  rw [show 2+fuel=(fuel+1)+1 by omega]
  change BrowserRuntime.run (fuel+1) (BrowserRuntime.step {state with machine := atElement i index done}) = _
  rw [consume_element]
  change BrowserRuntime.run fuel (BrowserRuntime.step {state with machine := atResponse i index done}) = _
  rw [resume_element state i index done before]
  rfl

theorem actual_elements (state : Browser.State) (i : Inputs) (count index : Nat) (done : List Value)
    (remaining : index+count=i.length) (fuel : Nat) :
    BrowserRuntime.run (2*count+fuel) {state with machine := next i index done} =
      BrowserRuntime.run fuel {state with machine := invoked i (done++values i index count)} := by
  induction count generalizing index done with
  | zero => simp [next,show index=i.length by omega,values]
  | succ count ih =>
    rw [show 2*(count+1)+fuel=2+(2*count+fuel) by omega,actual_element state i index done (by omega)]
    rw [ih (index+1) _ (by omega)]
    simp [values,List.range'_succ,List.map_cons,List.append_assoc]

theorem consume_length (state : Browser.State) (i : Inputs) :
    BrowserRuntime.step {state with machine := atLength i}={state with machine := lengthResponse i} := by
  rw [BrowserCoreStep.plain_step _ rfl rfl,MixkeyApply.consume_length]
  rfl

theorem resume_length (state : Browser.State) (i : Inputs) :
    BrowserRuntime.step {state with machine := lengthResponse i}={state with machine := next i 0 []} := by
  have passthrough : BrowserRuntime.step {state with machine := lengthResponse i}=
      {state with machine := {Builtins.builtinStep (lengthResponse i) with elapsed := i.base.elapsed}} :=
    BrowserCoreStep.resume_step state i.base (lengthContinuation i) (.number (Number.ofNat i.length)) (Or.inr (Or.inr rfl))
  rw [passthrough]
  rw [MixkeyApply.resume_length]
  unfold next
  split <;> rfl

theorem actual_apply (state : Browser.State) (i : Inputs) (fuel : Nat) :
    BrowserRuntime.run (2+2*i.length+fuel) {state with machine := atLength i}=
      BrowserRuntime.run fuel {state with machine := invoked i (values i 0 i.length)} := by
  rw [show 2+2*i.length+fuel=(2*i.length+fuel+1)+1 by omega]
  change BrowserRuntime.run (2*i.length+fuel+1) (BrowserRuntime.step {state with machine := atLength i}) = _
  rw [consume_length]
  change BrowserRuntime.run (2*i.length+fuel) (BrowserRuntime.step {state with machine := lengthResponse i}) = _
  rw [resume_length,actual_elements state i i.length 0 [] (by omega)]
  rfl

theorem invoke_codes (state : Browser.State) (i : Inputs) (notSeed : state.nativeSeedrandom≠some i.function) :
    BrowserRuntime.step {state with machine := invoked i (values i 0 i.length)}={state with machine := codesRequest i} := by
  have passthrough : BrowserRuntime.step {state with machine := invoked i (values i 0 i.length)}=
      {state with machine := {Builtins.builtinStep (invoked i (values i 0 i.length)) with elapsed := i.base.elapsed}} := by
    cases length : i.length with
    | zero =>
      simp only [values,length,List.range'_zero,List.map_nil]
      exact BrowserCoreStep.invoke_empty state i.base i.function (.number Number.positiveZero) notSeed
    | succ count =>
      simp only [values,length,List.range'_succ,List.map_cons,selected,MixkeyArray.byteValue]
      exact BrowserCoreStep.invoke_number state i.base i.function (.number Number.positiveZero) _ _
  rw [passthrough,MixkeyApply.invoke_codes]
  rfl

theorem respond_codes (state : Browser.State) (i : Inputs) :
    BrowserRuntime.step {state with machine := codesRequest i}={state with machine := returned i} := by
  have passthrough : BrowserRuntime.step {state with machine := codesRequest i}=
      {state with machine := {Builtins.builtinStep (codesRequest i) with elapsed := i.base.elapsed}} :=
    BrowserCoreStep.builtin_step state i.base ⟨"String","fromCharCode"⟩ (.number Number.positiveZero)
      (values i 0 i.length) false (Or.inl rfl)
  rw [passthrough]
  rw [MixkeyApply.respond_codes]
  rfl

theorem actual_codes (state : Browser.State) (i : Inputs) (notSeed : state.nativeSeedrandom≠some i.function) (fuel : Nat) :
    BrowserRuntime.run (2+fuel) {state with machine := invoked i (values i 0 i.length)}=
      BrowserRuntime.run fuel {state with machine := returned i} := by
  rw [show 2+fuel=(fuel+1)+1 by omega]
  change BrowserRuntime.run (fuel+1) (BrowserRuntime.step {state with machine := invoked i (values i 0 i.length)}) = _
  rw [invoke_codes state i notSeed]
  simp only [BrowserRuntime.run]
  change (match status (BrowserRuntime.step {state with machine := codesRequest i}).machine with
    | .unresolved nextRequest => _
    | .fault _ => _
    | _ => _) = _
  rw [respond_codes]
  cases remaining : i.base.continuation <;> simp [returned,result,status,remaining]

theorem complete_native_apply (state : Browser.State) (i : Inputs)
    (notSeed : state.nativeSeedrandom≠some i.function) (fuel : Nat) :
    BrowserRuntime.run (4+2*i.length+fuel) {state with machine := atLength i}=
      BrowserRuntime.run fuel {state with machine := returned i} := by
  rw [show 4+2*i.length+fuel=2+2*i.length+(2+fuel) by omega,actual_apply,actual_codes state i notSeed]

theorem actual_apply_request (state : Browser.State) (i : Inputs)
    (control : i.base.control=.unresolved (.builtin applyId (.object i.function) (arguments i) false))
    (notSeed : state.nativeSeedrandom≠some i.function) (fuel : Nat) :
    BrowserRuntime.run (5+2*i.length+fuel) {state with machine := i.base}=
      BrowserRuntime.run fuel {state with machine := returned i} := by
  have response : BrowserRuntime.step {state with machine := i.base}={state with machine := atLength i} := by
    have core : Builtins.builtinStep i.base=atLength i := by
      simp only [Builtins.builtinStep,control]
      exact native_apply_call i
    have prepared : i.base={i.base with control := .unresolved (.builtin applyId (.object i.function) (arguments i) false)} := by
      rw [←control]
    calc
      _ = {state with machine := {Builtins.builtinStep i.base with elapsed := i.base.elapsed}} := by
        have bridge := BrowserCoreStep.builtin_step state i.base applyId (.object i.function) (arguments i) false (Or.inr (Or.inr rfl))
        rw [←prepared] at bridge
        exact bridge
      _ = _ := by rw [core]; rfl
  rw [show 5+2*i.length+fuel=(4+2*i.length+fuel)+1 by omega]
  simp only [BrowserRuntime.run,status,control]
  rw [response]
  change BrowserRuntime.run (4+2*i.length+fuel) {state with machine := atLength i} = _
  exact complete_native_apply state i notSeed fuel

end CookieClicker.JavaScript.MixkeyApplyRuntime

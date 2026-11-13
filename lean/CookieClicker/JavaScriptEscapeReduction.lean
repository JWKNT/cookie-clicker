import CookieClicker.JavaScriptBrowserCoreStep
namespace CookieClicker.JavaScript.EscapeReduction

def slowStep (state : Browser.State) : Browser.State :=
  let next := BrowserRuntime.internalStep state
  {next with machine := {next.machine with elapsed := state.machine.elapsed}}

def reducedStep (state : Browser.State) : Browser.State :=
  if BrowserCoreStep.plain state.machine.control then
    match status state.machine with
    | .running => {state with machine := {Builtins.builtinStep state.machine with elapsed := state.machine.elapsed}}
    | _ => slowStep state
  else slowStep state

theorem step_reduction (state : Browser.State) : BrowserRuntime.step state = reducedStep state := by
  unfold reducedStep
  split
  · rename_i isPlain
    cases current : status state.machine with
    | running => exact BrowserCoreStep.plain_step state isPlain current
    | _ => rfl
  · rfl
end CookieClicker.JavaScript.EscapeReduction

import CookieClicker.JavaScriptEscapeInput

namespace CookieClicker.JavaScript.EscapeTime
open Browser BrowserInputState
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem allocate_elapsed (state next : Browser.State) (name : String) (kind : JSString)
    (data : Data) (bubbles cancelable composed trusted : Bool) (value : Value)
    (success : BrowserInput.allocate state name kind data bubbles cancelable composed trusted = .ok (value,next)) :
    next.machine.elapsed = state.machine.elapsed := by
  unfold BrowserInput.allocate at success
  generalize first : BrowserEventData.allocateEvent state kind .null = allocated at success
  cases allocated with
  | error failure => simp [bind,Except.bind] at success
  | ok pair =>
    rcases pair with ⟨event,middle⟩
    have clock := BrowserTime.allocate_event_elapsed state middle kind .null event first
    simp only [bind,Except.bind,pure,Except.pure] at success
    repeat' first | contradiction | (split at success)
    all_goals cases success; exact clock

theorem begin_elapsed (state : Browser.State) (device : EscapeInput.Device)
    (started : EscapeInput.Started) (success : EscapeInput.begin state device = .ok started) :
    started.browser.machine.elapsed = state.machine.elapsed := by
  unfold EscapeInput.begin at success
  simp only [bind,Except.bind,pure,Except.pure] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · split at success
      · contradiction
      · rename_i receiver receiverEq
        split at success
        · contradiction
        · rename_i pair input
          rcases pair with ⟨event,next⟩
          cases success
          exact (BrowserTime.dispatch_elapsed next receiver [event] true).trans
            (allocate_elapsed state next _ _ _ _ _ _ _ event input)

end CookieClicker.JavaScript.EscapeTime

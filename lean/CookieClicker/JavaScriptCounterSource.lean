import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptCounterSyntax

/-! Execution of the pinned Earn and Spend bodies in an explicit counter heap.
The theorems quantify over all operand bit patterns. They establish source
reads, compound assignments, and write order. A separate frame/refinement
proof must lift this heap to the initialized game and establish field invariants.
-/
namespace CookieClicker.JavaScript.CounterSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
attribute [local cbv_opaque] Number.add Number.sub Number.ofNat
private def key := JSString.ofString

open CounterSyntax

def counterObject (cookies earned : UInt64) : JSObject := {
  properties := [
    ⟨key "cookies", .data (.number cookies) true true true⟩,
    ⟨key "cookiesEarned", .data (.number earned) true true true⟩] }

def state (body : Stmt) (cookies earned amount : UInt64) : Machine := {
  heap := {
    objects := #[counterObject cookies earned]
    environments := #[⟨.declarative [
      { name := "Game", value := .object 0 },
      { name := "howmuch", value := .number amount }],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .statement body
  globalObject := 0 }

theorem actual_earn_body (cookies earned amount : UInt64) :
    (run 37 (state earnBody cookies earned amount)).heap.objects =
      #[counterObject (Number.add cookies amount) (Number.add earned amount)] := by
  cbv

theorem actual_earn_body_completion (cookies earned amount : UInt64) :
    status (run 37 (state earnBody cookies earned amount)) =
      .completion (.normal (some (.number (Number.add earned amount)))) := by
  cbv

theorem actual_spend_body (cookies earned amount : UInt64) :
    (run 20 (state spendBody cookies earned amount)).heap.objects =
      #[counterObject (Number.sub cookies amount) earned] := by
  cbv

theorem actual_spend_body_completion (cookies earned amount : UInt64) :
    status (run 20 (state spendBody cookies earned amount)) =
      .completion (.normal (some (.number (Number.sub cookies amount)))) := by
  cbv

def callState (body : Stmt) (cookies earned amount : UInt64) : Machine := {
  heap := {
    objects := #[counterObject cookies earned,
      { kind := .function ⟨none,["howmuch"],
          (match body with | .block statements => statements | other => [other]),0,false,none⟩ }]
    environments := #[⟨.declarative [{ name := "Game",value := .object 0 }],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .invoke (.object 1) (.object 0) [.number amount] false
  globalObject := 0 }

/-- Ordinary invocation includes argument binding and restores the caller.
The source function has no return statement and therefore returns undefined. -/
theorem actual_earn_call (cookies earned amount : UInt64) :
    let after := run 100 (callState earnBody cookies earned amount)
    status after = .value .undefined ∧
      after.heap.object? 0 = some (counterObject (Number.add cookies amount) (Number.add earned amount)) ∧
      after.context = (callState earnBody cookies earned amount).context := by
  cbv

theorem actual_spend_call (cookies earned amount : UInt64) :
    let after := run 100 (callState spendBody cookies earned amount)
    status after = .value .undefined ∧
      after.heap.object? 0 = some (counterObject (Number.sub cookies amount) earned) ∧
      after.context = (callState spendBody cookies earned amount).context := by
  cbv

end CookieClicker.JavaScript.CounterSource

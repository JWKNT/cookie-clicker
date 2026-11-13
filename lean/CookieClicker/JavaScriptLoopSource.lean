import CookieClicker.JavaScriptLoopArithmeticBridge
import CookieClicker.JavaScriptLoopSyntax
import CookieClicker.JavaScriptThresholdBridge
/-! Exact selected statements from the intact native Game.Loop body.
The latency assignment executes the actual Number operations, the native Math.min
builtin keeps the proved nonpositive delay, and the catch-up while executes zero
iterations with no heap changes. The default disabled timeout block also skips.
These are statements at explicit entry layouts; the initialized game,
surrounding callees and scheduler frame remain open.
-/
namespace CookieClicker.JavaScript.LoopSource
open LoopArithmeticBridge
set_option maxRecDepth 32768
set_option cbv.maxSteps 2000000
set_option maxHeartbeats 4000000
private def key := JSString.ofString
private def data (name : String) (value : Value) : OwnProperty := ⟨key name,.data value true true true⟩
def catchupStatement : Stmt := match LoopSyntax.LoopBody with
  | .block statements => statements[12]?.getD .empty
  | _ => .empty

def catchupState (bits : UInt64) : Machine := {
  heap := {
    objects := #[{properties := [data "accumulatedDelay" (.number bits)]}]
    environments := #[⟨.declarative [{name := "Game",value := .object 0}],none⟩]}
  context := ⟨0,0,.object 0,false⟩
  control := .statement catchupStatement
  globalObject := 0}

attribute [local cbv_opaque] Number.lessThan

theorem actual_catchup_test (bits : UInt64) :
    (run 12 (catchupState bits)).control =
      .expressionResult (.value (.boolean (Number.lessThan Number.positiveZero bits))) := by cbv

theorem actual_catchup_false_tail (bits : UInt64) :
    run 1 {run 12 (catchupState bits) with
      control := .expressionResult (.value (.boolean false))} =
      {catchupState bits with control := .completion (.normal none)} := by cbv

theorem actual_catchup_skipped (bits : UInt64)
    (notPositive : Number.lessThan Number.positiveZero bits = false) :
    run 13 (catchupState bits) =
      {catchupState bits with control := .completion (.normal none)} := by
  have control := actual_catchup_test bits
  rw [notPositive] at control
  have update : {run 12 (catchupState bits) with control := .expressionResult (.value (.boolean false))} =
      run 12 (catchupState bits) := by rw [← control]
  change run (12+1) (catchupState bits) = _
  rw [ThresholdBridge.run_add,← update]
  exact actual_catchup_false_tail bits

theorem actual_catchup_skipped_on_every_prefix (initial : UInt64) (n k : Nat)
    (entry : NegativeScaledValue initial 54 n) (bounded : n ≤ 2^106) :
    run 13 (catchupState (loopDelays initial k)) =
      {catchupState (loopDelays initial k) with control := .completion (.normal none)} :=
  actual_catchup_skipped _ (loop_delay_never_triggers_catchup initial n k entry bounded)

def latencyStatement : Stmt := match LoopSyntax.LoopBody with
  | .block statements => statements[8]?.getD .empty
  | _ => .empty

def latencyState (delay previous now : UInt64) : Machine := {
  heap := {
    objects := #[{properties := [data "accumulatedDelay" (.number delay),
      data "time" (.number previous),data "fps" (.number (Number.ofNat 30))]}]
    environments := #[⟨.declarative [{name := "Game",value := .object 0},
      {name := "time",value := .number now}],none⟩]}
  context := ⟨0,0,.object 0,false⟩
  control := .statement latencyStatement
  globalObject := 0}

attribute [local cbv_opaque] Number.add Number.sub Number.div Number.ofNat

theorem actual_latency_assignment (delay previous now : UInt64) :
    (run 80 (latencyState delay previous now)).heap.object? 0 =
      some {properties := [data "accumulatedDelay" (.number
        (Number.add delay (Number.sub (Number.sub now previous)
          (Number.div 4652007308841189376 (Number.ofNat 30))))),
        data "time" (.number previous),data "fps" (.number (Number.ofNat 30))]} := by cbv

theorem actual_latency_frame (delay previous now : UInt64) :
    run 80 (latencyState delay previous now) =
      {latencyState delay previous now with
        heap := { (latencyState delay previous now).heap with
          objects := #[{properties := [data "accumulatedDelay" (.number
            (Number.add delay (Number.sub (Number.sub now previous)
              (Number.div 4652007308841189376 (Number.ofNat 30))))),
            data "time" (.number previous),data "fps" (.number (Number.ofNat 30))]}] }
        control := .completion (.normal (some (.number
          (Number.add delay (Number.sub (Number.sub now previous)
            (Number.div 4652007308841189376 (Number.ofNat 30)))))))} := by cbv

theorem actual_latency_step (delay : UInt64) (time : Nat) (bounded : time+33 < 2^52) :
    (run 80 (latencyState delay (Number.ofNat time) (Number.ofNat (time+33)))).heap.object? 0 =
      some {properties := [data "accumulatedDelay" (.number (Number.add delay latencyCredit)),
        data "time" (.number (Number.ofNat time)),data "fps" (.number (Number.ofNat 30))]} := by
  rw [actual_latency_assignment]
  have literal : (4652007308841189376 : UInt64) = Number.ofNat 1000 := by decide +kernel
  rw [literal,native_latency_step time bounded]

theorem source_unconditional_logic_call :
    (match LoopSyntax.LoopBody with | .block statements => statements[5]? | _ => none) =
      some (.expression (.call (.member (.identifier "Game") (.identifier "Logic") false) [])) := rfl

theorem source_catchup_shape :
    catchupStatement = .while
      (.binary .greater (.member (.identifier "Game") (.identifier "accumulatedDelay") false)
        (.literal (.number 0)))
      (.block [
        .expression (.call (.member (.identifier "Game") (.identifier "Logic") false) []),
        .expression (.assignment .subtract
          (.member (.identifier "Game") (.identifier "accumulatedDelay") false)
          (.binary .divide (.literal (.number 4652007308841189376))
            (.member (.identifier "Game") (.identifier "fps") false)))]) := rfl

def clampStatement : Stmt := match LoopSyntax.LoopBody with
  | .block statements => statements[10]?.getD .empty
  | _ => .empty

def clampState (delay : UInt64) : Machine := {
  heap := {
    objects := #[{properties := [data "accumulatedDelay" (.number delay)]},
      {properties := [data "min" (.object 2)]},
      {kind := .builtin ⟨"Math","min"⟩}]
    environments := #[⟨.declarative [{name := "Game",value := .object 0},
      {name := "Math",value := .object 1}],none⟩]}
  context := ⟨0,0,.object 0,false⟩
  control := .statement clampStatement
  globalObject := 0}

attribute [local cbv_opaque] Number.minimum Number.mul

theorem actual_clamp_assignment (delay : UInt64) :
    (Builtins.run 100 (clampState delay)).heap.object? 0 =
      some {properties := [data "accumulatedDelay" (.number
        (Number.minimum (Number.minimum Number.positiveInfinity delay)
          (Number.mul 4652007308841189376 4617315517961601024)))]} := by cbv

theorem actual_clamp_unchanged (delay : UInt64) (n : Nat)
    (value : NegativeScaledValue delay 54 n) :
    (Builtins.run 100 (clampState delay)).heap.object? 0 =
      (clampState delay).heap.object? 0 := by
  rw [actual_clamp_assignment,negative_scaled_min_infinity delay 54 n (by decide) value]
  have cap : Number.mul 4652007308841189376 4617315517961601024 = Number.ofNat 5000 := by decide +kernel
  rw [cap,negative_scaled_clamp delay 54 n (by decide) value]
  rfl

def timeoutStatement : Stmt := match LoopSyntax.LoopBody with
  | .block statements => statements[9]?.getD .empty
  | _ => .empty

def timeoutState : Machine := {
  heap := {
    objects := #[{properties := [data "prefs" (.object 1)]},
      {properties := [data "timeout" (.number Number.positiveZero)]}]
    environments := #[⟨.declarative [{name := "Game",value := .object 0}],none⟩]}
  context := ⟨0,0,.object 0,false⟩
  control := .statement timeoutStatement
  globalObject := 0}

theorem actual_default_timeout_skipped :
    run 30 timeoutState = {timeoutState with control := .completion (.normal none)} := by cbv

end CookieClicker.JavaScript.LoopSource

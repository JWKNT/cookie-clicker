import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptGodzamokSyntax
import CookieClicker.JavaScriptLumpSyntax
import CookieClicker.JavaScriptScaledArithmeticBridge

/-! Execute the intact Godzamok conditional selected from the pinned sell body.
The native Pantheon hasGod, main hasAura and main hasBuff callbacks are included.
For every multiplier and deadline bit pattern, the existing-buff path adds the
native cent once, retains the deadline, and preserves the twelve entry objects
except for multClick. Invocation allocations remain part of the native result.
The completed sale prefix, arbitrary heap placement, UI admission and callback
schedule are separate obligations; this module does not prove a whole sale. -/
namespace CookieClicker.JavaScript.GodzamokSource
set_option maxRecDepth 262144
set_option cbv.maxSteps 4000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048
private def key := JSString.ofString
private def data (name : String) (value : Value) : OwnProperty := ⟨key name,.data value true true true⟩
private def fn (parameters : List String) (body : Stmt) : JSObject :=
  { kind := .function ⟨none,parameters,(match body with | .block statements => statements | other => [other]),0,false,none⟩ }

def godzamokBranch : Stmt := match GodzamokSyntax.sellBody with
  | .block statements => statements[6]?.getD .empty
  | _ => .empty

theorem source_branch_test :
    (match godzamokBranch with | .ifThenElse test _ _ => some test | _ => none) =
    some (.logical .and (.identifier "success")
      (.member (.identifier "Game") (.identifier "hasGod") false)) := rfl

def buff (multiplier deadline : UInt64) : JSObject := {properties := [
  data "multClick" (.number multiplier),data "time" (.number deadline)]}

def state (multiplier deadline : UInt64) : Machine := {
  heap := {
    objects := #[
      {properties := [data "hasGod" (.object 1),data "hasBuff" (.object 2),data "buffs" (.object 3),data "hasAura" (.object 9),data "dragonAuras" (.object 10),
        data "dragonAura" (.number Number.positiveZero),data "dragonAura2" (.number Number.positiveZero)]},
      fn ["what"] LumpSyntax.hasGodBody,
      fn ["what"] GodzamokSyntax.hasBuffBody,
      {properties := [data "Devastation" (.object 4)]},
      buff multiplier deadline,
      {properties := [data "gods" (.object 6),data "slot" (.object 8)]},
      {properties := [data "ruin" (.object 7)]},
      {properties := [data "id" (.number 4611686018427387904)]},
      {kind := .array,properties := [data "0" (.number 4611686018427387904),
        data "1" (.number 13830554455654793216),data "2" (.number 13830554455654793216),
        data "length" (.number 4613937818241073152)]},
      fn ["what"] GodzamokSyntax.hasAuraBody,
      {properties := [data "0" (.object 11)]},
      {properties := [data "name" (.string (key "No aura"))]}]
    environments := #[⟨.declarative [
      {name := "Game",value := .object 0},{name := "M",value := .object 5},
      {name := "success",value := .number Number.one},{name := "sold",value := .number Number.one},
      {name := "godLvl",value := .undefined},{name := "old",value := .undefined}],none⟩]}
  context := ⟨0,0,.object 0,false⟩
  control := .statement godzamokBranch
  globalObject := 0}

def result (multiplier deadline : UInt64) := run 312 (state multiplier deadline)

private theorem zero_lt_three : Number.lessThan 0 4613937818241073152 = true := by decide +kernel
private theorem two_eq_two : Number.equal 4611686018427387904 4611686018427387904 = true := by decide +kernel
private theorem one_eq_one : Number.equal 4607182418800017408 4607182418800017408 = true := by decide +kernel
private theorem one_times_cent : Number.mul 4607182418800017408 4576918229304087675 = 4576918229304087675 := by decide +kernel
private theorem zero_add_one : Number.add 0 4607182418800017408 = 4607182418800017408 := by decide +kernel
attribute [local cbv_opaque] Number.add Number.mul Number.equal Number.lessThan Number.ofNat Number.ofScientific
attribute [local cbv_eval] zero_add_one one_times_cent zero_lt_three two_eq_two one_eq_one

theorem actual_existing_buff_branch (multiplier deadline : UInt64) :
    (result multiplier deadline).heap.object? 4 =
      some (buff (Number.add multiplier 4576918229304087675) deadline) := by
  cbv

theorem actual_existing_buff_branch_returns (multiplier deadline : UInt64) :
    status (result multiplier deadline) =
      .completion (.normal (some (.number (Number.add multiplier 4576918229304087675)))) := by
  cbv

theorem actual_existing_buff_frame (multiplier deadline : UInt64) :
    (result multiplier deadline).heap.objects.toList.take 12 =
      (state (Number.add multiplier 4576918229304087675) deadline).heap.objects.toList := by
  cbv

theorem source_cent_literal : (4576918229304087675 : UInt64) = Number.ofScientific 1 (-2) := by
  decide +kernel

/-- Native source branch arithmetic agrees with the proved scaled recurrence.
The sale prefix must still establish sold=1, success, and this entry layout. -/
theorem source_scaled_step (multiplier : UInt64) (n : Nat)
    (value : ScaledArithmeticBridge.ScaledValue multiplier 59 n) (bounded : n ≤ 2^106) :
    ScaledArithmeticBridge.ScaledNormal
      (Number.add multiplier 4576918229304087675) 59
      (CookieClicker.FullGame.GodzamokRounding.roundedInteger
        (n+CookieClicker.FullGame.BootstrapArithmetic.centNumerator)) := by
  rw [source_cent_literal,ScaledArithmeticBridge.cent_credit_encoding]
  exact ScaledArithmeticBridge.native_scaled_add_value _ _ _ _ (by decide) value
    (by decide) (by decide) (by decide) (by dsimp [CookieClicker.FullGame.BootstrapArithmetic.centNumerator]; omega)

end CookieClicker.JavaScript.GodzamokSource

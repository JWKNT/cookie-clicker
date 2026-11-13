import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptLumpSyntax

/-! Execution facts for the extracted native sugar callbacks.
The explicit helper layout below records the early route's absence of lump-time
upgrades and Dragon's Curve, with no order god. Relating that layout to the
initialized whole-game heap is a separate source invariant.
-/
namespace CookieClicker.JavaScript.LumpSource
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

private theorem checked_ok_of_option {α : Type} (r : Checked α) (a : α)
    (h : r.toOption = some a) : r = .ok a := by
  cases r <;> simp_all [Except.toOption]

private def key := JSString.ofString
private def data (name : String) (value : Value) : OwnProperty :=
  ⟨key name, .data value true true true⟩
private def constantFunction (value : Literal) : JSObject :=
  { kind := .function ⟨none,["what"],[.return (some (.literal value))],0,false,none⟩ }

def earlyTimeState (pantheon : Bool) : Machine := {
  heap := {
    objects := #[
      { properties := [data "Has" (.object 1), data "auraMult" (.object 2),
        data "hasGod" (if pantheon then .object 2 else .undefined),
        data "BuildingsOwned" (.number (Number.ofNat (if pantheon then 2 else 1))),
        data "lumpMatureAge" (.number Number.one), data "lumpRipeAge" (.number Number.one),
        data "lumpOverripeAge" (.number Number.one)] },
      constantFunction (.boolean false), constantFunction (.number Number.positiveZero),
      { kind := .function ⟨none,[],
        (match LumpSyntax.computeLumpTimesBody with | .block body => body | other => [other]),0,false,none⟩ }]
    environments := #[⟨.declarative [{ name := "Game", value := .object 0 }],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .invoke (.object 3) (.object 0) [] false
  globalObject := 0 }

def earlyTimeResult (pantheon : Bool) : Machine := run 403 (earlyTimeState pantheon)

theorem early_time_call_returns (pantheon : Bool) : status (earlyTimeResult pantheon) = .value .undefined := by
  cases pantheon <;> decide +kernel

theorem early_time_call_maturity (pantheon : Bool) :
    lookupProperty (earlyTimeResult pantheon).heap 0 (key "lumpMatureAge") =
      .ok (some (.data (.number (Number.ofNat 72000000)) true true true)) := by
  apply checked_ok_of_option
  cases pantheon <;> decide +kernel

theorem early_time_call_ripe (pantheon : Bool) :
    lookupProperty (earlyTimeResult pantheon).heap 0 (key "lumpRipeAge") =
      .ok (some (.data (.number (Number.ofNat 82800000)) true true true)) := by
  apply checked_ok_of_option
  cases pantheon <;> decide +kernel

theorem early_time_call_overripe (pantheon : Bool) :
    lookupProperty (earlyTimeResult pantheon).heap 0 (key "lumpOverripeAge") =
      .ok (some (.data (.number (Number.ofNat 86400000)) true true true)) := by
  apply checked_ok_of_option
  cases pantheon <;> decide +kernel


def eligibilityState (total mode earned reset : UInt64) : Machine := {
  heap := {
    objects := #[
      { properties := [data "lumpsTotal" (.number total), data "ascensionMode" (.number mode),
          data "cookiesEarned" (.number earned), data "cookiesReset" (.number reset)] },
      { kind := .function ⟨none,[],
        (match LumpSyntax.canLumpsBody with | .block body => body | other => [other]),0,false,none⟩ }]
    environments := #[⟨.declarative [{ name := "Game", value := .object 0 }],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .invoke (.object 1) (.object 0) [] false
  globalObject := 0 }

theorem native_billion_activates :
    status (run 150 (eligibilityState (Number.neg Number.one) Number.positiveZero
      (Number.ofNat 1000000000) Number.positiveZero)) = .value (.boolean true) := by
  decide +kernel

theorem native_below_billion_does_not_activate :
    status (run 150 (eligibilityState (Number.neg Number.one) Number.positiveZero
      (Number.ofNat 999999999) Number.positiveZero)) = .value (.boolean false) := by
  decide +kernel

theorem native_born_again_does_not_first_activate :
    status (run 150 (eligibilityState (Number.neg Number.one) Number.one
      (Number.ofNat 1000000000) Number.positiveZero)) = .value (.boolean false) := by
  decide +kernel

theorem native_activated_lumps_survive_mode_condition :
    status (run 150 (eligibilityState Number.positiveZero Number.one
      Number.positiveZero Number.positiveZero)) = .value (.boolean true) := by
  decide +kernel

/-- Stop at the actual next source call. No substitute UpdateWrinklers body is
provided or assumed. This proves the source prefix, not the callee's frame rule. -/
def noGrandmaState : Machine := {
  heap := {
    objects := #[
      { properties := [data "Has" (.object 1), data "Objects" (.object 2),
          data "elderWrath" (.number (Number.ofNat 3)), data "elderWrathOld" (.number Number.positiveZero),
          data "elderWrathD" (.number Number.positiveZero), data "UpdateWrinklers" (.object 5)] },
      constantFunction (.boolean false),
      { properties := [data "Grandma" (.object 3)] },
      { properties := [data "amount" (.number Number.positiveZero)] },
      { kind := .function ⟨none,[],
        (match LumpSyntax.UpdateGrandmapocalypseBody with | .block body => body | other => [other]),0,false,none⟩ },
      { kind := .builtin ⟨"Game","UpdateWrinklers"⟩ }]
    environments := #[⟨.declarative [{ name := "Game", value := .object 0 }],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .invoke (.object 4) (.object 0) [] false
  globalObject := 0 }

def noGrandmaPrefix := run 300 noGrandmaState

theorem no_grandma_native_prefix_stops_at_wrinklers :
    status noGrandmaPrefix = .unresolved (.builtin ⟨"Game","UpdateWrinklers"⟩ (.object 0) [] false) := by
  decide +kernel

theorem no_grandma_native_prefix_forces_wrath_zero :
    lookupProperty noGrandmaPrefix.heap 0 (key "elderWrath") =
      .ok (some (.data (.number Number.positiveZero) true true true)) := by
  apply checked_ok_of_option
  decide +kernel

/-- Extract the third test inside the native type-selection loop. -/
def meatyCondition : Expr :=
  match LumpSyntax.computeLumpTypeBody with
  | .block body => match (body[5]? : Option Stmt) with
    | some (.forLoop _ _ _ (.block branches)) => match (branches[2]? : Option Stmt) with
      | some (.ifThenElse test _ _) => test
      | _ => .literal .null
    | _ => .literal .null
  | _ => .literal .null

theorem actual_meaty_condition : meatyCondition =
    .binary .less (.call (.member (.identifier "Math") (.identifier "random") false) [])
      (.binary .multiply (.literal (.number 4591870180066957722))
        (.member (.identifier "Game") (.identifier "elderWrath") false)) := rfl

private theorem wrath_zero_threshold :
    Number.mul 4591870180066957722 Number.positiveZero = Number.positiveZero := by
  decide +kernel

/-- A range condition on actual unpacked IEEE output, not independence or a
claim that explicitly seeded outputs are fresh uniform draws. -/
def NonnegativeOutput (draw : UInt64) : Prop :=
  match (Number.model draw).unpack with
  | .zero _ | .finite .positive .. | .infinity .positive => True
  | _ => False

theorem nonnegative_not_below_zero (draw : UInt64) (valid : NonnegativeOutput draw) :
    Number.lessThan draw Number.positiveZero = false := by
  have zero : (Number.model Number.positiveZero).unpack = .zero .positive := by rfl
  unfold Number.lessThan Float.Model.lt
  rw [zero]
  cases h : (Number.model draw).unpack <;>
    simp_all [NonnegativeOutput, Float.Model.UnpackedFloat.lt, Float.Model.UnpackedFloat.compare]
  all_goals split at valid <;> simp_all

def meatyGuardState (draw : UInt64) : Machine := {
  heap := {
    objects := #[
      { properties := [data "elderWrath" (.number Number.positiveZero)] },
      { properties := [data "random" (.object 2)] },
      constantFunction (.number draw)]
    environments := #[⟨.declarative [
      { name := "Game", value := .object 0 }, { name := "Math", value := .object 1 }],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .expression meatyCondition
  globalObject := 0 }

section
attribute [local cbv_opaque] Number.lessThan Number.mul
attribute [local cbv_eval] wrath_zero_threshold

theorem native_meaty_guard_value (draw : UInt64) :
    status (run 80 (meatyGuardState draw)) =
      .value (.boolean (Number.lessThan draw Number.positiveZero)) := by
  cbv
end

theorem native_meaty_guard_is_false (draw : UInt64) (valid : NonnegativeOutput draw) :
    status (run 80 (meatyGuardState draw)) = .value (.boolean false) := by
  rw [native_meaty_guard_value, nonnegative_not_below_zero draw valid]

/-- Inspect the native conditional chain; this is source data, not execution. -/
def conditionalBranches : Stmt → List Stmt
  | .ifThenElse _ yes (some no) => yes :: conditionalBranches no
  | .ifThenElse _ yes none => [yes]
  | _ => []

def harvestBranches : List Stmt :=
  match LumpSyntax.harvestLumpsBody with
  | .block body => conditionalBranches (body[3]?.getD (.block []))
  | _ => []

def literalMultiplierOptions (statement : Stmt) : List UInt64 :=
  let first : Stmt := match statement with
    | .block body => body[0]?.getD (Stmt.block [])
    | other => other
  match first with
  | .expression (.assignment .multiply (.identifier "total") (.literal (.number bits))) => [bits]
  | .expression (.assignment .multiply (.identifier "total")
      (.call (.identifier "choose") [.array choices])) =>
    choices.filterMap fun (choice : Option Expr) => match choice with
      | some (.literal (.number bits)) => some bits
      | _ => none
  | _ => []

def harvestOptions := harvestBranches.map literalMultiplierOptions

theorem actual_harvest_options : harvestOptions =
    [[2],[1,2],[2,3,4,5,6,7],[0,0,1,2,2],[1,2,3]].map
      (fun values => values.map Number.ofNat) := by
  decide +kernel

/-- Normal lumps retain amount1. The other four entries are selected by the
source conditional chain; entry3 is the only one that can pay zero. -/
def nonmeatyOptions : List UInt64 := [Number.one] ++
  ([0,1,2,4].flatMap fun index => harvestOptions[index]?.getD [])

theorem source_nonmeaty_options_are_one_through_seven :
    nonmeatyOptions.all (fun value => (List.range 7).any
      (fun index => value == Number.ofNat (index + 1))) = true := by
  decide +kernel

theorem source_meaty_options_contain_zero :
    (harvestOptions[3]?.getD []).contains Number.positiveZero = true := by
  decide +kernel

end CookieClicker.JavaScript.LumpSource

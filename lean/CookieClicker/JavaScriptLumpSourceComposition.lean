import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptLumpSyntax

/- Execute the intact pinned computeLumpTimes callback and its native Has,
auraMult and Pantheon hasGod helpers. The three explicit early layouts have
no time-changing upgrade, no dragon aura, and either no Pantheon or Ruin.
The third layout also exercises the complete native Rigidel lookup loop.
A full initialized-heap invariant and a frame theorem remain separate. -/

namespace CookieClicker.JavaScript.LumpSourceComposition
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048
private def key := JSString.ofString
private def data (name : String) (value : Value) : OwnProperty := ⟨key name,.data value true true true⟩
private def fn (parameters : List String) (body : Stmt) : JSObject :=
  { kind := .function ⟨none,parameters,(match body with | .block statements => statements | other => [other]),0,false,none⟩ }
private def notBought : JSObject := { properties := [data "bought" (.number Number.positiveZero)] }
private theorem checked_ok_of_option {α : Type} (r : Checked α) (a : α)
    (h : r.toOption = some a) : r = .ok a := by
  cases r <;> simp_all [Except.toOption]

def state (setup : Fin 3) : Machine := {
  heap := {
    objects := #[
      { properties := [data "Has" (.object 1), data "auraMult" (.object 2),
        data "hasGod" (if setup.val = 0 then .undefined else .object 4),
        data "BuildingsOwned" (.number (Number.ofNat (if setup.val = 0 then 1 else if setup.val = 1 then 2 else 1000))),
        data "lumpMatureAge" (.number Number.one), data "lumpRipeAge" (.number Number.one),
        data "lumpOverripeAge" (.number Number.one), data "Upgrades" (.object 5),
        data "ascensionMode" (.number Number.positiveZero), data "dragonAuras" (.object 11),
        data "dragonAura" (.number Number.positiveZero), data "dragonAura2" (.number Number.positiveZero)] },
      fn ["what"] LumpSyntax.HasBody,
      fn ["what"] LumpSyntax.auraMultBody,
      fn [] LumpSyntax.computeLumpTimesBody,
      fn ["what"] LumpSyntax.hasGodBody,
      { properties := [data "Stevia Caelestis" (.object 6), data "Diabetica Daemonicus" (.object 7),
          data "Ichor syrup" (.object 8), data "Sugar aging process" (.object 9),
          data "Glucose-charged air" (.object 10)] },
      notBought,notBought,notBought,notBought,notBought,
      { properties := [data "0" (.object 12)] },
      { properties := [data "name" (.string (key "No aura"))] },
      { properties := [data "gods" (.object 14),data "slot" (.object 16)] },
      { properties := [data "order" (.object 15)] },
      { properties := [data "id" (.number (Number.ofNat 10))] },
      { kind := .array, properties := [data "0" (.number (Number.ofNat 2)),
          data "1" (.number (Number.neg Number.one)), data "2" (.number (Number.neg Number.one)),
          data "length" (.number (Number.ofNat 3))] }]
    environments := #[⟨.declarative [{name := "Game",value := .object 0},{name := "M",value := .object 13}],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  control := .invoke (.object 3) (.object 0) [] false
  globalObject := 0 }

def result (setup : Fin 3) := run 2000 (state setup)

private def hasTimes (setup : Fin 3) : Bool :=
  (status (result setup) == .value .undefined) &&
  ((lookupProperty (result setup).heap 0 (key "lumpMatureAge")).toOption ==
    some (some (.data (.number (Number.ofNat 72000000)) true true true))) &&
  ((lookupProperty (result setup).heap 0 (key "lumpRipeAge")).toOption ==
    some (some (.data (.number (Number.ofNat 82800000)) true true true))) &&
  ((lookupProperty (result setup).heap 0 (key "lumpOverripeAge")).toOption ==
    some (some (.data (.number (Number.ofNat 86400000)) true true true)))

theorem native_helpers_and_timing : ∀ setup : Fin 3, hasTimes setup = true := by
  decide +kernel

theorem source_times (setup : Fin 3) :
    status (result setup) = .value .undefined ∧
    lookupProperty (result setup).heap 0 (key "lumpMatureAge") =
      .ok (some (.data (.number (Number.ofNat 72000000)) true true true)) ∧
    lookupProperty (result setup).heap 0 (key "lumpRipeAge") =
      .ok (some (.data (.number (Number.ofNat 82800000)) true true true)) ∧
    lookupProperty (result setup).heap 0 (key "lumpOverripeAge") =
      .ok (some (.data (.number (Number.ofNat 86400000)) true true true)) := by
  have h := native_helpers_and_timing setup
  simp only [hasTimes, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, checked_ok_of_option _ _ h.1.1.2,
    checked_ok_of_option _ _ h.1.2, checked_ok_of_option _ _ h.2⟩

end CookieClicker.JavaScript.LumpSourceComposition

import CookieClicker.RngPhase

/-! Generated from the pinned source by generate_rng_phase.mjs.
The extractor and host-leaf classifications are separate trust obligations.
Unknown callees remain arbitrary phase effects in the conservative programs.
No theorem below asserts whole JavaScript semantics or exception safety.
-/
namespace CookieClicker.FullGame.NativeRngPhase
open RngPhase

def helper0 : Code := .ret

theorem helper0_preserves : analyze (.invoke helper0) = ⟨identity, zero⟩ := by decide +kernel

def helper1 : Code := .ret

theorem helper1_preserves : analyze (.invoke helper1) = ⟨identity, zero⟩ := by decide +kernel

def helper2 : Code := (.seq (.loop (.effect identity)) .ret)

theorem helper2_preserves : analyze (.invoke helper2) = ⟨identity, zero⟩ := by decide +kernel

def helper3 : Code := (.seq (.branch .ret (.effect identity)) .ret)

theorem helper3_preserves : analyze (.invoke helper3) = ⟨identity, zero⟩ := by decide +kernel

def helper4 : Code := .ret

theorem helper4_preserves : analyze (.invoke helper4) = ⟨identity, zero⟩ := by decide +kernel

def helper5 : Code := .ret

theorem helper5_preserves : analyze (.invoke helper5) = ⟨identity, zero⟩ := by decide +kernel

def helper6 : Code := (.seq (.seq (.seq (.seq (.invoke helper3) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) .ret)

theorem helper6_preserves : analyze (.invoke helper6) = ⟨identity, zero⟩ := by decide +kernel

def localCallback0 : Code := (.seq (.seq (.seq (.seq (.seq (.effect seed) (.invoke helper5)) (.invoke helper1)) (.loop (.invoke helper3))) (.invoke helper0)) (.effect reset))

theorem localCallback0_checked : restoresFree localCallback0 = true := by decide +kernel

theorem localCallback0_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback0 free exit phase) : phase = free :=
  restores_free_sound localCallback0 localCallback0_checked exit phase execution

def conservativeCallback0 : Code := (.seq (.seq (.seq (.seq (.seq (.effect seed) (.invoke helper5)) (.invoke helper1)) (.loop (.invoke helper3))) (.invoke helper0)) (.effect reset))

theorem conservativeCallback0_checked : restoresFree conservativeCallback0 = true := by decide +kernel

theorem conservativeCallback0_restores (exit : Exit) (phase : Phase)
    (execution : Executes conservativeCallback0 free exit phase) : phase = free :=
  restores_free_sound conservativeCallback0 conservativeCallback0_checked exit phase execution

def localCallback1 : Code := (.seq (.seq (.seq (.seq (.seq (.branch (.seq (.branch (.seq (.seq (.seq (.seq (.branch (.invoke helper0) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.seq (.loop (.branch (.invoke helper0) (.effect identity))) (.branch (.seq (.seq (.seq (.branch (.invoke helper0) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.effect identity))) (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.branch (.invoke helper0) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.seq (.invoke helper0) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)))) (.invoke helper0)) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0))) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))))) (.effect identity)) (.branch (.branch (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)) (.effect identity)) (.seq (.seq (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.invoke helper3) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.invoke helper3)) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0)) (.invoke helper0)) (.invoke helper0)) (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0))) (.invoke helper0)) (.invoke helper0)) (.invoke helper0)) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0))) (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)) (.invoke helper0))) (.seq (.seq (.seq (.invoke helper0) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0))) (.seq (.seq (.seq (.seq (.invoke helper0) (.seq (.invoke helper0) (.invoke helper0))) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0))) (.effect identity))))) (.effect identity)) (.branch (.seq (.seq (.branch (.invoke helper0) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.effect identity))) (.branch (.seq (.seq (.branch (.seq (.seq (.seq (.invoke helper0) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0)) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.branch (.invoke helper0) (.effect identity)) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.branch (.invoke helper0) (.effect identity))) (.effect identity))) (.effect identity))) (.loop (.effect identity))) (.seq (.branch (.effect identity) (.invoke helper3)) (.branch (.seq (.loop (.invoke helper4)) (.branch (.seq (.invoke helper0) (.branch (.effect identity) (.branch (.seq (.effect seed) (.effect reset)) (.branch (.effect identity) (.invoke helper0))))) (.effect identity))) (.effect identity)))) (.invoke helper0))

theorem localCallback1_checked : restoresFree localCallback1 = true := by decide +kernel

theorem localCallback1_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback1 free exit phase) : phase = free :=
  restores_free_sound localCallback1 localCallback1_checked exit phase execution

def conservativeCallback1 : Code := (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.effect unknown) (.effect unknown)) (.seq (.effect unknown) (.effect unknown))) (.branch (.seq (.branch (.seq (.seq (.seq (.seq (.seq (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity)) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.seq (.branch (.effect identity) (.effect unknown)) (.branch (.effect unknown) (.effect identity)))) (.seq (.branch (.effect identity) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity)))) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.branch (.seq (.loop (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.seq (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity)) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.effect identity))) (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity)) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.seq (.invoke helper0) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)))) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0))) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))))) (.effect identity)) (.branch (.branch (.seq (.seq (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown))) (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown))) (.effect identity)) (.seq (.seq (.seq (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.effect unknown) (.branch (.effect unknown) (.effect identity))) (.seq (.effect unknown) (.branch (.effect unknown) (.effect identity)))) (.seq (.effect unknown) (.branch (.effect unknown) (.effect identity)))) (.seq (.effect unknown) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.invoke helper3) (.branch (.effect unknown) (.effect identity)))) (.seq (.effect unknown) (.branch (.effect unknown) (.effect identity)))) (.effect identity)) (.seq (.effect unknown) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity)))) (.branch (.effect unknown) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0)) (.invoke helper0)) (.invoke helper0)) (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0))) (.invoke helper0)) (.invoke helper0)) (.invoke helper0)) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0))) (.seq (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0)) (.invoke helper0))) (.seq (.seq (.seq (.invoke helper0) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0))) (.seq (.seq (.seq (.seq (.seq (.invoke helper0) (.seq (.invoke helper0) (.invoke helper0))) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.seq (.effect unknown) (.effect unknown))) (.invoke helper0))) (.effect unknown)) (.effect identity))))) (.effect identity))) (.branch (.branch (.seq (.effect unknown) (.effect unknown)) (.branch (.seq (.effect unknown) (.effect unknown)) (.branch (.seq (.effect unknown) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.effect identity)))))))))))))))) (.effect identity))) (.branch (.seq (.seq (.branch (.seq (.branch (.invoke helper0) (.seq (.effect unknown) (.invoke helper0))) (.effect unknown)) (.effect identity)) (.branch (.seq (.branch (.invoke helper0) (.seq (.effect unknown) (.invoke helper0))) (.effect unknown)) (.effect identity))) (.branch (.seq (.branch (.invoke helper0) (.seq (.effect unknown) (.invoke helper0))) (.effect unknown)) (.effect identity))) (.effect identity))) (.branch (.seq (.seq (.seq (.branch (.seq (.seq (.seq (.seq (.invoke helper0) (.seq (.invoke helper0) (.invoke helper0))) (.invoke helper0)) (.invoke helper0)) (.effect unknown)) (.effect identity)) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity)) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.invoke helper0) (.effect unknown)) (.effect identity))) (.branch (.seq (.seq (.effect unknown) (.invoke helper0)) (.effect unknown)) (.effect identity))) (.effect identity))) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.branch (.effect unknown) (.effect identity)))))))))))))) (.effect identity))) (.loop (.seq (.effect unknown) (.branch (.effect unknown) (.effect identity))))) (.seq (.seq (.branch (.effect identity) (.invoke helper3)) (.branch (.effect identity) (.effect unknown))) (.branch (.seq (.loop (.invoke helper4)) (.branch (.seq (.invoke helper0) (.branch (.effect unknown) (.branch (.seq (.seq (.effect seed) (.effect unknown)) (.effect reset)) (.branch (.seq (.seq (.seq (.effect unknown) (.effect unknown)) (.seq (.effect unknown) (.effect unknown))) (.effect unknown)) (.seq (.invoke helper0) (.effect unknown)))))) (.effect identity))) (.effect identity)))) (.branch (.branch (.effect identity) (.effect unknown)) (.effect identity))) (.invoke helper0)) (.effect unknown)) (.effect unknown))

def localCallback2 : Code := (.seq (.seq (.seq (.seq (.branch .ret (.effect identity)) (.branch (.seq (.loop (.effect seed)) (.loop (.effect identity))) (.effect identity))) (.branch (.branch (.loop (.effect identity)) (.branch (.loop (.effect identity)) (.effect identity))) (.effect identity))) (.effect reset)) (.loop (.branch (.seq (.seq (.seq (.effect seed) (.invoke helper0)) (.branch (.invoke helper0) (.effect identity))) (.effect reset)) (.effect identity))))

theorem localCallback2_checked : restoresFree localCallback2 = true := by decide +kernel

theorem localCallback2_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback2 free exit phase) : phase = free :=
  restores_free_sound localCallback2 localCallback2_checked exit phase execution

def conservativeCallback2 : Code := (.seq (.seq (.seq (.seq (.seq (.branch .ret (.effect identity)) (.branch (.seq (.effect unknown) (.effect unknown)) (.effect unknown))) (.branch (.seq (.seq (.loop (.seq (.seq (.effect seed) (.branch (.effect identity) (.effect unknown))) (.effect unknown))) (.loop (.seq (.effect unknown) (.effect unknown)))) (.effect unknown)) (.effect identity))) (.branch (.branch (.seq (.loop (.branch (.effect unknown) (.effect identity))) (.branch (.seq (.seq (.seq (.effect unknown) (.seq (.effect unknown) (.effect unknown))) (.effect unknown)) (.branch (.seq (.effect unknown) (.effect unknown)) (.effect identity))) (.effect identity))) (.branch (.loop (.effect identity)) (.effect identity))) (.effect identity))) (.effect reset)) (.loop (.seq (.branch (.effect identity) (.effect unknown)) (.branch (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.effect seed) (.invoke helper0)) (.branch (.invoke helper0) (.effect identity))) (.seq (.effect unknown) (.effect unknown))) (.effect unknown)) (.effect reset)) (.effect unknown)) (.effect unknown)) (.effect unknown)) (.effect unknown)) (.effect unknown)) (.effect unknown)) (.effect unknown)) (.effect unknown)))))

def unrestrictedTooltip : Code := (.seq (.seq (.seq (.seq (.branch .ret (.effect identity)) (.branch (.seq (.loop (.effect seed)) (.loop (.effect identity))) (.effect identity))) (.branch (.branch (.loop (.effect identity)) (.branch (.loop (.effect identity)) (.effect identity))) (.effect identity))) (.effect reset)) (.loop (.seq (.branch (.seq (.seq (.seq (.effect seed) (.invoke helper0)) (.branch (.invoke helper0) (.effect identity))) (.effect reset)) (.effect identity)) (.branch (.seq (.seq (.effect seed) (.effect seed)) (.branch (.seq (.branch (.invoke helper0) (.effect identity)) (.seq (.seq (.invoke helper0) (.invoke helper0)) (.invoke helper0))) (.effect identity))) (.effect identity)))))

theorem unrestricted_tooltip_not_certified : restoresFree unrestrictedTooltip = false := by decide +kernel

def localCallback3 : Code := (.seq (.effect seed) (.seq (.effect reset) .ret))

theorem localCallback3_checked : restoresFree localCallback3 = true := by decide +kernel

theorem localCallback3_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback3 free exit phase) : phase = free :=
  restores_free_sound localCallback3 localCallback3_checked exit phase execution

def conservativeCallback3 : Code := (.seq (.effect seed) (.seq (.effect reset) .ret))

theorem conservativeCallback3_checked : restoresFree conservativeCallback3 = true := by decide +kernel

theorem conservativeCallback3_restores (exit : Exit) (phase : Phase)
    (execution : Executes conservativeCallback3 free exit phase) : phase = free :=
  restores_free_sound conservativeCallback3 conservativeCallback3_checked exit phase execution

def localCallback4 : Code := (.seq (.seq (.seq (.invoke helper3) (.branch .ret (.effect identity))) (.seq (.seq (.invoke helper3) (.branch (.effect identity) (.invoke helper3))) (.branch .ret (.effect identity)))) (.seq (.invoke helper3) (.branch (.seq (.seq (.branch (.effect seed) (.branch (.effect seed) (.effect identity))) (.seq (.invoke helper6) (.branch (.seq (.effect reset) .ret) (.effect identity)))) (.effect reset)) (.effect identity))))

theorem localCallback4_checked : restoresFree localCallback4 = true := by decide +kernel

theorem localCallback4_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback4 free exit phase) : phase = free :=
  restores_free_sound localCallback4 localCallback4_checked exit phase execution

def conservativeCallback4 : Code := (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.invoke helper3) (.branch .ret (.effect identity))) (.seq (.seq (.invoke helper3) (.branch (.effect identity) (.invoke helper3))) (.branch .ret (.effect identity)))) (.seq (.invoke helper3) (.branch (.seq (.seq (.branch (.effect seed) (.branch (.effect seed) (.effect identity))) (.seq (.invoke helper6) (.branch (.seq (.seq (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.effect reset)) .ret) (.effect identity)))) (.effect reset)) (.effect identity)))) (.effect unknown)) (.effect unknown)) (.seq (.effect unknown) (.effect unknown))) (.effect unknown))

def localCallback5 : Code := (.seq (.seq (.seq (.effect seed) (.invoke helper0)) (.effect reset)) .ret)

theorem localCallback5_checked : restoresFree localCallback5 = true := by decide +kernel

theorem localCallback5_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback5 free exit phase) : phase = free :=
  restores_free_sound localCallback5 localCallback5_checked exit phase execution

def conservativeCallback5 : Code := (.seq (.seq (.seq (.effect seed) (.invoke helper0)) (.effect reset)) .ret)

theorem conservativeCallback5_checked : restoresFree conservativeCallback5 = true := by decide +kernel

theorem conservativeCallback5_restores (exit : Exit) (phase : Phase)
    (execution : Executes conservativeCallback5 free exit phase) : phase = free :=
  restores_free_sound conservativeCallback5 conservativeCallback5_checked exit phase execution

def localCallback6 : Code := (.seq (.branch (.effect identity) (.invoke helper3)) (.branch (.branch (.seq (.seq (.seq (.effect seed) (.invoke helper2)) (.seq (.invoke helper3) (.branch (.effect identity) (.invoke helper4)))) (.effect reset)) (.effect identity)) (.effect identity)))

theorem localCallback6_checked : restoresFree localCallback6 = true := by decide +kernel

theorem localCallback6_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback6 free exit phase) : phase = free :=
  restores_free_sound localCallback6 localCallback6_checked exit phase execution

def conservativeCallback6 : Code := (.seq (.seq (.branch (.effect identity) (.invoke helper3)) (.branch (.effect identity) (.effect unknown))) (.branch (.seq (.seq (.seq (.seq (.seq (.effect unknown) (.effect unknown)) (.effect unknown)) (.branch (.effect unknown) (.effect identity))) (.branch (.effect unknown) (.effect identity))) (.branch (.seq (.seq (.seq (.seq (.effect seed) (.invoke helper2)) (.effect unknown)) (.seq (.seq (.invoke helper3) (.branch (.effect identity) (.invoke helper4))) (.branch (.seq (.effect unknown) (.seq (.effect unknown) (.effect unknown))) (.effect identity)))) (.effect reset)) (.effect identity))) (.effect identity)))

def localCallback7 : Code := (.seq (.seq (.seq (.seq (.branch .ret (.effect identity)) (.effect seed)) (.effect reset)) (.branch .ret (.effect identity))) .ret)

theorem localCallback7_checked : restoresFree localCallback7 = true := by decide +kernel

theorem localCallback7_restores (exit : Exit) (phase : Phase)
    (execution : Executes localCallback7 free exit phase) : phase = free :=
  restores_free_sound localCallback7 localCallback7_checked exit phase execution

def conservativeCallback7 : Code := (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.branch (.effect identity) (.effect unknown)) (.branch .ret (.effect identity))) (.effect unknown)) (.effect seed)) (.effect unknown)) (.effect reset)) (.branch (.seq (.seq (.seq (.seq (.branch (.seq (.seq (.branch (.effect unknown) (.effect identity)) (.branch (.effect unknown) (.effect identity))) (.branch (.effect unknown) (.effect identity))) (.effect identity)) (.seq (.effect unknown) (.effect unknown))) (.effect unknown)) (.effect unknown)) .ret) (.effect identity))) (.effect unknown)) .ret)

end CookieClicker.FullGame.NativeRngPhase

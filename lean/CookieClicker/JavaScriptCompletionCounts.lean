import CookieClicker.JavaScriptCompletion

/-! Completion thresholds apply to every represented nonnegative finite integer.
Loss of unit-increment precision does not make a native threshold unavailable. -/
namespace CookieClicker.JavaScript.Completion
set_option exponentiation.threshold 4096
set_option maxRecDepth 16384

theorem nativeCount_exact (bits : UInt64) (label : String)
    (finite : Number.isFinite bits = true)
    (nonnegative : 0 ≤ Number.truncateInt bits)
    (integral : Number.equal bits (Number.ofInt (Number.truncateInt bits)) = true) :
    nativeCount (.number bits) label = .ok (Number.truncateInt bits).toNat := by
  simp [nativeCount,finite,nonnegative,integral,pure,Except.pure]

theorem nativeCount_two_pow_53 (label : String) :
    nativeCount (.number (Number.ofNat (2^53))) label = .ok (2^53) := by
  rw [nativeCount_exact _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem nativeCount_two_pow_1000 (label : String) :
    nativeCount (.number (Number.ofNat (2^1000))) label = .ok (2^1000) := by
  rw [nativeCount_exact _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem nativeCount_largest_finite (label : String) :
    nativeCount (.number 9218868437227405311) label = .ok (2^1024 - 2^971) := by
  rw [nativeCount_exact _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem nativeCount_negative_zero (label : String) :
    nativeCount (.number Number.negativeZero) label = .ok 0 := by
  rw [nativeCount_exact _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

end CookieClicker.JavaScript.Completion

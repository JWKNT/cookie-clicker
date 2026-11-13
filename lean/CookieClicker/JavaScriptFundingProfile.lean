import CookieClicker.JavaScriptFundingProgress
namespace CookieClicker.JavaScript.FundingEpisode
open Float.Model Float.Model.UnpackedFloat ScaledArithmeticBridge
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Scalar eight-building sum, with Temple level1's actual native factor.
The full CalculateGains descriptor/callback frame remains a separate theorem. -/
def profileCps : UInt64 :=
  ([Number.ofScientific 1 (-1),Number.one,Number.ofNat 8,Number.ofNat 47,
    Number.ofNat 260,Number.ofNat 1400,
    Number.mul (Number.ofNat 7800) (Number.add Number.one (Number.ofScientific 1 (-2))),
    Number.ofNat 44000] : List UInt64).foldl Number.add Number.positiveZero

def profileBase : UInt64 :=
  Number.add Number.one (Number.mul profileCps (Number.ofScientific 1 (-2)))

theorem native_profile_base : profileBase=
    (Float.Model.pack (.finite .positive 4722982983437386 (-43) (by decide))).toBits := by
  decide +kernel

theorem profile_mantissa_bounds :
    2^52≤4722982983437386 ∧ 4722982983437386≤576*2^43 := by decide +kernel

/-- The concrete scalar profile discharges the native credit premises. -/
theorem concrete_episode_gain (bank : UInt64) (n N : Nat)
    (bankValue : ScaledNormal bank 59 n) (countLower : 2^22≤N) (countUpper : N≤2^49)
    (funded : 256*N*S≤n) (bankUpper : n<2^118) :
    ∃ r, ScaledNormal (episode profileBase N bank) 59 r ∧
      n+168*N*S≤r ∧ r≤n+4528*N*S :=
  native_episode_gain bank profileBase n 4722982983437386 N bankValue
    profile_mantissa_bounds.1 profile_mantissa_bounds.2 native_profile_base
    countLower countUpper funded bankUpper

end CookieClicker.JavaScript.FundingEpisode

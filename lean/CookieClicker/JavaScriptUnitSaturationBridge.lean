import CookieClicker.JavaScriptScaledArithmeticBridge
import CookieClicker.JavaScriptRandomSmallChoiceBridge

/-! Native binary64 saturation for repeated diamond Godzamok increments from
sales of exactly 100 buildings. The retained arithmetic has a finite exact
prefix to 2^53. The complete sale/rebuy, funding and input invariants remain
separate requirements. -/
namespace CookieClicker.JavaScript.UnitSaturationBridge
open Float.Model Float.Model.UnpackedFloat
open ScaledArithmeticBridge DyadicArithmeticBridge
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem hundred_times_cent :
    Number.mul (Number.ofNat 100) (Number.ofScientific 1 (-2)) = Number.one := by
  decide +kernel

theorem unit_encoding : incrementBits (2^52) 52 (by decide) = Number.one := by
  decide +kernel

theorem initial_scaled : ScaledNormal Number.one 52 (2^52) := by
  exact ⟨2^52,-52,by decide,by decide,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel⟩

theorem numerator_iterations (k : Nat) :
    numeratorIterations (2^52) (2^52) k = unitIterations k * 2^52 := by
  induction k with
  | zero => simp [numeratorIterations,unitIterations]
  | succ k ih =>
    simp only [numeratorIterations,ih]
    rw [show unitIterations k * 2^52 + 2^52 = (unitIterations k+1)*2^52 by omega]
    rw [RandomSmallChoiceBridge.rounded_scale _ 52 (by omega)]
    rfl

theorem native_unit_scaled (k : Nat) :
    ScaledValue (nativeIterations Number.one Number.one k) 52
      (min (k+1) unitCap * 2^52) := by
  have value := native_iterations_scaled Number.one (2^52) (2^52) 52 k (by decide)
    (Or.inr initial_scaled) (by decide) (by decide) (by decide) (by decide)
  rw [unit_encoding,numerator_iterations,unit_iterations_exact] at value
  exact value

theorem native_unit_value (k : Nat) :
    let bits := nativeIterations Number.one Number.one k
    Number.isFinite bits = true ∧ Number.signBit bits = false ∧
      (Number.magnitudeFraction bits).1 = min (k+1) unitCap * (Number.magnitudeFraction bits).2 := by
  obtain ⟨finite,sign,value⟩ := scaled_cross_product _ 52 _ (by decide) (native_unit_scaled k)
  refine ⟨finite,sign,?_⟩
  have rearrange : ∀ n d : Nat, (n*2^52)*d = (n*d)*2^52 := by
    intro n d
    ac_rfl
  rw [rearrange] at value
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2^52) value

theorem cap_bits (bits : UInt64) (value : ScaledValue bits 52 (2^105)) :
    bits = Number.ofNat (2^53) := by
  rcases value with ⟨_,zero⟩ | normal
  · omega
  · obtain ⟨m,e,positive,lower,upper,scaleLower,expUpper,shape,represented⟩ := normal
    change m*2^(e+52).toNat = 2^105 at represented
    change (-52:Int) ≤ e at scaleLower
    have logM : m.log2 = 52 := (Nat.log2_eq_iff (by omega : m ≠ 0)).mpr ⟨lower,upper⟩
    have logEquality := congrArg Nat.log2 represented
    rw [log2_scaled m (e+52).toNat (by omega),logM] at logEquality
    have logCap : (2^105:Nat).log2 = 105 := by decide +kernel
    rw [logCap] at logEquality
    have gap : (e+52).toNat = 53 := by omega
    have exp : e = 1 := by omega
    rw [gap] at represented
    have mantissa : m = 2^52 := by omega
    subst m; subst e
    rw [shape]
    change (Float.Model.pack (.finite .positive (2^52) 1 (by decide))).toBits = Number.ofNat (2^53)
    decide +kernel

theorem native_unit_cap_reached :
    nativeIterations Number.one Number.one (2^53-1) = Number.ofNat (2^53) := by
  apply cap_bits
  have value := native_unit_scaled (2^53-1)
  have arithmetic : min (2^53-1+1) unitCap * 2^52 = 2^105 := by decide +kernel
  rw [arithmetic] at value
  exact value

theorem native_hundred_sale_cap_reached :
    nativeIterations Number.one
      (Number.mul (Number.ofNat 100) (Number.ofScientific 1 (-2))) (2^53-1) =
      Number.ofNat (2^53) := by
  rw [hundred_times_cent]
  exact native_unit_cap_reached

theorem native_cap_fixed :
    Number.add (Number.ofNat (2^53))
      (Number.mul (Number.ofNat 100) (Number.ofScientific 1 (-2))) = Number.ofNat (2^53) := by
  decide +kernel

end CookieClicker.JavaScript.UnitSaturationBridge

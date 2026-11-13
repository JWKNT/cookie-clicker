import CookieClicker.JavaScriptCssColor
import Init.Data.Float.Model.Float32

/-! The CSSOM alpha-byte choice uses binary32 arithmetic in Chromium87.
This checks its full 256-value domain against the integer choice used by the
color serializer. It proves this arithmetic identity, not parser or renderer
refinement. There are no native floating-point evaluation oracles. -/
namespace CookieClicker.JavaScript.CssColor

private def roundPositive32 (value : Float32.Model) : Nat :=
  match value.unpack with
  | .finite .positive mantissa exponent _ =>
    NumberString.roundRatio (mantissa*2^exponent.toNat) (2^(-exponent).toNat)
  | _ => 0

def alphaChoiceFloat32 (alphaByte : Nat) : Nat × Nat :=
  let hundred := roundPositive32 ((Float32.Model.ofNat (alphaByte*100)).div (Float32.Model.ofNat 255))
  let rounded := (Float32.Model.ofNat hundred).div (Float32.Model.ofNat 100)
  if roundPositive32 (rounded.mul (Float32.Model.ofNat 255)) == alphaByte then
    (hundred,2)
  else
    (roundPositive32 ((Float32.Model.ofNat (alphaByte*1000)).div (Float32.Model.ofNat 255)),3)

def alphaChoiceInteger (alphaByte : Nat) : Nat × Nat :=
  let hundred := NumberString.roundRatio (alphaByte*100) 255
  if NumberString.roundRatio (hundred*255) 100 == alphaByte then (hundred,2)
  else (NumberString.roundRatio (alphaByte*1000) 255,3)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem alpha_choice_domain_certificate :
    (List.range 256).all (fun value => alphaChoiceFloat32 value == alphaChoiceInteger value) = true := by
  decide +kernel

theorem alpha_choice_exact (value : Nat) (bound : value < 256) :
    alphaChoiceFloat32 value = alphaChoiceInteger value := by
  have checked := List.all_eq_true.mp alpha_choice_domain_certificate value (List.mem_range.mpr bound)
  simpa using checked

def formatAlphaChoice (choice : Nat × Nat) : String :=
  let (coefficient,exponent) := NumberString.stripZeros 6 choice.1 (-(choice.2 : Int))
  if choice.1 == 0 then "0" else NumberString.formatDecimal coefficient exponent

theorem css_alpha_uses_integer_choice (value : UInt8) :
    cssAlpha value = formatAlphaChoice (alphaChoiceInteger value.toNat) := by
  simp only [cssAlpha,alphaChoiceInteger]
  split <;> rfl

theorem css_alpha_float32_choice (value : UInt8) :
    cssAlpha value = formatAlphaChoice (alphaChoiceFloat32 value.toNat) := by
  rw [alpha_choice_exact value.toNat value.toNat_lt]
  exact css_alpha_uses_integer_choice value

end CookieClicker.JavaScript.CssColor

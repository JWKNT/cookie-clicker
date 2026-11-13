import CookieClicker.JavaScriptSeasonNumericEpact
namespace CookieClicker.JavaScript.SeasonNumeric
open NaturalSeasons
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

/-- Only the 21 negative-offset pairs are checked here. All unbounded year and
quotient arithmetic is handled by the universal native arithmetic lemmas. -/
theorem negative_tail_cases : ∀ (i j : Fin 7), i.val<j.val →
    Number.add (Number.sub (Number.ofNat i.val) (Number.ofNat j.val)) (Number.ofNat 40)=Number.ofNat (i.val+40-j.val) ∧
    Number.add (Number.sub (Number.ofNat i.val) (Number.ofNat j.val)) (Number.ofNat 28)=Number.ofNat (i.val+28-j.val) := by
  decide +kernel

theorem native_offset_add (i j k : Int) (ib : 0≤i ∧ i≤28) (jb : 0≤j ∧ j≤6)
    (constant : k=28 ∨ k=40) :
    Number.add (Number.sub (enc i) (enc j)) (enc k)=enc (i-j+k) := by
  by_cases order : j≤i
  · rw [enc_sub i j (by omega) (by omega) (by omega) (by omega) order,
      enc_add (i-j) k (by omega) (by omega) (by omega) (by omega)]
  · have ip : i.toNat<7 := by omega
    have jp : j.toNat<7 := by omega
    have cases := negative_tail_cases ⟨i.toNat,ip⟩ ⟨j.toNat,jp⟩ (by change i.toNat<j.toNat;omega)
    dsimp only at cases
    have cast28 : i.toNat+28-j.toNat=(i-j+28).toNat := by omega
    have cast40 : i.toNat+40-j.toNat=(i-j+40).toNat := by omega
    rcases constant with rfl | rfl
    · simpa only [enc,cast28,show (28:Int).toNat=28 from rfl] using cases.2
    · simpa only [enc,cast40,show (40:Int).toNat=40 from rfl] using cases.1

theorem native_easterMonth (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.easterMonth (enc y)=enc (easterMonth y) := by
  have ib:=epact_bounds y
  have jb:=easterWeekday_bounds y
  have lb:=easterOffset_bounds y
  unfold NaturalSeasonNumber.easterMonth NaturalSeasonNumber.easterOffset easterMonth
  rw [literal 3,literal 40,literal 44]
  simp only [Int.cast_ofNat_Int]
  rw [native_epact y low high,native_easterWeekday y low high,
    native_offset_add (epact y) (easterWeekday y) 40 ib jb (by omega)]
  change Number.add (enc 3) (Number.floor (Number.div (enc (easterOffset y+40)) (enc 44)))= _
  rw [enc_div_floor (easterOffset y+40) 44 (by omega) (by omega) (by omega) (by omega),
    enc_add 3 ((easterOffset y+40)/44) (by omega) (by omega) (by omega) (by omega)]

theorem native_easterMonthDay (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.easterMonthDay (enc y)=enc (easterMonthDay y) := by
  have ib:=epact_bounds y
  have jb:=easterWeekday_bounds y
  have lb:=easterOffset_bounds y
  have dates:=easter_date_bounds y
  have monthBound : 3≤easterMonth y ∧ easterMonth y≤4 := by omega
  have dayNonnegative : 0≤easterOffset y+28-31*(easterMonth y/4) := by
    unfold easterMonthDay at dates
    omega
  unfold NaturalSeasonNumber.easterMonthDay NaturalSeasonNumber.easterOffset easterMonthDay
  rw [literal 28,literal 31,literal 4]
  simp only [Int.cast_ofNat_Int]
  rw [native_epact y low high,native_easterWeekday y low high,native_easterMonth y low high,
    native_offset_add (epact y) (easterWeekday y) 28 ib jb (by omega)]
  change Number.sub (enc (easterOffset y+28)) (Number.mul (enc 31) (Number.floor (Number.div (enc (easterMonth y)) (enc 4))))= _
  rw [enc_div_floor (easterMonth y) 4 (by omega) (by omega) (by omega) (by omega),
    enc_mul 31 (easterMonth y/4) (by omega) (by omega) (by omega) (by omega),
    enc_sub (easterOffset y+28) (31*(easterMonth y/4)) (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The complete pure Number expression for the native Easter month/day agrees
with the extracted integer computus for the entire future ordinary Date prefix.
The range extends beyond the Date limit; no year enumeration is used. -/
theorem native_computus (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.easterMonth (enc y)=enc (easterMonth y) ∧
    NaturalSeasonNumber.easterMonthDay (enc y)=enc (easterMonthDay y) :=
  ⟨native_easterMonth y low high,native_easterMonthDay y low high⟩

/-- Numeric correspondence in the exact encoding used by the native Date year
getter and constructor arguments. This does not assert local-time/UTC agreement. -/
theorem native_computus_ofInt (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.easterMonth (Number.ofInt y)=Number.ofInt (easterMonth y) ∧
    NaturalSeasonNumber.easterMonthDay (Number.ofInt y)=Number.ofInt (easterMonthDay y) := by
  have h:=native_computus y low high
  have dates:=easter_date_bounds y
  rw [enc_ofInt y (by omega),enc_ofInt (easterMonth y) (by omega),
    enc_ofInt (easterMonthDay y) (by omega)] at h
  exact h

theorem native_constructor_month (y : Int) (low : 1970≤y) (high : y≤1000000) :
    Number.sub (NaturalSeasonNumber.easterMonth (Number.ofInt y)) (Number.ofNat 1)=
      Number.ofInt (easterMonth y-1) := by
  have dates:=easter_date_bounds y
  rw [←enc_ofInt y (by omega),native_easterMonth y low high,literal 1]
  simp only [Int.cast_ofNat_Int]
  rw [enc_sub (easterMonth y) 1 (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_ofInt (easterMonth y-1) (by omega)]

end CookieClicker.JavaScript.SeasonNumeric

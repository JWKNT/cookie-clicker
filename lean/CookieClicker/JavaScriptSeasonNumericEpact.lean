import CookieClicker.JavaScriptSeasonNumericBase
namespace CookieClicker.JavaScript.SeasonNumeric
open NaturalSeasons
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

theorem correction_product_bounds (i n : Int) (ib : 0≤i ∧ i≤29) (nb : 0≤n ∧ n≤18) :
    0≤(i/28)*(29/(i+1)) ∧ (i/28)*(29/(i+1))≤1 ∧
    0≤(i/28)*(29/(i+1))*((21-n)/11) ∧ (i/28)*(29/(i+1))*((21-n)/11)≤1 ∧
    0≤(i/28)*(1-(i/28)*(29/(i+1))*((21-n)/11)) ∧
      (i/28)*(1-(i/28)*(29/(i+1))*((21-n)/11))≤i := by
  by_cases low : i≤27
  · have d : i/28=0 := by omega
    simp only [d,Int.zero_mul,Int.sub_zero]
    omega
  · have cases : i=28 ∨ i=29 := by omega
    rcases cases with h | h <;> subst i <;> simp <;> omega

theorem native_correctEpact (i n : Int) (ib : 0≤i ∧ i≤29) (nb : 0≤n ∧ n≤18) :
    NaturalSeasonNumber.correctEpact (enc i) (enc n)=enc (correctEpact i n) := by
  have qr:=correction_product_bounds i n ib nb
  have rn : 0≤29/(i+1) := Int.ediv_nonneg (by omega) (by omega)
  have rb : 29/(i+1)≤29 := Int.ediv_le_self (i+1) (by omega)
  unfold NaturalSeasonNumber.correctEpact correctEpact
  rw [literal 28,literal 1,literal 29,literal 21,literal 11]
  simp only [Int.cast_ofNat_Int]
  rw [enc_div_floor i 28 (by omega) (by omega) (by omega) (by omega),
    enc_add i 1 (by omega) (by omega) (by omega) (by omega),
    enc_div_floor 29 (i+1) (by omega) (by omega) (by omega) (by omega),
    enc_sub 21 n (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_div_floor (21-n) 11 (by omega) (by omega) (by omega) (by omega),
    enc_mul (i/28) (29/(i+1)) (by omega) (by omega) (by omega) (by omega),
    enc_mul ((i/28)*(29/(i+1))) ((21-n)/11) (by omega) (by omega) (by omega) (by omega),
    enc_sub 1 ((i/28)*(29/(i+1))*((21-n)/11)) (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_mul (i/28) (1-(i/28)*(29/(i+1))*((21-n)/11)) (by omega) (by omega) (by omega) (by omega),
    enc_sub i ((i/28)*(1-(i/28)*(29/(i+1))*((21-n)/11))) (by omega) (by omega) (by omega) (by omega) (by omega)]

theorem native_epact (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.epact (enc y)=enc (epact y) := by
  unfold NaturalSeasonNumber.epact epact
  rw [native_epact0 y low high,native_goldenNumber y low high]
  exact native_correctEpact (epact0 y) (goldenNumber y) (epact0_bounds y) (goldenNumber_bounds y)

theorem native_rawWeekday (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.rawWeekday (enc y)=enc (rawWeekday y) := by
  have c:=century_bounds y low high
  have i:=epact_bounds y
  have r:=raw_weekday_bounds y low high
  have cy : century y≤y := by unfold century;omega
  unfold NaturalSeasonNumber.rawWeekday rawWeekday
  rw [literal 4,literal 2]
  simp only [Int.cast_ofNat_Int]
  rw [native_epact y low high,native_century y low high,
    enc_div_floor y 4 (by omega) (by omega) (by omega) (by omega),
    enc_add y (y/4) (by omega) (by omega) (by omega) (by omega),
    enc_add (y+y/4) (epact y) (by omega) (by omega) (by omega) (by omega),
    enc_add (y+y/4+epact y) 2 (by omega) (by omega) (by omega) (by omega),
    enc_sub (y+y/4+epact y+2) (century y) (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_div_floor (century y) 4 (by omega) (by omega) (by omega) (by omega),
    enc_add (y+y/4+epact y+2-century y) (century y/4) (by omega) (by omega) (by omega) (by omega)]

theorem native_easterWeekday (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.easterWeekday (enc y)=enc (easterWeekday y) := by
  have r:=raw_weekday_bounds y low high
  unfold NaturalSeasonNumber.easterWeekday easterWeekday
  rw [literal 7]
  simp only [Int.cast_ofNat_Int]
  rw [native_rawWeekday y low high,
    enc_div_floor (rawWeekday y) 7 (by omega) (by omega) (by omega) (by omega),
    enc_mul 7 (rawWeekday y/7) (by omega) (by omega) (by omega) (by omega),
    enc_sub (rawWeekday y) (7*(rawWeekday y/7)) (by omega) (by omega) (by omega) (by omega) (by omega)]

end CookieClicker.JavaScript.SeasonNumeric

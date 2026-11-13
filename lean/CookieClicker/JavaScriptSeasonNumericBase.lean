import CookieClicker.JavaScriptCalendarMultiplication
import CookieClicker.JavaScriptSeasonNumericFormula
import CookieClicker.JavaScriptNaturalSeasons
namespace CookieClicker.JavaScript.SeasonNumeric
open NaturalSeasons
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

abbrev enc (n : Int) : UInt64 := Number.ofNat n.toNat

theorem literal (n : Nat) : Number.ofNat n=enc (n:Int) := rfl

theorem enc_ofInt (n : Int) (nonnegative : 0≤n) : enc n=Number.ofInt n := by
  change Number.ofInt (n.toNat:Int)=Number.ofInt n
  rw [Int.toNat_of_nonneg nonnegative]

theorem enc_add (a b : Int) (an : 0≤a) (bn : 0≤b) (ab : a<2^40) (bb : b<2^40) :
    Number.add (enc a) (enc b)=enc (a+b) := by
  unfold enc
  rw [NaturalArithmetic.native_add_small a.toNat b.toNat (by omega) (by omega),Int.toNat_add an bn]

theorem enc_sub (a b : Int) (an : 0≤a) (bn : 0≤b) (ab : a<2^40) (bb : b<2^40) (order : b≤a) :
    Number.sub (enc a) (enc b)=enc (a-b) := by
  unfold enc
  rw [NaturalArithmetic.native_sub_small a.toNat b.toNat (by omega) (by omega) (by omega),Int.toNat_sub'' an bn]

theorem enc_mul (a b : Int) (an : 0≤a) (bn : 0≤b) (ab : a<2^40) (bb : b<2^40) :
    Number.mul (enc a) (enc b)=enc (a*b) := by
  unfold enc
  rw [CalendarMultiplication.native_mul a.toNat b.toNat (by omega) (by omega),Int.toNat_mul an bn]

theorem enc_div_floor (a b : Int) (an : 0≤a) (bp : 0<b) (ab : a<2^40) (bb : b<2^40) :
    Number.floor (Number.div (enc a) (enc b))=enc (a/b) := by
  unfold enc
  rw [IntegerDivision.native_div_floor a.toNat b.toNat (by omega) (by omega) (by omega)]
  congr 1
  have ac : (a.toNat:Int)=a := Int.toNat_of_nonneg an
  have bc : (b.toNat:Int)=b := Int.toNat_of_nonneg (by omega)
  conv => rhs; rw [←ac,←bc,←Int.natCast_ediv,Int.toNat_natCast]

theorem century_bounds (y : Int) (low : 1970≤y) (high : y≤1000000) :
    19≤century y ∧ century y≤10000 := by unfold century;omega

theorem correction_bounds (y : Int) (low : 1970≤y) (high : y≤1000000) :
    0≤centuryCorrection y ∧ centuryCorrection y≤399 ∧ centuryCorrection y≤century y := by
  have h:=century_bounds y low high
  unfold centuryCorrection
  omega

theorem raw_epact_bounds (y : Int) (low : 1970≤y) (high : y≤1000000) :
    15≤rawEpact y ∧ rawEpact y≤10357 ∧
    0≤century y-century y/4-(century y-centuryCorrection y)/3 := by
  have c:=century_bounds y low high
  have k:=correction_bounds y low high
  have n:=goldenNumber_bounds y
  unfold rawEpact
  omega

theorem raw_weekday_bounds (y : Int) (low : 1970≤y) (high : y≤1000000) :
    0≤rawWeekday y ∧ rawWeekday y<2000000 := by
  have c:=century_bounds y low high
  have i:=epact_bounds y
  unfold rawWeekday century at *
  omega

theorem native_century (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.century (enc y)=enc (century y) := by
  unfold NaturalSeasonNumber.century century
  exact enc_div_floor y 100 (by omega) (by omega) (by omega) (by omega)

theorem native_goldenNumber (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.goldenNumber (enc y)=enc (goldenNumber y) := by
  unfold NaturalSeasonNumber.goldenNumber goldenNumber
  rw [literal 19]
  simp only [Int.cast_ofNat_Int]
  rw [enc_div_floor y 19 (by omega) (by omega) (by omega) (by omega),
    enc_mul 19 (y/19) (by omega) (by omega) (by omega) (by omega),
    enc_sub y (19*(y/19)) (by omega) (by omega) (by omega) (by omega) (by omega)]

theorem native_centuryCorrection (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.centuryCorrection (enc y)=enc (centuryCorrection y) := by
  have c:=century_bounds y low high
  unfold NaturalSeasonNumber.centuryCorrection centuryCorrection
  rw [literal 17,literal 25]
  simp only [Int.cast_ofNat_Int]
  rw [native_century y low high,enc_sub (century y) 17 (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_div_floor (century y-17) 25 (by omega) (by omega) (by omega) (by omega)]

theorem native_rawEpact (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.rawEpact (enc y)=enc (rawEpact y) := by
  have c:=century_bounds y low high
  have k:=correction_bounds y low high
  have n:=goldenNumber_bounds y
  have r:=raw_epact_bounds y low high
  unfold NaturalSeasonNumber.rawEpact rawEpact
  rw [literal 4,literal 3,literal 19,literal 15]
  simp only [Int.cast_ofNat_Int]
  rw [native_century y low high,native_centuryCorrection y low high,native_goldenNumber y low high,
    enc_div_floor (century y) 4 (by omega) (by omega) (by omega) (by omega),
    enc_sub (century y) (century y/4) (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_sub (century y) (centuryCorrection y) (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_div_floor (century y-centuryCorrection y) 3 (by omega) (by omega) (by omega) (by omega),
    enc_sub (century y-century y/4) ((century y-centuryCorrection y)/3) (by omega) (by omega) (by omega) (by omega) (by omega),
    enc_mul 19 (goldenNumber y) (by omega) (by omega) (by omega) (by omega),
    enc_add (century y-century y/4-(century y-centuryCorrection y)/3) (19*goldenNumber y) (by omega) (by omega) (by omega) (by omega),
    enc_add (century y-century y/4-(century y-centuryCorrection y)/3+19*goldenNumber y) 15 (by omega) (by omega) (by omega) (by omega)]

theorem native_epact0 (y : Int) (low : 1970≤y) (high : y≤1000000) :
    NaturalSeasonNumber.epact0 (enc y)=enc (epact0 y) := by
  have r:=raw_epact_bounds y low high
  unfold NaturalSeasonNumber.epact0 epact0
  rw [literal 30]
  simp only [Int.cast_ofNat_Int]
  rw [native_rawEpact y low high,
    enc_div_floor (rawEpact y) 30 (by omega) (by omega) (by omega) (by omega),
    enc_mul 30 (rawEpact y/30) (by omega) (by omega) (by omega) (by omega),
    enc_sub (rawEpact y) (30*(rawEpact y/30)) (by omega) (by omega) (by omega) (by omega) (by omega)]

end CookieClicker.JavaScript.SeasonNumeric

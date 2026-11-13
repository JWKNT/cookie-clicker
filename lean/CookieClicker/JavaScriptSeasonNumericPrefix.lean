import CookieClicker.JavaScriptSeasonNumericTail
import CookieClicker.JavaScriptCalendarYear
namespace CookieClicker.JavaScript.SeasonNumeric
open NaturalSeasons

theorem native_prefix_year_bounds (time : Int) (nonnegative : 0≤time)
    (nativeRange : time≤8640000000000000) :
    1970≤(Calendar.fields time).year ∧ (Calendar.fields time).year≤1000000 := by
  have interval:=CalendarYear.fields_year_bracket time
  simp only [Calendar.millisecondsPerDay] at interval
  constructor
  · by_cases low : 1970≤(Calendar.fields time).year
    · exact low
    · have order : (Calendar.fields time).year+1≤1970 := by omega
      have h:=CalendarYear.yearStart_mono ((Calendar.fields time).year+1) 1970 order
      rw [Calendar.yearStart_epoch] at h
      omega
  · by_cases high : (Calendar.fields time).year≤1000000
    · exact high
    · have order : 1000001≤(Calendar.fields time).year := by omega
      have h:=CalendarYear.yearStart_mono 1000001 (Calendar.fields time).year order
      have start : 100000001≤Calendar.yearStart 1000001 := by decide +kernel
      omega

/-- Full Number computus for the year returned by the configured UTC decoder at
any nonnegative ordinary Date timestamp. This preserves the model's explicit
UTC setting; it does not assert equivalence to another local time zone. -/
theorem native_prefix_computus (time : Int) (nonnegative : 0≤time)
    (nativeRange : time≤8640000000000000) :
    NaturalSeasonNumber.easterMonth (Number.ofInt (Calendar.fields time).year)=
      Number.ofInt (easterMonth (Calendar.fields time).year) ∧
    NaturalSeasonNumber.easterMonthDay (Number.ofInt (Calendar.fields time).year)=
      Number.ofInt (easterMonthDay (Calendar.fields time).year) := by
  have b:=native_prefix_year_bounds time nonnegative nativeRange
  exact native_computus_ofInt (Calendar.fields time).year b.1 b.2

theorem native_prefix_constructor_month (time : Int) (nonnegative : 0≤time)
    (nativeRange : time≤8640000000000000) :
    Number.sub (NaturalSeasonNumber.easterMonth (Number.ofInt (Calendar.fields time).year)) (Number.ofNat 1)=
      Number.ofInt (easterMonth (Calendar.fields time).year-1) := by
  have b:=native_prefix_year_bounds time nonnegative nativeRange
  exact native_constructor_month (Calendar.fields time).year b.1 b.2

end CookieClicker.JavaScript.SeasonNumeric

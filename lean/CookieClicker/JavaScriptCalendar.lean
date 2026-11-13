import Std

/-! Unbounded UTC Gregorian calendar arithmetic. All absolute timestamps and
calendar components are integers. This module does not convert timestamps to
binary64 or impose the native Date range. Source-level numeric coercions remain
a separate integration obligation.
-/
namespace CookieClicker.JavaScript.Calendar

def millisecondsPerDay : Int := 86400000

def leapYear (year : Int) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Days from the UTC epoch to January 1. Division is Euclidean, including
negative years; the Gregorian calendar includes year zero. -/
def yearStart (year : Int) : Int :=
  365*(year-1970)+(year-1969)/4-(year-1901)/100+(year-1601)/400

def monthLength (year : Int) (month : Nat) : Nat :=
  if month == 1 then if leapYear year then 29 else 28
  else if [3,5,8,10].contains month then 30 else 31

def monthStart (year : Int) (month : Nat) : Int :=
  ((List.range month).map (monthLength year) |>.foldl (· + ·) 0 : Nat)

def dateDay (year month day : Int) : Int :=
  let y := year+month/12
  yearStart y+monthStart y (month%12).toNat+day-1

/-- Constructor normalization permits out-of-range component fields. -/
def fromComponents (year month day hour minute second millisecond : Int) : Int :=
  dateDay year month day*millisecondsPerDay + hour*3600000 + minute*60000 + second*1000 + millisecond

private def searchYear : Nat → Int → Int → Int → Int
  | 0, _, lo, _ => lo
  | fuel+1, day, lo, hi =>
    let mid := (lo+hi)/2
    if yearStart mid ≤ day then searchYear fuel day mid hi
    else searchYear fuel day lo mid

def yearOfDay (day : Int) : Int :=
  let base := 400*((day+719528)/146097)
  searchYear 9 day base (base+400)

structure Fields where
  year : Int
  month : Nat
  day : Nat
  weekday : Nat
  hour : Nat
  minute : Nat
  second : Nat
  millisecond : Nat
  deriving Repr, DecidableEq

def fields (time : Int) : Fields := Id.run do
  let absoluteDay := time/millisecondsPerDay
  let year := yearOfDay absoluteDay
  let mut day := (absoluteDay-yearStart year).toNat
  let mut month := 0
  for _ in List.range 11 do
    if day ≥ monthLength year month then
      day := day-monthLength year month
      month := month+1
  let rest := (time%millisecondsPerDay).toNat
  return {
    year := year
    month := month
    day := day+1
    weekday := ((absoluteDay+4)%7).toNat
    hour := rest/3600000
    minute := rest/60000%60
    second := rest/1000%60
    millisecond := rest%1000 }

private def pad (n width : Nat) : String :=
  let digits := toString n
  String.ofList (List.replicate (width-digits.length) '0') ++ digits
private def weekdayName (n : Nat) := ["Sun","Mon","Tue","Wed","Thu","Fri","Sat"][n]?.getD ""
private def monthName (n : Nat) := ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"][n]?.getD ""
private def fullYear (year : Int) := if year < 0 then "-" ++ pad year.natAbs 4 else pad year.natAbs 4
private def timeText (f : Fields) := pad f.hour 2 ++ ":" ++ pad f.minute 2 ++ ":" ++ pad f.second 2

def toUTCString (time : Int) : String :=
  let f := fields time
  weekdayName f.weekday ++ ", " ++ pad f.day 2 ++ " " ++ monthName f.month ++ " " ++
    fullYear f.year ++ " " ++ timeText f ++ " GMT"

def toDateString (time : Int) : String :=
  let f := fields time
  weekdayName f.weekday ++ " " ++ monthName f.month ++ " " ++ pad f.day 2 ++ " " ++ fullYear f.year

def toTimeString (time : Int) : String :=
  timeText (fields time) ++ " GMT+0000 (Coordinated Universal Time)"

def toString (time : Int) : String := toDateString time ++ " " ++ toTimeString time

def toISOString (time : Int) : String :=
  let f := fields time
  let year := if 0 ≤ f.year && f.year ≤ 9999 then pad f.year.toNat 4
    else (if f.year < 0 then "-" else "+") ++ pad f.year.natAbs 6
  year ++ "-" ++ pad (f.month+1) 2 ++ "-" ++ pad f.day 2 ++ "T" ++ timeText f ++
    "." ++ pad f.millisecond 3 ++ "Z"

theorem yearStart_four_hundred (year : Int) : yearStart (year+400) = yearStart year+146097 := by
  unfold yearStart
  omega

theorem leapYear_four_hundred (year : Int) : leapYear (year+400) = leapYear year := by
  simp [leapYear, Int.add_emod]

theorem monthLength_four_hundred (year : Int) (month : Nat) :
    monthLength (year+400) month = monthLength year month := by
  simp [monthLength, leapYear_four_hundred]

theorem monthStart_four_hundred (year : Int) (month : Nat) :
    monthStart (year+400) month = monthStart year month := by
  have same : monthLength (year+400) = monthLength year := funext (monthLength_four_hundred year)
  simp [monthStart, same]

theorem yearStart_epoch : yearStart 1970 = 0 := by decide
theorem yearStart_zero : yearStart 0 = -719528 := by decide
theorem epoch_fields : fields 0 = ⟨1970,0,1,4,0,0,0,0⟩ := by decide +kernel
theorem before_epoch_fields : fields (-1) = ⟨1969,11,31,3,23,59,59,999⟩ := by decide +kernel
theorem leap_day_fields : fields 951782400000 = ⟨2000,1,29,2,0,0,0,0⟩ := by decide +kernel

end CookieClicker.JavaScript.Calendar

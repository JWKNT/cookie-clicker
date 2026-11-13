import CookieClicker.JavaScriptCalendar

/-! Exact year decoding for every integer UTC day. The public helper follows
all branches of the original private nine-step binary search. -/
namespace CookieClicker.JavaScript.CalendarYear
open Calendar
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

def search : Nat → Int → Int → Int → Int
  | 0, _, lo, _ => lo
  | fuel+1, day, lo, hi =>
    let mid := (lo+hi)/2
    if yearStart mid ≤ day then search fuel day mid hi
    else search fuel day lo mid

theorem source_search (day : Int) :
    yearOfDay day=search 9 day (400*((day+719528)/146097))
      (400*((day+719528)/146097)+400) := rfl

theorem yearStart_strict (x y : Int) (ordered : x<y) : yearStart x<yearStart y := by
  unfold yearStart
  omega

theorem yearStart_mono (x y : Int) (ordered : x≤y) : yearStart x≤yearStart y := by
  by_cases same : x=y
  · simp [same]
  · have strict:=yearStart_strict x y (by omega)
    omega

theorem block_start (q : Int) : yearStart (400*q)=146097*q-719528 := by
  unfold yearStart
  omega

theorem block_bracket (day : Int) :
    yearStart (400*((day+719528)/146097))≤day ∧
      day<yearStart (400*((day+719528)/146097)+400) := by
  rw [yearStart_four_hundred,block_start]
  omega

theorem search_correct (fuel : Nat) (day lo hi year : Int)
    (lower : lo≤year) (upper : year<hi) (width : hi-lo≤(2:Int)^fuel)
    (starts : yearStart year≤day) (ends : day<yearStart (year+1)) :
    search fuel day lo hi=year := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [search]
    simp only [Int.pow_zero] at width
    omega
  | succ fuel ih =>
    rw [search]
    simp only [Int.pow_succ] at width
    split
    · rename_i before
      have after : (lo+hi)/2≤year := by
        by_cases inside : (lo+hi)/2≤year
        · exact inside
        · have h:=yearStart_mono (year+1) ((lo+hi)/2) (by omega)
          omega
      exact ih ((lo+hi)/2) hi after upper (by omega)
    · rename_i after
      have before : year<(lo+hi)/2 := by
        by_cases inside : year<(lo+hi)/2
        · exact inside
        · have h:=yearStart_mono ((lo+hi)/2) year (by omega)
          omega
      exact ih lo ((lo+hi)/2) lower before (by omega)

theorem search_bracket (fuel : Nat) (day lo hi : Int)
    (starts : yearStart lo≤day) (ends : day<yearStart hi)
    (width : hi-lo≤(2:Int)^fuel) :
    yearStart (search fuel day lo hi)≤day ∧
      day<yearStart (search fuel day lo hi+1) := by
  induction fuel generalizing lo hi with
  | zero =>
    have ordered : lo<hi := by
      by_cases ordered : lo<hi
      · exact ordered
      · have h:=yearStart_mono hi lo (by omega)
        omega
    have adjacent : hi=lo+1 := by
      simp only [Int.pow_zero] at width
      omega
    simpa only [search,adjacent] using And.intro starts ends
  | succ fuel ih =>
    rw [search]
    simp only [Int.pow_succ] at width
    split
    · rename_i before
      exact ih ((lo+hi)/2) hi before ends (by omega)
    · rename_i after
      exact ih lo ((lo+hi)/2) starts (by omega) (by omega)

theorem yearOfDay_bracket (day : Int) :
    yearStart (yearOfDay day)≤day ∧day<yearStart (yearOfDay day+1) := by
  obtain ⟨starts,ends⟩:=block_bracket day
  rw [source_search]
  exact search_bracket 9 day _ _ starts ends (by omega)

theorem yearOfDay_interval (day year : Int)
    (starts : yearStart year≤day) (ends : day<yearStart (year+1)) :
    yearOfDay day=year := by
  let base:=400*((day+719528)/146097)
  obtain ⟨baseStart,baseEnd⟩:=block_bracket day
  change yearStart base≤day at baseStart
  change day<yearStart (base+400) at baseEnd
  have lower : base≤year := by
    by_cases inside : base≤year
    · exact inside
    · have h:=yearStart_mono (year+1) base (by omega)
      omega
  have upper : year<base+400 := by
    by_cases inside : year<base+400
    · exact inside
    · have h:=yearStart_mono (base+400) year (by omega)
      omega
  rw [source_search]
  exact search_correct 9 day base (base+400) year lower upper (by omega) starts ends

theorem fields_year (time : Int) : (fields time).year=yearOfDay (time/millisecondsPerDay) := by
  simp [fields]

theorem fields_year_interval (time year : Int)
    (starts : yearStart year≤time/millisecondsPerDay)
    (ends : time/millisecondsPerDay<yearStart (year+1)) : (fields time).year=year := by
  rw [fields_year]
  exact yearOfDay_interval _ _ starts ends

theorem fields_year_bracket (time : Int) :
    yearStart (fields time).year≤time/millisecondsPerDay ∧
      time/millisecondsPerDay<yearStart ((fields time).year+1) := by
  rw [fields_year]
  exact yearOfDay_bracket _

end CookieClicker.JavaScript.CalendarYear

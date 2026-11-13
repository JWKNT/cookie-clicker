import CookieClicker.JavaScriptNaturalSeasons
import CookieClicker.JavaScriptCalendarYear
namespace CookieClicker.JavaScript.NaturalSeasons

theorem yearStart_next (y : Int) :
    Calendar.yearStart (y+1) = Calendar.yearStart y + 365 + leap y := by
  unfold Calendar.yearStart leap Calendar.leapYear
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
    omega
  · rename_i h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
    omega

def dayMillis : Rat := 86400000

def dailyIndex (first target : Rat) : Nat := ((target - first) / dayMillis).ceil.toNat

def dailyDue (first : Rat) (index : Nat) : Rat := first + (index : Rat) * dayMillis

theorem daily_grid (first target : Rat) (future : first ≤ target) :
    target ≤ dailyDue first (dailyIndex first target) ∧
    dailyDue first (dailyIndex first target) < target + dayMillis := by
  let q := (target - first) / dayMillis
  have floorLow : q ≤ (q.ceil : Rat) := Rat.le_ceil
  have floorHigh : (q.ceil : Rat) < q + 1 := Rat.ceil_lt
  have nonnegative : 0 ≤ q := by dsimp [q,dayMillis]; grind
  have integerNonnegative : 0 ≤ q.ceil := by
    have z : (0 : Rat) ≤ (q.ceil : Rat) := Rat.le_trans nonnegative floorLow
    exact Rat.intCast_le_intCast.mp z
  have cast : (q.ceil.toNat : Rat) = (q.ceil : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg integerNonnegative]
  change target ≤ first + (q.ceil.toNat : Rat) * dayMillis ∧
    first + (q.ceil.toNat : Rat) * dayMillis < target + dayMillis
  rw [cast]
  dsimp [q,dayMillis] at floorLow floorHigh ⊢
  grind

/-- The first scheduled point in a two-day window leaves a full day of slack.
The theorem does not supply a save/load callback duration. -/
theorem daily_window_slack (first start : Rat) (future : first ≤ start) :
    start ≤ dailyDue first (dailyIndex first start) ∧
    dailyDue first (dailyIndex first start) + dayMillis < start + 2*dayMillis := by
  have h := daily_grid first start future
  constructor
  · exact h.1
  · grind

theorem annual_window_lower (y : Int) (season : Season) (h : needed season) :
    41 ≤ windowBegin y season := by
  have l := leap_bounds y
  have e := easter_ordinal_bounds y
  cases season with
  | none => exact False.elim h
  | fools => exact False.elim h
  | valentines => simp [windowBegin]
  | halloween => simp only [windowBegin]; omega
  | christmas => simp only [windowBegin]; omega
  | easter => simp only [windowBegin]; split <;> omega

def windowStart (y : Int) (season : Season) : Int :=
  (Calendar.yearStart y + windowBegin y season - 1)*86400000

/-- A daily request phase is fixed independently of the game's outcomes. The
chosen next-year subwindow is never farther than 733 days from the current year.
This bound is deliberately loose; no minimization claim is made. -/
theorem next_year_window (now first : Rat) (y : Int) (season : Season)
    (required : needed season)
    (inYear : ((Calendar.yearStart y * 86400000 : Int) : Rat) ≤ now ∧
      now < ((Calendar.yearStart (y+1) * 86400000 : Int) : Rat))
    (firstDue : first ≤ now + dayMillis) :
    first ≤ (windowStart (y+1) season : Rat) ∧
    now ≤ (windowStart (y+1) season : Rat) ∧
    (windowStart (y+1) season : Rat) + 2*dayMillis ≤ now + 733*dayMillis := by
  have beginLow := annual_window_lower (y+1) season required
  have beginHigh := (annual_window_bounds (y+1) season required).2
  have l := leap_bounds y
  have lnext := leap_bounds (y+1)
  have next := yearStart_next y
  have lo : Calendar.yearStart (y+1)*86400000 + 86400000 ≤ windowStart (y+1) season := by
    unfold windowStart
    omega
  have hi : windowStart (y+1) season + 2*86400000 ≤ Calendar.yearStart y*86400000 + 733*86400000 := by
    unfold windowStart
    omega
  have lor := Rat.intCast_le_intCast.mpr lo
  have hir := Rat.intCast_le_intCast.mpr hi
  simp only [Rat.intCast_add, Rat.intCast_mul] at lor hir
  dsimp [dayMillis] at firstDue ⊢
  grind

def utcDay (time : Rat) : Int := time.floor / 86400000

/-- The UTC Date read at any point in the chosen two-date interval has one of
those two ordinals. This uses rational elapsed time and the actual integer read. -/
theorem utc_day_window (time : Rat) (y : Int) (season : Season)
    (lo : (windowStart y season : Rat) ≤ time)
    (hi : time < (windowStart y season : Rat) + 2*dayMillis) :
    Calendar.yearStart y + windowBegin y season - 1 ≤ utcDay time ∧
    utcDay time ≤ Calendar.yearStart y + windowBegin y season := by
  have low : windowStart y season ≤ time.floor := Rat.le_floor_iff.mpr lo
  have hiCast : time < ((windowStart y season + 2*86400000 : Int) : Rat) := by
    have two : (2 : Rat)*86400000 = 172800000 := by grind
    simp only [dayMillis, two] at hi
    simpa using hi
  have high : time.floor < windowStart y season + 2*86400000 := Rat.floor_lt_iff.mpr hiCast
  unfold utcDay windowStart at *
  omega

/-- Uniform recurrence on the fixed daily grid, retaining a full day for the
native restoration chain. No input sequence or callback is skipped. -/
theorem daily_next_year (now first : Rat) (y : Int) (season : Season)
    (required : needed season)
    (inYear : ((Calendar.yearStart y * 86400000 : Int) : Rat) ≤ now ∧
      now < ((Calendar.yearStart (y+1) * 86400000 : Int) : Rat))
    (firstDue : first ≤ now + dayMillis) :
    ∃ n : Nat, now ≤ dailyDue first n ∧ dailyDue first n < now + 733*dayMillis ∧
      ∀ time : Rat, dailyDue first n ≤ time → time ≤ dailyDue first n + dayMillis →
        Calendar.yearStart (y+1) + windowBegin (y+1) season - 1 ≤ utcDay time ∧
        utcDay time ≤ Calendar.yearStart (y+1) + windowBegin (y+1) season := by
  have w := next_year_window now first y season required inYear firstDue
  let start : Rat := windowStart (y+1) season
  let n := dailyIndex first start
  have g := daily_grid first start w.1
  have slack := daily_window_slack first start w.1
  refine ⟨n, ?_, ?_, ?_⟩
  · exact Rat.le_trans w.2.1 g.1
  · dsimp [n,start] at *
    have := w.2.2
    dsimp [dayMillis] at *
    grind
  · intro time lower upper
    apply utc_day_window
    · exact Rat.le_trans g.1 lower
    · have : time < start + 2*dayMillis := by grind
      exact this

def yearAt (time : Rat) : Int := (Calendar.fields time.floor).year

/-- The pinned January-zero constructor, before subtracting the current Date. -/
theorem january_zero (y : Int) :
    Calendar.fromComponents y 0 0 0 0 0 0 = (Calendar.yearStart y - 1)*86400000 := by
  simp [Calendar.fromComponents, Calendar.dateDay, Calendar.monthStart,
    Calendar.millisecondsPerDay]

def sourceOrdinal (time : Rat) : Int :=
  (time.floor - Calendar.fromComponents (yearAt time) 0 0 0 0 0 0) / 86400000

def baseSeasonAt (time : Rat) : Season := select (yearAt time) (sourceOrdinal time)

theorem source_ordinal (time : Rat) :
    sourceOrdinal time = utcDay time - Calendar.yearStart (yearAt time) + 1 := by
  unfold sourceOrdinal utcDay
  rw [january_zero]
  omega

theorem actual_year_interval (time : Rat) :
    ((Calendar.yearStart (yearAt time)*86400000 : Int) : Rat) ≤ time ∧
    time < ((Calendar.yearStart (yearAt time+1)*86400000 : Int) : Rat) := by
  have h := CalendarYear.fields_year_bracket time.floor
  change Calendar.yearStart (yearAt time) ≤ utcDay time ∧
    utcDay time < Calendar.yearStart (yearAt time+1) at h
  have low : Calendar.yearStart (yearAt time)*86400000 ≤ time.floor := by
    unfold utcDay at h
    omega
  have high : time.floor < Calendar.yearStart (yearAt time+1)*86400000 := by
    unfold utcDay at h
    omega
  exact ⟨Rat.le_floor_iff.mp low, Rat.floor_lt_iff.mp high⟩

theorem window_actual_year (time : Rat) (y : Int) (season : Season)
    (required : needed season)
    (inside : Calendar.yearStart y + windowBegin y season - 1 ≤ utcDay time ∧
      utcDay time ≤ Calendar.yearStart y + windowBegin y season) : yearAt time = y := by
  have wb := annual_window_bounds y season required
  have yn := yearStart_next y
  apply CalendarYear.fields_year_interval
  · change Calendar.yearStart y ≤ utcDay time
    omega
  · change utcDay time < Calendar.yearStart (y+1)
    omega

theorem window_actual_season (time : Rat) (y : Int) (season : Season)
    (required : needed season)
    (inside : Calendar.yearStart y + windowBegin y season - 1 ≤ utcDay time ∧
      utcDay time ≤ Calendar.yearStart y + windowBegin y season) : baseSeasonAt time = season := by
  have yy := window_actual_year time y season required inside
  unfold baseSeasonAt
  rw [source_ordinal, yy]
  apply annual_window_selected y season required
  omega

/-- Every season in the extracted guard calculation recurs within a uniform 733-day bound on any
fixed daily rational-phase schedule whose first request is at most one day away.
The exact extended UTC decoder supplies the year; it is not an input oracle. -/
theorem daily_season_recurrence (now first : Rat) (season : Season)
    (required : needed season) (firstDue : first ≤ now + dayMillis) :
    ∃ n : Nat, now ≤ dailyDue first n ∧ dailyDue first n < now + 733*dayMillis ∧
      ∀ time : Rat, dailyDue first n ≤ time → time ≤ dailyDue first n + dayMillis →
        baseSeasonAt time = season := by
  obtain ⟨n,lo,hi,window⟩ := daily_next_year now first (yearAt now) season required
    (actual_year_interval now) firstDue
  refine ⟨n,lo,hi,?_⟩
  intro time after before
  exact window_actual_season time (yearAt now+1) season required (window time after before)

/-- A schedule committed at the new-save epoch meets the recurrence premise at
every later time. No seed or observed outcome enters the schedule. -/
theorem committed_daily_recurrence (epoch now : Rat) (season : Season)
    (required : needed season) (later : epoch ≤ now) :
    ∃ n : Nat, now ≤ dailyDue (epoch+dayMillis) n ∧
      dailyDue (epoch+dayMillis) n < now + 733*dayMillis ∧
      ∀ time : Rat, dailyDue (epoch+dayMillis) n ≤ time →
        time ≤ dailyDue (epoch+dayMillis) n + dayMillis → baseSeasonAt time = season := by
  apply daily_season_recurrence now (epoch+dayMillis) season required
  grind

theorem yearAt_nonnegative_time (time : Rat) (positive : 0 ≤ time) : 1970 ≤ yearAt time := by
  have yr := actual_year_interval time
  by_cases after : 1970 ≤ yearAt time
  · exact after
  have y : yearAt time + 1 ≤ 1970 := by omega
  have last := CalendarYear.yearStart_mono (yearAt time+1) 1970 y
  rw [Calendar.yearStart_epoch] at last
  have lastMillis : Calendar.yearStart (yearAt time+1)*86400000 ≤ 0 := by omega
  have lastRat := Rat.intCast_le_intCast.mpr lastMillis
  grind

/-- On the selected future UTC domain, Date's special 1900 adjustment for years
0..99 is absent at every reported maintenance opportunity. -/
theorem future_committed_recurrence (epoch now : Rat) (season : Season)
    (required : needed season) (epochNonnegative : 0 ≤ epoch) (later : epoch ≤ now) :
    ∃ n : Nat, now ≤ dailyDue (epoch+dayMillis) n ∧
      dailyDue (epoch+dayMillis) n < now + 733*dayMillis ∧
      ∀ time : Rat, dailyDue (epoch+dayMillis) n ≤ time →
        time ≤ dailyDue (epoch+dayMillis) n + dayMillis →
          100 ≤ yearAt time ∧ baseSeasonAt time = season := by
  obtain ⟨n,lo,hi,window⟩ := committed_daily_recurrence epoch now season required later
  refine ⟨n,lo,hi,?_⟩
  intro time after before
  have nonnegative : 0 ≤ time := by grind
  have year := yearAt_nonnegative_time time nonnegative
  exact ⟨by omega,window time after before⟩

/-- Native save loading uses the base season when the saved string is empty. -/
def loadedSeason (base saved : Season) : Season :=
  if saved = .none then base else saved

/-- The season assignment of the pinned Logic expiration branch. Its prior
Notify/Unlock calls and the positive-timer decrement are separate source work. -/
def expiredSeason (base current : Season) (timer : Int) (eternal : Bool) : Season :=
  if timer ≤ 0 ∧ current ≠ .none ∧ current ≠ base ∧ eternal = false then base else current

theorem loaded_expired_base (base saved : Season) (timer : Int) (expired : timer ≤ 0) :
    expiredSeason base (loadedSeason base saved) timer false = base := by
  unfold loadedSeason
  split
  · unfold expiredSeason
    simp
  · unfold expiredSeason
    by_cases same : saved = base
    · simp [same]
    · simp_all

/-- The timer assignment paired with the native season-expiration assignment.
The no-paid-switch tail starts at reset timer 0; a successful current-save load
retains 0 or -1, and this branch cannot create a positive timer. -/
def expiredTimer (base current : Season) (timer : Int) (eternal : Bool) : Int :=
  if timer ≤ 0 ∧ current ≠ .none ∧ current ≠ base ∧ eternal = false then -1 else timer

theorem loaded_expired_timer (base saved : Season) (timer : Int) (expired : timer ≤ 0) :
    expiredTimer base (loadedSeason base saved) timer false ≤ 0 := by
  unfold expiredTimer
  split <;> omega

/-- Composition of the pinned load fallback and the expiration assignments.
This is a field-transition theorem. It does not assume that notification calls
terminate or that the source scheduler reaches this branch. -/
theorem loaded_expiration_state (base saved : Season) (timer : Int) (expired : timer ≤ 0) :
    expiredSeason base (loadedSeason base saved) timer false = base ∧
    expiredTimer base (loadedSeason base saved) timer false ≤ 0 :=
  ⟨loaded_expired_base base saved timer expired,
    loaded_expired_timer base saved timer expired⟩

/-- The field-transition conclusion at one of the recurrent schedule points,
for every saved season and every already-expired timer. The source calls before
these assignments, storage/parse behavior, and reload latency remain explicit. -/
theorem recurrent_loaded_season (epoch now : Rat) (season : Season)
    (required : needed season) (epochNonnegative : 0 ≤ epoch) (later : epoch ≤ now) :
    ∃ n : Nat, now ≤ dailyDue (epoch+dayMillis) n ∧
      dailyDue (epoch+dayMillis) n < now + 733*dayMillis ∧
      ∀ (time : Rat) (saved : Season) (timer : Int),
        dailyDue (epoch+dayMillis) n ≤ time →
        time ≤ dailyDue (epoch+dayMillis) n + dayMillis → timer ≤ 0 →
        expiredSeason (baseSeasonAt time) (loadedSeason (baseSeasonAt time) saved) timer false = season ∧
        expiredTimer (baseSeasonAt time) (loadedSeason (baseSeasonAt time) saved) timer false ≤ 0 := by
  obtain ⟨n,lo,hi,window⟩ := future_committed_recurrence epoch now season required epochNonnegative later
  refine ⟨n,lo,hi,?_⟩
  intro time saved timer after before expired
  have state := loaded_expiration_state (baseSeasonAt time) saved timer expired
  exact ⟨state.1.trans (window time after before).2,state.2⟩

end CookieClicker.JavaScript.NaturalSeasons

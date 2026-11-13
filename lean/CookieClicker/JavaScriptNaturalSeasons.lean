import CookieClicker.JavaScriptNaturalSeasonFormula

namespace CookieClicker.JavaScript.NaturalSeasons

theorem leap_bounds (y : Int) : 0 ≤ leap y ∧ leap y ≤ 1 := by
  unfold leap
  split <;> omega

theorem goldenNumber_bounds (y : Int) : 0 ≤ goldenNumber y ∧ goldenNumber y ≤ 18 := by
  unfold goldenNumber
  omega

theorem epact0_bounds (y : Int) : 0 ≤ epact0 y ∧ epact0 y ≤ 29 := by
  unfold epact0
  omega

theorem correctEpact_bounds (i n : Int) (hi : 0 ≤ i ∧ i ≤ 29)
    (hn : 0 ≤ n ∧ n ≤ 18) : 0 ≤ correctEpact i n ∧ correctEpact i n ≤ 28 := by
  by_cases low : i ≤ 27
  · have div : i / 28 = 0 := by omega
    simp [correctEpact, div]
    omega
  · have cases : i = 28 ∨ i = 29 := by omega
    rcases cases with h | h
    · subst i
      simp [correctEpact]
      omega
    · subst i
      simp [correctEpact]

theorem epact_bounds (y : Int) : 0 ≤ epact y ∧ epact y ≤ 28 :=
  correctEpact_bounds _ _ (epact0_bounds y) (goldenNumber_bounds y)

theorem easterWeekday_bounds (y : Int) : 0 ≤ easterWeekday y ∧ easterWeekday y ≤ 6 := by
  unfold easterWeekday
  omega

theorem easterOffset_bounds (y : Int) : -6 ≤ easterOffset y ∧ easterOffset y ≤ 28 := by
  have := epact_bounds y
  have := easterWeekday_bounds y
  unfold easterOffset
  omega

theorem easter_date_bounds (y : Int) :
    (easterMonth y = 3 ∧ 22 ≤ easterMonthDay y ∧ easterMonthDay y ≤ 31) ∨
    (easterMonth y = 4 ∧ 1 ≤ easterMonthDay y ∧ easterMonthDay y ≤ 25) := by
  have h := easterOffset_bounds y
  unfold easterMonthDay easterMonth
  by_cases low : easterOffset y ≤ 3
  · left
    have hdiv : (easterOffset y + 40) / 44 = 0 := by omega
    simp only [hdiv]
    omega
  · right
    have hdiv : (easterOffset y + 40) / 44 = 1 := by omega
    simp only [hdiv]
    omega

theorem march_start (y : Int) : Calendar.monthStart y 2 = 59 + leap y := by
  unfold Calendar.monthStart leap
  rw [show List.range 2 = [0,1] by decide]
  cases h : Calendar.leapYear y <;> simp [Calendar.monthLength, h]

theorem april_start (y : Int) : Calendar.monthStart y 3 = 90 + leap y := by
  unfold Calendar.monthStart leap
  rw [show List.range 3 = [0,1,2] by decide]
  cases h : Calendar.leapYear y <;> simp [Calendar.monthLength, h]

theorem easter_ordinal_bounds (y : Int) :
    81 + leap y ≤ easterOrdinal y ∧ easterOrdinal y ≤ 115 + leap y := by
  rcases easter_date_bounds y with ⟨m, d⟩ | ⟨m, d⟩
  · simp only [easterOrdinal, m]
    change 81 + leap y ≤ Calendar.monthStart y 2 + easterMonthDay y ∧ Calendar.monthStart y 2 + easterMonthDay y ≤ 115 + leap y
    rw [march_start]
    omega
  · simp only [easterOrdinal, m]
    change 81 + leap y ≤ Calendar.monthStart y 3 + easterMonthDay y ∧ Calendar.monthStart y 3 + easterMonthDay y ≤ 115 + leap y
    rw [april_start]
    omega

def needed : Season → Prop
  | .valentines | .halloween | .christmas | .easter => True
  | _ => False

/-- A two-date subwindow which avoids the earlier native Business-day guard. -/
def windowBegin (y : Int) : Season → Int
  | .valentines => 41
  | .halloween => 297 + leap y
  | .christmas => 349 + leap y
  | .easter => if easterOrdinal y - 6 < 90 - leap y
      then easterOrdinal y - 7 else easterOrdinal y - 1
  | _ => 1

theorem valentines_selected (y day : Int) (h : 41 ≤ day ∧ day ≤ 46) :
    select y day = .valentines := by simp [select, h]

theorem halloween_selected (y day : Int)
    (h : 297 + leap y ≤ day ∧ day ≤ 304 + leap y) :
    select y day = .halloween := by
  have l := leap_bounds y
  have nv : ¬ (41 ≤ day ∧ day ≤ 46) := by omega
  have nf : ¬ (90 ≤ day + leap y ∧ day ≤ 92 + leap y) := by omega
  have hh : 304 - 7 + leap y ≤ day ∧ day ≤ 304 + leap y := by omega
  simp only [select, if_neg nv, if_neg nf, if_pos hh]

theorem christmas_selected (y day : Int)
    (h : 349 + leap y ≤ day ∧ day ≤ 365 + leap y) :
    select y day = .christmas := by
  have l := leap_bounds y
  have nv : ¬ (41 ≤ day ∧ day ≤ 46) := by omega
  have nf : ¬ (90 ≤ day + leap y ∧ day ≤ 92 + leap y) := by omega
  have nh : ¬ (304 - 7 + leap y ≤ day ∧ day ≤ 304 + leap y) := by omega
  simp only [select, if_neg nv, if_neg nf, if_neg nh, if_pos h]

theorem easter_selected (y day : Int)
    (h : easterOrdinal y - 7 ≤ day ∧ day ≤ easterOrdinal y)
    (outside : day + leap y < 90 ∨ 92 + leap y < day) :
    select y day = .easter := by
  have l := leap_bounds y
  have e := easter_ordinal_bounds y
  have nv : ¬ (41 ≤ day ∧ day ≤ 46) := by omega
  have nf : ¬ (90 ≤ day + leap y ∧ day ≤ 92 + leap y) := by omega
  have nh : ¬ (304 - 7 + leap y ≤ day ∧ day ≤ 304 + leap y) := by omega
  have nc : ¬ (349 + leap y ≤ day ∧ day ≤ 365 + leap y) := by omega
  simp only [select, if_neg nv, if_neg nf, if_neg nh, if_neg nc, if_pos h]

theorem easter_window (y day : Int)
    (h : windowBegin y .easter ≤ day ∧ day ≤ windowBegin y .easter + 1) :
    select y day = .easter := by
  have l := leap_bounds y
  simp only [windowBegin] at h
  split at h
  · apply easter_selected y day <;> omega
  · apply easter_selected y day <;> omega

theorem annual_window_bounds (y : Int) (season : Season) (h : needed season) :
    1 ≤ windowBegin y season ∧ windowBegin y season + 1 ≤ 365 + leap y := by
  have l := leap_bounds y
  have e := easter_ordinal_bounds y
  cases season with
  | none => exact False.elim h
  | fools => exact False.elim h
  | valentines => simp only [windowBegin]; omega
  | halloween => simp only [windowBegin]; omega
  | christmas => simp only [windowBegin]; omega
  | easter => simp only [windowBegin]; split <;> omega

theorem annual_window_selected (y : Int) (season : Season) (h : needed season)
    (day : Int) (inside : windowBegin y season ≤ day ∧ day ≤ windowBegin y season + 1) :
    select y day = season := by
  cases season with
  | none => exact False.elim h
  | fools => exact False.elim h
  | valentines => apply valentines_selected; simp only [windowBegin] at inside; omega
  | halloween => apply halloween_selected; simp only [windowBegin] at inside; omega
  | christmas => apply christmas_selected; simp only [windowBegin] at inside; omega
  | easter => exact easter_window y day inside

end CookieClicker.JavaScript.NaturalSeasons

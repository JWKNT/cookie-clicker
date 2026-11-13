import CookieClicker.JavaScriptCursorQuotePrefix
import CookieClicker.JavaScriptCursorGetPriceArithmetic

/-! Exact quote values for the admitted zero/one-Cursor profile, including
Starter kit's free-copy floor. These facts discharge the finite-number premise
of the full source sum call; they do not replace source execution. -/
namespace CookieClicker.JavaScript.CursorQuoteArithmetic
open CursorGetPriceArithmetic
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem native_sum (starter : Bool) :
    CursorQuotePrefix.sum 4624633867356078080 (free starter) 4607857958744122982=raw true starter := by
  unfold CursorQuotePrefix.sum
  rw [show Number.one=amount true from rfl,raw_profile true starter]
  cases starter <;> decide +kernel

theorem native_sum_stable (starter : Bool) :
    Number.mul (CursorQuotePrefix.sum 4624633867356078080 (free starter) 4607857958744122982) Number.one=
      CursorQuotePrefix.sum 4624633867356078080 (free starter) 4607857958744122982 := by
  rw [native_sum]
  exact native_price_stable true starter

theorem native_sum_quote (starter : Bool) :
    Number.ceil (CursorQuotePrefix.sum 4624633867356078080 (free starter) 4607857958744122982)=quote true starter := by
  rw [native_sum]
  exact native_quote true starter

end CookieClicker.JavaScript.CursorQuoteArithmetic

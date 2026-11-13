import CookieClicker.JavaScriptCursorGetPriceRead

/-! Exact binary64 arithmetic in the zero/one-Cursor price profile. The
free-copy floor is included; these are the source formula's values, not
a replacement for the source-call proof. -/
namespace CookieClicker.JavaScript.CursorGetPriceArithmetic
open CursorGetPriceRead
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def amount (owned : Bool) : UInt64 := if owned then 4607182418800017408 else 0
def free (starter : Bool) : UInt64 := if starter then 4621819117588971520 else 0
def raw (owned starter : Bool) : UInt64 :=
  if owned && !starter then 4625548661030387712 else 4624633867356078080
def quote (owned starter : Bool) : UInt64 :=
  if owned && !starter then 4625759767262920704 else 4624633867356078080

theorem raw_profile (owned starter : Bool) :
    rawValue 4624633867356078080 (amount owned) (free starter) 4607857958744122982=raw owned starter := by
  cases owned <;> cases starter <;> decide +kernel

theorem native_price_stable (owned starter : Bool) :
    Number.mul (raw owned starter) Number.one=raw owned starter := by
  cases owned <;> cases starter <;> decide +kernel

theorem native_quote (owned starter : Bool) : Number.ceil (raw owned starter)=quote owned starter := by
  cases owned <;> cases starter <;> decide +kernel

end CookieClicker.JavaScript.CursorGetPriceArithmetic

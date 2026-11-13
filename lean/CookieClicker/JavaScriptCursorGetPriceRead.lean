import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptBuildingMathRead
import CookieClicker.JavaScriptSourceRead

/-! The actual raw getPrice expression, before modifyBuildingPrice. The
native Math calls and this/Game reads retain their actual descriptors. -/
namespace CookieClicker.JavaScript.CursorGetPriceRead
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def raw : Expr := match CursorCycleSyntax.getPriceBody with
  | .block (.variable [(_,some expression)]::_)=>expression | _=>.unsupported "missing price initializer"

def thisField (name : String) : Expr := .member .this (.identifier name) false

def difference : Expr := .binary .subtract (thisField "amount") (thisField "free")
def exponent : Expr := BuildingMathRead.call "max" [.literal (.number 0),difference]
def increase : Expr := .member (.identifier "Game") (.identifier "priceIncrease") false

def rawValue (base amount free rate : UInt64) : UInt64 :=
  Number.mul base (Math.pow rate (Number.maximum 0 (Number.sub amount free)))

structure Inputs (base : Machine) (price amount free rate : UInt64) where
  building : ObjectId
  game : ObjectId
  receiver : base.context.thisValue=.object building
  gameRead : Reads base (.identifier "Game") (.object game) 3
  priceRead : DataEdge base building (JSString.ofString "basePrice") (.number price)
  amountRead : DataEdge base building (JSString.ofString "amount") (.number amount)
  freeRead : DataEdge base building (JSString.ofString "free") (.number free)
  rateRead : DataEdge base game (JSString.ofString "priceIncrease") (.number rate)
  maximum : BuildingMathRead.Binding base "max"
  power : BuildingMathRead.Binding base "pow"

theorem this_read (base : Machine) : Reads base .this base.context.thisValue 1 := by
  intro continuation ordinary fuel
  rw [Nat.add_comm 1 fuel]
  rfl

private theorem max_zero : Number.maximum Number.negativeInfinity 0=0 := by decide +kernel

theorem maximum_read (base : Machine) (binding : BuildingMathRead.Binding base "max")
    (expression : Expr) (value : UInt64) (ticks : Nat) (read : Reads base expression (.number value) ticks) :
    Reads base (BuildingMathRead.call "max" [.literal (.number 0),expression])
      (.number (Number.maximum 0 value)) (1+ticks+13) := by
  apply BuildingMathRead.binary base "max" binding (.literal (.number 0)) expression
    (.number 0) (.number value) (.number (Number.maximum 0 value)) 1 ticks
    (literal base (.number 0)) read
  simp [Builtins.mathCall,List.mapM,List.mapM.loop,toNumber,max_zero,bind,Except.bind,pure,Except.pure]

theorem Inputs.raw_read {base : Machine} {price amount free rate : UInt64}
    (h : Inputs base price amount free rate) : Reads base raw (.number (rawValue price amount free rate)) 55 := by
  have receiver : Reads base .this (.object h.building) 1 := by
    simpa only [h.receiver] using this_read base
  have bp : Reads base (thisField "basePrice") (.number price) 5 := h.priceRead.dot _ 1 receiver
  have a : Reads base (thisField "amount") (.number amount) 5 := h.amountRead.dot _ 1 receiver
  have f : Reads base (thisField "free") (.number free) 5 := h.freeRead.dot _ 1 receiver
  have sub : Reads base difference (.number (Number.sub amount free)) 13 :=
    binary_value base .subtract _ _ (.number amount) (.number free) (.number (Number.sub amount free)) 5 5
      a f rfl rfl (by decide) (by rfl)
  have exp : Reads base exponent (.number (Number.maximum 0 (Number.sub amount free))) 27 :=
    maximum_read base h.maximum difference (Number.sub amount free) 13 sub
  have inc : Reads base increase (.number rate) 7 := h.rateRead.dot _ 3 h.gameRead
  have pow := BuildingMathRead.pow_read base h.power increase exponent rate
    (Number.maximum 0 (Number.sub amount free)) 7 27 inc exp
  exact binary_value base .multiply _ _ (.number price)
    (.number (Math.pow rate (Number.maximum 0 (Number.sub amount free))))
    (.number (rawValue price amount free rate)) 5 47 bp pow rfl rfl (by decide) (by rfl)

end CookieClicker.JavaScript.CursorGetPriceRead

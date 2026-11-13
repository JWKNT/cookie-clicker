import CookieClicker.JavaScriptLocalAssign
import CookieClicker.JavaScriptBuildingMathRead
import CookieClicker.JavaScriptSaleNumericSource

/-! The sale header uses native multiplication and Math.floor before it writes
its existing price binding. Arbitrary Number bit patterns are retained. -/
namespace CookieClicker.JavaScript.SaleFloor
open SourceRead SourceBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def product : Expr := .binary .multiply (.identifier "price") (.identifier "giveBack")
def expression : Expr := BuildingMathRead.call "floor" [product]
def statement : Stmt := .expression (.assignment .assign (.identifier "price") expression)

theorem original_statement : (SaleNumericSource.loopBody[2]?).getD .empty=statement := rfl

theorem source_read (base : Machine) (binding : BuildingMathRead.Binding base "floor")
    (price giveBack : UInt64)
    (priceRead : Reads base (.identifier "price") (.number price) 3)
    (giveBackRead : Reads base (.identifier "giveBack") (.number giveBack) 3) :
    Reads base expression (.number (Number.floor (Number.mul price giveBack))) 21 := by
  have read : Reads base product (.number (Number.mul price giveBack)) 9 :=
    binary_value base .multiply _ _ (.number price) (.number giveBack)
      (.number (Number.mul price giveBack)) 3 3 priceRead giveBackRead rfl rfl (by decide) rfl
  exact BuildingMathRead.unary base "floor" binding product (.number (Number.mul price giveBack))
    (.number (Number.floor (Number.mul price giveBack))) 9 read rfl

theorem source_assignment (base : Machine) (binding : BuildingMathRead.Binding base "floor")
    (slot : Slot base "price") (price giveBack : UInt64)
    (priceRead : Reads base (.identifier "price") (.number price) 3)
    (giveBackRead : Reads base (.identifier "giveBack") (.number giveBack) 3) (fuel : Nat) :
    Builtins.run (28+fuel) {base with control:=.statement ((SaleNumericSource.loopBody[2]?).getD .empty)}=
      Builtins.run fuel {slot.after (.number (Number.floor (Number.mul price giveBack))) with
        control:=.completion (.normal (some (.number (Number.floor (Number.mul price giveBack)))))} :=
  LocalAssign.source_assignment base "price" slot expression _ 21
    (source_read base binding price giveBack priceRead giveBackRead) rfl fuel

end CookieClicker.JavaScript.SaleFloor

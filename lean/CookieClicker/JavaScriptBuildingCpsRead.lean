import CookieClicker.JavaScriptBuildingMathRead

namespace CookieClicker.JavaScript.BuildingCpsRead
open SourceRead BuildingMathRead BuildingCpsArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def nExpression : Expr := .member .this (.identifier "n") false
def baseExpression : Expr := .member .this (.identifier "baseCps") false
def digitsExpression : Expr := .identifier "digits"
def ln10Expression : Expr := .member (.identifier "Math") (.identifier "LN10") false

def rawExpression : Expr := .binary .divide
  (call "ceil" [.binary .multiply
    (call "pow" [.binary .multiply nExpression (.literal (.number Number.one)),
      .binary .add (.binary .multiply nExpression (.literal (.number half))) (.literal (.number two))])
    (.literal (.number ten))]) (.literal (.number ten))

def scaleExpression : Expr := .binary .divide
  (call "pow" [.literal (.number ten),call "ceil" [.binary .divide
    (call "log" [call "ceil" [baseExpression]]) ln10Expression]]) (.literal (.number hundred))

def roundExpression : Expr := .binary .multiply
  (call "round" [.binary .divide baseExpression digitsExpression]) digitsExpression

theorem raw_source : BuildingConstructorSyntax.cpsPrefix.headD .empty=
    .expression (.assignment .assign baseExpression rawExpression) := rfl

theorem scale_source : (BuildingConstructorSyntax.cpsPrefix.drop 1).headD .empty=
    .variable [("digits",some scaleExpression)] := rfl

theorem round_source : (BuildingConstructorSyntax.cpsPrefix.drop 2).headD .empty=
    .expression (.assignment .assign baseExpression roundExpression) := rfl

theorem numeric_add (base : Machine) (left right : Expr) (a b : UInt64)
    (leftTicks rightTicks : Nat) (readLeft : Reads base left (.number a) leftTicks)
    (readRight : Reads base right (.number b) rightTicks) :
    Reads base (.binary .add left right) (.number (Number.add a b)) (leftTicks+rightTicks+3) := by
  apply binary_value base .add left right (.number a) (.number b) (.number (Number.add a b))
    leftTicks rightTicks readLeft readRight rfl rfl (by decide)
  rfl

theorem numeric_multiply (base : Machine) (left right : Expr) (a b : UInt64)
    (leftTicks rightTicks : Nat) (readLeft : Reads base left (.number a) leftTicks)
    (readRight : Reads base right (.number b) rightTicks) :
    Reads base (.binary .multiply left right) (.number (Number.mul a b)) (leftTicks+rightTicks+3) := by
  apply binary_value base .multiply left right (.number a) (.number b) (.number (Number.mul a b))
    leftTicks rightTicks readLeft readRight rfl rfl (by decide)
  rfl

theorem numeric_divide (base : Machine) (left right : Expr) (a b : UInt64)
    (leftTicks rightTicks : Nat) (readLeft : Reads base left (.number a) leftTicks)
    (readRight : Reads base right (.number b) rightTicks) :
    Reads base (.binary .divide left right) (.number (Number.div a b)) (leftTicks+rightTicks+3) := by
  apply binary_value base .divide left right (.number a) (.number b) (.number (Number.div a b))
    leftTicks rightTicks readLeft readRight rfl rfl (by decide)
  rfl

theorem raw_read (base : Machine) (power : BuildingMathRead.Binding base "pow") (ceiling : BuildingMathRead.Binding base "ceil")
    (n : UInt64) (readN : Reads base nExpression (.number n) 5) :
    Reads base rawExpression (.number (raw n)) 55 := by
  have multiplied:=numeric_multiply base _ _ n Number.one 5 1 readN (literal _ (.number Number.one))
  have halved:=numeric_multiply base _ _ n half 5 1 readN (literal _ (.number half))
  have exponent:=numeric_add base _ _ (Number.mul n half) two 9 1 halved (literal _ (.number two))
  have powered:=pow_read base power _ _ (Number.mul n Number.one) (Number.add (Number.mul n half) two)
    9 13 multiplied exponent
  have timesTen:=numeric_multiply base _ _ _ ten 35 1 powered (literal _ (.number ten))
  have ceilingRead:=ceil_read base ceiling _ _ 39 timesTen
  exact numeric_divide base _ _ _ ten 51 1 ceilingRead (literal _ (.number ten))

theorem scale_read (base : Machine) (power : BuildingMathRead.Binding base "pow")
    (ceiling : BuildingMathRead.Binding base "ceil") (logarithm : BuildingMathRead.Binding base "log")
    (value : UInt64) (readValue : Reads base baseExpression (.number value) 5)
    (readLn10 : Reads base ln10Expression (.number ln10) 7) :
    Reads base scaleExpression (.number (digits value)) 69 := by
  have initialCeil:=ceil_read base ceiling _ _ 5 readValue
  have logged:=log_read base logarithm _ _ 17 initialCeil
  have divided:=numeric_divide base _ _ _ ln10 29 7 logged readLn10
  have exponent:=ceil_read base ceiling _ _ 39 divided
  have powered:=pow_read base power _ _ ten _ 1 51 (literal _ (.number ten)) exponent
  exact numeric_divide base _ _ _ hundred 65 1 powered (literal _ (.number hundred))

theorem round_read (base : Machine) (rounding : BuildingMathRead.Binding base "round")
    (value scale : UInt64) (readValue : Reads base baseExpression (.number value) 5)
    (readScale : Reads base digitsExpression (.number scale) 3) :
    Reads base roundExpression (.number (rounded value scale)) 29 := by
  have divided:=numeric_divide base _ _ value scale 5 3 readValue readScale
  have roundedRead:=BuildingMathRead.round_read base rounding _ _ 11 divided
  exact numeric_multiply base _ _ _ scale 23 3 roundedRead readScale

end CookieClicker.JavaScript.BuildingCpsRead

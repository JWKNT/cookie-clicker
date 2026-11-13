import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptBuildingConstructorSyntax

/-! Operation-order formulas of the three actual numeric constructor statements.
Each row below is checked by the Lean kernel; native-engine observations supply
comparison expectations, not axioms. Interpreter/property composition is separate. -/
namespace CookieClicker.JavaScript.BuildingCpsArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def ten : UInt64 := 4621819117588971520
def half : UInt64 := 4602678819172646912
def two : UInt64 := 4611686018427387904
def hundred : UInt64 := 4636737291354636288
def ln10 : UInt64 := 4612367379483415830

def raw (n : UInt64) : UInt64 :=
  Number.div (Number.ceil (Number.mul
    (Math.pow (Number.mul n Number.one) (Number.add (Number.mul n half) two)) ten)) ten

def digits (value : UInt64) : UInt64 :=
  Number.div (Math.pow ten (Number.ceil (Number.div (Math.log (Number.ceil value)) ln10))) hundred

def rounded (value scale : UInt64) : UInt64 :=
  Number.mul (Number.round (Number.div value scale)) scale

def output (n : UInt64) : UInt64 × UInt64 :=
  let value:=raw n
  let scale:=digits value
  (rounded value scale,scale)

theorem source_1 : output 4607182418800017408=(4607182418800017408,4576918229304087675) := by
  decide +kernel

theorem source_2 : output 4611686018427387904=(4620693217682128896,4591870180066957722) := by
  decide +kernel

theorem source_3 : output 4613937818241073152=(4631811479262199808,4607182418800017408) := by
  decide +kernel

theorem source_4 : output 4616189618054758400=(4643281584563159040,4621819117588971520) := by
  decide +kernel

theorem source_5 : output 4617315517961601024=(4653872080561897472,4636737291354636288) := by
  decide +kernel

theorem source_6 : output 4618441417868443648=(4665298205397745664,4636737291354636288) := by
  decide +kernel

theorem source_7 : output 4619567317775286272=(4676280127535972352,4652007308841189376) := by
  decide +kernel

theorem source_8 : output 4620693217682128896=(4688173544813625344,4666723172467343360) := by
  decide +kernel

theorem source_9 : output 4621256167635550208=(4699622759393656832,4681608360884174848) := by
  decide +kernel

theorem source_10 : output 4621819117588971520=(4711630319722168320,4681608360884174848) := by
  decide +kernel

theorem source_11 : output 4622382067542392832=(4723992962176909312,4696837146684686336) := by
  decide +kernel

theorem source_12 : output 4622945017495814144=(4735993811619020800,4711630319722168320) := by
  decide +kernel

theorem source_13 : output 4623507967449235456=(4748372148421132288,4726483295884279808) := by
  decide +kernel

theorem source_14 : output 4624070917402656768=(4761306230503243776,4741671816366391296) := by
  decide +kernel

theorem source_15 : output 4624633867356078080=(4774227205385355264,4756540486875873280) := by
  decide +kernel

theorem source_16 : output 4625196817309499392=(4787328404267466752,4771362005757984768) := by
  decide +kernel

theorem source_17 : output 4625478292286210048=(4800329203522207744,4771362005757984768) := by
  decide +kernel

theorem source_18 : output 4625759767262920704=(4813532802404319232,4786511204640096256) := by
  decide +kernel

theorem source_19 : output 4626041242239631360=(4827011601286430720,4801453603149578240) := by
  decide +kernel

end CookieClicker.JavaScript.BuildingCpsArithmetic

import CookieClicker.JavaScriptBuildingCpsPrefix
import CookieClicker.JavaScriptProductionArithmetic

namespace CookieClicker.JavaScript.BuildingCpsCases
open BuildingCpsArithmetic BuildingCpsPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure Row where
  id : Nat
  n : UInt64
  cps : UInt64
  scale : UInt64
  indexPositive : 0<id
  indexBelow20 : id<20
  indexEncoding : n=Number.ofNat id
  nonzero : Number.equal n Number.positiveZero=false
  computed : output n=(cps,scale)
  finite : Number.isFinite cps=true
  mantissa : Nat
  exponent : Int
  positive : 0<mantissa
  lower : 2^52≤mantissa
  upper : mantissa<2^53
  exponentLower : -1074≤exponent
  exponentUpper : exponent≤971
  encoding : cps=(Float.Model.pack (.finite .positive mantissa exponent positive)).toBits

def row1 : Row := {
  id:=1,n:=4607182418800017408,cps:=4607182418800017408,scale:=4576918229304087675
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_1,finite:=by decide
  mantissa:=4503599627370496,exponent:=-52
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row2 : Row := {
  id:=2,n:=4611686018427387904,cps:=4620693217682128896,scale:=4591870180066957722
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_2,finite:=by decide
  mantissa:=4503599627370496,exponent:=-49
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row3 : Row := {
  id:=3,n:=4613937818241073152,cps:=4631811479262199808,scale:=4607182418800017408
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_3,finite:=by decide
  mantissa:=6614661952700416,exponent:=-47
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row4 : Row := {
  id:=4,n:=4616189618054758400,cps:=4643281584563159040,scale:=4621819117588971520
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_4,finite:=by decide
  mantissa:=4573968371548160,exponent:=-44
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row5 : Row := {
  id:=5,n:=4617315517961601024,cps:=4653872080561897472,scale:=4636737291354636288
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_5,finite:=by decide
  mantissa:=6157265115545600,exponent:=-42
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row6 : Row := {
  id:=6,n:=4618441417868443648,cps:=4665298205397745664,scale:=4636737291354636288
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_6,finite:=by decide
  mantissa:=8576190696652800,exponent:=-40
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row7 : Row := {
  id:=7,n:=4619567317775286272,cps:=4676280127535972352,scale:=4652007308841189376
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_7,finite:=by decide
  mantissa:=6047313952768000,exponent:=-37
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row8 : Row := {
  id:=8,n:=4620693217682128896,cps:=4688173544813625344,scale:=4666723172467343360
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_8,finite:=by decide
  mantissa:=8933531975680000,exponent:=-35
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row9 : Row := {
  id:=9,n:=4621256167635550208,cps:=4699622759393656832,scale:=4681608360884174848
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_9,finite:=by decide
  mantissa:=6871947673600000,exponent:=-32
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row10 : Row := {
  id:=10,n:=4621819117588971520,cps:=4711630319722168320,scale:=4681608360884174848
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_10,finite:=by decide
  mantissa:=5368709120000000,exponent:=-29
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row11 : Row := {
  id:=11,n:=4622382067542392832,cps:=4723992962176909312,scale:=4696837146684686336
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_11,finite:=by decide
  mantissa:=8724152320000000,exponent:=-27
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row12 : Row := {
  id:=12,n:=4622945017495814144,cps:=4735993811619020800,scale:=4711630319722168320
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_12,finite:=by decide
  mantissa:=7214202880000000,exponent:=-24
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row13 : Row := {
  id:=13,n:=4623507967449235456,cps:=4748372148421132288,scale:=4726483295884279808
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_13,finite:=by decide
  mantissa:=6081740800000000,exponent:=-21
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row14 : Row := {
  id:=14,n:=4624070917402656768,cps:=4761306230503243776,scale:=4741671816366391296
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_14,finite:=by decide
  mantissa:=5505024000000000,exponent:=-18
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row15 : Row := {
  id:=15,n:=4624633867356078080,cps:=4774227205385355264,scale:=4756540486875873280
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_15,finite:=by decide
  mantissa:=4915200000000000,exponent:=-15
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row16 : Row := {
  id:=16,n:=4625196817309499392,cps:=4787328404267466752,scale:=4771362005757984768
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_16,finite:=by decide
  mantissa:=4505600000000000,exponent:=-12
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row17 : Row := {
  id:=17,n:=4625478292286210048,cps:=4800329203522207744,scale:=4771362005757984768
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_17,finite:=by decide
  mantissa:=8499200000000000,exponent:=-10
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row18 : Row := {
  id:=18,n:=4625759767262920704,cps:=4813532802404319232,scale:=4786511204640096256
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_18,finite:=by decide
  mantissa:=8192000000000000,exponent:=-7
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def row19 : Row := {
  id:=19,n:=4626041242239631360,cps:=4827011601286430720,scale:=4801453603149578240
  indexPositive:=by decide,indexBelow20:=by decide,indexEncoding:=by decide
  nonzero:=by decide,computed:=source_19,finite:=by decide
  mantissa:=8160000000000000,exponent:=-4
  positive:=by decide,lower:=by decide,upper:=by decide
  exponentLower:=by decide,exponentUpper:=by decide,encoding:=by decide }

def rows : List Row := [row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19]

theorem rows_indices : rows.map Row.id=List.range' 1 19 := by decide

theorem Row.times_one (row : Row) : Number.mul row.cps Number.one=row.cps := by
  rw [row.encoding]
  exact ProductionArithmetic.normal_times_one row.mantissa row.exponent row.positive row.lower row.upper
    row.exponentLower row.exponentUpper

theorem Row.zero_times (row : Row) : Number.mul Number.positiveZero row.cps=Number.positiveZero := by
  rw [row.encoding]
  exact ProductionArithmetic.zero_times_normal row.mantissa row.exponent row.positive row.lower row.upper
    row.exponentLower row.exponentUpper

theorem Row.native_branch (row : Row) (base : Machine) (input : Inputs base row.n) (fuel : Nat) :
    Builtins.run (189+fuel) {base with control:=.statement BuildingConstructorSyntax.numericBranch}=
      Builtins.run fuel {input.after with
        control:=.completion (.normal (some (.number row.cps)))
        continuation:=.statementList BuildingConstructorSyntax.priceSuffix (some (.number (raw row.n)))::base.continuation} := by
  have run:=input.native_branch row.nonzero fuel
  simpa only [row.computed,Prod.fst] using run

theorem Row.stored_descriptor (row : Row) (base : Machine) (input : Inputs base row.n) :
    checkedObject input.after.heap input.cps.id=.ok
      (setOwnProperty input.finalSlot.object (JSString.ofString "baseCps")
        (.data (.number row.cps) true input.cps.enumerable input.cps.configurable)) := by
  have expected : rounded (raw row.n) (digits (raw row.n))=row.cps := congrArg Prod.fst row.computed
  have stored:=input.finalSlot.updated_present (.number (rounded (raw row.n) (digits (raw row.n))))
  simpa only [Inputs.after,BuildingStore.Slot.updated,expected,Inputs.finalSlot,BuildingStore.Slot.transport,BuildingStore.Slot.next] using stored

theorem Row.own_descriptor (row : Row) (base : Machine) (input : Inputs base row.n) :
    ownProperty (input.finalSlot.updated (.number (rounded (raw row.n) (digits (raw row.n)))))
      (JSString.ofString "baseCps")=
      some (.data (.number row.cps) true input.cps.enumerable input.cps.configurable) := by
  have expected : rounded (raw row.n) (digits (raw row.n))=row.cps := congrArg Prod.fst row.computed
  simpa only [expected,Inputs.finalSlot,BuildingStore.Slot.transport,BuildingStore.Slot.next] using input.finalSlot.updated_own (.number (rounded (raw row.n) (digits (raw row.n))))

theorem Row.digits_binding (row : Row) (base : Machine) (input : Inputs base row.n) :
    readBinding input.after.heap base.context.lexicalEnvironment "digits"=.ok (.number row.scale) := by
  have actual : readBinding input.afterDigits.heap base.context.lexicalEnvironment "digits"=
      .ok (.number (digits (raw row.n))) := by
    change readBinding (input.localDigits.after (.number (digits (raw row.n)))).heap
      (input.cps.after (.number (raw row.n))).context.lexicalEnvironment "digits"=_
    simp [readBinding,input.localDigits.updated_present (.number (digits (raw row.n))),
      input.localDigits.updated_found (.number (digits (raw row.n))),
      Except.bind,bind,Except.pure,pure]
  have expected : digits (raw row.n)=row.scale := congrArg Prod.snd row.computed
  change readBinding input.afterDigits.heap base.context.lexicalEnvironment "digits"=_
  rw [actual,expected]

theorem Row.other_object (row : Row) (base : Machine) (input : Inputs base row.n)
    (id : ObjectId) (different : id≠input.cps.id) :
    input.after.heap.objects[id]?=base.heap.objects[id]? := by
  have finalDifferent : id≠input.finalSlot.id := different
  calc
    _=input.afterDigits.heap.objects[id]? := input.finalSlot.other_object _ id finalDifferent
    _=input.afterRaw.heap.objects[id]? := rfl
    _=base.heap.objects[id]? := input.cps.other_object _ id different

end CookieClicker.JavaScript.BuildingCpsCases

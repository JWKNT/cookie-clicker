import CookieClicker.JavaScriptGrandmaMagic
import CookieClicker.JavaScriptReadCombinators

namespace CookieClicker.JavaScript.GrandmaReturn
open SourceRead TieredRead GrandmaTiered
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def expression : Expr := .binary .multiply
  (.binary .add (.member (.identifier "me") (.identifier "baseCps") false) (.identifier "add"))
  (.identifier "mult")
def statement : Stmt := (GrandmaSource.body.drop 17).headD .empty

theorem source_statement : statement=.return (some expression) := rfl

theorem local_add (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : GrandmaLocals.Values)
    (suffix : Array LexicalEnvironment) :
    Reads (GrandmaLocals.start base objects leading outer values suffix) (.identifier "add") values.add 3 := by
  apply local_identifier _ "add" values.add (GrandmaLocals.bindings values) (some outer)
  · exact GrandmaLocals.checked_local objects leading outer values suffix
  · exact GrandmaLocals.has_add values
  · exact GrandmaLocals.read_add objects leading outer values suffix

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

theorem native_return (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (value add mult : UInt64) (addValue : state.values.add=.number add)
    (multValue : state.values.mult=.number mult)
    (read : Reads (machine base old state)
      (.member (.identifier "me") (.identifier "baseCps") false) (.number value) 7)
    (fuel : Nat) :
    Builtins.run (21+fuel) {machine base old state with control:=.statement statement}=
      Builtins.run fuel {machine base old state with
        control:=.completion (.return (.number (Number.mul (Number.add value add) mult)))} := by
  have addRead : Reads (machine base old state) (.identifier "add") (.number add) 3 := by
    simpa only [addValue,machine,Reads,GrandmaLocals.start] using
      local_add {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        state.objects old.environments old.closureScope state.values state.suffix
  have multRead : Reads (machine base old state) (.identifier "mult") (.number mult) 3 := by
    simpa only [multValue,machine,Reads,GrandmaLocals.start] using
      GrandmaBody.local_mult {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        state.objects old.environments old.closureScope state.values state.suffix
  have summed:=numeric_add (machine base old state) _ _ value add 7 3 read addRead
  have product:=numeric_multiply (machine base old state) _ _ (Number.add value add) mult 13 3 summed multRead
  rw [source_statement]
  exact return_read (machine base old state) expression _ 19 product fuel

theorem no_upgrade_arithmetic :
    Number.mul (Number.add Number.one Number.positiveZero) Number.one=Number.one := by decide +kernel

end CookieClicker.JavaScript.GrandmaReturn

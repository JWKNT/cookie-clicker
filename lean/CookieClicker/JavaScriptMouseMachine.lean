import CookieClicker.JavaScriptMouseGuards
import CookieClicker.JavaScriptMouseBody
namespace CookieClicker.JavaScript.MouseMachine
abbrev State := MouseGuards.LocalState

def machine (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine :=
  MouseLocals.start {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix

theorem one_mul_one : Number.mul Number.one Number.one=Number.one := by decide +kernel

theorem values_mult_same (values : MouseLocals.Values) (mult : values.mult=.number Number.one) :
    {values with mult:=.number Number.one}=values := by cases values;simp_all

end CookieClicker.JavaScript.MouseMachine

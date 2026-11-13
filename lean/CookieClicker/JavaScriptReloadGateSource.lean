import CookieClicker.JavaScriptReloadGateSyntax
import CookieClicker.JavaScriptBrowserTime

namespace CookieClicker.JavaScript.ReloadGateSource
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option cbv.maxSteps 3000000

def data (name:String) (value:Value) : OwnProperty :=
 ⟨JSString.ofString name,.data value true true true⟩

def start (saved:Value) (elapsed:Rat) : Machine := {
 heap := {
   objects := #[{properties := [data "saveData" saved]},
     {kind := .builtin ⟨"Browser.Timer","setTimeout"⟩}]
   environments := #[⟨.declarative [{name := "App",value := .object 0},
     {name := "setTimeout",value := .object 1}],none⟩]}
 context:=⟨0,0,.undefined,false⟩
 control:=.statement ReloadGateSyntax.scheduling
 globalObject:=0
 elapsed}

def stage (saved:Value) (elapsed:Rat) (ticks:Nat) := Builtins.run ticks (start saved elapsed)

attribute [local cbv_opaque] truthy
@[local cbv_eval] theorem truthy_object (id:ObjectId) : truthy (.object id)=true := rfl
@[local cbv_eval] theorem truthy_boolean (value:Bool) : truthy (.boolean value)=value := rfl

theorem native_request (saved:Value) (elapsed:Rat) :
 (stage saved elapsed 28).control=.unresolved (.builtin ⟨"Browser.Timer","setTimeout"⟩
   .undefined [.object 2,.number 4636737291354636288] false) := by
 cases h:truthy saved <;> cbv <;> simp only [h] <;> cbv

theorem native_elapsed (saved:Value) (elapsed:Rat) :
 (stage saved elapsed 28).elapsed=elapsed := by
 cases h:truthy saved <;> cbv <;> simp only [h] <;> cbv

end CookieClicker.JavaScript.ReloadGateSource

import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptGodzamokSyntax
import CookieClicker.JavaScriptLumpSyntax
import CookieClicker.JavaScriptProductionSyntax
import CookieClicker.JavaScriptBuiltins

/-! The intact Cursor price helper graph for the proposed fixed route profile.
All source callbacks are retained. This explicit heap is a source entry profile;
its correspondence to initialized game objects is a separate obligation. -/
namespace CookieClicker.JavaScript.CursorPriceState
set_option maxRecDepth 262144
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 8000000
private def key := JSString.ofString
private def data (name : String) (value : Value) : OwnProperty := ⟨key name,.data value true true true⟩
private def fields (properties : List (String × Value)) : JSObject :=
  { properties := properties.map fun (name,value) => data name value }
private def fn (parameters : List String) (body : Stmt) : JSObject :=
  { kind := .function ⟨none,parameters,(match body with | .block statements => statements | other => [other]),0,false,none⟩ }
private def native (name : String) : JSObject := {kind := .builtin ⟨"Math",name⟩}
private def n (value : Nat) : Value := .number (Number.ofNat value)
private def unowned : JSObject := fields [("bought",n 0)]

def objects (owned free : Bool) (bank multiplier bought : UInt64) : Array JSObject := #[
  fields [("priceIncrease",.number 4607857958744122982),("modifyBuildingPrice",.object 3),
    ("Has",.object 5),("auraMult",.object 6),("hasBuff",.object 7),("eff",.object 8),("hasGod",.object 9),
    ("Upgrades",.object 10),("ascensionMode",n 0),("effs",.object 17),("buffs",.object 18),
    ("dragonAura",n 0),("dragonAura2",n 0),("dragonAuras",.object 19),
    ("cookies",.number bank)],
  fields [("basePrice",n 15),("amount",n (if owned then 1 else 0)),("free",n (if free then 10 else 0)),
    ("getPrice",.object 2),("getSellMultiplier",.object 4),("fortune",.object 16),("bought",.number bought)],
  fn ["n"] CursorCycleSyntax.getPriceBody,
  fn ["building","price"] CursorCycleSyntax.modifyBuildingPriceBody,
  fn [] CursorCycleSyntax.getSellMultiplierBody,
  fn ["what"] LumpSyntax.HasBody,
  fn ["what"] LumpSyntax.auraMultBody,
  fn ["what"] GodzamokSyntax.hasBuffBody,
  fn ["name","def"] ProductionSyntax.effBody,
  fn ["what"] LumpSyntax.hasGodBody,
  fields [("Season savings",.object 11),("Santa's dominion",.object 12),("Faberge egg",.object 13),
    ("Divine discount",.object 14),("Fortune #100",.object 15),("Fortune #001",.object 16)],
  unowned,unowned,unowned,unowned,unowned,
  fields [("name",.string (key "Fortune #001")),("bought",n 0)],
  fields [],
  fields [("Devastation",.object 31)],
  fields [("0",.object 20)],
  fields [("name",.string (key "No aura"))],
  fields [("gods",.object 22),("slot",.object 25)],
  fields [("ruin",.object 23),("creation",.object 24)],
  fields [("id",n 2)],
  fields [("id",n 5)],
  {kind := .array, properties := [data "0" (n 2),data "1" (.number 13830554455654793216),
    data "2" (.number 13830554455654793216),⟨key "length",.data (n 3) true false false⟩]},
  fields [("max",.object 27),("pow",.object 28),("ceil",.object 29),("floor",.object 30)],
  native "max",native "pow",native "ceil",native "floor",
  fields [("multClick",.number multiplier),("time",n 300)] ]

def state (owned free : Bool) (bank multiplier bought : UInt64) (method : String := "getPrice") : Machine := {
  heap := {
    objects := objects owned free bank multiplier bought
    environments := #[⟨.declarative [
      {name := "Game",value := .object 0},{name := "cursor",value := .object 1},
      {name := "M",value := .object 21},{name := "Math",value := .object 26}],none⟩] }
  context := ⟨0,0,.object 0,false⟩
  globalObject := 0
  control := .expression (.call (.member (.identifier "cursor") (.identifier method) false) []) }

def result (owned free : Bool) (bank multiplier bought : UInt64) (method : String := "getPrice") : Machine :=
  Builtins.run 3000 (state owned free bank multiplier bought method)


end CookieClicker.JavaScript.CursorPriceState

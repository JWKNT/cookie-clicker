import CookieClicker.JavaScriptPriceGod

/-! The complete native modifyBuildingPrice body for the stated unowned
upgrade, no-price-buff, no-aura and diamond-Godzamok profile. All thirteen
source statements and twelve source calls execute with retained allocations. -/
namespace CookieClicker.JavaScript.PriceComplete
open SourceRead TieredRead PriceStages PriceCalls PriceStatements
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def upgradeAfter {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : TieredSuffix.HasZero (machine base leading outer s) what) : State :=
  afterHas base leading outer s h.scopes.closureScope h.function h.frame.upgrade what

def yes (index : Nat) : Stmt := match statement index with | .ifThenElse _ result _=>result | _=>.empty

structure Inputs (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) where
  savings : TieredSuffix.HasZero (machine base leading outer s) (JSString.ofString "Season savings")
  santa : TieredSuffix.HasZero (machine base leading outer (upgradeAfter savings)) (JSString.ofString "Santa's dominion")
  egg : TieredSuffix.HasZero (machine base leading outer (upgradeAfter santa)) (JSString.ofString "Faberge egg")
  divine : TieredSuffix.HasZero (machine base leading outer (upgradeAfter egg)) (JSString.ofString "Divine discount")
  fortune100 : TieredSuffix.HasZero (machine base leading outer (upgradeAfter divine)) (JSString.ofString "Fortune #100")
  aura : Aura (machine base leading outer (upgradeAfter fortune100)) auraName
  everything : Buff (machine base leading outer aura.after) (JSString.ofString "Everything must go")
  pixies : Buff (machine base leading outer everything.after) (JSString.ofString "Crafty pixies")
  goblins : Buff (machine base leading outer pixies.after) (JSString.ofString "Nasty goblins")
  fortuneName : JSString
  fortuneHas : TieredSuffix.HasZero (machine base leading outer goblins.after) fortuneName
  building : ObjectId
  fortuneUpgrade : ObjectId
  buildingValue : s.values.building=.object building
  fortuneSelected : DataEdge (machine base leading outer goblins.after) building
    (JSString.ofString "fortune") (.object fortuneUpgrade)
  fortuneNameRead : DataEdge (machine base leading outer goblins.after) fortuneUpgrade
    (JSString.ofString "name") (.string fortuneName)
  effect : Effect (machine base leading outer (upgradeAfter fortuneHas)) effectName
  god : PriceGod.Inputs (machine base leading outer effect.after)

def Inputs.final {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs base leading outer s) : State := h.god.after

theorem Inputs.final_values {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs base leading outer s) : h.final.values={s.values with godLvl:=.boolean false} := rfl

theorem native_return (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (price : UInt64) (value : s.values.price=.number price) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (5+fuel) {machine base leading outer s with control:=.statement (statement 12),continuation}=
      Builtins.run fuel {machine base leading outer s with control:=.completion (.return (.number price)),continuation} := by
  have read : Reads (machine base leading outer s) (.identifier "price") (.number price) 3 := by
    simpa only [value,machine] using PriceArithmetic.local_price base s.objects leading outer s.values s.suffix
  exact return_read {machine base leading outer s with continuation} _ _ 3 read fuel

attribute [local cbv_opaque] machine

theorem Inputs.native_body {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs base leading outer s) (price : UInt64) (value : s.values.price=.number price)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1152+fuel) (machine base leading outer s)=
      Builtins.run fuel {machine base leading outer h.final with control:=.completion (.return (.number price))} := by
  rw [show 1152+fuel=1+(1151+fuel) by omega,Nat.add_comm 1 (1151+fuel)]
  change Builtins.run (1151+fuel) {machine base leading outer s with
    control:=.statement (statement 0),continuation:=.statementList (PriceSource.body.drop 1) none::base.continuation}=_
  change Builtins.run (1151+fuel) {machine base leading outer s with
    control:=.statement (hasStatement (JSString.ofString "Season savings") (yes 0)),continuation:=.statementList (PriceSource.body.drop 1) none::base.continuation}=_
  rw [show 1151+fuel=81+(1070+fuel) by omega,native_has_false base leading outer s (JSString.ofString "Season savings") (yes 0) h.savings,
    show 1070+fuel=1+(1069+fuel) by omega,Nat.add_comm 1 (1069+fuel)]
  change Builtins.run (1069+fuel) {machine base leading outer (upgradeAfter h.savings) with
    control:=.statement (statement 1),continuation:=.statementList (PriceSource.body.drop 2) none::base.continuation}=_
  change Builtins.run (1069+fuel) {machine base leading outer (upgradeAfter h.savings) with
    control:=.statement (hasStatement (JSString.ofString "Santa's dominion") (yes 1)),continuation:=.statementList (PriceSource.body.drop 2) none::base.continuation}=_
  rw [show 1069+fuel=81+(988+fuel) by omega,native_has_false base leading outer (upgradeAfter h.savings) (JSString.ofString "Santa's dominion") (yes 1) h.santa,
    show 988+fuel=1+(987+fuel) by omega,Nat.add_comm 1 (987+fuel)]
  change Builtins.run (987+fuel) {machine base leading outer (upgradeAfter h.santa) with
    control:=.statement (statement 2),continuation:=.statementList (PriceSource.body.drop 3) none::base.continuation}=_
  change Builtins.run (987+fuel) {machine base leading outer (upgradeAfter h.santa) with
    control:=.statement (hasStatement (JSString.ofString "Faberge egg") (yes 2)),continuation:=.statementList (PriceSource.body.drop 3) none::base.continuation}=_
  rw [show 987+fuel=81+(906+fuel) by omega,native_has_false base leading outer (upgradeAfter h.santa) (JSString.ofString "Faberge egg") (yes 2) h.egg,
    show 906+fuel=1+(905+fuel) by omega,Nat.add_comm 1 (905+fuel)]
  change Builtins.run (905+fuel) {machine base leading outer (upgradeAfter h.egg) with
    control:=.statement (statement 3),continuation:=.statementList (PriceSource.body.drop 4) none::base.continuation}=_
  change Builtins.run (905+fuel) {machine base leading outer (upgradeAfter h.egg) with
    control:=.statement (hasStatement (JSString.ofString "Divine discount") (yes 3)),continuation:=.statementList (PriceSource.body.drop 4) none::base.continuation}=_
  rw [show 905+fuel=81+(824+fuel) by omega,native_has_false base leading outer (upgradeAfter h.egg) (JSString.ofString "Divine discount") (yes 3) h.divine,
    show 824+fuel=1+(823+fuel) by omega,Nat.add_comm 1 (823+fuel)]
  change Builtins.run (823+fuel) {machine base leading outer (upgradeAfter h.divine) with
    control:=.statement (statement 4),continuation:=.statementList (PriceSource.body.drop 5) none::base.continuation}=_
  change Builtins.run (823+fuel) {machine base leading outer (upgradeAfter h.divine) with
    control:=.statement (hasStatement (JSString.ofString "Fortune #100") (yes 4)),continuation:=.statementList (PriceSource.body.drop 5) none::base.continuation}=_
  rw [show 823+fuel=81+(742+fuel) by omega,native_has_false base leading outer (upgradeAfter h.divine) (JSString.ofString "Fortune #100") (yes 4) h.fortune100,
    show 742+fuel=1+(741+fuel) by omega,Nat.add_comm 1 (741+fuel)]
  change Builtins.run (741+fuel) {machine base leading outer (upgradeAfter h.fortune100) with
    control:=.statement (statement 5),continuation:=.statementList (PriceSource.body.drop 6) none::base.continuation}=_
  rw [show 741+fuel=179+(562+fuel) by omega,native_aura h.aura price value stable,
    show 562+fuel=1+(561+fuel) by omega,Nat.add_comm 1 (561+fuel)]
  change Builtins.run (561+fuel) {machine base leading outer h.aura.after with
    control:=.statement (statement 6),continuation:=.statementList (PriceSource.body.drop 7) (some (.number price))::base.continuation}=_
  change Builtins.run (561+fuel) {machine base leading outer h.aura.after with
    control:=.statement (buffStatement (JSString.ofString "Everything must go") (yes 6)),continuation:=.statementList (PriceSource.body.drop 7) (some (.number price))::base.continuation}=_
  rw [show 561+fuel=44+(517+fuel) by omega,native_buff h.everything (yes 6),
    show 517+fuel=1+(516+fuel) by omega,Nat.add_comm 1 (516+fuel)]
  change Builtins.run (516+fuel) {machine base leading outer h.everything.after with
    control:=.statement (statement 7),continuation:=.statementList (PriceSource.body.drop 8) (some (.number price))::base.continuation}=_
  change Builtins.run (516+fuel) {machine base leading outer h.everything.after with
    control:=.statement (buffStatement (JSString.ofString "Crafty pixies") (yes 7)),continuation:=.statementList (PriceSource.body.drop 8) (some (.number price))::base.continuation}=_
  rw [show 516+fuel=44+(472+fuel) by omega,native_buff h.pixies (yes 7),
    show 472+fuel=1+(471+fuel) by omega,Nat.add_comm 1 (471+fuel)]
  change Builtins.run (471+fuel) {machine base leading outer h.pixies.after with
    control:=.statement (statement 8),continuation:=.statementList (PriceSource.body.drop 9) (some (.number price))::base.continuation}=_
  change Builtins.run (471+fuel) {machine base leading outer h.pixies.after with
    control:=.statement (buffStatement (JSString.ofString "Nasty goblins") (yes 8)),continuation:=.statementList (PriceSource.body.drop 9) (some (.number price))::base.continuation}=_
  rw [show 471+fuel=44+(427+fuel) by omega,native_buff h.goblins (yes 8),
    show 427+fuel=1+(426+fuel) by omega,Nat.add_comm 1 (426+fuel)]
  change Builtins.run (426+fuel) {machine base leading outer h.goblins.after with
    control:=.statement (statement 9),continuation:=.statementList (PriceSource.body.drop 10) (some (.number price))::base.continuation}=_
  rw [show 426+fuel=101+(325+fuel) by omega,native_fortune h.fortuneHas h.building h.fortuneUpgrade h.buildingValue h.fortuneSelected h.fortuneNameRead,
    show 325+fuel=1+(324+fuel) by omega,Nat.add_comm 1 (324+fuel)]
  change Builtins.run (324+fuel) {machine base leading outer (upgradeAfter h.fortuneHas) with
    control:=.statement (statement 10),continuation:=.statementList (PriceSource.body.drop 11) (some (.number price))::base.continuation}=_
  rw [show 324+fuel=68+(256+fuel) by omega,native_effect h.effect price value stable,
    show 256+fuel=1+(255+fuel) by omega,Nat.add_comm 1 (255+fuel)]
  change Builtins.run (255+fuel) {machine base leading outer h.effect.after with
    control:=.statement (statement 11),continuation:=.statementList (PriceSource.body.drop 12) (some (.number price))::base.continuation}=_
  rw [show 255+fuel=248+(7+fuel) by omega,h.god.native_statement,
    show 7+fuel=1+(6+fuel) by omega,Nat.add_comm 1 (6+fuel)]
  change Builtins.run (6+fuel) {machine base leading outer h.final with
    control:=.statement (statement 12),
    continuation:=.statementList [] (some (.number price))::base.continuation}=_
  rw [show 6+fuel=5+(1+fuel) by omega,native_return base leading outer h.final price value,
    Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.PriceComplete

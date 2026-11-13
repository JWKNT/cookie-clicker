import CookieClicker.JavaScriptPriceRegistryHelpers

/-! Complete price execution from one entry catalogue. All later Has, aura,
buff, effect and Pantheon frames are constructed from the same original heap,
using the already-proved allocation frames for the preceding source calls. -/
namespace CookieClicker.JavaScript.PriceRegistryComplete
open SourceRead TieredRead PriceStages PriceRegistryScope PriceRegistry PriceRegistryHelpers
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure Profile {base : Machine} (world : World base) where
  savings : Upgrade world (JSString.ofString "Season savings")
  santa : Upgrade world (JSString.ofString "Santa's dominion")
  egg : Upgrade world (JSString.ofString "Faberge egg")
  divine : Upgrade world (JSString.ofString "Divine discount")
  fortune100 : Upgrade world (JSString.ofString "Fortune #100")
  fortuneName : JSString
  fortune : Upgrade world fortuneName
  building : ObjectId
  fortuneUpgrade : ObjectId
  fortuneSelected : DataEdge base building (JSString.ofString "fortune") (.object fortuneUpgrade)
  fortuneNameRead : DataEdge base fortuneUpgrade (JSString.ofString "name") (.string fortuneName)
  everything : lookupProperty base.heap world.buffTable (JSString.ofString "Everything must go")=.ok none
  pixies : lookupProperty base.heap world.buffTable (JSString.ofString "Crafty pixies")=.ok none
  goblins : lookupProperty base.heap world.buffTable (JSString.ofString "Nasty goblins")=.ok none
  effect : lookupProperty base.heap world.effectTable PriceStatements.effectName=.ok none
  god : God world

def construct {base : Machine} (world : World base) (profile : Profile world) (s : State)
    (extension : HeapExtension.Extends base.heap (current world s).heap)
    (building : s.values.building=.object profile.building) :
    PriceComplete.Inputs base base.heap.environments world.priceScope.path.closureScope s := by
  let savings:=upgrade profile.savings s extension
  let s1:=PriceComplete.upgradeAfter savings
  have e1:=upgrade_extends profile.savings s extension
  let santa:=upgrade profile.santa s1 e1
  let s2:=PriceComplete.upgradeAfter santa
  have e2:=upgrade_extends profile.santa s1 e1
  let egg:=upgrade profile.egg s2 e2
  let s3:=PriceComplete.upgradeAfter egg
  have e3:=upgrade_extends profile.egg s2 e2
  let divine:=upgrade profile.divine s3 e3
  let s4:=PriceComplete.upgradeAfter divine
  have e4:=upgrade_extends profile.divine s3 e3
  let fortune100:=upgrade profile.fortune100 s4 e4
  let s5:=PriceComplete.upgradeAfter fortune100
  have e5:=upgrade_extends profile.fortune100 s4 e4
  let aura:=PriceRegistryHelpers.aura world s5 PriceStatements.auraName e5 (by decide)
  let s6:=aura.after
  have e6:=HeapExtension.trans e5 (PriceRetention.aura aura)
  let everything:=buff world s6 (JSString.ofString "Everything must go") e6 profile.everything
  let s7:=everything.after
  have e7:=HeapExtension.trans e6 (PriceRetention.buff everything)
  let pixies:=buff world s7 (JSString.ofString "Crafty pixies") e7 profile.pixies
  let s8:=pixies.after
  have e8:=HeapExtension.trans e7 (PriceRetention.buff pixies)
  let goblins:=buff world s8 (JSString.ofString "Nasty goblins") e8 profile.goblins
  let s9:=goblins.after
  have e9:=HeapExtension.trans e8 (PriceRetention.buff goblins)
  let fortune:=upgrade profile.fortune s9 e9
  let s10:=PriceComplete.upgradeAfter fortune
  have e10:=upgrade_extends profile.fortune s9 e9
  let effect:=PriceRegistryHelpers.effect world s10 PriceStatements.effectName e10 profile.effect
  let s11:=effect.after
  have e11:=HeapExtension.trans e10 (PriceRetention.effect effect)
  let god:=PriceRegistryHelpers.god profile.god s11 e11
  exact {
    savings,santa,egg,divine,fortune100,aura,everything,pixies,goblins
    fortuneName:=profile.fortuneName,fortuneHas:=fortune
    building:=profile.building,fortuneUpgrade:=profile.fortuneUpgrade
    buildingValue:=building
    fortuneSelected:=profile.fortuneSelected.extend e9
    fortuneNameRead:=profile.fortuneNameRead.extend e9
    effect,god }

theorem native_body {base : Machine} (world : World base) (profile : Profile world) (s : State)
    (extension : HeapExtension.Extends base.heap (current world s).heap)
    (building : s.values.building=.object profile.building)
    (price : UInt64) (value : s.values.price=.number price)
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1152+fuel) (current world s)=
      Builtins.run fuel {current world (construct world profile s extension building).final with
        control:=.completion (.return (.number price))} :=
  (construct world profile s extension building).native_body price value stable fuel

theorem retained_objects {base : Machine} (world : World base) (profile : Profile world) (s : State)
    (extension : HeapExtension.Extends base.heap (current world s).heap)
    (building : s.values.building=.object profile.building) :
    HeapExtension.Extends base.heap
      (current world (construct world profile s extension building).final).heap :=
  HeapExtension.trans extension (PriceRetention.body_extends (construct world profile s extension building))

end CookieClicker.JavaScript.PriceRegistryComplete

import Lean
import CookieClicker.Inventory
import CookieClicker.JavaScriptNumberString

/-! Parser for normalized JSON observations. Parser correctness is not a
formal refinement proof for the game JavaScript extractor. -/
namespace CookieClicker.FullGame
open Lean

private def field (j : Json) (name : String) : Except String Json := j.getObjVal? name

private def textField (j : Json) (name : String) : Except String String := do
  (← field j name).getStr?

private def countField (j : Json) (name : String) : Except String Nat := do
  let value ← field j name
  let .num _ := value | throw s!"Number required: {name}"
  -- JSON observations carry native Numbers. Parse their decimal text with the
  -- same binary64 conversion, including values outside the safe-integer range.
  let bits := JavaScript.NumberString.toNumber (JavaScript.JSString.ofString value.compress)
  if JavaScript.Number.isFinite bits && JavaScript.Number.isInteger bits &&
      !(JavaScript.Number.lessThan bits JavaScript.Number.positiveZero) then
    return (JavaScript.Number.truncateInt bits).toNat
  throw s!"Nonnegative finite integer required: {name}"

private def recordField (j : Json) (name : String) : Except String Json := do
  let value ← field j name
  let _ ← value.getObj?
  return value

private def stringsField (j : Json) (name : String) : Except String (List String) := do
  let values ← (← field j name).getArr?
  let values ← values.toList.mapM Json.getStr?
  if values.eraseDups.length != values.length then throw s!"Duplicate entries: {name}"
  return values

private def observedBool (j : Json) (name : String) : Bool :=
  ((field j name).bind Json.getBool?).toOption.getD false

private def observedCount (j : Json) (name : String) : Nat :=
  (countField j name).toOption.getD 0

/-- Decode only normalized observations. Malformed required fields fail closed. -/
def decodeSnapshot (j : Json) : Except String Snapshot := do
  let r := Pinned.requirements
  let schemaVersion ← countField j "schemaVersion"
  let gameVersion ← textField j "gameVersion"
  let edition ← textField j "edition"
  let achievements ← recordField j "achievements"
  let upgrades ← recordField j "upgrades"
  let p ← recordField j "progression"
  let history ← recordField j "history"
  let historyGameVersion ← textField history "gameVersion"
  let historyEdition ← textField history "edition"
  let accessed ← stringsField history "accessedUpgrades"
  let seeds ← stringsField p "gardenSeeds"
  let spells ← stringsField p "grimoireSpells"
  let gods ← stringsField p "pantheonGods"
  let levels ← recordField p "buildingLevels"
  let amounts ← recordField p "buildingAmounts"
  let highest ← recordField p "buildingHighest"
  let minigames ← recordField p "minigames"
  for (name, _) in r.buildingLevels do
    let _ ← countField levels name
  let _ ← countField levels "Farm"
  let _ ← countField amounts "Farm"
  for (name, _) in r.marketGoods do
    let _ ← countField highest name
  let achievementsOwned ← countField p "achievementsOwned"
  let dragonLevel ← countField p "dragonLevel"
  let santaLevel ← countField p "santaLevel"
  let ascensionMode ← countField p "ascensionMode"
  let onAscend ← (← field p "onAscend").getBool?
  let ascendTimer ← countField p "ascendTimer"
  let reincarnateTimer ← countField p "reincarnateTimer"
  let stockOfficeLevel ← countField p "stockOfficeLevel"
  return {
    schemaVersion, gameVersion, edition, historyGameVersion, historyEdition,
    achievements := observedBool achievements, achievementsOwned,
    upgrades := fun name => {
      bought := observedBool ((field upgrades name).toOption.getD Json.null) "bought"
      unlocked := observedBool ((field upgrades name).toOption.getD Json.null) "unlocked" },
    accessedUpgrades := accessed.contains,
    dragonLevel, santaLevel, ascensionMode, onAscend, ascendTimer, reincarnateTimer,
    buildingLevels := observedCount levels,
    buildingAmounts := observedCount amounts,
    buildingHighest := observedCount highest,
    minigames := observedBool minigames,
    gardenSeeds := seeds.contains,
    stockOfficeLevel,
    grimoireSpells := spells.contains,
    pantheonGods := gods.contains }

end CookieClicker.FullGame

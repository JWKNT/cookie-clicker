/** Synthetic predicate fixtures. These observations are not reachable-state certificates. */
import { readFileSync } from 'node:fs';
export const r = JSON.parse(readFileSync(new URL('../model/completion-requirements.json', import.meta.url)));
export const terminal = {
  schemaVersion: 1, gameVersion: r.gameVersion, edition: r.edition,
  achievements: Object.fromEntries(r.normalAchievements.map(x => [x.name, true])),
  upgrades: Object.fromEntries([...r.ownedUpgrades, ...r.accessUpgrades]
    .map(x => [x.name, { bought: true, unlocked: true }])),
  history: { gameVersion: r.gameVersion, edition: r.edition, accessedUpgrades: [] },
  progression: {
    achievementsOwned: r.normalAchievements.length,
    dragonLevel: r.dragonLevel, santaLevel: r.santaLevel, ascensionMode: r.ascensionMode,
    onAscend: false, ascendTimer: 0, reincarnateTimer: 0,
    buildingLevels: Object.fromEntries(r.buildingLevels.map(x => [x.building, x.level])),
    buildingAmounts: { Farm: Math.max(...r.soils.map(x => x.farmAmount)) },
    buildingHighest: Object.fromEntries(r.marketGoods.map(x => [x.building, x.highest])),
    minigames: Object.fromEntries(r.minigames.map(x => [x.building, true])),
    gardenSeeds: r.seeds.map(x => x.key), stockOfficeLevel: r.officeLevel,
    grimoireSpells: r.spells.map(x => x.key), pantheonGods: r.gods.map(x => x.key),
  },
};

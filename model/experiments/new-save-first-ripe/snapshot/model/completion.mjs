/**
 * Terminal predicate for the pinned vanilla game and explicit completion profile.
 * This module reads normalized data. It does not mutate a game or prove that a
 * supplied snapshot can be reached by legal play.
 */

const isRecord = value => value !== null && typeof value === 'object' && !Array.isArray(value);
// Threshold checks need the represented integer, not exact unit increments.
// Native binary64 counts at and above 2^53 remain valid nonnegative integers.
const isCount = value => Number.isInteger(value) && value >= 0;
const identity = ({ id, name }) => ({ id, name });
const unique = (items, key, label) => {
  if (!Array.isArray(items) || new Set(items.map(x => x[key])).size !== items.length) {
    throw new Error(`Invalid or duplicate ${label}`);
  }
};

/** Select every required identity; unknown pools are errors, not exclusions. */
export function buildCompletionContract(catalogue, profile) {
  if (catalogue.schemaVersion !== 1 || profile.schemaVersion !== 1
      || catalogue.gameVersion !== profile.gameVersion || catalogue.edition !== profile.edition) {
    throw new Error('Completion catalogue/profile version or edition mismatch');
  }
  for (const field of ['achievements', 'upgrades', 'buildings']) {
    unique(catalogue[field], 'id', `${field} IDs`);
    unique(catalogue[field], 'name', `${field} names`);
  }
  const achievementPools = new Set(profile.achievementPools);
  const ownedPools = new Set(profile.upgradeOwnershipPools);
  const accessPools = new Set(profile.upgradeAccessPools);
  const ignoredAchievementPools = new Set(profile.excludedAchievementPools);
  const ignoredUpgradePools = new Set(profile.excludedUpgradePools);
  for (const item of catalogue.achievements) {
    if (!achievementPools.has(item.pool) && !ignoredAchievementPools.has(item.pool)) {
      throw new Error(`Unclassified achievement pool: ${item.pool}`);
    }
    if (item.normal !== achievementPools.has(item.pool)) throw new Error(`Normal-achievement classification differs: ${item.name}`);
  }
  for (const item of catalogue.upgrades) {
    if (![ownedPools, accessPools, ignoredUpgradePools].some(pools => pools.has(item.pool))) {
      throw new Error(`Unclassified upgrade pool: ${item.pool}`);
    }
  }
  const excluded = new Set(profile.sugarAchievementExclusions.map(x => x.name));
  if (excluded.size !== profile.sugarAchievementExclusions.length) throw new Error('Duplicate sugar achievement exclusion');
  for (const name of excluded) {
    if (!catalogue.achievements.some(x => x.name === name && x.normal && x.vanilla)) {
      throw new Error(`Sugar exclusion is not a vanilla normal achievement: ${name}`);
    }
  }
  for (const name of profile.retainedSugarAchievements) {
    if (excluded.has(name) || !catalogue.achievements.some(x => x.name === name && x.normal && x.vanilla)) {
      throw new Error(`Required sugar achievement is excluded or absent: ${name}`);
    }
  }
  const buildings = new Map(catalogue.buildings.map(x => [x.name, x]));
  const buildingIds = new Map(catalogue.buildings.map(x => [x.id, x.name]));
  const buildingLevels = Object.entries(profile.requiredBuildingLevels).map(([building, level]) => {
    if (!buildings.has(building) || !isCount(level)) throw new Error(`Invalid required building level: ${building}`);
    return { building, level };
  });
  const minigames = Object.entries(profile.requiredMinigames).map(([building, name]) => {
    if (buildings.get(building)?.minigame !== name) throw new Error(`Unknown minigame: ${building}/${name}`);
    return { building, name };
  });
  const maximumId = items => Math.max(...items.map(x => x.id));
  const contract = {
    schemaVersion: 1, profileId: profile.id, profileVersion: profile.version,
    gameVersion: catalogue.gameVersion, edition: catalogue.edition, sourceHashes: { ...catalogue.sourceHashes },
    normalAchievements: catalogue.achievements.filter(x => x.vanilla && x.normal).map(identity),
    minimumNormalAchievements: Math.max(...catalogue.cosmetics.milks.map(x => (x.rank ?? 0) * 25)),
    requiredAchievements: catalogue.achievements.filter(x => x.vanilla && x.normal && !excluded.has(x.name)).map(identity),
    excludedAchievements: catalogue.achievements.filter(x => excluded.has(x.name)).map(identity),
    ownedUpgrades: catalogue.upgrades.filter(x => x.vanilla && ownedPools.has(x.pool)).map(identity),
    accessUpgrades: catalogue.upgrades.filter(x => x.vanilla && accessPools.has(x.pool)).map(identity),
    seeds: catalogue.garden.seeds.map(({ id, key }) => ({ id, key })),
    soils: catalogue.garden.soils.map(({ id, key, req }) => ({ id, key, farmAmount: req })),
    minigames, buildingLevels,
    marketGoods: catalogue.market.goods.map(({ id, building }) => {
      if (!buildingIds.has(building)) throw new Error(`Unknown market-good building: ${building}`);
      return { id, building: buildingIds.get(building), highest: 1 };
    }),
    loans: catalogue.market.loans.map(({ id, minOfficeLevel }) => ({ id, officeLevel: minOfficeLevel })),
    spells: catalogue.grimoire.spells.map(({ id, key }) => ({ id, key })),
    gods: catalogue.pantheon.gods.map(({ id, key }) => ({ id, key })),
    dragonLevel: maximumId(catalogue.dragon.levels),
    santaLevel: maximumId(catalogue.santa.levels),
    officeLevel: maximumId(catalogue.market.offices),
    gardenLevel: catalogue.garden.plotLimits.length,
    ascensionMode: profile.normalAscensionMode,
  };
  for (const field of ['seeds', 'soils', 'spells', 'gods']) unique(contract[field], 'key', field);
  return contract;
}

/**
 * Report unmet terminal conditions. `valid` means structurally valid input;
 * legality and provenance of a trajectory are separate model obligations.
 */
export function assessCompletion(snapshot, contract) {
  const issues = [];
  const missing = [];
  let requiredCount = 0;
  const check = (category, key, condition, required, actual) => {
    requiredCount++;
    if (!condition) missing.push({ category, key, required, actual: actual ?? null });
  };
  if (!isRecord(snapshot)) return { complete: false, valid: false, profileId: contract.profileId,
    requiredCount: 0, satisfiedCount: 0, missing, issues: ['Snapshot must be an object'] };
  if (snapshot.schemaVersion !== 1) issues.push('Snapshot schemaVersion must be 1');
  if (snapshot.gameVersion !== contract.gameVersion) issues.push('Game version differs from completion contract');
  if (snapshot.edition !== contract.edition) issues.push('Game edition differs from completion contract');
  const section = name => {
    if (!isRecord(snapshot[name])) issues.push(`Missing or invalid ${name}`);
    return isRecord(snapshot[name]) ? snapshot[name] : {};
  };
  const achievements = section('achievements');
  const upgrades = section('upgrades');
  const progression = section('progression');
  const history = section('history');
  const stringSet = (value, name) => {
    if (!Array.isArray(value) || value.some(x => typeof x !== 'string') || new Set(value).size !== value.length) {
      issues.push(`Invalid ${name}: expected distinct strings`);
      return new Set();
    }
    return new Set(value);
  };
  const accessed = stringSet(history.accessedUpgrades, 'history.accessedUpgrades');
  if (history.gameVersion !== contract.gameVersion) issues.push('Upgrade access history has a different game version');
  if (history.edition !== contract.edition) issues.push('Upgrade access history has a different game edition');
  const seeds = stringSet(progression.gardenSeeds, 'progression.gardenSeeds');
  const spells = stringSet(progression.grimoireSpells, 'progression.grimoireSpells');
  const gods = stringSet(progression.pantheonGods, 'progression.pantheonGods');
  const levels = isRecord(progression.buildingLevels) ? progression.buildingLevels : {};
  const amounts = isRecord(progression.buildingAmounts) ? progression.buildingAmounts : {};
  const highest = isRecord(progression.buildingHighest) ? progression.buildingHighest : {};
  const minigames = isRecord(progression.minigames) ? progression.minigames : {};
  const normalAchievementsOwned = contract.normalAchievements.filter(x => achievements[x.name] === true).length;
  const countCheck = (category, key, actual, required, exact = false) => {
    if (!isCount(actual)) issues.push(`Invalid nonnegative integer: ${category}.${key}`);
    check(category, key, isCount(actual) && (exact ? actual === required : actual >= required), required, actual);
  };
  for (const { name } of contract.requiredAchievements) check('achievement', name, achievements[name] === true, true, achievements[name]);
  check('cosmeticUnlock', 'milkChoices', normalAchievementsOwned >= contract.minimumNormalAchievements,
    contract.minimumNormalAchievements, normalAchievementsOwned);
  // The native milk selector reads this counter, not a recount of won flags.
  countCheck('progression', 'achievementsOwned', progression.achievementsOwned, contract.minimumNormalAchievements);
  for (const { name } of contract.ownedUpgrades) check('ownedUpgrade', name, upgrades[name]?.bought === true, true, upgrades[name]?.bought);
  for (const { name } of contract.accessUpgrades) {
    const present = upgrades[name]?.unlocked === true || upgrades[name]?.bought === true
      || (history.gameVersion === contract.gameVersion && history.edition === contract.edition && accessed.has(name));
    check('accessUpgrade', name, present, true, present);
  }
  for (const { building, name } of contract.minigames) check('minigame', name, minigames[building] === true, true, minigames[building]);
  for (const { building, level } of contract.buildingLevels) countCheck('buildingLevel', building, levels[building], level);
  for (const { key } of contract.seeds) check('gardenSeed', key, seeds.has(key), true, seeds.has(key));
  for (const { key, farmAmount } of contract.soils) countCheck('gardenSoil', key, amounts.Farm, farmAmount);
  for (const { id, building, highest: threshold } of contract.marketGoods) countCheck('marketGood', String(id), highest[building], threshold);
  for (const { id, officeLevel } of contract.loans) countCheck('marketLoan', String(id), progression.stockOfficeLevel, officeLevel);
  for (const { key } of contract.spells) check('grimoireSpell', key, spells.has(key), true, spells.has(key));
  for (const { key } of contract.gods) check('pantheonGod', key, gods.has(key), true, gods.has(key));
  countCheck('progression', 'dragonLevel', progression.dragonLevel, contract.dragonLevel);
  countCheck('progression', 'santaLevel', progression.santaLevel, contract.santaLevel);
  countCheck('progression', 'stockOfficeLevel', progression.stockOfficeLevel, contract.officeLevel);
  countCheck('progression', 'gardenLevel', levels.Farm, contract.gardenLevel);
  countCheck('progression', 'ascensionMode', progression.ascensionMode, contract.ascensionMode, true);
  check('progression', 'onAscend', progression.onAscend === false, false, progression.onAscend);
  countCheck('progression', 'ascendTimer', progression.ascendTimer, 0, true);
  countCheck('progression', 'reincarnateTimer', progression.reincarnateTimer, 0, true);
  return { complete: issues.length === 0 && missing.length === 0, valid: issues.length === 0,
    profileId: contract.profileId, requiredCount, satisfiedCount: requiredCount - missing.length,
    missing, issues: [...new Set(issues)] };
}

/** Read current game fields without calls to game actions or mutation of a save. */
export function captureCompletionSnapshot(game, previousHistory = {}, { edition } = {}) {
  const gameVersion = String(game.version);
  const objects = Object.values(game.Objects || {});
  const upgrades = Object.values(game.Upgrades || {});
  const previousAccess = previousHistory.gameVersion === gameVersion && previousHistory.edition === edition
    && Array.isArray(previousHistory.accessedUpgrades)
    ? previousHistory.accessedUpgrades.filter(name => typeof name === 'string') : [];
  const accessed = new Set(previousAccess);
  for (const item of upgrades) if (item.bought === 1 || item.bought === true || item.unlocked === 1 || item.unlocked === true) accessed.add(item.name);
  const truth = value => value === 1 || value === true;
  const ready = name => {
    const building = game.Objects?.[name];
    return !!building && !!building.minigameUrl && !!building.minigameLoaded && !!building.minigame && building.level >= 1;
  };
  const garden = game.Objects?.Farm?.minigame;
  const market = game.Objects?.Bank?.minigame;
  return {
    schemaVersion: 1, gameVersion, edition,
    achievements: Object.fromEntries(Object.values(game.Achievements || {}).map(x => [x.name, truth(x.won)])),
    upgrades: Object.fromEntries(upgrades.map(x => [x.name, { id: x.id, bought: truth(x.bought), unlocked: truth(x.unlocked) }])),
    history: { gameVersion, edition, accessedUpgrades: [...accessed].sort() },
    progression: {
      achievementsOwned: game.AchievementsOwned,
      dragonLevel: game.dragonLevel, santaLevel: game.santaLevel, ascensionMode: game.ascensionMode,
      onAscend: truth(game.OnAscend), ascendTimer: game.AscendTimer, reincarnateTimer: game.ReincarnateTimer,
      buildingLevels: Object.fromEntries(objects.map(x => [x.name, x.level])),
      buildingAmounts: Object.fromEntries(objects.map(x => [x.name, x.amount])),
      buildingHighest: Object.fromEntries(objects.map(x => [x.name, x.highest])),
      minigames: Object.fromEntries(['Farm', 'Bank', 'Temple', 'Wizard tower'].map(name => [name, ready(name)])),
      gardenSeeds: garden?.plants ? Object.keys(garden.plants).filter(key => truth(garden.plants[key].unlocked)) : [],
      stockOfficeLevel: market?.officeLevel ?? 0,
      grimoireSpells: Object.keys(game.Objects?.['Wizard tower']?.minigame?.spells || {}),
      pantheonGods: Object.keys(game.Objects?.Temple?.minigame?.gods || {}),
    },
  };
}

/**
 * Section: the Garden under autoplay
 *
 * Breeding comes first. New seeds only come from mutations, which grow in empty tiles next to mature
 * plants of the right kinds (the game's mutation table), and each new seed brings the garden closer to
 * "Keeper of the conservatory" and to better plants: Thumbcorn (+2% click power, most of the income once
 * Godzamok multiplies clicks), Clover and Golden clover (golden cookies 1% and 3% more often). Autoplay
 * breeds along the chains whose parents can be planted: it plants the target's two parent kinds on a
 * checkerboard, so every empty tile touches both, uproots whatever else sprouts there (weeds, or more of
 * the parents), and lets a new kind grow up and picks it when mature, which unlocks its seed. Wood chips
 * (three mutation rolls a tick) or else fertilizer (a tick every 3 minutes) speed this up.
 *
 * With nothing left to breed, it plants the seed whose passive effect is worth most over its mature
 * life, keeping one tile free for mutations, on clay (effects x1.25). Plants are picked when mature, just
 * before they would die of old age (a mature harvest counts toward the harvest achievements). Effects
 * are valued with the auto-buyer's long-run income: +1% CpS raises everything that scales with CpS, +2%
 * click power the auto-clicker's (Godzamok-boosted) income, +1% golden cookie frequency the golden
 * cookie income.
 */

import { AutoplayEconomy, MilkMultiplier } from '../../Cache/PP/AutoplayValue.js';
import { AutoBuyState } from './AutoBuy.js';

/** New seed, and the two parent kinds whose mature neighbours mutate an empty tile into it */
const BREEDING = [
  ['thumbcorn', 'bakerWheat', 'bakerWheat'],
  ['cronerice', 'bakerWheat', 'thumbcorn'],
  ['gildmillet', 'cronerice', 'thumbcorn'],
  ['clover', 'bakerWheat', 'gildmillet'],
  ['shimmerlily', 'clover', 'gildmillet'],
  ['elderwort', 'shimmerlily', 'cronerice'],
  ['goldenClover', 'bakerWheat', 'gildmillet'],
  ['bakeberry', 'bakerWheat', 'bakerWheat'],
  ['chocoroot', 'bakerWheat', 'brownMold'],
  ['whiteChocoroot', 'chocoroot', 'whiteMildew'],
  ['whiskerbloom', 'shimmerlily', 'whiteChocoroot'],
  ['chimerose', 'shimmerlily', 'whiskerbloom'],
  ['nursetulip', 'whiskerbloom', 'whiskerbloom'],
  ['tidygrass', 'bakerWheat', 'whiteChocoroot'],
  ['queenbeet', 'chocoroot', 'bakeberry'],
  ['duketater', 'queenbeet', 'queenbeet'],
];

/**
 * Share of long-run income a mature plant adds, for the seeds whose effect the model covers
 * @param	{string}	key	Seed key
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{number}	Cookies per second
 */
function PlantValue(key, economy) {
  const cpsIncome = economy.cps * economy.growth.cps;
  const clickIncome = economy.clicks * economy.growth.click;
  if (['bakerWheat', 'bakeberry', 'chocoroot', 'whiteMildew'].includes(key))
    return 0.01 * cpsIncome;
  if (key === 'thumbcorn') return 0.02 * clickIncome;
  if (key === 'clover') return 0.01 * economy.golden;
  if (key === 'goldenClover') return 0.03 * economy.golden;
  if (key === 'shimmerlily') return 0.01 * economy.golden;
  if (key === 'drowsyfern') return 0.03 * cpsIncome - 0.05 * clickIncome - 0.1 * economy.golden;
  if (key === 'whiskerbloom') {
    // Milk 0.2% stronger: each kitten's factor 1 + k * milk * m grows with m
    const m = MilkMultiplier();
    const milk = Game.milkProgress || 0;
    let ratio = 1;
    [0.1, 0.125, 0.15, 0.175, 0.2, 0.2, 0.2, 0.2].forEach((k) => {
      ratio *= (1 + k * milk * m * 1.002) / (1 + k * milk * m);
    });
    return (ratio - 1) * cpsIncome;
  }
  return 0;
}

/**
 * Seconds a plant of this seed spends mature: it ages by ageTick + up to ageTickR per growth tick of the
 * soil, matures at `mature` and dies at 100
 * @param	{object}	me	Seed
 * @param	{number}	tickSeconds	Seconds per growth tick
 * @returns	{number}
 */
function MatureSeconds(me, tickSeconds) {
  const perTick = me.ageTick + me.ageTickR / 2;
  return me.immortal ? Infinity : (Math.max(100 - me.mature, 0) / perTick) * tickSeconds;
}

/**
 * The next seed to breed: the first in BREEDING still locked whose parents are both unlocked
 * @param	{object}	M	Garden minigame
 * @returns	{string[]|null}	[seed, parent, parent]
 */
function BreedingTarget(M) {
  return (
    BREEDING.find(
      ([seed, a, b]) =>
        M.plants[seed] &&
        !M.plants[seed].unlocked &&
        M.plants[a] &&
        M.plants[a].unlocked &&
        M.plants[b] &&
        M.plants[b].unlocked,
    ) || null
  );
}

/**
 * What a tile holds while breeding: on a checkerboard, parent tiles alternate between the two parent
 * kinds by column, so every empty tile has both among its neighbours ('' for an empty tile)
 * @param	{string[]}	target	[seed, parent, parent]
 * @param	{number}	x	Column
 * @param	{number}	y	Row
 * @returns	{string}	Seed key, or '' to keep empty
 */
function BreedingRole(target, x, y) {
  if ((x + y) % 2 !== 0) return '';
  return x % 2 === 0 ? target[1] : target[2];
}

/**
 * Switches the soil when the one wanted differs and the game allows it, as its button does
 * @param	{object}	M	Garden minigame
 * @param	{string[]}	wanted	Soil keys, best first
 * @returns	{boolean}	Whether it switched
 */
function ChooseSoil(M, wanted) {
  const soil = wanted.map((key) => M.soils[key]).find((me) => me && M.parent.amount >= me.req);
  if (!soil || soil.id === M.soil || M.nextSoil > Date.now()) return false;
  const button = l(`gardenSoil-${soil.id}`);
  if (!button) return false;
  button.click();
  return true;
}

/**
 * Plants a seed in an empty tile if the cookies not kept back for the "Lucky!" bank or a season cover it
 * @param	{object}	M	Garden minigame
 * @param	{object}	me	Seed
 * @param	{number}	x	Column
 * @param	{number}	y	Row
 * @returns	{boolean}	Whether it planted
 */
function Plant(M, me, x, y) {
  const { next } = AutoBuyState;
  if (!M.canPlant(me) || Game.cookies - (next ? next.reserve : 0) < M.getCost(me)) return false;
  return M.useTool(me.id, x, y);
}

/**
 * Tends the garden: breeds the next seed, or plants the best seed for its passive effect, and picks
 * plants while mature
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoGarden() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const farm = Game.Objects.Farm;
  if (!settings.AutoGarden || !farm.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0) return;
  const M = farm.minigame;
  if (!M || !M.plot || M.freeze) return;
  const tiles = [];
  for (let y = 0; y < 6; y++)
    for (let x = 0; x < 6; x++) if (M.isTileUnlocked(x, y)) tiles.push([x, y]);
  const target = BreedingTarget(M);
  if (ChooseSoil(M, target ? ['woodchips', 'fertilizer'] : ['clay'])) return;

  for (let i = 0; i < tiles.length; i++) {
    const [x, y] = tiles[i];
    const tile = M.plot[y][x];
    if (tile[0] >= 1) {
      const me = M.plantsById[tile[0] - 1];
      const mature = tile[1] >= me.mature;
      if (!me.unlocked) {
        // A new kind: let it grow up, and picking it then unlocks its seed
        if (mature) {
          M.harvest(x, y, 1);
          return;
        }
      } else if (target && BreedingRole(target, x, y) !== me.key) {
        // Anything else in a breeding tile, or the wrong kind in a parent tile, makes way
        M.harvest(x, y, 1);
        return;
      } else if (!me.immortal && mature && tile[1] + me.ageTick + me.ageTickR >= 100) {
        // Pick it while mature, just before the tick that could kill it
        M.harvest(x, y, 1);
        return;
      }
    }
  }

  const empty = tiles.filter(([x, y]) => M.plot[y][x][0] === 0);
  if (target) {
    for (let i = 0; i < empty.length; i++) {
      const [x, y] = empty[i];
      const role = BreedingRole(target, x, y);
      if (role && Plant(M, M.plants[role], x, y)) return;
    }
    return;
  }

  // Plant the best seed in every empty tile but the last one, kept free for mutations
  if (empty.length <= 1) return;
  const economy = AutoplayEconomy(Game.cookies);
  const tickSeconds = (M.soilsById[M.soil] ? M.soilsById[M.soil].tick : 5) * 60;
  let best = null;
  let bestGain = 0;
  M.plantsById.forEach((me) => {
    if (!me.unlocked || me.plantable === false || me.weed) return;
    const gain = PlantValue(me.key, economy) * MatureSeconds(me, tickSeconds) - M.getCost(me);
    if (gain > bestGain) {
      best = me;
      bestGain = gain;
    }
  });
  if (!best) return;
  // Planting competes with the auto-buyer: it must pay back faster (while mature) than the purchase the
  // buyer is saving for
  const { next } = AutoBuyState;
  if (next && M.getCost(best) / PlantValue(best.key, economy) > next.payback) return;
  Plant(M, best, empty[0][0], empty[0][1]);
}

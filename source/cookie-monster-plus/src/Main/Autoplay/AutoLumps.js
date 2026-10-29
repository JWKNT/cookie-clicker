/**
 * Section: sugar lumps under autoplay
 *
 * Ripe lumps are harvested at once. Lumps go first to the minigames, which are worth far more than a
 * building level (the Pantheon holds Godzamok), then to the Sugar frenzy each run once Sugar craving is
 * owned (triple CpS for an hour: two hours of income for one lump), then to cursor levels up to 4, which
 * the Stock Market's offices require before they open the first loan (+50% CpS for the last two hours of
 * every run), and then to building levels, which are permanent: each level adds 1% to that building's
 * CpS, and level 10 also earns an achievement (more milk).
 */

import { AchievementValue } from '../../Cache/PP/AutoplayValue.js';

/** Minigame buildings, most valuable first under autoplay */
const MINIGAME_ORDER = ['Temple', 'Wizard tower', 'Farm', 'Bank'];
/** Cursor level the second office upgrade requires, which opens the first loan */
const LOAN_CURSOR_LEVEL = 4;

/** Set by the Pantheon when a much better arrangement waits for worship swaps that a lump would refill */
export const LumpState = { holdForSwaps: false };

/**
 * Accepts the game's confirmation prompt with the given id, as a player clicking "Yes" would
 * @param	{string}	id	Prompt id
 */
export function ConfirmPrompt(id) {
  if (Game.promptOn && l(`promptContent${id}`) && l('promptOption0')) l('promptOption0').click();
}

/**
 * Raises a building's level by one with sugar lumps, accepting the game's prompt
 * @param	{object}	me	Building
 */
function LevelUp(me) {
  me.levelUp();
  ConfirmPrompt('SpendLump');
}

/**
 * Share of CpS gained per lump by the next level of a building: a level adds 1% of the building's CpS
 * before levels, costs (level + 1) lumps, and level 10 earns an achievement
 * @param	{object}	me	Building
 * @param	{number}	totalCps	Sum of the buildings' CpS
 * @returns	{number}
 */
export function LevelValue(me, totalCps) {
  const cost = me.level + 1;
  const share = totalCps > 0 ? me.storedTotalCps / totalCps : 0;
  let gain = (0.01 * share) / (1 + 0.01 * me.level);
  if (me.level + 1 === 10 && me.levelAchiev10 && !Game.HasAchiev(me.levelAchiev10.name))
    gain += AchievementValue();
  return gain / cost;
}

/**
 * Activates the Sugar frenzy (once per ascension, with Sugar craving), accepting the game's prompt
 * @returns	{boolean}	Whether it did
 */
function SugarFrenzy() {
  const me = Game.Upgrades['Sugar frenzy'];
  if (!me || !me.unlocked || me.bought || Game.lumps < 1 || !me.clickFunction) return false;
  me.clickFunction();
  ConfirmPrompt('SpendLump');
  return true;
}

/**
 * Spends lumps: minigames first, then the Sugar frenzy, then cursor levels for the first loan, then the
 * building level with the best gain per lump, saving up for each when it costs more than the lumps at
 * hand (spending on something worse first would only delay it). With "Sugar baking" every unspent lump
 * (up to 100) already adds 1% of CpS, more than any level
 */
function SpendLumps() {
  if (LumpState.holdForSwaps) return;
  for (let i = 0; i < MINIGAME_ORDER.length; i++) {
    const me = Game.Objects[MINIGAME_ORDER[i]];
    if (me && me.level === 0 && me.amount > 0) {
      if (Game.lumps >= 1) LevelUp(me);
      return;
    }
  }
  if (SugarFrenzy()) return;
  const cursor = Game.Objects.Cursor;
  if (Game.Objects.Bank.minigameLoaded && cursor.level < LOAN_CURSOR_LEVEL) {
    if (Game.lumps >= cursor.level + 1) LevelUp(cursor);
    return;
  }
  if (Game.Has('Sugar baking') && Game.lumps <= 100) return;
  const totalCps = Object.keys(Game.Objects).reduce(
    (sum, name) => sum + Game.Objects[name].storedTotalCps,
    0,
  );
  let best = null;
  let bestValue = 0;
  Object.keys(Game.Objects).forEach((name) => {
    const me = Game.Objects[name];
    if (me.amount === 0) return;
    const value = LevelValue(me, totalCps);
    if (value > bestValue) {
      best = me;
      bestValue = value;
    }
  });
  if (best && Game.lumps >= best.level + 1) LevelUp(best);
}

/**
 * Harvests ripe lumps, tries "Hand-picked" once the minigames are open (a mature but unripe lump yields
 * nothing half the time, so it costs half a lump a try), and spends lumps
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoLumps() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoLumps || !Game.canLumps() || Game.OnAscend || Game.AscendTimer > 0) return;
  const age = Date.now() - Game.lumpT;
  if (age >= Game.lumpRipeAge) {
    Game.clickLump();
    return;
  }
  const minigamesDone = MINIGAME_ORDER.every(
    (name) => !Game.Objects[name] || Game.Objects[name].level > 0,
  );
  if (!Game.HasAchiev('Hand-picked') && minigamesDone && age >= Game.lumpMatureAge) {
    Game.clickLump();
    return;
  }
  SpendLumps();
}

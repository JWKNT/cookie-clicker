/**
 * Section: the dragon under autoplay
 *
 * The dragon starts over every run. Training costs cookies for the first levels and then 100 of each
 * building in turn; the payoffs are Radiant Appetite (all production x2, level 19), Dragon Guts (two more
 * wrinklers that digest and return 20% more, level 25), the dragon cookie and the second aura. Training
 * toward the next payoff goes ahead when buying the sacrificed buildings back costs at most an hour of
 * income (a quarter of an hour for the smaller steps). Auras are picked by trying them in the game's CpS
 * formula and the auto-buyer's income model, and changed only when the gain pays back the building a
 * change costs within half an hour.
 */

import { AutoplayEconomy } from '../../Cache/PP/AutoplayValue.js';
import { ConfirmPrompt } from './AutoLumps.js';

/** Dragon levels after which a payoff is available, and seconds of income worth paying for each */
const MILESTONES = [
  { level: 19, budget: 3600 }, // Radiant Appetite
  { level: 25, budget: 3600 }, // Dragon Guts
  { level: 26, budget: 900 }, // dragon cookie
  { level: 27, budget: 1800 }, // second aura, "Here be dragon"
];
/** Auras the model can value; the rest work through selling, drops, sugar lumps or minigames */
const AURA_NAMES = [
  'Breath of Milk',
  'Dragon Cursor',
  'Elder Battalion',
  'Dragon God',
  'Arcane Aura',
  'Epoch Manipulator',
  'Radiant Appetite',
  'Reality Bending',
  'Dragon Guts',
];
/** Seconds within which a new aura must pay back the building that switching costs */
const AURA_PAYBACK = 1800;
/** Seconds between aura re-evaluations (and right after every training step) */
const AURA_CHECK_SECONDS = 60;

let LastAuraCheck = 0;

/**
 * Cookies to buy back n of a building after sacrificing them: the copies below the current amount cost
 * price / 1.15^k for k = 1..n, a sum of price * (1 - 1.15^-n) / 0.15
 * @param	{object}	me	Building
 * @param	{number}	n	Copies sacrificed
 * @returns	{number}
 */
export function RebuyCost(me, n) {
  return (me.getPrice() * (1 - 1.15 ** -n)) / 0.15;
}

/**
 * Cookies the training step from a dragon level costs
 * @param	{number}	level	Dragon level
 * @returns	{number}
 */
function StepCost(level) {
  const objects = Object.keys(Game.Objects).map((name) => Game.Objects[name]);
  if (level < 5) return 1000000 * 2 ** level;
  if (level < 25) return RebuyCost(objects[level - 5], 100);
  const n = level === 25 ? 50 : 200;
  return objects.reduce((sum, me) => sum + RebuyCost(me, n), 0);
}

/**
 * Copies of each building the training steps from `from` up to `to` need at hand: steps 5 to 24 take
 * 100 of one building each, then the dragon cookie takes 50 and the second aura 200 of every building
 * (after the earlier sacrifices)
 * @param	{number}	from	Dragon level
 * @param	{number}	to	Dragon level reached
 * @returns	{boolean}	Whether the buildings are there now
 */
function PathAvailable(from, to) {
  const objects = Object.keys(Game.Objects).map((name) => Game.Objects[name]);
  const taken = objects.map(() => 0);
  for (let l = Math.max(from, 5); l < to; l++) {
    if (l < 25) {
      if (objects[l - 5].amount - taken[l - 5] < 100) return false;
      taken[l - 5] += 100;
    } else {
      const need = l === 25 ? 50 : 200;
      if (objects.some((me, i) => me.amount - taken[i] < need)) return false;
    }
  }
  return true;
}

/**
 * Whether training the next level goes ahead. The first five levels only cost a few million cookies
 * (and teach Breath of Milk). After that each step sacrifices buildings and pays off only at the next
 * milestone, so the steps go ahead once every building the way there needs is at hand and buying them
 * all back costs no more than that milestone's budget in seconds of income
 * @returns	{boolean}
 */
function TrainingPays() {
  const level = Game.dragonLevel;
  if (level >= Game.dragonLevels.length - 1 || !Game.dragonLevels[level].cost()) return false;
  if (level < 5) return true;
  const milestone = MILESTONES.find((m) => m.level > level);
  if (!milestone || !PathAvailable(level, milestone.level)) return false;
  let cost = 0;
  for (let l = level; l < milestone.level; l++) cost += StepCost(l);
  return cost <= AutoplayEconomy(Game.cookies).income * milestone.budget;
}

/**
 * Long-run income with the given auras: sets them, lets the game recompute CpS, scores the result and
 * restores the auras. Arcane Aura also brings golden cookies 5% sooner
 * @param	{number}	primary	Aura id
 * @param	{number}	secondary	Aura id
 * @returns	{number}	Cookies per second
 */
function ScoreAuras(primary, secondary) {
  const saved = [Game.dragonAura, Game.dragonAura2];
  const arcane = Number(
    Object.keys(Game.dragonAuras).find((k) => Game.dragonAuras[k].name === 'Arcane Aura'),
  );
  const before = 1 - Game.auraMult('Arcane Aura') * 0.05;
  Game.dragonAura = primary;
  Game.dragonAura2 = secondary;
  Game.CalculateGains();
  const after = 1 - Game.auraMult('Arcane Aura') * 0.05;
  const { income } = AutoplayEconomy(Game.cookies, Number.isFinite(arcane) ? after / before : 1);
  [Game.dragonAura, Game.dragonAura2] = saved;
  Game.CalculateGains();
  return income;
}

/**
 * Sets an aura through the game's own aura prompt, which charges one of the highest buildings
 * @param	{number}	aura	Aura id
 * @param	{number}	slot	0 for the primary aura, 1 for the secondary
 */
function SetAura(aura, slot) {
  Game.SetDragonAura(aura, slot);
  ConfirmPrompt('PickDragonAura');
  if (Game.specialTab) Game.ToggleSpecialMenu(0);
}

/**
 * Picks the best primary aura (and secondary once trained), switching only when it pays
 */
function ChooseAuras() {
  if (Date.now() - LastAuraCheck < AURA_CHECK_SECONDS * 1000) return;
  LastAuraCheck = Date.now();
  const ids = AURA_NAMES.map((name) =>
    Number(Object.keys(Game.dragonAuras).find((k) => Game.dragonAuras[k].name === name)),
  ).filter((id) => Number.isFinite(id) && Game.dragonLevel >= id + 4);
  if (!ids.length) return;
  const twoAuras = Game.dragonLevel >= Game.dragonLevels.length - 1;
  const current = ScoreAuras(Game.dragonAura, Game.dragonAura2);
  let best = [Game.dragonAura, Game.dragonAura2];
  let bestIncome = current;
  ids.forEach((a) => {
    (twoAuras ? ids : [Game.dragonAura2]).forEach((b) => {
      if (a === b && a !== 0) return;
      const income = ScoreAuras(a, b);
      if (income > bestIncome) {
        best = [a, b];
        bestIncome = income;
      }
    });
  });
  let highest = null;
  Object.keys(Game.Objects).forEach((name) => {
    if (Game.Objects[name].amount > 0) highest = Game.Objects[name];
  });
  const switchCost = highest ? highest.getPrice() / 1.15 : 0;
  const changes = Number(best[0] !== Game.dragonAura) + Number(best[1] !== Game.dragonAura2);
  if (!changes || (bestIncome - current) * AURA_PAYBACK < switchCost * changes) return;
  if (best[0] !== Game.dragonAura) SetAura(best[0], 0);
  else if (best[1] !== Game.dragonAura2) SetAura(best[1], 1);
}

/** Upgrades petting the dragon can drop, one per quarter of an hour, and seconds between petting sessions */
const DRAGON_DROPS = ['Dragon scale', 'Dragon claw', 'Dragon fang', 'Dragon teddy bear'];
const PET_SECONDS = 60;
/** Pets per session: each has a 1 in 20 chance to drop the current quarter-hour's upgrade */
const PETS = 20;

let LastPet = 0;

/**
 * With "Pet the dragon", pets the dragon in its menu until this quarter-hour's drop shows up (each drop
 * is an upgrade for this run)
 * @returns	{boolean}	Whether it petted
 */
function PetDragon() {
  if (!Game.Has('Pet the dragon') || Game.dragonLevel < 8) return false;
  if (DRAGON_DROPS.every((name) => Game.Has(name) || Game.HasUnlocked(name))) return false;
  if (Date.now() - LastPet < PET_SECONDS * 1000) return false;
  LastPet = Date.now();
  const { volume } = Game;
  Game.volume = 0;
  Game.specialTab = 'dragon';
  Game.ToggleSpecialMenu(1);
  for (let i = 0; i < PETS; i++) Game.ClickSpecialPic();
  Game.ToggleSpecialMenu(0);
  Game.volume = volume;
  return true;
}

/**
 * Buys the dragon egg, trains the dragon, pets it for its drops and picks its auras
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoDragon() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoDragon || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  const egg = Game.Upgrades['A crumbly egg'];
  if (!egg) return;
  if (!egg.bought) {
    if (egg.unlocked && Game.cookies >= egg.getPrice()) egg.buy();
    return;
  }
  if (TrainingPays()) {
    Game.UpgradeDragon();
    if (Game.specialTab) Game.ToggleSpecialMenu(0);
    LastAuraCheck = 0;
    return;
  }
  if (PetDragon()) return;
  ChooseAuras();
}

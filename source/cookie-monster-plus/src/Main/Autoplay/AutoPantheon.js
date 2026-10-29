/**
 * Section: the Pantheon under autoplay
 *
 * Tries every arrangement of the gods worth slotting, scores each by the long-run income the
 * auto-buyer uses (the game's own CpS and click power with those gods, plus golden cookies and
 * wrinklers), and moves gods into the best arrangement with the worship swaps a player would spend.
 */

import { AutoplayEconomy } from '../../Cache/PP/AutoplayValue.js';
import { ConfirmPrompt, LumpState } from './AutoLumps.js';

/**
 * Gods worth trying. Godzamok is worth his "Devastation" buff, which autoplay keeps growing by selling
 * and buying back buildings (the economy counts its average). Holobore is only useful without auto
 * golden cookies (clicking one unslots it). Left out: Skruuia (turns every golden cookie into a wrath
 * cookie with extra clots and ruin, which the model does not cover; a pledge-free Grandmapocalypse does
 * the same for wrinklers), Cyclius (averages to nothing), Dotjeiess (weakens heavenly chips), Selebrak
 * and Rigidel (marginal)
 */
const CANDIDATES = ['ruin', 'mother', 'industry', 'labor', 'decadence', 'asceticism'];
/** How much less often golden cookies appear with Mokalsium and Jeremy in each slot */
const SLOWER = { mother: [1.15, 1.1, 1.05], industry: [1.1, 1.06, 1.03] };
/** Seconds between re-evaluations, and while a slot is empty (as after every ascension) */
const CHECK_SECONDS = 300;
const EMPTY_CHECK_SECONDS = 5;
/** Improvement in income needed to spend swaps on a new arrangement */
const MIN_GAIN = 0.01;
/**
 * Improvement worth a sugar lump to refill the swaps when they run short (from none, the next swap takes
 * 16 hours); Godzamok's buff alone multiplies income many times over
 */
const REFILL_GAIN = 0.5;

let LastCheck = 0;

/**
 * Factor on the golden cookie interval for an arrangement, relative to the gods slotted now
 * @param	{number[]}	slots	God ids per slot
 * @returns	{number}
 */
function IntervalFactor(slots) {
  const M = Game.Objects.Temple.minigame;
  let factor = 1;
  Object.keys(SLOWER).forEach((key) => {
    const slot = M.gods[key] ? slots.indexOf(M.gods[key].id) : -1;
    if (slot !== -1) factor *= SLOWER[key][slot];
  });
  return factor;
}

/**
 * Long-run income with the gods in the given slots: slots them, lets the game recompute CpS and click
 * power, scores the result and puts the original gods back
 * @param	{number[]}	slots	God ids per slot
 * @param	{number}	baseFactor	IntervalFactor of the current arrangement
 * @returns	{number}	Cookies per second
 */
function Score(slots, baseFactor) {
  const M = Game.Objects.Temple.minigame;
  const saved = M.slot.slice();
  const apply = (arrangement) => {
    Object.keys(M.godsById).forEach((id) => {
      M.godsById[id].slot = -1;
    });
    arrangement.forEach((id, slot) => {
      M.slot[slot] = id;
      if (id !== -1) M.godsById[id].slot = slot;
    });
  };
  apply(slots);
  Game.CalculateGains();
  const { income } = AutoplayEconomy(Game.cookies, IntervalFactor(slots) / baseFactor);
  apply(saved);
  Game.CalculateGains();
  return income;
}

/**
 * Moves gods into the given slots, one swap per god dropped into a slot (as dragging them would), and
 * moves their pictures in the Pantheon like a drop does
 * @param	{number[]}	slots	God ids per slot
 */
function Arrange(slots) {
  const M = Game.Objects.Temple.minigame;
  slots.forEach((id, slot) => {
    if (id === -1 || M.slot[slot] === id || M.swaps < 1) return;
    M.slotGod(M.godsById[id], slot);
    M.useSwap(1);
    M.lastSwapT = 0;
  });
  M.godsById.forEach((god) => {
    const div = l(`templeGod${god.id}`);
    const placeholder = l(`templeGodPlaceholder${god.id}`);
    if (!div || !placeholder) return;
    if (god.slot !== -1 && l(`templeSlot${god.slot}`)) {
      l(`templeSlot${god.slot}`).appendChild(div);
      placeholder.style.display = 'inline-block';
    } else {
      placeholder.parentNode.insertBefore(div, placeholder);
      placeholder.style.display = 'none';
    }
  });
}

/**
 * Refills the worship swaps with a sugar lump, accepting the game's prompt, as the Pantheon's refill
 * button does
 * @returns	{boolean}	Whether the swaps are full now
 */
function RefillSwaps() {
  const M = Game.Objects.Temple.minigame;
  if (Game.lumps < 1 || !Game.canRefillLump()) return false;
  Game.refillLump(1, () => {
    M.swaps = 3;
    M.swapT = Date.now();
  });
  ConfirmPrompt('SpendLump');
  return M.swaps >= 3;
}

/**
 * Slots the best gods once the Pantheon is unlocked, re-checking every few minutes, and refills the
 * worship swaps with a sugar lump when a much better arrangement waits for them
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoPantheon() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const temple = Game.Objects.Temple;
  if (!settings.AutoPantheon || !temple.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0)
    return;
  const M = temple.minigame;
  if (!M) return;
  const soon = M.slot.includes(-1) || (LumpState.holdForSwaps && Game.lumps >= 1);
  if (Date.now() - LastCheck < (soon ? EMPTY_CHECK_SECONDS : CHECK_SECONDS) * 1000) return;
  LastCheck = Date.now();

  const ids = CANDIDATES.filter(
    (key) => M.gods[key] && (key !== 'asceticism' || !settings.AutoGolden),
  ).map((key) => M.gods[key].id);
  const baseFactor = IntervalFactor(M.slot);
  const current = Score(M.slot.slice(), baseFactor);
  let best = null;
  let bestIncome = current;
  ids.forEach((a) => {
    ids.forEach((b) => {
      ids.forEach((c) => {
        if (a === b || a === c || b === c) return;
        const income = Score([a, b, c], baseFactor);
        if (income > bestIncome) {
          best = [a, b, c];
          bestIncome = income;
        }
      });
    });
  });
  // Slots are filled diamond first; an empty slot is worth filling even when swaps run short
  const moves = best ? best.filter((id, slot) => M.slot[slot] !== id).length : 0;
  const filling = M.slot.includes(-1);
  const better = best !== null && bestIncome > current * (1 + MIN_GAIN);
  LumpState.holdForSwaps =
    better && !filling && M.swaps < moves && bestIncome > current * (1 + REFILL_GAIN);
  if (LumpState.holdForSwaps && RefillSwaps()) LumpState.holdForSwaps = false;
  if (better && (M.swaps >= moves || filling)) Arrange(best);
}

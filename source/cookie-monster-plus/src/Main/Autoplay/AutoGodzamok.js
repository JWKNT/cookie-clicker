/**
 * Section: Godzamok combos under autoplay
 *
 * Every frame with Godzamok slotted, sells and buys back each building type whose round trip pays (see
 * Cache/PP/Godzamok.js), within a few milliseconds, so the "Devastation" buff keeps growing for its ten
 * seconds and starts again when it runs out. The building counts are back where they were before the
 * frame ends, so CpS never changes and only click power needs recomputing.
 */

import { AutoClickRate } from '../../Cache/PP/AutoplayValue.js';
import {
  BUDGET_MS,
  BUFF_SECONDS,
  CycleTypes,
  DevastationBonus,
  GodzamokState,
  MAX_PASSES,
} from '../../Cache/PP/Godzamok.js';

/** Below this many seconds left, let the buff run out and start a fresh one instead */
const MIN_SECONDS = 0.5;

let Next = 0;

/**
 * Sells and buys back building types round-robin until the frame's time budget is spent
 * It is called by Autoplay() every frame
 */
export default function AutoGodzamok() {
  if (Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0 || !DevastationBonus())
    return;
  const buff = Game.hasBuff('Devastation');
  const seconds = buff ? buff.time / Game.fps : BUFF_SECONDS;
  if (seconds < MIN_SECONDS) return;
  const clickIncome = (AutoClickRate() * Game.computedMouseCps) / (buff ? buff.multClick : 1);
  const types = CycleTypes(clickIncome, seconds, Game.cookies);
  if (!types.length) return;

  const { volume, buyMode, recalculateGains } = Game;
  Game.volume = 0; // no sale and purchase sounds
  Game.buyMode = 1; // in sell mode, buy() sells
  const start = performance.now();
  let units = 0;
  let intact = true;
  for (let pass = 0; pass < MAX_PASSES * types.length && intact; pass++) {
    if (pass > 0 && performance.now() - start >= BUDGET_MS) break;
    const me = types[Next % types.length];
    Next = (Next + 1) % types.length;
    const n = me.amount;
    me.sell(-1);
    me.buy(n);
    units += n;
    intact = me.amount === n;
  }
  const elapsed = performance.now() - start;
  if (units > 0) GodzamokState.msPerUnit = 0.9 * GodzamokState.msPerUnit + (0.1 * elapsed) / units;
  Game.volume = volume;
  Game.buyMode = buyMode;
  // Counts and CpS are unchanged, so skip the full recalculation (and Cookie Monster's resimulation that
  // follows it) unless a purchase fell short; the buff only changes click power
  Game.recalculateGains = intact ? recalculateGains : 1;
  Game.computedMouseCps = Game.mouseCps();
}

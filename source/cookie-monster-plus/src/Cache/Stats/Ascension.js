/** Section: Caches the state of the optimal ascension advisor */

import GetCPSBuffMult from '../CPS/GetCPSBuffMult.js';
import FillCMDCache from '../FillCMDCache.js';
import {
  CacheCurrWrinklerCPSMult,
  CacheLastChoEgg,
  CacheWrinklersTotal,
  CookiesDiff,
  WrinkDiff,
} from '../VariablesAndData.js';
import { AutoClickRate } from '../PP/AutoplayValue.js';
import { PlanAscension, SpeedModel } from './AscensionMath.js';
import HeavenlyPurchaseOrder, { HeavenlyContext } from './HeavenlyPlan.js';

/** Seconds of income history used to average golden cookie effects into the income estimate */
const INCOME_WINDOW = 600;
/** Golden cookies may at most add this multiple of passive income to the estimate */
const MAX_ACTIVE_BONUS = 1;
/** The plan is a dynamic program (~20-60 ms), so it is refreshed less often than once per second */
const PLAN_INTERVAL = 5;
/** Runs younger than this are too short to measure how fast they grow */
const MIN_RUN_TIME = 600;

/**
 * Stores the latest advisor results
 * @item	{object}	state		Inputs of the planner (see PlanAscension)
 * @item	{object}	plan		Result of PlanAscension
 * @item	{boolean}	applicable	False in Born again mode or when no prestige can be earned
 * @item	{object}	heavenlyContext	Income shares valuing heavenly upgrades (see HeavenlyContext)
 * @item	{object[]}	heavenlyOrder	Order in which heavenly chips get spent (see HeavenlyPurchaseOrder)
 */
export const AscensionCache = {
  state: null,
  plan: null,
  applicable: false,
  lastPlan: 0,
  heavenlyContext: null,
  heavenlyOrder: [],
};

/**
 * Game.GetHeavenlyMultiplier() with all five "Heavenly ..." store upgrades bought, which every run does
 * within minutes once Legacy is owned
 * @returns	{number}	h in M = 1 + 0.01·h·P
 */
export function HeavenlyMultiplierPotential() {
  let mult = 1;
  mult *= 1 + Game.auraMult('Dragon God') * 0.05;
  if (Game.Has('Lucky digit')) mult *= 1.01;
  if (Game.Has('Lucky number')) mult *= 1.01;
  if (Game.Has('Lucky payout')) mult *= 1.01;
  if (Game.hasGod) {
    const godLvl = Game.hasGod('creation');
    if (godLvl === 1) mult *= 0.7;
    else if (godLvl === 2) mult *= 0.8;
    else if (godLvl === 3) mult *= 0.9;
  }
  return mult * Game.heavenlyPower;
}

/**
 * Cookies per second gained from automatic clicking, without click buffs
 * @returns	{number}
 */
export function AutoClickIncome() {
  const rate = AutoClickRate();
  if (!rate) return 0;
  let clickBuff = 1;
  Object.keys(Game.buffs).forEach((i) => {
    if (typeof Game.buffs[i].multClick !== 'undefined') clickBuff *= Game.buffs[i].multClick;
  });
  return (rate * Game.computedMouseCps) / (clickBuff > 0 ? clickBuff : 1);
}

/**
 * Collects the inputs of the ascension planner from the game
 * Cookies held by wrinklers and the Chocolate egg payout are counted, as they can be cashed in right
 * before ascending. Income is the unbuffed CpS (with wrinkler returns and automatic clicks), raised to
 * the average income of the last ten minutes once that much history exists, so golden cookies count
 * but a single lucky streak or offline production credited at load cannot dominate the estimate.
 * @returns	{{state: object, heavenly: object, heavenlyContext: object, heavenlyOrder: object[]}}
 */
export function GetAscensionInputs() {
  const choEgg =
    Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg') ? CacheLastChoEgg : 0;
  const buffMult = GetCPSBuffMult();
  const clickIncome = AutoClickIncome();
  const baseIncome =
    (Game.cookiesPs * (1 - Game.cpsSucked + CacheCurrWrinklerCPSMult)) /
      (buffMult > 0 ? buffMult : 1) +
    clickIncome;
  let income = baseIncome;
  if (CookiesDiff && WrinkDiff && CookiesDiff.queue.length >= INCOME_WINDOW) {
    const averageIncome =
      CookiesDiff.calcAverage(INCOME_WINDOW) + WrinkDiff.calcAverage(INCOME_WINDOW);
    income = Math.min(Math.max(baseIncome, averageIncome), (1 + MAX_ACTIVE_BONUS) * baseIncome);
  }
  const overhead = Number(
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AscendOverhead,
  );

  const heavenlyContext = HeavenlyContext(baseIncome, clickIncome);
  const heavenlyOrder = HeavenlyPurchaseOrder(heavenlyContext);

  return {
    state: {
      cookiesReset: Game.cookiesReset,
      cookiesRun: Game.cookiesEarned + CacheWrinklersTotal + choEgg,
      income,
      runTime: Math.max(1, (Date.now() - Game.startDate) / 1000),
      overhead: Number.isFinite(overhead) && overhead >= 0 ? overhead : 60,
    },
    heavenly: {
      levels: Game.prestige,
      chips: Game.heavenlyChips,
      hasLegacy: !!Game.Upgrades.Legacy.bought,
      power: HeavenlyMultiplierPotential(),
      // Owned heavenly upgrades speed up the current and future runs alike, so they cancel out
      ownedMult: 1,
      upgrades: heavenlyOrder.map((item) => ({ cost: item.cost, mult: item.mult })),
    },
    heavenlyContext,
    heavenlyOrder,
  };
}

/**
 * This function caches the ascension advisor
 * It is called by CM.Cache.LoopCache() and CM.Cache.InitCache()
 * @param	{boolean}	force	Recalculate now instead of waiting for the next interval
 */
export default function CacheAscension(force) {
  if (!force && (Game.T / Game.fps) % 1 !== 0) return;

  AscensionCache.applicable = Game.ascensionMode !== 1 && Game.heavenlyPower > 0;
  const now = Date.now() / 1000;
  if (!force && AscensionCache.plan !== null && now - AscensionCache.lastPlan < PLAN_INTERVAL)
    return;
  AscensionCache.lastPlan = now;

  const { state, heavenly, heavenlyContext, heavenlyOrder } = GetAscensionInputs();
  AscensionCache.state = state;
  AscensionCache.heavenlyContext = heavenlyContext;
  AscensionCache.heavenlyOrder = heavenlyOrder;
  AscensionCache.plan =
    state.runTime >= MIN_RUN_TIME
      ? PlanAscension(state, SpeedModel(heavenly))
      : { applicable: false };

  FillCMDCache({
    CacheAscension: {
      applicable: AscensionCache.applicable,
      state: AscensionCache.state,
      plan: AscensionCache.plan,
      heavenlyOrder: heavenlyOrder.map(({ name, cost, mult }) => ({ name, cost, mult })),
    },
  });
}

/**
 * Section: the Grandmapocalypse under autoplay
 *
 * Research goes all the way to the Elder Pact: the upgrades on the way add CpS, and the pact makes the
 * Elder Pledge come back by itself at a price that stops growing at 8^14 cookies, nothing late in a run.
 * A pledge holds the wrath off for half an hour (an hour with Sacrificial rolling pins), so autoplay picks
 * the stage that earns more: wrath (wrath cookies, and wrinklers that turn CpS into about six times as
 * much income) or calm (golden cookies, whose Frenzies also multiply click income). It compares the
 * long-run income of both and pledges whenever calm wins, which it does once Godzamok makes clicks most
 * of the income. Otherwise it keeps its wrinklers and pops them when cashing in beats keeping them. It
 * takes the elder achievements on the way (pledge, covenant and revoke five times), and bursts every
 * wrinkler that appears for "Wrinklesquisher" and "Moistburster" (50 and 200 in one run) when what they
 * are worth beats the income given up meanwhile.
 */

import {
  AchievementWorth,
  AutoplayEconomy,
  WrinklerFactor,
} from '../../Cache/PP/AutoplayValue.js';
import { AscensionCache } from '../../Cache/Stats/Ascension.js';
import { PokeState } from './AutoAchievements.js';

/** Research that starts and deepens the Grandmapocalypse; the game asks for confirmation first */
const ELDER_RESEARCH = ['One mind', 'Communal brainsweep', 'Elder Pact'];
/** Seconds a new wrinkler spends crawling to the cookie before it starts digesting */
const CRAWL_SECONDS = 10;
/** Run length assumed when the ascension planner has no estimate */
const DEFAULT_REMAINING = 7200;
/** Wrinklers burst in one run for each achievement */
const SPREE_TARGETS = [
  ['Wrinklesquisher', 50],
  ['Moistburster', 200],
];
/** Seconds between comparisons of the stages */
const STAGE_CHECK_SECONDS = 10;

let LastStageCheck = 0;
let Stages = null;

/**
 * Average seconds a free wrinkler slot stays empty, from the game's spawn chance per frame
 * @param	{number}	[wrath]	Elder wrath to assume (the current one by default)
 * @returns	{number}
 */
export function WrinklerRespawnSeconds(wrath = Game.elderWrath) {
  let chance = 0.00001 * wrath * Game.eff('wrinklerSpawn');
  if (Game.Has('Unholy bait')) chance *= 5;
  if (Game.hasGod) chance *= [1, 2.5, 2, 1.5][Game.hasGod('scorn') || 0];
  if (Game.Has('Wrinkler doormat')) chance = 0.1;
  return chance > 0 ? 1 / (chance * Game.fps) + CRAWL_SECONDS : Infinity;
}

/**
 * Cookies a wrinkler must hold before popping it pays. Popped now, its cookies grow with the economy
 * for the rest of the run, a factor e^(rho T) - 1 more by the end (income grows like t^(beta - 1) in a
 * run whose cookies grow like t^beta, so rho = (beta - 1) / t). Its slot meanwhile stays empty for the
 * respawn time, and the other n - 1 wrinklers each digest a twentieth less: about (2n - 1) / 20 of CpS
 * goes missing, returned x1.1, minus the twentieth of CpS that is no longer withered. Pop when the gain
 * beats that loss, which also compounds until the end
 * @param	{number}	wrinklers	Wrinklers digesting now
 * @returns	{number}	Cookies
 */
export function PopThreshold(wrinklers) {
  const respawn = WrinklerRespawnSeconds();
  if (!Number.isFinite(respawn)) return Infinity;
  const { plan, state } = AscensionCache;
  const remaining =
    plan && plan.applicable && Number.isFinite(plan.remaining)
      ? Math.max(plan.remaining, 0)
      : DEFAULT_REMAINING;
  const rho =
    plan && plan.applicable && plan.beta > 1 && state && state.runTime > 0
      ? (plan.beta - 1) / state.runTime
      : 0;
  const growth = Math.expm1(rho * remaining);
  if (!(growth > 0)) return Infinity;
  const lossPerSecond = (0.05 * (2 * wrinklers - 1) * 1.1 - 0.05) * Game.cookiesPs;
  return (lossPerSecond * respawn * (growth + 1)) / growth;
}

/**
 * Buys the next Grandmapocalypse research once it is unlocked and affordable, skipping the game's
 * confirmation prompt (buying with bypass is what its "Yes" button does)
 * @returns	{boolean}	Whether something was bought
 */
function BuyElderResearch() {
  for (let i = 0; i < ELDER_RESEARCH.length; i++) {
    const me = Game.Upgrades[ELDER_RESEARCH[i]];
    if (me && me.unlocked && !me.bought && Game.cookies >= me.getPrice()) {
      me.buy(1);
      return true;
    }
  }
  return false;
}

/**
 * "Elder nap", "Elder slumber" and "Elder calm": pledge, sign the covenant (which ends the pledge at
 * once), revoke it, and repeat until five pledges. With the Elder Pact the pledge comes back by itself
 * right away, so this takes seconds and a negligible amount of cookies instead of hours of peace
 * @returns	{boolean}	Whether something was bought
 */
function ElderAchievements() {
  if (Game.HasAchiev('Elder slumber') && Game.HasAchiev('Elder calm')) return false;
  if (!Game.Has('Elder Pact')) return false;
  const pledge = Game.Upgrades['Elder Pledge'];
  const covenant = Game.Upgrades['Elder Covenant'];
  const revoke = Game.Upgrades['Revoke Elder Covenant'];
  const affordable = (me) => me && me.unlocked && !me.bought && Game.cookies >= me.getPrice();
  if (covenant && covenant.bought) {
    if (affordable(revoke)) {
      revoke.buy(1);
      return true;
    }
    return false;
  }
  if (pledge && pledge.bought) {
    if (affordable(covenant)) {
      covenant.buy(1);
      return true;
    }
    return false;
  }
  if (affordable(pledge)) {
    pledge.buy(1);
    return true;
  }
  return false;
}

/**
 * Seconds of play left in this run, from the ascension planner
 * @returns	{number}
 */
function RunRemaining() {
  const { plan } = AscensionCache;
  return plan && plan.applicable && Number.isFinite(plan.remaining)
    ? Math.max(plan.remaining, 0)
    : DEFAULT_REMAINING;
}

/**
 * Long-run income in calm (a pledge holds: golden cookies, no wrinklers), in wrath with every wrinkler
 * kept, and in wrath with every wrinkler burst at once (a spree), refreshed every few seconds
 * @returns	{{calm: number, wrath: number, spree: number}}
 */
function StageIncomes() {
  if (!Stages || Date.now() - LastStageCheck > STAGE_CHECK_SECONDS * 1000) {
    LastStageCheck = Date.now();
    const income = (stage, W) => AutoplayEconomy(Game.cookies, 1, { stage, W }).income;
    Stages = {
      calm: income(0, 1),
      wrath: income(3, WrinklerFactor(Game.getWrinklersMax())),
      spree: income(3, 1),
    };
  }
  return Stages;
}

/**
 * How many wrinklers this run should burst for the next bursting achievement, if one is worth it: the
 * spree gives up the better stage's income for as long as the bursts take (every slot refills on its
 * own, so a burst comes every respawn time / slots), which must cost less than the achievement is
 * worth and fit in what is left of the run
 * @returns	{number}	Target count, 0 for none
 */
function SpreeTarget() {
  if (!Game.Has('Elder Pact')) return 0;
  const wait = (WrinklerRespawnSeconds(3) - CRAWL_SECONDS) / Math.max(Game.getWrinklersMax(), 1);
  if (!Number.isFinite(wait) || wait <= 0) return 0;
  const { calm, wrath, spree } = StageIncomes();
  const loss = 1 - spree / Math.max(calm, wrath);
  let from = Game.wrinklersPopped;
  for (let i = 0; i < SPREE_TARGETS.length; i++) {
    const [name, target] = SPREE_TARGETS[i];
    if (!Game.HasAchiev(name)) {
      const fits = (target - Game.wrinklersPopped) * wait <= RunRemaining();
      const cost = Math.max(target - from, 0) * wait * Math.max(loss, 0);
      return fits && cost <= AchievementWorth(1) ? target : 0;
    }
    from = Math.max(from, target);
  }
  return 0;
}

/**
 * Bursts every wrinkler as soon as it appears, except the one being poked for "Wrinkler poker"
 */
function Spree() {
  let spared = Game.HasAchiev('Wrinkler poker') ? null : PokeState.target;
  if (!Game.HasAchiev('Wrinkler poker') && !spared)
    spared = Game.wrinklers.find((me) => me.phase > 0 && me.type === 0) || null;
  for (let i = 0; i < Game.wrinklers.length; i++) {
    const me = Game.wrinklers[i];
    if (me.phase > 0 && me !== spared) me.hp = 0;
  }
}

/**
 * Revokes the Elder Covenant left by the elder achievements: it costs 5% of CpS for as long as it
 * holds, while a pledge holds the wrath off for free
 * @returns	{boolean}	Whether it revoked
 */
function RevokeCovenant() {
  const covenant = Game.Upgrades['Elder Covenant'];
  const revoke = Game.Upgrades['Revoke Elder Covenant'];
  if (!covenant || !covenant.bought || !revoke || !revoke.unlocked || revoke.bought) return false;
  if (Game.cookies < revoke.getPrice()) return false;
  revoke.buy(1);
  return true;
}

/**
 * Renews the Elder Pledge once it has run out (with the Elder Pact it unlocks again by itself)
 * @returns	{boolean}	Whether it pledged
 */
function Pledge() {
  const me = Game.Upgrades['Elder Pledge'];
  if (!me || !me.unlocked || me.bought || Game.cookies < me.getPrice()) return false;
  me.buy(1);
  return true;
}

/**
 * Pops the fattest normal wrinkler if it holds more than PopThreshold. Shiny wrinklers return three times
 * as much and are left for the ascension
 */
function PopWrinklers() {
  const digesting = Game.wrinklers.filter((me) => me.phase === 2);
  if (!digesting.length) return;
  const threshold = PopThreshold(digesting.length);
  let fattest = null;
  digesting.forEach((me) => {
    if (me.type === 0 && (fattest === null || me.sucked > fattest.sucked)) fattest = me;
  });
  if (fattest && fattest.sucked * 1.1 > threshold) fattest.hp = 0;
}

/**
 * Runs the Grandmapocalypse: research, the elder achievements (the wrath at its peak once, then
 * pledging, signing and revoking the covenant), bursting sprees, the choice of stage and wrinkler popping
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoElder() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoElder || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  if (BuyElderResearch()) return;
  // "Grandmapocalypse" needs the wrath at its peak once, which it reaches a minute or two after the pact
  if (Game.Has('Elder Pact') && !Game.HasAchiev('Grandmapocalypse')) {
    PopWrinklers();
    return;
  }
  if (ElderAchievements()) return;
  if (RevokeCovenant()) return;
  if (SpreeTarget() > Game.wrinklersPopped) {
    Spree();
    return;
  }
  const { calm, wrath } = StageIncomes();
  if (Game.Has('Elder Pact') && calm > wrath && Pledge()) return;
  PopWrinklers();
}

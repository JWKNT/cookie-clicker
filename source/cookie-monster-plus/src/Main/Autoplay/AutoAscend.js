import { KittenMilkFactor, MilkMultiplier } from '../../Cache/PP/AutoplayValue.js';
import { AscensionCache, AutoClickIncome } from '../../Cache/Stats/Ascension.js';
import HeavenlyPurchaseOrder, { HeavenlyContext } from '../../Cache/Stats/HeavenlyPlan.js';
import { CacheWrinklersNormal } from '../../Cache/VariablesAndData.js';
import Beautify from '../../Disp/BeautifyAndFormatting/Beautify.js';
import { FormatPercent } from '../../Disp/HelperFunctions/AscensionSummary.js';
import PopAllNormalWrinklers from '../../Disp/HelperFunctions/PopWrinklers.js';
import { ReadySeconds, SUSTAIN_SECONDS } from '../CheckStates/Ascension.js';
import { AvailableLoans, LOANS } from './AutoMarket.js';
import { ChallengeDone, ChallengeDue, ChallengeRun } from './Challenge.js';

/** Seconds to let wrinklers pop before ascending, and to show the heavenly screen before leaving it */
const CASH_IN_SECONDS = 2;
const HEAVEN_SECONDS = 1.5;
/** Seconds before a loan runs out at which the run may end early to avoid its interest */
const LOAN_EXIT_SECONDS = 60;

let Phase = 'idle';
let PhaseSince = 0;
/** Whether the run being left is a Born again run */
let LeavingChallenge = false;

/**
 * Buys a heavenly upgrade after the unowned parents it requires, as the ascension screen only allows
 * upgrades whose parents are all owned
 * @param	{object}	me	A heavenly upgrade
 * @returns	{boolean}	Whether it is owned afterwards
 */
function BuyWithParents(me) {
  if (me.bought) return true;
  if (me.showIf && !me.showIf()) return false;
  for (let i = 0; i < me.parents.length; i++) {
    if (me.parents[i] !== -1 && !BuyWithParents(me.parents[i])) return false;
  }
  return me.getPrice() <= Game.heavenlyChips && me.buy() === 1;
}

/** Permanent upgrade slots, in the order of Game.permanentUpgrades */
const PERMANENT_SLOTS = [
  'Permanent upgrade slot I',
  'Permanent upgrade slot II',
  'Permanent upgrade slot III',
  'Permanent upgrade slot IV',
  'Permanent upgrade slot V',
];

/**
 * How much an upgrade kept in a permanent slot multiplies CpS at the start of a run, as a logarithm:
 * milk carries over, so a kitten multiplies CpS by 1 + k * milk at once, and a cookie by 1 + its power;
 * other upgrades act on buildings the run has yet to buy
 * @param	{object}	me	Upgrade
 * @returns	{number}
 */
export function StartValue(me) {
  const k = KittenMilkFactor(me.name);
  if (k) return Math.log1p(k * (Game.milkProgress || 0) * MilkMultiplier());
  const power = typeof me.power === 'function' ? me.power(me) : me.power;
  return me.pool === 'cookie' && power > 0 ? Math.log1p(power / 100) : 0;
}

/**
 * Puts the upgrades worth most at the start of a run into the permanent slots owned, as picking them in
 * the ascension screen does (candidates are the upgrades bought last run that the game allows there)
 */
function FillPermanentSlots() {
  const owned = PERMANENT_SLOTS.map((name, i) => (Game.Has(name) ? i : -1)).filter((i) => i !== -1);
  if (!owned.length) return;
  const candidates = Object.keys(Game.Upgrades)
    .map((name) => Game.Upgrades[name])
    .filter(
      (me) =>
        me.bought &&
        me.unlocked &&
        !me.noPerm &&
        (me.pool === '' || me.pool === 'cookie') &&
        StartValue(me) > 0,
    )
    .sort((a, b) => StartValue(b) - StartValue(a));
  owned.forEach((slot, i) => {
    if (candidates[i]) Game.permanentUpgrades[slot] = candidates[i].id;
  });
  if (Game.BuildAscendTree) Game.BuildAscendTree();
}

/**
 * Spends heavenly chips: Legacy first, then along the purchase order the ascension planner assumes
 * (best production gain per chip, parents included), buying as many items as the chips cover and
 * saving the rest for the next one; then fills the permanent upgrade slots
 */
export function SpendHeavenlyChips() {
  if (!BuyWithParents(Game.Upgrades.Legacy)) return;
  const context =
    AscensionCache.heavenlyContext || HeavenlyContext(Game.cookiesPs, AutoClickIncome());
  const order = HeavenlyPurchaseOrder(context);
  for (let i = 0; i < order.length && order[i].cost <= Game.heavenlyChips; i++) {
    order[i].bundle.forEach((me) => {
      if (!me.bought) me.buy();
    });
  }
  FillPermanentSlots();
}

/**
 * Whether ending the run now costs less than the interest of a loan about to run out: the interest
 * divides CpS for hours, which delays the run by about (1 - multiplier) of the time it covers
 * @returns	{boolean}
 */
function LoanExit() {
  const { plan } = AscensionCache;
  if (!plan || !plan.applicable || plan.costOfAscendingNow === null) return false;
  return LOANS.some((loan) => {
    const buff = Game.hasBuff(`Loan ${loan.id}`);
    if (!buff || buff.time / Game.fps > LOAN_EXIT_SECONDS) return false;
    const penalty = (1 - loan.interest) * Math.min(loan.interestSeconds, plan.remaining);
    return plan.costOfAscendingNow < penalty;
  });
}

/**
 * Ascends when the advisor has said so for SUSTAIN_SECONDS (or a Born again run is over): pops normal
 * wrinklers and buys the Chocolate egg first, spends the heavenly chips and reincarnates, into a Born
 * again run when the challenge achievements are due
 * It is called every logic frame, also while ascending
 */
export default function AutoAscend() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const now = Date.now();
  const elapsed = (now - PhaseSince) / 1000;
  const enter = (phase) => {
    Phase = phase;
    PhaseSince = now;
  };

  if (Phase === 'idle') {
    if (!settings.AutoAscend || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
      return;
    if (ChallengeRun() ? !ChallengeDone() : ReadySeconds() < SUSTAIN_SECONDS && !LoanExit())
      return;
    if (CacheWrinklersNormal > 0) PopAllNormalWrinklers();
    const egg = Game.Upgrades['Chocolate egg'];
    if (egg && egg.unlocked && !egg.bought) egg.buy();
    enter('cashing');
  } else if (Phase === 'cashing') {
    if (elapsed < CASH_IN_SECONDS) return;
    const { plan } = AscensionCache;
    LeavingChallenge = ChallengeRun();
    if (
      !settings.AutoAscend ||
      (!LeavingChallenge && (!plan || !plan.ascendNow) && !LoanExit())
    ) {
      enter('idle');
      return;
    }
    // The bank is about to be lost, so a loan's down payment costs nothing now: "Debt evasion"
    const loans = AvailableLoans();
    if (!Game.HasAchiev('Debt evasion') && loans.length)
      Game.Objects.Bank.minigame.takeLoan(loans[0].id);
    if (LeavingChallenge)
      Game.Notify(
        'Cookie Monster+ ended the Born again run',
        `Neverclick: ${Game.HasAchiev('Neverclick') ? 'won' : 'missed'}, Hardcore: ${
          Game.HasAchiev('Hardcore') ? 'won' : 'missed'
        }. Back to a normal run.`,
        [10, 0],
      );
    else
      Game.Notify(
        'Cookie Monster+ ascended',
        `+${Beautify(plan.levelsNow)} prestige levels, +${FormatPercent(
          plan.speedGainNow * 100,
        )} production in every future run.`,
        [19, 7],
      );
    Game.Ascend(1);
    enter('ascending');
  } else if (Phase === 'ascending') {
    if (Game.OnAscend) enter('heaven');
    else if (elapsed > 30 && Game.AscendTimer === 0) enter('idle');
  } else if (Phase === 'heaven') {
    if (!Game.OnAscend) enter('idle');
    else if (elapsed >= HEAVEN_SECONDS) {
      SpendHeavenlyChips();
      Game.nextAscensionMode = ChallengeDue(LeavingChallenge) ? 1 : 0;
      Game.Reincarnate(1);
      enter('reincarnating');
    }
  } else if (Phase === 'reincarnating' && !Game.OnAscend && Game.ReincarnateTimer === 0) {
    enter('idle');
  }
}

import { KittenMilkFactor, MilkMultiplier } from '../../Cache/PP/AutoplayValue.js';
import { AscensionCache, AutoClickIncome } from '../../Cache/Stats/Ascension.js';
import HeavenlyPurchaseOrder, { HeavenlyContext } from '../../Cache/Stats/HeavenlyPlan.js';
import Beautify from '../../Disp/BeautifyAndFormatting/Beautify.js';
import { FormatPercent } from '../../Disp/HelperFunctions/AscensionSummary.js';
import { ReadySeconds, SUSTAIN_SECONDS } from '../CheckStates/Ascension.js';
import { AvailableLoans, LOANS } from './AutoMarket.js';
import { ClickMarketLoan } from './MarketControls.js';
import { ChallengeDone, ChallengeDue, ChallengeRun } from './Challenge.js';
import { CastBeforeAscension } from './AutoGrimoire.js';
import {
  BuyForStarsInHeaven, CashInChocolateEgg, LuckyPrestigeWait, RequestWrinklerPayouts,
  SkipAscensionAnimation, SpendHeavenlyOrder, STARS_BUDGET,
} from './AscensionActions.js';

/** Seconds before a loan runs out at which the run may end early to avoid its interest */
const LOAN_EXIT_SECONDS = 60;

let Phase = 'idle';
let PhaseSince = 0;
/** Whether the run being left is a Born again run */
let LeavingChallenge = false;

/** Keep the cash-in bank available until the egg is bought or the reset is cancelled. */
export function AscensionCashInProgress() {
  return Phase === 'cashing';
}

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
 * saving the rest for the next one; then the cheapest upgrades still missing for "All the stars in
 * heaven" if they cost at most STARS_BUDGET of the chips; then fills the permanent upgrade slots
 */
export function SpendHeavenlyChips() {
  if (!BuyWithParents(Game.Upgrades.Legacy)) return;
  const budget = STARS_BUDGET * Game.heavenlyChips;
  const context =
    AscensionCache.heavenlyContext || HeavenlyContext(Game.cookiesPs, AutoClickIncome());
  const order = HeavenlyPurchaseOrder(context);
  SpendHeavenlyOrder(order);
  BuyForStarsInHeaven(budget);
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
 * Ascends when the advisor has said so for SUSTAIN_SECONDS (or a Born again run is over): pops all
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
    if (
      !settings.AutoAscend || Game.promptOn || Game.OnAscend
      || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0
    )
      return;
    if (ChallengeRun() ? !ChallengeDone() : ReadySeconds() < SUSTAIN_SECONDS && !LoanExit())
      return;
    // Payout occurs in a later native game update, before cash-in can continue.
    RequestWrinklerPayouts();
    enter('cashing');
  } else if (Phase === 'cashing') {
    if (Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0) {
      enter('idle');
      return;
    }
    const { plan } = AscensionCache;
    LeavingChallenge = ChallengeRun();
    if (
      !settings.AutoAscend ||
      (!LeavingChallenge && (!plan || !plan.ascendNow) && !LoanExit())
    ) {
      enter('idle');
      return;
    }
    if (Game.promptOn) return;
    // A wrinkler can start storing cookies after cash-in begins. Include it before the egg.
    RequestWrinklerPayouts();
    if (!CashInChocolateEgg()) return;
    // The bank is about to be lost, so a loan's down payment costs nothing now: "Debt evasion"
    const loans = AvailableLoans();
    if (!Game.HasAchiev('Debt evasion') && loans.length && !ClickMarketLoan(loans[0].id)) return;
    if (LuckyPrestigeWait(elapsed)) return;
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
    if (!LeavingChallenge) CastBeforeAscension();
    Game.Ascend(1);
    enter('ascending');
    SkipAscensionAnimation();
  } else if (Phase === 'ascending') {
    if (Game.OnAscend) enter('heaven');
    else if (elapsed > 30 && Game.AscendTimer === 0) enter('idle');
  } else if (Phase === 'heaven') {
    if (!Game.OnAscend) enter('idle');
    else if (!settings.AutoAscend) enter('idle');
    else if (!Game.promptOn && Game.AscendTimer === 0 && Game.ReincarnateTimer === 0) {
      SpendHeavenlyChips();
      Game.nextAscensionMode = ChallengeDue(LeavingChallenge) ? 1 : 0;
      Game.Reincarnate(1);
      enter('reincarnating');
    }
  } else if (Phase === 'reincarnating' && !Game.OnAscend && Game.ReincarnateTimer === 0) {
    enter('idle');
  }
}

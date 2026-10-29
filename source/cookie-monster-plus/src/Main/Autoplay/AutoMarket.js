/**
 * Section: the Stock Market under autoplay
 *
 * Goods cost "dollars", seconds of the highest raw CpS of the run, and their prices drift back toward a
 * resting value of 10 + 10 * (good index) + (bank level - 1). Buying carries an overhead of 20% (less with
 * brokers); selling is free. Buying well below the resting value and selling at or above it therefore
 * clears the overhead with room to spare, using only the prices the market shows. Spending is capped to
 * a share of the bank so the market never starves the auto-buyer.
 *
 * The offices are upgraded whenever the cursors allow (it sacrifices cheap cursors and needs cursor
 * levels), since they open loans. A loan multiplies CpS for a while against a down payment of part of the
 * bank, and then divides it for longer; ascending before the interest starts avoids it ("Debt evasion").
 * So a loan is taken once the ascension planner expects the run to end before it runs out, even on its
 * slow estimate, and the ascension routine ends the run early rather than pay the interest.
 */

import { AscensionCache } from '../../Cache/Stats/Ascension.js';

/** Buy below this share of a good's resting value, sell at or above SELL_AT */
const BUY_BELOW = 0.6;
const SELL_AT = 1;
/** Share of the bank (above any reserve) the market may hold in goods at once */
const BANK_SHARE = 0.1;

/**
 * Loans: CpS multiplier, its seconds, the interest multiplier and its seconds, and the office level
 * above which the loan is offered (from the game's loan table and bank display)
 */
export const LOANS = [
  { id: 1, mult: 1.5, seconds: 2 * 3600, interest: 0.25, interestSeconds: 4 * 3600, office: 1 },
  { id: 2, mult: 2, seconds: 40, interest: 0.1, interestSeconds: 40 * 60, office: 3 },
  { id: 3, mult: 1.2, seconds: 48 * 3600, interest: 0.8, interestSeconds: 120 * 3600, office: 4 },
];
/** Share of the loan's time the planner's slow estimate of the run may use up */
const LOAN_MARGIN = 0.9;

/**
 * Loans the offices offer now and that are not running (nor their interest)
 * @returns	{object[]}	Entries of LOANS
 */
export function AvailableLoans() {
  const bank = Game.Objects.Bank;
  if (!bank.minigameLoaded || !bank.minigame || Game.ascensionMode !== 0) return [];
  const M = bank.minigame;
  return LOANS.filter(
    (loan) =>
      M.officeLevel > loan.office &&
      !Game.hasBuff(`Loan ${loan.id}`) &&
      !Game.hasBuff(`Loan ${loan.id} (interest)`),
  );
}

/**
 * Takes the loans whose boost outlasts the rest of the run on the planner's slow estimate
 */
function TakeLoans() {
  const { plan } = AscensionCache;
  if (!plan || !plan.applicable || !Number.isFinite(plan.remainingSlow)) return;
  AvailableLoans().forEach((loan) => {
    if (loan.id !== 2 && plan.remainingSlow <= LOAN_MARGIN * loan.seconds)
      Game.Objects.Bank.minigame.takeLoan(loan.id);
  });
}

/**
 * Upgrades the office when the cursors allow, as its button does
 * @returns	{boolean}	Whether it upgraded
 */
function UpgradeOffice() {
  const M = Game.Objects.Bank.minigame;
  const office = M.offices[M.officeLevel];
  const cursor = Game.Objects.Cursor;
  if (!office || !office.cost || !l('bankOfficeUpgrade')) return false;
  if (cursor.amount < office.cost[0] || cursor.level < office.cost[1]) return false;
  l('bankOfficeUpgrade').click();
  return true;
}

/**
 * Cookies currently tied up in goods, at today's prices
 * @param	{object}	M	Market minigame
 * @returns	{number}
 */
function Holdings(M) {
  return M.goodsById.reduce(
    (sum, me) => sum + me.stock * M.getGoodPrice(me) * Game.cookiesPsRawHighest,
    0,
  );
}

/**
 * Upgrades the office, takes loans that will not reach their interest, and trades every active good:
 * sells what reached its resting value, buys what fell far below it
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoMarket() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const bank = Game.Objects.Bank;
  if (!settings.AutoMarket || !bank.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0) return;
  const M = bank.minigame;
  if (!M || !M.goodsById) return;
  if (UpgradeOffice()) return;
  TakeLoans();
  for (let id = 0; id < M.goodsById.length; id++) {
    const me = M.goodsById[id];
    if (me.active) {
      const rest = M.getRestingVal(id);
      const price = M.getGoodPrice(me);
      if (me.stock > 0 && price >= rest * SELL_AT && M.sellGood(id, me.stock)) return;
      if (price <= rest * BUY_BELOW && me.stock < M.getGoodMaxStock(me)) {
        const overhead = 1 + 0.01 * (20 * 0.95 ** M.brokers);
        const unit = Game.cookiesPsRawHighest * price * overhead;
        const budget = Game.cookies * BANK_SHARE - Holdings(M);
        const n = Math.min(M.getGoodMaxStock(me) - me.stock, Math.floor(budget / unit));
        if (n > 0 && M.buyGood(id, n)) return;
      }
    }
  }
}

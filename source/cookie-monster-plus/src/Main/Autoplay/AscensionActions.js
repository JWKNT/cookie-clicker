/** Cash-in and purchase actions shared by the ascension planner and automation. */

/** Request every stored wrinkler payout before the bank is used for the egg. */
export function RequestWrinklerPayouts() {
  for (let i = 0; i < Game.wrinklers.length; i++) {
    const me = Game.wrinklers[i];
    if (me.phase > 0 && me.sucked > 0 && me.hp > 0.5) me.hp = 0;
  }
}

/** Use the game's Escape handler only during the ascension started by the caller. */
export function SkipAscensionAnimation() {
  if (
    Game.promptOn || Game.OnAscend || Game.AscendTimer <= 0 || Game.ReincarnateTimer > 0
  ) return false;
  const event = new KeyboardEvent('keyup', {
    key: 'Escape', code: 'Escape', keyCode: 27, which: 27,
  });
  // Cookie Clicker 2.053 reads keyCode. Some event constructors ignore its initializer.
  if (event.keyCode !== 27) Object.defineProperty(event, 'keyCode', { value: 27 });
  window.dispatchEvent(event);
  return Game.AscendTimer >= Game.AscendDuration;
}

/** Egg payout from a specified bank after its purchase price, without asset liquidation. */
export function ChocolateEggPayout(bank) {
  const egg = Game.Upgrades['Chocolate egg'];
  if (!egg || !egg.unlocked || egg.bought) return 0;
  return 0.05 * Math.max(0, bank - egg.getPrice());
}

/** Buy the egg after pending wrinkler payouts. Return false while a payout is pending. */
export function CashInChocolateEgg() {
  if (Game.wrinklers.some((me) => me.phase > 0 && me.hp <= 0.5)) return false;
  const egg = Game.Upgrades['Chocolate egg'];
  if (egg && egg.unlocked && !egg.bought) egg.buy();
  return true;
}

/** Seconds of cash-in that may pass while ascending waits for a prestige level with four 7s. */
export const LUCKY_WAIT_SECONDS = 60;

/**
 * Wait before ascending for a prestige level whose digits contain four 7s: only then does the ascension
 * screen sell "Lucky payout" (+1% prestige effect and golden cookie duration in every later run).
 * The game earns no cookies during the ascension animation, so the frame that starts the ascension
 * fixes the prestige level, and each frame adds about CpS / fps cookies.
 */
export function LuckyPrestigeWait(elapsed) {
  const me = Game.Upgrades['Lucky payout'];
  if (!me || me.bought || elapsed > LUCKY_WAIT_SECONDS) return false;
  if (me.parents.some((parent) => parent !== -1 && !parent.bought)) return false;
  const prestige = Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned));
  return `${prestige}`.split('7').length - 1 < 4;
}

/** Buy the affordable prefix of a planned heavenly order, including partial parent bundles. */
export function SpendHeavenlyOrder(order) {
  const upgrades = order.flatMap((item) => item.bundle);
  for (let i = 0; i < upgrades.length; i++) {
    const me = upgrades[i];
    if (!me.bought && (me.getPrice() > Game.heavenlyChips || me.buy() !== 1)) break;
  }
}

/** Heavenly upgrades owned for "All the stars in heaven", which the game awards at reincarnation. */
export const STARS_IN_HEAVEN = 100;
/** Share of the chips held at ascension that the upgrades bought only for that count may cost. */
export const STARS_BUDGET = 0.01;
/** Never bought for the count, with their children: the Sugar frenzy takes the lumps that other uses need, and the veil breaks on every click. */
const NOT_FOR_STARS = ['Sugar craving', 'Shimmering veil'];

/**
 * Buy the cheapest available heavenly upgrades that are still missing for "All the stars in heaven",
 * when all of them cost at most `budget` chips. One achievement adds 4% milk to every run.
 */
export function BuyForStarsInHeaven(budget) {
  if (Game.HasAchiev('All the stars in heaven')) return 0;
  const all = Game.PrestigeUpgrades;
  const taken = new Set();
  const ready = (me) => me === -1 || me.bought || taken.has(me);
  let missing = STARS_IN_HEAVEN - all.filter((me) => me.bought).length;
  let cost = 0;
  while (missing > 0) {
    let next = null;
    for (let i = 0; i < all.length; i++) {
      const me = all[i];
      if (!me.bought && !taken.has(me) && !NOT_FOR_STARS.includes(me.name)
        && (!me.showIf || me.showIf()) && me.parents.every(ready)
        && (next === null || me.getPrice() < next.getPrice())) next = me;
    }
    if (next === null) return 0;
    taken.add(next);
    cost += next.getPrice();
    missing -= 1;
  }
  if (cost > Math.min(budget, Game.heavenlyChips)) return 0;
  let bought = 0;
  taken.forEach((me) => {
    if (me.buy() === 1) bought += 1;
  });
  return bought;
}

import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import { Copies, KeepPlan, MAX_COPIES, Rank } from '../../src/Main/Autoplay/AutoBuy.js';

/** A building whose copies cost 1.15 times the copy before them, rounded up as in the game */
function Building(basePrice, value) {
  const me = {
    basePrice,
    amount: 0,
    free: 0,
    getPrice() {
      return Math.ceil(this.basePrice * 1.15 ** Math.max(0, this.amount - this.free));
    },
  };
  return { name: 'Building', me, building: true, value };
}

function Upgrade(price, value) {
  return { name: 'Upgrade', me: { bought: 0, getPrice: () => price }, building: false, value };
}

const NoReserve = {
  keepLucky: false,
  bankPayback: Infinity,
  luckyBank: 0,
  seasonReserve: 0,
  seasonPayback: 60,
};

describe('Burst purchases', () => {
  const saved = {};
  before(() => {
    global.Game = Game;
    saved.modifyBuildingPrice = Game.modifyBuildingPrice;
    saved.priceIncrease = Game.priceIncrease;
    Game.modifyBuildingPrice = (me, price) => price;
    Game.priceIncrease = 1.15;
  });
  after(() => {
    Game.modifyBuildingPrice = saved.modifyBuildingPrice;
    Game.priceIncrease = saved.priceIncrease;
  });

  it('Ranks affordable purchases by payback period and names the runner-up', () => {
    const cheap = Building(100, 1);
    const slow = Upgrade(500, 2);
    const { best, second } = Rank([slow, cheap], 1000, 10, NoReserve);
    expect(best.c).to.equal(cheap);
    expect(second.c).to.equal(slow);
    expect(best.pp).to.equal(100);
    expect(second.pp).to.equal(250);
  });

  it('Adds the time to save up above the "Lucky!" bank to a slow purchase', () => {
    const rules = { ...NoReserve, keepLucky: true, bankPayback: 150, luckyBank: 600 };
    const { best } = Rank([Upgrade(500, 2)], 1000, 10, rules);
    expect(best.reserve).to.equal(600);
    expect(best.reason).to.equal('lucky');
    expect(best.pp).to.equal((500 - 400) / 10 + 250);
  });

  it('Buys copies of a building while they pay back no slower than the runner-up', () => {
    const { best, second } = Rank([Building(100, 1), Upgrade(10000, 50)], 1e6, 10, NoReserve);
    // Copies cost 100, 115, 133, 153, 175 and 202. The runner-up pays back in 200 seconds.
    expect(Copies(best, second, 1e6, NoReserve)).to.equal(5);
  });

  it('Buys only the copies that the bank pays for, and at least one', () => {
    const building = Building(100, 1);
    // 100 + 115 + 133 = 348 fits in 400. A fourth copy costs 153 more.
    expect(Copies(Rank([building], 400, 10, NoReserve).best, null, 400, NoReserve)).to.equal(3);
    expect(Copies(Rank([building], 100, 10, NoReserve).best, null, 100, NoReserve)).to.equal(1);
  });

  it('Stops before the first copy that would keep the "Lucky!" bank back', () => {
    const rules = { ...NoReserve, keepLucky: true, bankPayback: 140, luckyBank: 1e5 };
    const { best } = Rank([Building(100, 1)], 1e6, 10, rules);
    // Copies pay back in 100, 115, 133 and 153 seconds. Only the fourth is slower than 140 seconds.
    expect(best.reserve).to.equal(0);
    expect(Copies(best, null, 1e6, rules)).to.equal(3);
  });

  it('Keeps cookies for a seasonal action only from purchases that pay back slowly', () => {
    const rules = { ...NoReserve, seasonReserve: 900 };
    const fast = Rank([Upgrade(500, 10)], 1000, 10, rules).best; // pays back in 50 seconds
    expect(fast.reserve).to.equal(0);
    const slow = Rank([Upgrade(500, 2)], 1000, 10, rules).best; // pays back in 250 seconds
    expect(slow.reserve).to.equal(900);
    expect(slow.reason).to.equal('season');
  });

  it('Checks the plan a few times a second while it saves up, and at once when it is affordable', () => {
    const next = { price: 10, reserve: 2 };
    expect(KeepPlan(100, 105, next, 5)).to.equal(true);
    expect(KeepPlan(100, 105, null, 0)).to.equal(true);
    expect(KeepPlan(100, 105, next, 12)).to.equal(false);
    expect(KeepPlan(105, 105, next, 5)).to.equal(false);
  });

  it('Ignores a check scheduled in an earlier run, after an ascension resets Game.T', () => {
    // Game.Reset() sets Game.T to 0. A check scheduled at frame 27010 must not stop the new run.
    expect(KeepPlan(3, 27010, null, 0)).to.equal(false);
    expect(KeepPlan(3, 27010, { price: 10, reserve: 0 }, 5)).to.equal(false);
  });

  it('Buys at most MAX_COPIES copies at once', () => {
    const { best } = Rank([Building(1, 1e300)], 1e300, 10, NoReserve);
    expect(Copies(best, null, 1e300, NoReserve)).to.equal(MAX_COPIES);
  });
});

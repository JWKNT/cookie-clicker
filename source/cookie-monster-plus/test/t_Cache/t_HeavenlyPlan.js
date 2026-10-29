import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import HeavenlyPurchaseOrder, {
  HeavenlyUpgradeValues,
} from '../../src/Cache/Stats/HeavenlyPlan.js';

/** Builds mock heavenly upgrades: {name: [price, parentNames]} */
function MockUpgrades(spec) {
  const upgrades = {};
  Object.keys(spec).forEach((name) => {
    upgrades[name] = {
      name,
      bought: false,
      price: spec[name][0],
      getPrice() {
        return this.price;
      },
    };
  });
  Object.keys(spec).forEach((name) => {
    upgrades[name].parents = spec[name][1].map((parent) => upgrades[parent]);
  });
  return upgrades;
}

/** Time to earn the chips for a purchase order when chips come in at a rate proportional to speed */
function OrderTime(items) {
  let speed = 1;
  let time = 0;
  items.forEach((item) => {
    time += item.cost / speed;
    speed *= item.mult;
  });
  return time;
}

function Permutations(list) {
  if (list.length <= 1) return [list];
  return list.flatMap((item, i) =>
    Permutations([...list.slice(0, i), ...list.slice(i + 1)]).map((rest) => [item, ...rest]),
  );
}

const ctx = { clickShare: 0, golden: { frenzy: 0, lucky: 0, total: 0 }, autoplay: {} };

describe('HeavenlyPurchaseOrder', () => {
  const saved = {};
  before(() => {
    global.Game = Game;
    ['Upgrades', 'heralds', 'milkProgress', 'lumps'].forEach((key) => {
      saved[key] = Game[key];
    });
    Game.lumps = 0;
  });
  after(() => {
    Object.keys(saved).forEach((key) => {
      Game[key] = saved[key];
    });
  });

  it('Ranks by time saved per chip, (1 - 1/m) / cost, not by log-gain per chip', () => {
    // Heralds x4 for 100 chips vs Kitten angels x1.25 for 25 chips: ln(m)/cost prefers Heralds,
    // the exact exchange index prefers Kitten angels (0.008 > 0.0075)
    Game.heralds = 300;
    Game.milkProgress = 2.5;
    Game.Upgrades = MockUpgrades({
      Legacy: [1, []],
      Heralds: [100, ['Legacy']],
      'Kitten angels': [25, ['Legacy']],
    });
    const order = HeavenlyPurchaseOrder(ctx).map((item) => item.name);
    expect(order).to.deep.equal(['Kitten angels', 'Heralds']);
  });

  it('Buys parents in the same bundle, before the upgrade that needs them', () => {
    Game.heralds = 0;
    Game.milkProgress = 0;
    Game.Upgrades = MockUpgrades({
      Legacy: [1, []],
      'Heavenly cookies': [3, ['Legacy']],
      'Tin of british tea biscuits': [25, ['Heavenly cookies']],
      'Box of macarons': [25, ['Heavenly cookies']],
      'Box of brand biscuits': [25, ['Heavenly cookies']],
      'Tin of butter cookies': [25, ['Heavenly cookies']],
      'Starter kit': [
        50,
        [
          'Tin of british tea biscuits',
          'Box of macarons',
          'Box of brand biscuits',
          'Tin of butter cookies',
        ],
      ],
    });
    const order = HeavenlyPurchaseOrder(ctx);
    expect(order[0].name).to.equal('Heavenly cookies');
    const kit = order.find((item) => item.name === 'Starter kit');
    expect(kit.bundle.map((me) => me.name)).to.deep.equal(['Starter kit']);
    const flattened = order.flatMap((item) => item.bundle.map((me) => me.name));
    expect(flattened.indexOf('Starter kit')).to.equal(flattened.length - 1);
  });

  it('Matches the brute-force optimal order when there are no parent constraints', () => {
    Game.heralds = 40;
    Game.milkProgress = 3;
    const names = [
      'Heavenly cookies',
      'Heralds',
      'Kitten angels',
      'Sugar crystal cookies',
      'Divine bakeries',
      'Synergies Vol. I',
    ];
    let seed = 7;
    const random = () => {
      seed = (seed * 16807) % 2147483647;
      return seed / 2147483647;
    };
    for (let trial = 0; trial < 20; trial++) {
      const spec = { Legacy: [1, []] };
      names.forEach((name) => {
        spec[name] = [Math.round(1 + random() * 1000), ['Legacy']];
      });
      Game.Upgrades = MockUpgrades(spec);
      const order = HeavenlyPurchaseOrder(ctx);
      const items = names.map((name) => ({
        cost: spec[name][0],
        mult: HeavenlyUpgradeValues[name](ctx),
      }));
      const best = Math.min(...Permutations(items).map(OrderTime));
      expect(OrderTime(order)).to.be.closeTo(best, best * 1e-12);
    }
  });
});

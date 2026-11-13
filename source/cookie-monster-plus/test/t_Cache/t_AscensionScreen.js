import { afterEach, beforeEach, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import {
  BuyForStarsInHeaven,
  LUCKY_WAIT_SECONDS,
  LuckyPrestigeWait,
} from '../../src/Main/Autoplay/AscensionActions.js';

/** Builds mock heavenly upgrades: {name: [price, parentNames, bought]}, as Game.PrestigeUpgrades */
function MockPrestige(spec) {
  const upgrades = {};
  Object.keys(spec).forEach((name) => {
    upgrades[name] = {
      name,
      bought: !!spec[name][2],
      price: spec[name][0],
      getPrice() {
        return this.price;
      },
      buy() {
        if (this.bought || Game.heavenlyChips < this.price) return 0;
        if (this.parents.some((me) => me !== -1 && !me.bought)) return 0;
        Game.heavenlyChips -= this.price;
        this.bought = true;
        Game.log.push(this.name);
        return 1;
      },
    };
  });
  Object.keys(spec).forEach((name) => {
    upgrades[name].parents = spec[name][1].map((parent) => upgrades[parent]);
    if (!spec[name][1].length) upgrades[name].parents = [-1];
  });
  return upgrades;
}

describe('All the stars in heaven', () => {
  let saved;
  let upgrades;
  beforeEach(() => {
    global.Game = Game;
    saved = { ...Game };
    // 96 owned upgrades, so four more earn the achievement
    const spec = {};
    for (let i = 0; i < 96; i++) spec[`Owned ${i}`] = [1, [], true];
    Object.assign(spec, {
      Root: [1, [], true],
      Cheap: [5, ['Root']],
      Child: [1, ['Cheap']],
      Dear: [50, ['Root']],
      Dearer: [70, ['Root']],
      'Sugar craving': [1, ['Root']],
      'Sugar aging process': [1, ['Sugar craving']],
      'Shimmering veil': [1, ['Root']],
      Hidden: [2, ['Root']],
    });
    spec['Owned 95'][2] = false;
    upgrades = MockPrestige(spec);
    upgrades.Hidden.showIf = () => false;
    Game.PrestigeUpgrades = Object.values(upgrades);
    Game.HasAchiev = () => false;
    Game.heavenlyChips = 1000;
    Game.log = [];
  });
  afterEach(() => {
    Object.keys(Game).forEach((key) => {
      if (!(key in saved)) delete Game[key];
    });
    Object.assign(Game, saved);
  });

  it('Buys the cheapest available upgrades, parents first, never the sugar frenzy or the veil', () => {
    expect(BuyForStarsInHeaven(100)).to.equal(4);
    expect(Game.log).to.deep.equal(['Owned 95', 'Cheap', 'Child', 'Dear']);
    expect(Game.heavenlyChips).to.equal(1000 - 1 - 5 - 1 - 50);
    expect(upgrades['Sugar craving'].bought).to.equal(false);
    expect(upgrades['Shimmering veil'].bought).to.equal(false);
  });

  it('Buys none of them when together they cost more than the budget', () => {
    expect(BuyForStarsInHeaven(56)).to.equal(0);
    expect(Game.log).to.deep.equal([]);
    Game.heavenlyChips = 50;
    expect(BuyForStarsInHeaven(100)).to.equal(0);
    expect(Game.log).to.deep.equal([]);
  });

  it('Buys nothing once the achievement is owned or no upgrades are missing', () => {
    Game.HasAchiev = (name) => name === 'All the stars in heaven';
    expect(BuyForStarsInHeaven(1000)).to.equal(0);
    Game.HasAchiev = () => false;
    upgrades['Owned 95'].bought = true;
    upgrades.Dear.bought = true;
    upgrades.Dearer.bought = true;
    upgrades.Cheap.bought = true;
    expect(BuyForStarsInHeaven(1000)).to.equal(0);
    expect(Game.log).to.deep.equal([]);
  });
});

describe('Lucky payout', () => {
  let saved;
  let payout;
  beforeEach(() => {
    global.Game = Game;
    saved = { ...Game };
    const parents = [{ bought: true }, { bought: true }];
    payout = { name: 'Lucky payout', bought: false, parents };
    Game.Upgrades = { 'Lucky payout': payout };
    Game.cookiesReset = 0;
    // As in the game: prestige is the cube root of all-time cookies in trillions
    Game.HowMuchPrestige = (cookies) => Math.cbrt(cookies / 1e12);
  });
  afterEach(() => {
    Object.keys(Game).forEach((key) => {
      if (!(key in saved)) delete Game[key];
    });
    Object.assign(Game, saved);
  });

  it('Waits until the prestige level that ascending gives contains four 7s', () => {
    Game.cookiesEarned = 1777.5 ** 3 * 1e12;
    expect(LuckyPrestigeWait(0)).to.equal(true);
    Game.cookiesEarned = 7777.5 ** 3 * 1e12;
    expect(LuckyPrestigeWait(0)).to.equal(false);
    Game.cookiesEarned = 707077.5 ** 3 * 1e12;
    expect(LuckyPrestigeWait(0)).to.equal(false);
  });

  it('Does not wait once it is owned, without its parents or after the time limit', () => {
    Game.cookiesEarned = 1712.5 ** 3 * 1e12;
    expect(LuckyPrestigeWait(LUCKY_WAIT_SECONDS + 1)).to.equal(false);
    payout.parents[1].bought = false;
    expect(LuckyPrestigeWait(0)).to.equal(false);
    payout.parents[1].bought = true;
    payout.bought = true;
    expect(LuckyPrestigeWait(0)).to.equal(false);
    delete Game.Upgrades['Lucky payout'];
    expect(LuckyPrestigeWait(0)).to.equal(false);
  });
});

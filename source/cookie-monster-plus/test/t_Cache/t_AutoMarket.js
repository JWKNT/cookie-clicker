import { describe, it } from 'mocha';
import { expect } from 'chai';
import { readFileSync } from 'node:fs';
import { runInNewContext } from 'node:vm';

function Source(name) {
  return readFileSync(new URL(`../../src/Main/Autoplay/${name}.js`, import.meta.url), 'utf8')
    .replace(/^import[\s\S]*?;\n/gm, '').replace(/export (default )?/g, '');
}

function Fixture() {
  const events = [];
  const buffs = {};
  const M = {
    officeLevel: 0, offices: [{ cost: [100, 2] }, { cost: 0 }], goodsById: [],
    takeLoan() { throw new Error('Direct loan call bypassed its button'); },
  };
  const bank = { id: 5, minigameLoaded: true, onMinigame: true, minigame: M };
  const controls = {
    bankOfficeUpgrade: { style: {}, click() { M.officeLevel += 1; events.push('office'); } },
    bankLoan1: { style: { display: 'none' }, click() { buffs['Loan 1'] = { time: 100 }; events.push('loan'); } },
    productMinigameButton5: { style: {}, click() { bank.onMinigame = true; events.push('open'); } },
  };
  const Game = {
    Objects: { Bank: bank, Cursor: { amount: 1000, level: 12 } },
    ascensionMode: 0, OnAscend: false, AscendTimer: 0, ReincarnateTimer: 0,
    promptOn: false, onMenu: '', cookies: 10000, cookiesPsRawHighest: 1,
    hasBuff: (name) => buffs[name] || 0, HasAchiev: () => false,
    Notify() {}, Ascend() { events.push('ascend'); this.AscendTimer = 1; },
    mods: { cookieMonsterFramework: { saveData: { cookieMonsterMod: {
      settings: { AutoMarket: true, AutoAscend: true },
    } } } },
  };
  const context = { Game, l: (id) => controls[id], Date };
  runInNewContext(`var AscensionCache={plan:{applicable:true,remainingSlow:10,ascendNow:true,levelsNow:1,speedGainNow:0.1}};
    ${Source('MarketControls')}\n${Source('AutoMarket')}`, context);
  return { context, Game, M, controls, events };
}

describe('Visible native market controls', () => {
  it('Rejects a hidden office and accepts a visible control with a cosmetic disabled class', () => {
    const { context, M, controls, events } = Fixture();
    controls.bankOfficeUpgrade.style.display = 'none';
    runInNewContext('AutoMarket();', context);
    expect(M.officeLevel).to.equal(0);
    expect(events).to.deep.equal([]);
    delete controls.bankOfficeUpgrade.style.display;
    controls.bankOfficeUpgrade.className = 'bankButtonOff';
    runInNewContext('AutoMarket();', context);
    expect(M.officeLevel).to.equal(1);
    expect(events).to.deep.equal(['office']);
  });

  it('Opens the market before acting and waits for the next native draw', () => {
    const { context, Game, M, events } = Fixture();
    Game.Objects.Bank.onMinigame = false;
    runInNewContext('AutoMarket();', context);
    expect(events).to.deep.equal(['open']);
    expect(M.officeLevel).to.equal(0);
    runInNewContext('AutoMarket();', context);
    expect(events).to.deep.equal(['open', 'office']);
  });

  it('Checks hidden ancestors and uses the visible loan handler instead of takeLoan', () => {
    const { context, M, controls, events } = Fixture();
    M.officeLevel = 2;
    controls.bankLoan1.style.display = '';
    controls.bankLoan1.parentNode = { style: { display: 'none' } };
    expect(runInNewContext('ClickMarketLoan(1)', context)).to.equal(false);
    expect(events).to.deep.equal([]);
    controls.bankLoan1.parentNode.style.display = '';
    expect(runInNewContext('ClickMarketLoan(1)', context)).to.equal(true);
    expect(events).to.deep.equal(['loan']);
  });

  it('Keeps ascension cash-in pending until the planned loan button is visible', () => {
    const { context, M, controls, events } = Fixture();
    M.officeLevel = 2;
    runInNewContext(`
      var KittenMilkFactor=()=>0, MilkMultiplier=()=>1, AutoClickIncome=()=>0;
      var HeavenlyPurchaseOrder=()=>[], HeavenlyContext=()=>({});
      var Beautify=String, FormatPercent=String, ReadySeconds=()=>10, SUSTAIN_SECONDS=10;
      var ChallengeDone=()=>false, ChallengeDue=()=>false, ChallengeRun=()=>false;
      var CashInChocolateEgg=()=>true, RequestWrinklerPayouts=()=>{};
      var CastBeforeAscension=()=>0;
      var SkipAscensionAnimation=()=>{}, SpendHeavenlyOrder=()=>{};
      var BuyForStarsInHeaven=()=>0, LuckyPrestigeWait=()=>false, STARS_BUDGET=0.01;
      ${Source('AutoAscend')}
      AutoAscend(); AutoAscend();`, context);
    expect(runInNewContext('Phase', context)).to.equal('cashing');
    expect(events).to.deep.equal([]);
    controls.bankLoan1.style.display = '';
    runInNewContext('AutoAscend();', context);
    expect(events).to.deep.equal(['loan', 'ascend']);
    expect(runInNewContext('Phase', context)).to.equal('ascending');
  });
});

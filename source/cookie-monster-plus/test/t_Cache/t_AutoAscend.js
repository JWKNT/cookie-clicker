import { afterEach, beforeEach, describe, it } from 'mocha';
import { expect } from 'chai';
import { readFileSync } from 'node:fs';
import { runInNewContext } from 'node:vm';
import { createRuntime, hasGameSource } from '../NativeEngine.js';
import { Game } from '../GlobalsForTesting.js';
import {
  CashInChocolateEgg, ChocolateEggPayout, RequestWrinklerPayouts, SpendHeavenlyOrder,
} from '../../src/Main/Autoplay/AscensionActions.js';
import HeavenlyPurchaseOrder from '../../src/Cache/Stats/HeavenlyPlan.js';
import { WrinklerPayout } from '../../src/Cache/Wrinklers/Wrinklers.js';

/** Load production functions with planner dependencies isolated from the browser-only framework. */
function AutomationSources() {
  const load = (name) => readFileSync(
    new URL(`../../src/Main/Autoplay/${name}.js`, import.meta.url), 'utf8',
  ).replace(/^import[\s\S]*?;\n/gm, '').replace(/export (default )?/g, '');
  return `${load('AscensionActions')}\n${load('AutoAscend')}\n${load('Autoplay')}`;
}

const Dependencies = `
  var AscensionCache={plan:{applicable:true,ascendNow:true,levelsNow:1,speedGainNow:0.2}};
  var ReadySeconds=()=>10, SUSTAIN_SECONDS=10;
  var KittenMilkFactor=()=>0, MilkMultiplier=()=>1;
  var AutoClickIncome=()=>0, HeavenlyPurchaseOrder=()=>[], HeavenlyContext=()=>({});
  var Beautify=String, FormatPercent=String;
  var AvailableLoans=()=>[], LOANS=[];
  var ChallengeDone=()=>false, ChallengeDue=()=>false, ChallengeRun=()=>false;
  var AutoAchievements=()=>{}, AutoBuy=()=>{}, UpdateAutoClicker=()=>{}, AutoDragon=()=>{};
  var AutoElder=()=>{}, AutoGarden=()=>{}, AutoGodzamok=()=>{}, AutoGolden=()=>{};
  var CastBeforeAscension=()=>0;
  var AutoGrimoire=()=>{}, AutoLumps=()=>{}, AutoMarket=()=>{}, AutoPantheon=()=>{}, AutoSeasons=()=>{};
`;

describe('Ascension execution', () => {
  let saved;
  beforeEach(() => {
    global.Game = Game;
    saved = { ...Game };
  });
  afterEach(() => {
    Object.keys(Game).forEach((key) => {
      if (!(key in saved)) delete Game[key];
    });
    Object.assign(Game, saved);
  });

  it('Waits for wrinkler payouts before buying the Chocolate egg', () => {
    Game.cookies = 100;
    Game.wrinklers = [{ phase: 2, hp: 0, sucked: 1000, type: 1 }];
    const egg = {
      unlocked: true,
      bought: false,
      getPrice: () => 10,
      buy() {
        Game.cookies -= 10;
        Game.cookies *= 1.05;
        this.bought = true;
      },
    };
    Game.Upgrades = { 'Chocolate egg': egg };
    expect(CashInChocolateEgg()).to.equal(false);
    expect(egg.bought).to.equal(false);
    // The game's next tick collects the shiny wrinkler, then clears its phase.
    Game.cookies += 3300;
    Game.wrinklers[0].phase = 0;
    expect(CashInChocolateEgg()).to.equal(true);
    expect(Game.cookies).to.equal(3559.5);
  });

  it('Requests any new stored payout before using the bank and leaves empty wrinklers alone', () => {
    Game.wrinklers = [
      { phase: 2, hp: 3, sucked: 100, type: 1 },
      { phase: 1, hp: 3, sucked: 0, type: 0 },
      { phase: 0, hp: 3, sucked: 0, type: 0 },
    ];
    RequestWrinklerPayouts();
    expect(Game.wrinklers.map((me) => me.hp)).to.deep.equal([0, 3, 3]);
    Game.wrinklers[1].sucked = 1;
    RequestWrinklerPayouts();
    expect(Game.wrinklers[1].hp).to.equal(0);
  });

  it('Forecasts only the egg payout from the actual bank after paying for the egg', () => {
    Game.Upgrades = {
      'Chocolate egg': { unlocked: true, bought: false, getPrice: () => 10 },
    };
    expect(ChocolateEggPayout(100)).to.equal(4.5);
    expect(ChocolateEggPayout(5)).to.equal(0);
    Game.Upgrades['Chocolate egg'].bought = true;
    expect(ChocolateEggPayout(100)).to.equal(0);
  });

  it('Includes Dragon Guts in normal and shiny wrinkler payouts with the other pop bonuses', () => {
    Game.Has = (name) => ['Sacrilegious corruption', 'Wrinklerspawn'].includes(name);
    Game.auraMult = (name) => (name === 'Dragon Guts' ? 1 : 0);
    Game.hasGod = (name) => (name === 'scorn' ? 1 : 0);
    const normal = 1000 * 1.2 * 1.1 * 1.05 * 1.05 * 1.15;
    expect(WrinklerPayout({ sucked: 1000, type: 0 })).to.be.closeTo(normal, 1e-9);
    expect(WrinklerPayout({ sucked: 1000, type: 1 })).to.be.closeTo(3 * normal, 1e-9);
    Game.auraMult = () => 0;
    expect(WrinklerPayout({ sucked: 1000, type: 0 })).to.be.closeTo(normal / 1.2, 1e-9);
  });

  it('Runs the actual autoplay loop without spending during cash-in, then resumes after cash-in', () => {
    // Load the loop with injected subsystems. The browser-only framework cannot load directly in Node.
    const source = readFileSync(
      new URL('../../src/Main/Autoplay/Autoplay.js', import.meta.url), 'utf8',
    ).replace(/^import .*;\n/gm, '').replace('export default function', 'function');
    const calls = [];
    let cashing = true;
    const context = {
      Game: { T: 0, fps: 30 },
      AscensionCashInProgress: () => cashing,
      ChallengeRun: () => false,
    };
    [
      'AutoAchievements', 'AutoAscend', 'AutoBuy', 'UpdateAutoClicker', 'AutoDragon',
      'AutoElder', 'AutoGarden', 'AutoGodzamok', 'AutoGolden', 'AutoGrimoire',
      'AutoLumps', 'AutoMarket', 'AutoPantheon', 'AutoSeasons',
    ].forEach((name) => { context[name] = () => calls.push(name); });
    runInNewContext(`${source}\nAutoplay();`, context);
    expect(calls).to.deep.equal(['UpdateAutoClicker', 'AutoGolden', 'AutoAscend']);
    calls.length = 0;
    context.Game.T = 1;
    runInNewContext('Autoplay();', context);
    expect(calls).to.deep.equal(['AutoGolden', 'AutoAscend']);
    calls.length = 0;
    cashing = false;
    runInNewContext('Autoplay();', context);
    expect(calls).to.deep.equal(['AutoGolden', 'AutoGodzamok', 'AutoElder', 'AutoBuy', 'AutoAscend']);
  });

  it('Buys an affordable parent even when the rest of its chosen bundle is unaffordable', () => {
    const makeUpgrade = (name, cost, parents = []) => ({
      name, bought: false, parents,
      getPrice: () => cost,
      buy() {
        if (Game.heavenlyChips < cost || parents.some((me) => !me.bought)) return 0;
        Game.heavenlyChips -= cost;
        this.bought = true;
        return 1;
      },
    });
    const legacy = makeUpgrade('Legacy', 1);
    legacy.bought = true;
    const parent = makeUpgrade('Kitten angels', 100, [legacy]);
    const child = makeUpgrade('Heralds', 1, [parent]);
    Game.Upgrades = { Legacy: legacy, 'Kitten angels': parent, Heralds: child };
    Game.heavenlyChips = 100;
    Game.heralds = 300;
    Game.milkProgress = 10;
    Game.Has = (name) => !!Game.Upgrades[name]?.bought;
    const context = {
      clickShare: 0, golden: { frenzy: 0, lucky: 0, total: 0 }, autoplay: {},
    };
    SpendHeavenlyOrder(HeavenlyPurchaseOrder(context));
    expect(parent.bought).to.equal(true);
    expect(child.bought).to.equal(false);
    expect(Game.heavenlyChips).to.equal(0);
  });

  it('Does not close unrelated prompts or take over a manual ascent during cash-in', () => {
    const context = {
      Game: {
        T: 1, fps: 30, promptOn: true, OnAscend: false, AscendTimer: 0,
        ReincarnateTimer: 0, wrinklers: [],
        mods: { cookieMonsterFramework: { saveData: { cookieMonsterMod: { settings: { AutoAscend: true } } } } },
      },
      Date, window: { dispatchEvent() { throw new Error('Unexpected Escape'); } },
    };
    runInNewContext(`${Dependencies}\n${AutomationSources()}\nAutoplay();`, context);
    expect(runInNewContext('Phase', context)).to.equal('idle');
    expect(context.Game.promptOn).to.equal(true);
    context.Game.promptOn = false;
    runInNewContext('Autoplay();', context);
    expect(runInNewContext('Phase', context)).to.equal('cashing');
    context.Game.AscendTimer = 1;
    runInNewContext('Autoplay();', context);
    expect(runInNewContext('Phase', context)).to.equal('idle');
    expect(context.Game.AscendTimer).to.equal(1);
  });

  (hasGameSource() ? it : it.skip)('Runs the production autoplay phases through native payout, Escape, heaven and reincarnation without fixed waits', () => {
    const runtime = createRuntime();
    // Fixture only: a recommended ascent, unlocked egg and shiny wrinkler are prepared.
    // Planner functions and other autoplay systems are isolated; the phase code and game transitions are real.
    runtime.evaluate(`
      ${Dependencies}
      class KeyboardEvent { constructor(type,options) { this.type=type; Object.assign(this,options); } }
      Game.mods.cookieMonsterFramework={saveData:{cookieMonsterMod:{settings:{AutoAscend:true}}}};
      Game.cookies=2e12; Game.cookiesEarned=2e12;
      Game.Upgrades['Chocolate egg'].unlocked=1;
      Game.SpawnWrinkler(Game.wrinklers[0]);
      Object.assign(Game.wrinklers[0],{type:1,phase:2,close:1,sucked:1e12,hp:3});
      var testEvents=[];
      var nativeEggBuy=Game.Upgrades['Chocolate egg'].buy;
      Game.Upgrades['Chocolate egg'].buy=function(){testEvents.push({event:'egg',bank:Game.cookies,time:Date.now()});return nativeEggBuy.apply(this,arguments);};
      var nativeAscend=Game.Ascend;
      Game.Ascend=function(){testEvents.push({event:'ascend',time:Date.now()});return nativeAscend.apply(this,arguments);};
      var nativeReincarnate=Game.Reincarnate;
      Game.Reincarnate=function(){testEvents.push({event:'reincarnate',time:Date.now()});return nativeReincarnate.apply(this,arguments);};
      ${AutomationSources()}
      Game.registerHook('logic',Autoplay);
    `);
    runtime.advance(40);
    expect(runtime.evaluate('Phase')).to.equal('cashing');
    expect(runtime.Game.Upgrades['Chocolate egg'].bought).to.equal(0);
    expect(runtime.Game.wrinklers[0].hp).to.equal(0);
    // Repeated calls before a game frame must still wait for the actual payout.
    runtime.evaluate('Autoplay();');
    expect(runtime.Game.Upgrades['Chocolate egg'].bought).to.equal(0);
    runtime.advance(40);
    expect(runtime.Game.wrinklersPopped).to.equal(1);
    expect(runtime.Game.Upgrades['Chocolate egg'].bought).to.equal(1);
    expect(runtime.Game.AscendTimer).to.equal(runtime.Game.AscendDuration);
    expect(runtime.Game.AscendDuration).to.equal(5 * runtime.Game.fps);
    runtime.advance(120);
    const events = Array.from(runtime.context.testEvents, (event) => ({ ...event }));
    expect(events.map((event) => event.event)).to.deep.equal(['egg', 'ascend', 'reincarnate']);
    expect(events[0].bank).to.be.closeTo(5.3e12, 1);
    expect(events[2].time - events[1].time).to.be.lessThan(200);
    expect(runtime.evaluate('Phase')).to.equal('reincarnating');
    // Stop the synthetic always-ready planner from requesting another ascension.
    runtime.evaluate('Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoAscend=false;');
    runtime.advance(1500);
    expect(runtime.Game.OnAscend).to.equal(0);
    expect(runtime.Game.ReincarnateTimer).to.equal(0);
  });

});

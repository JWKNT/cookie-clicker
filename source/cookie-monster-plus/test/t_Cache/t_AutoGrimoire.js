import { afterEach, beforeEach, describe, it } from 'mocha';
import { expect } from 'chai';
import { readFileSync } from 'node:fs';
import { runInNewContext } from 'node:vm';
import { createRuntime, hasGameSource } from '../NativeEngine.js';
import { CastBeforeAscension } from '../../src/Main/Autoplay/AutoGrimoire.js';

function Fixture() {
  const spells = { "haggler's charm": { cost: 10 }, 'diminish ineptitude': { cost: 6 } };
  const M = {
    spells, magic: 20, magicM: 20, spellsCastTotal: 0,
    getSpellCost: (spell) => spell.cost,
    castSpell(spell) { this.magic -= spell.cost; this.spellsCastTotal += 1; return true; },
  };
  const game = {
    mods: { cookieMonsterFramework: { saveData: { cookieMonsterMod: { settings: { AutoGrimoire: true } } } } },
    Objects: { 'Wizard tower': { amount: 1, minigame: M } },
    isMinigameReady: () => true, HasAchiev: () => M.spellsCastTotal >= 999,
    promptOn: false, OnAscend: false, ascensionMode: 0, AscendTimer: 0, ReincarnateTimer: 0,
  };
  return { game, M };
}

function AscensionFixture(overrides = {}) {
  const calls = [];
  const { game } = Fixture();
  game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoAscend = true;
  game.HasAchiev = () => false;
  game.Notify = () => calls.push('notify');
  game.Ascend = () => calls.push('ascend');
  const context = {
    Game: game, Date, AscensionCache: { plan: { applicable: true, ascendNow: true, levelsNow: 1, speedGainNow: 1 } },
    ReadySeconds: () => 10, SUSTAIN_SECONDS: 10, ChallengeRun: () => false,
    ChallengeDone: () => true, LOANS: [],
    RequestWrinklerPayouts: () => calls.push('wrinklers'),
    CashInChocolateEgg: () => { calls.push('egg'); return true; },
    AvailableLoans: () => [{ id: 1 }],
    ClickMarketLoan: () => { calls.push('loan'); return true; },
    LuckyPrestigeWait: () => { calls.push('lucky'); return false; },
    CastBeforeAscension: () => calls.push('spells'),
    SkipAscensionAnimation: () => calls.push('skip'),
    Beautify: String, FormatPercent: String,
    ...overrides,
  };
  const source = readFileSync(new URL('../../src/Main/Autoplay/AutoAscend.js', import.meta.url), 'utf8')
    .replace(/^import[\s\S]*?;\n/gm, '').replace(/export (default )?/g, '');
  runInNewContext(`${source}\nAutoAscend(); AutoAscend();`, context);
  return calls;
}

describe('Magic before committed ascension', () => {
  let saved;
  beforeEach(() => { saved = global.Game; });
  afterEach(() => { global.Game = saved; });

  it('Uses the cheaper eligible spell and stops when magic is insufficient', () => {
    const { game, M } = Fixture(); global.Game = game;
    expect(CastBeforeAscension()).to.equal(3);
    expect(M.magic).to.equal(2); expect(M.spellsCastTotal).to.equal(3);
  });
  it('Stops at the actual achievement and does not cast when it is already won', () => {
    const { game, M } = Fixture(); global.Game = game; M.spellsCastTotal = 998;
    expect(CastBeforeAscension()).to.equal(1); expect(M.spellsCastTotal).to.equal(999);
    const { magic } = M; expect(CastBeforeAscension()).to.equal(0); expect(M.magic).to.equal(magic);
  });
  it('Respects disablement, challenge, prompt, transition and minigame guards', () => {
    const changes = [
      (g) => Object.assign(g.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings, { AutoGrimoire: false }),
      (g) => Object.assign(g, { ascensionMode: 1 }), (g) => Object.assign(g, { promptOn: true }),
      (g) => Object.assign(g, { OnAscend: true }), (g) => Object.assign(g, { AscendTimer: 1 }),
      (g) => Object.assign(g, { ReincarnateTimer: 1 }), (g) => Object.assign(g.Objects['Wizard tower'], { amount: 0 }),
      (g) => Object.assign(g, { isMinigameReady: () => false }),
    ];
    changes.forEach((change) => {
      const { game, M } = Fixture(); global.Game = game; change(game);
      expect(CastBeforeAscension()).to.equal(0); expect(M.spellsCastTotal).to.equal(0);
    });
  });
  it('Rejects nonfinite, zero, negative and fractional native-cost results', () => {
    [Infinity, NaN, 0, -1, 1.5].forEach((cost) => {
      const { game, M } = Fixture(); global.Game = game; M.getSpellCost = () => cost;
      expect(CastBeforeAscension()).to.equal(0);
    });
    [Infinity, NaN, -1].forEach((magic) => {
      const { game, M } = Fixture(); global.Game = game; M.magic = magic;
      expect(CastBeforeAscension()).to.equal(0);
    });
  });
  it('Stops on a rejected or nonprogressing callback and has a finite action bound', () => {
    const { game, M } = Fixture(); global.Game = game;
    M.castSpell = () => false; expect(CastBeforeAscension()).to.equal(0);
    M.castSpell = () => true; expect(CastBeforeAscension()).to.equal(1);
    M.magic = 1000; M.magicM = 1000; M.getSpellCost = () => 1;
    M.castSpell = () => { M.magic -= 1; M.spellsCastTotal += 1; return true; };
    expect(CastBeforeAscension()).to.equal(32);
  });
  it('Runs after cash-in, loan and Lucky gates, immediately before Ascend', () => {
    expect(AscensionFixture()).to.deep.equal(['wrinklers', 'wrinklers', 'egg', 'loan', 'lucky', 'notify', 'spells', 'ascend', 'skip']);
  });
  it('Does not invoke the spell drain while any final gate blocks ascension', () => {
    [
      { ReadySeconds: () => 0 },
      { AscensionCache: { plan: { applicable: true, ascendNow: false } } },
      { CashInChocolateEgg: () => false }, { ClickMarketLoan: () => false },
      { LuckyPrestigeWait: () => true },
    ].forEach((overrides) => {
      const calls = AscensionFixture(overrides);
      expect(calls).not.to.include('spells'); expect(calls).not.to.include('ascend');
    });
    const calls = AscensionFixture({ ChallengeRun: () => true });
    expect(calls).not.to.include('spells'); expect(calls).to.include('ascend');
    const { game } = Fixture();
    game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoAscend = false;
    expect(AscensionFixture({ Game: game })).to.deep.equal([]);
  });

  [[47, 'diminish ineptitude', 997], [700, "haggler's charm", 998]].forEach(([towers, spellKey, startingCount]) => {
    [false, true].forEach((failure) => {
      it(`Retains native resources and progress for ${spellKey}, ${failure ? 'failure' : 'success'}`, function nativeCase() {
        if (!hasGameSource()) { this.skip(); return; }
        const runtime = createRuntime({ recordAudit: false }); const G = runtime.Game;
        // Supplied resource boundary. These tests do not prove that it is
        // reached from a new save or expose branch controls to the policy.
        G.cookies = 1e100; G.cookiesEarned = 1e100; G.lumps = 136; G.lumpsTotal = 136;
        runtime.advance(200); runtime.act({ type: 'buy-building', id: 7, amount: towers });
        runtime.act({ type: 'level-building', id: 7 });
        if (G.promptOn) runtime.act({ type: 'prompt', option: 0 });
        runtime.advance(20);
        const M = G.Objects['Wizard tower'].minigame;
        G.mods.cookieMonsterFramework = { saveData: { cookieMonsterMod: { settings: { AutoGrimoire: true } } } };
        M.spellsCastTotal = startingCount; global.Game = G;
        const cast = M.castSpell; const chosen = [];
        // Exercise each intact native branch with the source's internal test
        // option. Production code always uses the ordinary one-argument call.
        M.castSpell = (spell) => { chosen.push(spell); return cast(spell, { failChanceSet: failure ? 1 : 0 }); };
        const before = [G.cookies, G.cookiesEarned, G.lumps, G.lumpsTotal, runtime.clock.now];
        expect(CastBeforeAscension()).to.equal(999 - startingCount);
        expect(chosen.every((spell) => spell === M.spells[spellKey])).to.equal(true);
        expect([G.cookies, G.cookiesEarned, G.lumps, G.lumpsTotal, runtime.clock.now]).to.deep.equal(before);
        expect(M.spellsCastTotal).to.equal(999); expect(G.HasAchiev('A wizard is you')).to.equal(1);
        const buffNames = { 'diminish ineptitude': ['Magic adept', 'Magic inept'],
          "haggler's charm": ["Haggler's luck", "Haggler's misery"] };
        const buff = buffNames[spellKey][Number(failure)];
        expect(!!G.hasBuff(buff)).to.equal(true);
        runtime.act({ type: 'ascend' }); runtime.act({ type: 'key', code: 27, down: true });
        runtime.act({ type: 'key', code: 27, down: false }); runtime.advance(40);
        runtime.act({ type: 'reincarnate' });
        expect(!!G.hasBuff(buff)).to.equal(false); expect(M.spellsCastTotal).to.equal(999);
        expect(G.HasAchiev('A wizard is you')).to.equal(1); expect(M.magic).to.equal(5);
      });
    });
  });
});

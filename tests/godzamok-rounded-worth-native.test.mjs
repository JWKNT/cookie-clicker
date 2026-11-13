import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'The pinned Steam source is required';
const source = readFileSync(new URL('../source/cookie-monster-plus/src/Cache/PP/Godzamok.js', import.meta.url), 'utf8')
  .replace(/export /g, '');

for (const slot of [0, 1, 2]) {
  test(`Godzamok valuation matches native multiplier rounding in slot ${slot}`, { skip }, () => {
    // Supplied numeric boundaries test the intact native sell/buy methods.
    // They do not assert that a new save has reached these large multipliers.
    const r = createRuntime({ recordAudit: false }); r.advance(200);
    const G = r.Game, temple = G.Objects.Temple, cursor = G.Objects.Cursor;
    r.evaluate(r.source.sources['minigamePantheon.js'], 'minigamePantheon.js');
    temple.level = 1; temple.amount = 1; temple.minigame.launch(); temple.minigameLoaded = true;
    r.act({ type: 'pantheon-slot', god: 'ruin', slot }, { observe: false });
    G.mods.cookieMonsterFramework = { saveData: { cookieMonsterMod: { settings: { AutoGodzamok: 1 } } } };
    r.evaluate(`(function(){${source};window.testCycleWorth=CycleWorth;window.testProjectCycle=ProjectCycle;})()`);
    const unit = 100 * 2 ** slot;
    const cases = [[null, 1], [2 ** 53, 1], [2 ** 53 - 1, unit], [2 ** 53, unit],
      [2 ** 53 + 2, unit], [2 ** 53 + 4, unit], [2 ** 53, 2 * unit]];
    for (const [multiplier, amount] of cases) {
      G.killBuff('Devastation');
      if (multiplier !== null) G.gainBuff('devastation', 10, multiplier);
      cursor.amount = amount; cursor.bought = amount; G.BuildingsOwned = amount + 1;
      G.cookies = 2 ** 300; G.cookiesEarned = G.cookies;
      const before = G.hasBuff('Devastation')?.multClick ?? 1;
      const projected = r.context.testProjectCycle(cursor, G.cookies);
      const worth = r.context.testCycleWorth(cursor, 1, 1, G.cookies);
      assert.equal(projected.net, 0); assert.equal(projected.canRebuy, true);
      cursor.sell(-1);
      const actual = G.buffs.Devastation.multClick - before;
      assert.equal(actual, before + amount * [0.01, 0.005, 0.0025][slot] - before);
      assert.equal(worth, actual > 0, `multiplier=${multiplier}, sold=${amount}`);
      cursor.buy(amount);
      assert.equal(cursor.amount, amount); assert.equal(G.cookies, 2 ** 300);
    }
  });
}

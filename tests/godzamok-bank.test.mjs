import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { ProjectCycle, CycleCost } from '../source/cookie-monster-plus/src/Cache/PP/Godzamok.js';

test('bank projection matches native store controls across free floors, rounding boundaries and partial buybacks', {
  skip: !hasGameSource() && 'Pinned Steam source is unavailable',
}, () => {
  const previousGame = globalThis.Game;
  try {
    const cases = [
      { name: 'Cursor', amount: 4, free: 3, bank: 55 },
      { name: 'Farm', amount: 10, free: 0, bank: 1e30 },
      { name: 'Cursor', amount: 10, free: 10, bank: 2 ** 58 },
      { name: 'Cursor', amount: 10, free: 10, bank: 2 ** 57 },
      { name: 'Cursor', amount: 10, free: 10, bank: 2 ** 57 + 32 },
      { name: 'Cursor', amount: 10, free: 10, bank: 2 ** 57 - 16 },
      { name: 'Farm', amount: 3, free: 0, bank: 2000 },
      { name: 'Farm', amount: 10, free: 0, bank: 1e9, discounts: true },
    ];
    let zeroLoss = 0;
    let incomplete = 0;
    let roundedDifference = 0;
    for (const fixture of cases) {
      const runtime = createRuntime();
      const G = runtime.Game;
      globalThis.Game = G;
      const building = G.Objects[fixture.name];
      building.amount = fixture.amount; building.bought = fixture.amount;
      building.highest = fixture.amount; building.free = fixture.free; building.locked = 0;
      building.l.classList.remove('toggledOff');
      G.cookies = fixture.bank; G.cookiesEarned = fixture.bank; G.BuildingsOwned = fixture.amount;
      if (fixture.discounts) {
        for (const name of ['Season savings', "Santa's dominion", 'Faberge egg', 'Divine discount', 'Fortune #100']) G.Upgrades[name].earn();
        G.dragonAura = G.dragonAurasBN['Earth Shatterer'].id;
        G.dragonAura2 = G.dragonAurasBN['Reality Bending'].id;
      }
      const projection = ProjectCycle(building, fixture.bank);
      assert.equal(G.cookies, fixture.bank, 'projection must not spend or credit the native bank');
      assert.equal(building.amount, fixture.amount, 'projection must not sell native buildings');
      runtime.act({ type: 'store-bulk', id: 1 });
      runtime.act({ type: 'store-bulk', id: 5 });
      runtime.act({ type: 'click-product', id: building.id });
      assert.equal(building.amount, 0);
      assert.equal(G.cookies, projection.afterSale, `${fixture.name} sale bank`);
      runtime.act({ type: 'store-bulk', id: 0 });
      runtime.act({ type: 'store-bulk', id: 2 });
      for (let copy = 0; copy < fixture.amount; copy++) runtime.act({ type: 'click-product', id: building.id });
      assert.equal(G.cookies, projection.afterBuyback, `${fixture.name} buyback bank`);
      assert.equal(building.amount, projection.bought);
      assert.equal(projection.canRebuy, building.amount === fixture.amount);
      assert.equal(fixture.bank - G.cookies, projection.net);
      if (projection.canRebuy && projection.net === 0) zeroLoss++;
      if (!projection.canRebuy) incomplete++;
      if (projection.canRebuy && projection.net !== CycleCost(building).net) roundedDifference++;
    }
    assert.ok(zeroLoss > 0);
    assert.ok(incomplete > 0);
    assert.ok(roundedDifference > 0);
  } finally {
    if (previousGame === undefined) delete globalThis.Game;
    else globalThis.Game = previousGame;
  }
});

test('native Godzamok remains slotted and credits a sale when the last Temple is sold', {
  skip: !hasGameSource() && 'Pinned Steam source is unavailable',
}, () => {
  const runtime = createRuntime();
  const G = runtime.Game;
  const temple = G.Objects.Temple;
  runtime.evaluate(runtime.source.sources['minigamePantheon.js'], 'minigamePantheon.js');
  temple.level = 1; temple.amount = 10; temple.highest = 10; temple.bought = 10; temple.locked = 0;
  temple.l.classList.remove('toggledOff');
  temple.minigame.launch(); temple.minigameLoaded = true;
  runtime.act({ type: 'pantheon-slot', god: 'ruin', slot: 0 });
  assert.equal(G.hasGod('ruin'), 1);
  runtime.act({ type: 'store-bulk', id: 1 });
  runtime.act({ type: 'store-bulk', id: 5 });
  runtime.act({ type: 'click-product', id: temple.id });
  assert.equal(temple.amount, 0);
  assert.equal(G.hasGod('ruin'), 1, 'native hasGod reads the slots, not the current Temple count');
  assert.equal(G.hasBuff('Devastation').multClick, 1.1);
});

test('a native finite zero-time cycle prefix preserves the large bank and reaches the unit-increment rounding boundary', {
  skip: !hasGameSource() && 'Pinned Steam source is unavailable',
}, () => {
  const runtime = createRuntime({ recordAudit: false });
  runtime.advance(200);
  const G = runtime.Game, temple = G.Objects.Temple, mine = G.Objects.Mine;
  runtime.evaluate(runtime.source.sources['minigamePantheon.js'], 'minigamePantheon.js');
  temple.level = 1; temple.amount = 1; temple.highest = 1;
  temple.minigame.launch(); temple.minigameLoaded = true;
  mine.amount = 101; mine.highest = 101; mine.bought = 101; mine.locked = 0;
  mine.l.classList.remove('toggledOff');
  G.BuildingsOwned = 102; G.cookies = 2 ** 90; G.cookiesEarned = G.cookies;
  G.CalculateGains();
  const action = value => runtime.act(value, { observe: false });
  action({ type: 'pantheon-slot', god: 'ruin', slot: 0 });
  action({ type: 'store-bulk', id: 4 });
  const bank = G.cookies, time = runtime.clock.now, clickBefore = G.computedMouseCps;
  const cycle = () => {
    action({ type: 'store-bulk', id: 1 });
    action({ type: 'click-product', id: mine.id });
    action({ type: 'store-bulk', id: 0 });
    action({ type: 'click-product', id: mine.id });
    assert.equal(mine.amount, 101);
    assert.equal(G.cookies, bank);
    assert.equal(runtime.clock.now, time);
  };
  for (let i = 0; i < 1000; i++) cycle();
  assert.equal(G.hasBuff('Devastation').multClick, 1001);
  assert.equal(G.hasBuff('Devastation').time, 300);
  assert.equal(G.computedMouseCps, clickBefore, 'gains are recomputed on the next native frame');

  // A separate prepared boundary probe. It does not execute the enormous
  // prefix needed to reach this value; Lean checks that numeric recurrence.
  G.hasBuff('Devastation').multClick = 2 ** 53 - 2;
  const boundary = [];
  for (let i = 0; i < 4; i++) { cycle(); boundary.push(G.hasBuff('Devastation').multClick); }
  assert.deepEqual(boundary, [2 ** 53 - 1, 2 ** 53, 2 ** 53, 2 ** 53]);
  runtime.advance(34);
  assert.equal(G.computedMouseCps, clickBefore * 2 ** 53);
});

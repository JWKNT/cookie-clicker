import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { createPolicySession, replayPolicyTrace } from '../model/policy-runtime.mjs';
import { maintenanceSchedule, maintenanceRequestTime } from '../model/maintenance-schedule.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource();

test('maintenance commitments contain clock data only and cannot be changed after startup', () => {
  const input = { atMs: [0, 1000, 4000] };
  const fixed = maintenanceSchedule(input); input.atMs[1] = 50;
  assert.deepEqual(fixed, { atMs: [0, 1000, 4000] });
  assert(Object.isFrozen(fixed)); assert(Object.isFrozen(fixed.atMs));
  assert.equal(maintenanceRequestTime(fixed, 3), Infinity);
  assert.equal(maintenanceRequestTime(maintenanceSchedule({ firstMs: 1000, everyMs: 2000 }), 4), 9000);
  for (const schedule of [{ atMs: [1, 1] }, { atMs: [-1] }, { atMs: [Infinity] }, { firstMs: 0, everyMs: 0 }, { atMs: [1], condition: 'bad outcome' }, () => true]) {
    assert.throws(() => maintenanceSchedule(schedule), /Maintenance reload/);
  }
});

test('scheduled native save/current reload preserves earned new-save progress and replays exactly', { skip }, () => {
  const schedule = { atMs: [1000, 2000] };
  const transitions = [];
  const session = createPolicySession({ maintenanceReload: schedule, onTransition: e => transitions.push(e) });
  schedule.atMs[0] = 10;
  const policy = session.policy;
  policy.act({ type: 'wait', milliseconds: 100 });
  policy.act({ type: 'click' });
  policy.act({ type: 'tiny-cookie' });
  policy.act({ type: 'name-bakery', name: 'Maintenance fixture' });
  policy.act({ type: 'wait', milliseconds: 2400 });
  const end = policy.observe();
  assert.equal(end.cookies, 1);
  assert.equal(end.achievements['Tiny cookie'], true);
  assert.equal(end.elapsedMs, 2500);
  assert.equal(session.exportSummary().reloadCount, 2);
  assert.deepEqual(transitions.filter(e => e.kind === 'maintenance-request').map(e => e.elapsedMs), [1000, 2000]);
  assert(transitions.filter(e => e.kind === 'maintenance-reload').every(e => e.elapsedMs > 1000));
  const trace = session.exportTrace();
  assert.deepEqual(replayPolicyTrace(trace).policy.observe(), end);
  assert.deepEqual(trace.environment.maintenanceReload, { atMs: [1000, 2000] });
  assert.equal(trace.actions.length, 5); // Reloads follow the fixed clock, not extra policy actions.
  assert.throws(() => policy.act({ type: 'reload' }), /unknown action type/);
});

test('native maintenance discards the old realm and callbacks, and preserves its current save seed', { skip }, () => {
  const r = createRuntime({ maintenanceReload: { atMs: [1000] } });
  r.advance(900); r.act({ type: 'click' });
  const priorContext = r.context; const priorGame = r.Game;
  const seed = priorGame.seed;
  r.evaluate('var oldTaskCalled=false;setTimeout(function(){oldTaskCalled=true;},1000);');
  r.advance(1200);
  assert.notEqual(r.context, priorContext); assert.notEqual(r.Game, priorGame);
  assert.equal(priorContext.oldTaskCalled, false);
  assert.equal(r.context.oldTaskCalled, undefined);
  assert.equal(r.Game.seed, seed); assert.equal(r.Game.cookies, 1);
  assert.equal(r.auditCounts().reloadCount, 1);
  assert.throws(() => r.context.App.reload(), /Unscheduled reload/);
});

test('native reload retains saved outcomes and applies native minigame, buff and shimmer changes', { skip }, () => {
  // Diagnostic implication fixture only. It does not assert that these values
  // have been obtained by the legal new-save trajectory tested above.
  const r = createRuntime({ diagnosticMode: true, maintenanceReload: { atMs: [2000] } });
  r.advance(100);
  r.evaluate(`
    for (var name of ['Farm','Bank','Temple','Wizard tower']) {
      Game.Objects[name].level=1;Game.Objects[name].amount=1;Game.Objects[name].highest=1;
    }
    Game.LoadMinigames();
  `);
  r.advance(500);
  const G = r.Game; const garden = G.Objects.Farm.minigame; const market = G.Objects.Bank.minigame;
  garden.freeze = 1; garden.plot[0][0] = [1, 42.875]; garden.harvestsTotal = 77;
  const good = market.goodsById[0];
  good.val = 12.3456; good.d = -0.1299; good.prev = 23.4567; good.stock = 3; good.last = 1;
  G.Objects['Wizard tower'].minigame.spellsCastTotal = 19;
  G.Objects.Temple.minigame.slot[0] = 2;
  G.lumps = 15; G.lumpsTotal = 27; G.lumpT = r.clock.now; G.lumpCurrentType = 4;
  G.gainBuff('devastation', 10, 2); G.buffs.Devastation.multClick = 1234;
  G.drawT = 2 ** 53;
  new G.shimmer('golden', { type: 'cookie storm drop' }, true);
  const savedLumpTime = G.lumpT; const seed = G.seed;
  r.advance(1900);
  const restored = r.Game;
  assert(restored.drawT < 100); assert.equal(restored.seed, seed);
  assert.equal(restored.shimmers.length, 0);
  assert.equal(restored.buffs.Devastation.multClick, 2);
  assert.deepEqual(Array.from(restored.Objects.Farm.minigame.plot[0][0]), [1, 42]);
  assert.equal(restored.Objects.Farm.minigame.harvestsTotal, 77);
  const restoredGood = restored.Objects.Bank.minigame.goodsById[0];
  assert.equal(restoredGood.val, 12.34); assert.equal(restoredGood.d, -0.12); assert.equal(restoredGood.prev, 23.45);
  assert.equal(restoredGood.stock, 3); assert.equal(restoredGood.last, 1);
  assert(restored.Objects.Bank.minigame.tickT < 20);
  assert.equal(restored.Objects['Wizard tower'].minigame.spellsCastTotal, 19);
  assert.equal(restored.Objects.Temple.minigame.slot[0], 2);
  assert.equal(restored.lumps, 15); assert.equal(restored.lumpsTotal, 27);
  assert.equal(restored.lumpT, savedLumpTime); assert.equal(restored.lumpCurrentType, 4);
});

test('a precommitted request waits for initial save loading and repeats by fixed clock', { skip }, () => {
  const requests = [];
  const r = createRuntime({ maintenanceReload: { firstMs: 0, everyMs: 500 },
    onTransition: e => { if (e.kind === 'maintenance-request') requests.push(e.elapsedMs); } });
  r.advance(1400);
  assert.deepEqual(requests, [100, 500, 1000]);
  assert.equal(r.auditCounts().reloadCount, 3);
});

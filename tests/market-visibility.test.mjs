import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { decideMarketAction } from '../model/market-policy.mjs';

const skip = !hasGameSource();
function fixture() {
  const r = createRuntime({ diagnosticMode: true });
  // Funded/leveled entry conditions isolate actual market DOM callbacks.
  // This fixture is not a new-save trajectory or a reachability proof.
  for (const b of Object.values(r.Game.Objects)) b.amount = b.highest = 750;
  r.Game.Objects.Cursor.amount = 2000;
  r.Game.Objects.Cursor.level = 12;
  r.Game.Objects.Bank.level = 1;
  r.evaluate(r.source.sources['minigameMarket.js'], 'minigameMarket.js');
  const M = r.Game.Objects.Bank.minigame;
  M.launch(); r.Game.Objects.Bank.minigameLoaded = true;
  r.Game.Objects.Bank.switchMinigame(true);
  r.Game.cookies = 1e100; r.Game.cookiesPsRawHighest = 10;
  return { r, M };
}

test('native office display survives reset and a hidden upgrade cannot be clicked', { skip }, () => {
  const { r, M } = fixture();
  M.officeLevel = 5; r.Game.drawT = 10; M.draw();
  assert.equal(r.context.l('bankOfficeUpgrade').style.display, 'none');
  r.Game.drawT = 2 ** 53; M.reset(); M.draw();
  assert.equal(M.officeLevel, 0);
  assert.equal(r.snapshot().market.officeUpgradeVisible, false);
  assert.throws(() => r.act({ type: 'market-office' }), /market control bankOfficeUpgrade is hidden/);
  assert.equal(M.officeLevel, 0);
  const decision = decideMarketAction(r.snapshot());
  assert.equal(decision.status, 'waiting');
  assert.equal(decision.action.type, 'wait');
  // A diagnostic earlier draw counter isolates the missing redraw, without
  // claiming that normal play can decrease drawT.
  r.Game.drawT = 10; M.draw();
  r.act({ type: 'market-office' });
  assert.equal(M.officeLevel, 1);
});

test('loan access waits for the rendered button and dispatches its native handler', { skip }, () => {
  const { r, M } = fixture();
  M.officeLevel = 2;
  assert.equal(r.snapshot().market.loans[0].visible, false);
  assert.throws(() => r.act({ type: 'market-loan', id: 1 }), /market control bankLoan1 is hidden/);
  assert.equal(r.Game.hasBuff('Loan 1'), 0);
  r.Game.drawT = 10; M.draw();
  r.act({ type: 'market-loan', id: 1 });
  assert(r.Game.hasBuff('Loan 1'));
});

test('a hidden good row cannot be traded before the native activation update', { skip }, () => {
  const { r, M } = fixture();
  const good = M.goodsById[0];
  good.active = false; M.updateGoodStyle(good.id);
  assert.equal(good.building.highest, 750);
  assert.equal(r.snapshot().market.goods[0].visible, false);
  assert.throws(() => r.act({ type: 'market-buy', id: 0, amount: 1 }), /market control bankGood-0 is hidden/);
  assert.equal(good.stock, 0);
  r.Game.T = 10; M.logic();
  r.act({ type: 'market-buy', id: 0, amount: 1 });
  assert.equal(good.stock, 1);
});

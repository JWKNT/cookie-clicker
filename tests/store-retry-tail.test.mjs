import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource();

// These are native source/DOM implications from explicit diagnostic states.
// They do not establish that the proposed route reaches those states.
test('upgrade unlock and purchase still use native DOM after drawT saturation', { skip }, () => {
  const r = createRuntime({ diagnosticMode: true });
  r.act({ type: 'wait', milliseconds: 200 });
  r.Game.drawT = 2 ** 53;
  r.Game.cookies = 0;
  r.Game.Unlock('Reinforced index finger');
  r.act({ type: 'wait', milliseconds: 100 });
  const u = r.Game.Upgrades['Reinforced index finger'];
  const i = r.Game.UpgradesInStore.indexOf(u);
  assert(i >= 0);
  const button = r.context.l(`upgrade${i}`);
  assert(button);
  assert.equal(button.classList.contains('enabled'), false);
  // The stale affordability class does not disable the native click handler.
  r.Game.cookies = 100;
  button.click();
  assert.equal(u.bought, 1);
  assert.equal(r.Game.drawT, 2 ** 53);
  r.Game.Reset(false);
  assert.equal(u.bought, 0);
  assert.equal(r.Game.drawT, 2 ** 53);
  r.Game.Unlock(u.name);
  r.act({ type: 'wait', milliseconds: 100 });
  const nextIndex = r.Game.UpgradesInStore.indexOf(u);
  assert(nextIndex >= 0);
  assert(r.context.l(`upgrade${nextIndex}`));
});

test('normal reset retains previously visible product rows after drawT saturation', { skip }, () => {
  const r = createRuntime({ diagnosticMode: true });
  r.act({ type: 'wait', milliseconds: 200 });
  r.Game.cookies = r.Game.cookiesEarned = 2 ** 90;
  r.Game.drawT = 5;
  r.Game.Draw();
  assert(r.Game.ObjectsById.every(b => !b.l.classList.contains('toggledOff')));
  r.Game.drawT = 2 ** 53;
  r.Game.Reset(false);
  assert(r.Game.ObjectsById.every(b => !b.l.classList.contains('toggledOff')));
  r.Game.cookies = 2 ** 90;
  const you = r.Game.Objects.You;
  you.l.click();
  assert.equal(you.amount, 1);
  assert.equal(r.Game.drawT, 2 ** 53);
  // In contrast, BuildStore initializes hidden rows. The route must avoid a
  // later screen-reader preference rebuild, rather than presume a redraw.
  r.Game.BuildStore();
  assert(r.Game.ObjectsById.every(b => b.l.classList.contains('toggledOff')));
  r.Game.Draw();
  assert(r.Game.ObjectsById.every(b => b.l.classList.contains('toggledOff')));
});

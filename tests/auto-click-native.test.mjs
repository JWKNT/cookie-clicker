import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'The pinned Steam source is required';
const autoClickSource = readFileSync(new URL('../source/cookie-monster-plus/src/Main/Autoplay/AutoClick.js', import.meta.url), 'utf8')
  .replace(/^import .*;\n/gm, '').replace(/export default /g, '').replace(/export function /g, 'function ');

for (const seeded of [false, true]) {
  test(`Auto-click preserves native click bookkeeping with ${seeded ? 'seeded' : 'free'} random draws`, { skip }, () => {
    const reference = createRuntime({ randomSeed: 42 });
    const modified = createRuntime({ randomSeed: 42 });
    for (const r of [reference, modified]) {
      r.advance(1000);
      if (seeded) r.evaluate('Math.seedrandom("click-bookkeeping-fixture");');
    }
    let click;
    const originalInterval = modified.context.setInterval;
    modified.context.setInterval = callback => { click = callback; return 1; };
    modified.Game.mods.cookieMonsterFramework = {
      saveData: { cookieMonsterMod: { settings: { AutoClick: 1, AutoClickRate: 50 } } },
    };
    modified.evaluate(`(function(){const ClicksAllowed=()=>true;${autoClickSource}\nUpdateAutoClicker();})()`);
    modified.context.setInterval = originalInterval;
    modified.Game.volume = 73;
    reference.Game.volume = 0;
    const nativeSound = modified.Game.playCookieClickSound;
    for (let i = 0; i < 8; i++) {
      for (const r of [reference, modified]) r.advance(20);
      reference.Game.mouseX = reference.Game.cookieOriginX;
      reference.Game.mouseY = reference.Game.cookieOriginY;
      reference.Game.ClickCookie();
      click();
      assert.equal(modified.Game.volume, 73);
      assert.equal(modified.Game.playCookieClickSound, nativeSound);
      for (const field of ['cookies', 'cookiesEarned', 'handmadeCookies', 'cookieClicks', 'cookieClickSound', 'lastClick']) {
        assert.equal(modified.Game[field], reference.Game[field], field);
      }
      assert.equal(modified.auditCounts().randomDrawCount, reference.auditCounts().randomDrawCount);
      const beforeRejected = {
        clicks: modified.Game.cookieClicks,
        sound: modified.Game.cookieClickSound,
        draws: modified.auditCounts().randomDrawCount,
      };
      reference.Game.ClickCookie();
      click();
      assert.deepEqual({
        clicks: modified.Game.cookieClicks,
        sound: modified.Game.cookieClickSound,
        draws: modified.auditCounts().randomDrawCount,
      }, beforeRejected, 'The native 20 ms guard must reject a same-time repeat');
      assert.equal(modified.Game.volume, 73);
    }
    assert.equal(modified.evaluate('Math.random()'), reference.evaluate('Math.random()'));
    assert.equal(modified.Game.cookieClicks, 8);
  });
}

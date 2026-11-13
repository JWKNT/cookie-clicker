import test from 'node:test';
import assert from 'node:assert/strict';
import { decideMiscAction, miscPolicySource } from '../model/misc-policy.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
function skipEarlyGoals(r) {
  for (const name of ['Cookie-dunker', 'Just wrong', 'Early bird', 'Fading luck']) r.Game.Win(name);
}

test('misc source works in the restricted VM and does not retain VM globals across compiled-code reuse', { skip }, () => {
  const r = createRuntime();
  assert.deepEqual(decidePolicy(miscPolicySource(), r.snapshot(), [], null), decideMiscAction(r.snapshot()));
  const source = '() => { globalThis.calls = (globalThis.calls || 0)+1; return {type:"wait", milliseconds:globalThis.calls}; }';
  assert.equal(decidePolicy(source, {}, []).milliseconds, 1);
  assert.equal(decidePolicy(source, {}, []).milliseconds, 1);
});

test('Cookie-dunker uses native viewport geometry and restores the larger viewport', { skip }, () => {
  const r = createRuntime();
  r.act({type:'name-bakery',name:'Dunk test'}); r.act({type:'tiny-cookie'}); r.act({type:'forgotten-madeleine'});
  let decision=decideMiscAction(r.snapshot());
  assert.deepEqual(decision.action,{type:'resize',width:1200,height:200});
  r.act(decision.action); r.advance(12000);
  assert.equal(r.Game.HasAchiev('Cookie-dunker'),1);
  decision=decideMiscAction(r.snapshot(),decision.memory);
  assert.deepEqual(decision.action,{type:'resize',width:1200,height:900});
});

test('Just wrong sells an actual grandma instead of setting an achievement', { skip }, () => {
  const r=createRuntime();
  r.Game.cookies=1000; r.Game.Objects.Grandma.locked=0;
  r.act({type:'buy-building',id:1,amount:1});
  const decision=decideMiscAction(r.snapshot());
  assert.deepEqual(decision.action,{type:'sell-building',id:1,amount:1});
  r.act(decision.action);
  assert.equal(r.Game.Objects.Grandma.amount,0);
  assert.equal(r.Game.HasAchiev('Just wrong'),1);
});

test('golden-cookie arbitration gets Early bird and holds a later native spawn for Fading luck', { skip }, () => {
  const r=createRuntime(); r.advance(1000);
  // Synthetic natural-spawn fixture. The controller never sees or sets spawnLead.
  r.Game.Win('Cookie-dunker');
  r.evaluate("var s=new Game.shimmer('golden');s.spawnLead=1;s.force='multiply cookies';");
  let decision=decideMiscAction(r.snapshot()); r.act(decision.action);
  assert.equal(r.Game.HasAchiev('Early bird'),1);
  r.evaluate("var s=new Game.shimmer('golden');s.spawnLead=1;s.force='multiply cookies';");
  decision=decideMiscAction(r.snapshot());
  assert.equal(decision.action,null);
  assert.deepEqual(decision.deferShimmerIds,[r.Game.shimmers[0].id]);
  r.advance(decision.wakeAfterMs);
  decision=decideMiscAction(r.snapshot(),decision.memory);
  assert.equal(decision.action?.type,'click-shimmer');
  r.act(decision.action);
  assert.equal(r.Game.HasAchiev('Fading luck'),1);
});

test('self-gifting keeps the displayed code and respects the native cooldown', { skip }, () => {
  const r=createRuntime(); skipEarlyGoals(r);
  r.evaluate("Game.Upgrades['Wrapping paper'].bought=1;Game.cookies=2e9;");
  let decision=decideMiscAction(r.snapshot());
  assert.equal(decision.action?.type,'gift-send'); r.act(decision.action);
  decision=decideMiscAction(r.snapshot(),decision.memory);
  assert.equal(decision.action?.type,'close-prompt'); assert(decision.memory.giftCode);
  r.act(decision.action);
  const pending=decideMiscAction(r.snapshot(),decision.memory);
  assert.equal(pending.action,null);
  // Shorten only this funded fixture's cooldown, then execute its real expiry.
  r.evaluate("Game.hasBuff('Gifted out').time=1;");r.advance(100);
  decision=decideMiscAction(r.snapshot(),pending.memory);
  assert.equal(decision.action?.type,'gift-redeem');r.act(decision.action);
  assert.equal(r.Game.HasAchiev('No time like the present'),1);
});

test('Thick-skinned uses paid veil restoration and ordinary clicks with no seed access', { skip }, () => {
  const r=createRuntime();skipEarlyGoals(r);r.advance(1000);
  r.evaluate("Game.Upgrades['Shimmering veil'].bought=1;Game.Upgrades['Reinforced membrane'].bought=1;Game.Upgrades['Shimmering veil [on]'].bought=1;Game.Unlock('Shimmering veil [off]');Game.cookies=1e15;Game.unbuffedCps=1;Game.Win('Neverclick');Game.Win('Hardcore');");
  let memory={};let paid=0;
  for(let i=0;i<200&&!r.Game.HasAchiev('Thick-skinned');i++) {
    const d=decideMiscAction(r.snapshot(),memory);memory=d.memory;
    if(d.action){ if(d.action.type==='buy-upgrade') paid++;r.act(d.action); }
    r.advance(20);
  }
  assert(paid>0);
  assert.equal(r.Game.HasAchiev('Thick-skinned'),1);
});

test('Golden switch exposes both toggle states and restores native golden-cookie spawns', { skip }, () => {
  const r=createRuntime();skipEarlyGoals(r);
  // Funded catalogue fixture; the actions still use the native toggle callbacks.
  r.Game.Upgrades['Golden switch'].bought=1;
  r.Game.cookiesPs=1;r.Game.cookies=1e12;
  r.Game.Unlock('Golden switch [off]');r.Game.Win("Black cat's paw");
  let d=decideMiscAction(r.snapshot());
  assert.deepEqual(d.action,{type:'buy-upgrade',id:r.Game.Upgrades['Golden switch [off]'].id});
  r.act(d.action);
  assert.equal(r.Game.Has('Golden switch [off]'),1);
  d=decideMiscAction(r.snapshot(),d.memory);
  assert.deepEqual(d.action,{type:'buy-upgrade',id:r.Game.Upgrades['Golden switch [on]'].id});
  r.act(d.action);
  assert.equal(r.Game.Has('Golden switch [off]'),0);
  assert(r.snapshot().history.accessedUpgrades.includes('Golden switch [on]'));
});

test('gift resource requests retain a deferred Fading luck target and respect the gift cooldown', { skip }, () => {
  const r=createRuntime();skipEarlyGoals(r);
  r.Game.Achievements['Fading luck'].won=0;
  r.Game.Upgrades['Wrapping paper'].bought=1;r.Game.cookies=1e9-1;
  r.evaluate("var s=new Game.shimmer('golden');s.spawnLead=1;");
  let d=decideMiscAction(r.snapshot());
  assert.equal(d.status,'needs-resources');assert.equal(d.requiredCookies,1e9);
  assert.equal(d.action,null);assert.deepEqual(d.deferShimmerIds,[r.Game.shimmers[0].id]);assert(d.wakeAfterMs>0);
  r.Game.cookies=1e9;d=decideMiscAction(r.snapshot(),d.memory);r.act(d.action);
  d=decideMiscAction(r.snapshot(),d.memory);r.act(d.action);
  r.Game.cookies=0;d=decideMiscAction(r.snapshot(),d.memory);
  assert.equal(d.action,null);assert.notEqual(d.status,'needs-resources');
  assert.equal(d.requiredCookies,undefined);assert(d.memory.giftCode);
});

test('a veil reserve uses its native price and becomes an executable restoration at that bank', { skip }, () => {
  const r=createRuntime();skipEarlyGoals(r);
  r.Game.Win('Neverclick');r.Game.Win('Hardcore');
  r.Game.Upgrades['Shimmering veil'].bought=1;r.Game.Upgrades['Reinforced membrane'].bought=1;
  r.Game.Upgrades['Shimmering veil [on]'].bought=1;r.Game.Unlock('Shimmering veil [off]');
  r.Game.unbuffedCps=2;r.Game.cookies=0;
  const price=r.Game.Upgrades['Shimmering veil [off]'].getPrice();
  let d=decideMiscAction(r.snapshot());
  assert.equal(d.goal,'Thick-skinned');assert.equal(d.status,'needs-resources');assert.equal(d.requiredCookies,price);
  assert.equal(d.action,null);assert.deepEqual(d.deferShimmerIds,[]);assert.equal(d.wakeAfterMs,1000);
  r.Game.cookies=price;d=decideMiscAction(r.snapshot(),d.memory);r.act(d.action);
  assert.equal(r.Game.cookies,0);assert.equal(r.Game.Has('Shimmering veil [off]'),1);
});

test('Golden switch requests the cycle reserve and can recover if its actual restoration becomes unaffordable', { skip }, () => {
  const r=createRuntime();skipEarlyGoals(r);
  r.Game.Upgrades['Golden switch'].bought=1;r.Game.Unlock('Golden switch [off]');r.Game.Win("Black cat's paw");
  r.Game.cookiesPs=1;r.Game.cookies=0;
  const enablePrice=r.Game.Upgrades['Golden switch [off]'].getPrice();
  let d=decideMiscAction(r.snapshot());
  assert.equal(d.status,'needs-resources');assert.equal(d.requiredCookies,enablePrice*100);
  r.Game.cookies=d.requiredCookies;d=decideMiscAction(r.snapshot(),d.memory);r.act(d.action);
  // An intervening external spending fixture must not silently leave the switch on.
  r.Game.cookies=0;d=decideMiscAction(r.snapshot(),d.memory);
  const restorePrice=r.Game.Upgrades['Golden switch [on]'].getPrice();
  assert.equal(d.status,'needs-resources');assert.equal(d.requiredCookies,restorePrice);
  assert.equal(d.memory.restoreGoldenSwitch,true);assert.equal(d.action,null);
  assert.deepEqual(d.deferShimmerIds,[]);assert(d.wakeAfterMs>0);
  r.Game.cookies=restorePrice;d=decideMiscAction(r.snapshot(),d.memory);r.act(d.action);
  assert.equal(r.Game.Has('Golden switch [off]'),0);
});

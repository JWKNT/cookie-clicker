import test from 'node:test';
import assert from 'node:assert/strict';
import {createRuntime} from '../model/runtime.mjs';
import {hasGameSource} from '../model/game-source.mjs';
import {helperSetupPolicySource} from '../model/helper-setup-policy.mjs';
import {completionPolicySource} from '../model/completion-policy.mjs';
import {decideAscensionAction} from '../model/ascension-policy.mjs';
import {decidePolicy} from '../model/policy-runtime.mjs';
import {HELPER_ART_EXCLUSIONS,helperSweepActions} from '../model/helper-cover.mjs';
import {readFileSync} from 'node:fs';
const skip=!hasGameSource();
const witness=JSON.parse(readFileSync(new URL('../model/helper-seeds-witness.json',import.meta.url)));
const source=helperSetupPolicySource();
function prepared(){
  const r=createRuntime({diagnosticMode:true,recordAudit:false});
  for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press','Cookie-dunker','Hardcore','Neverclick','Just wrong'])r.Game.Win(n);
  return r;
}
function helperObservation(r){const o=r.snapshot();delete o.seasonal.helperGrandmas;return o;}
function plan(r,m={}){return decidePolicy(source,helperObservation(r),[],m);}
function boundary(r){
  // Explicit funded, post-reset setup boundary; not a new-save funding claim.
  r.Game.resets=1;r.Game.cookies=r.Game.cookiesEarned=1e12;
  r.Game.Upgrades['Season switcher'].earn();r.advance(5100);
}

test('helper setup uses no seed or sprite positions and defers to an ordinary scheduled reset',{skip},()=>{
  const r=prepared();assert.equal(plan(r).status,'deferred');boundary(r);
  r.Game.Upgrades[HELPER_ART_EXCLUSIONS[0]].earn();
  const d=plan(r);assert.equal(d.status,'deferred');assert.equal(d.action,null);assert(!source.includes('helperGrandmas'));assert(!source.includes('Game.seed'));
});

test('the complete policy withholds all18 artwork offers and permanent candidates before the helper flag',{skip},()=>{
  const r=prepared(),o=r.snapshot();r.Game.cookies=1e15;
  o.cookies=1e15;o.shop.upgrades=HELPER_ART_EXCLUSIONS.map(name=>({id:r.Game.Upgrades[name].id,name,price:1,canBuy:true,pool:''}));
  o.ascension.permanentCandidates=o.shop.upgrades.map(u=>({...u}));
  const before=structuredClone(o);
  const d=decidePolicy(completionPolicySource(),o,[],{restoreViewport:true,growth:{nextClick:100,nextPurchase:0}});
  assert.notEqual(d.action.type,'buy-upgrade');assert.deepEqual(o,before);
  o.achievements["Baby it's old outside"]=true;
  const released=decidePolicy(completionPolicySource(),o,[],{restoreViewport:true,growth:{nextClick:100,nextPurchase:0}});
  assert.equal(released.action.type,'buy-upgrade');assert(o.shop.upgrades.some(u=>u.id===released.action.id));
});

test('fixed helper sweep succeeds for the known worst two-art seed after native purchases',{skip},()=>{
  const r=prepared();boundary(r);r.Game.seed=witness.firstMaximumSeed;
  let m={},sweep=null,steps=0;
  for(;steps<100;steps++) {
    const d=plan(r,m);m=d.memory;
    if(d.status==='complete')break;
    assert.equal(d.status,'acting',d.reason);
    if(d.action.type==='sequence' && d.action.actions.length>2)sweep=d.action.actions;
    // Replay flat source actions without supplying sprite coordinates from observations.
    for(const a of d.action.type==='sequence'?d.action.actions:[d.action])r.act(a,{observe:false});
  }
  assert(steps<100);assert.deepEqual(sweep,helperSweepActions());
  assert.equal(r.Game.HasAchiev("Baby it's old outside"),1);
  assert.equal(r.Game.Objects.Grandma.amount,24);assert.equal(r.Game.season,'christmas');
  assert(HELPER_ART_EXCLUSIONS.every(name=>!r.Game.Has(name)));
  assert.equal(r.Game.mouseDown,0);assert.equal(r.Game.resets,1);
});

test('already won helper, prompt, challenge, missing funding and failed-sweep gates remain explicit',{skip},()=>{
  const r=prepared();boundary(r);r.Game.cookies=0;
  assert.equal(plan(r).status,'needs-resources');
  r.Game.ascensionMode=1;assert.equal(plan(r).status,'deferred');r.Game.ascensionMode=0;
  r.Game.Prompt('<h3>Unrelated</h3>',['Close']);assert.equal(plan(r).status,'deferred');r.Game.ClosePrompt();
  assert.equal(plan(r,{attempted:true}).status,'blocked');
  r.Game.Win("Baby it's old outside");assert.equal(plan(r,{attempted:true}).status,'complete');
});

test('a scheduled native reset clears all18 owned artwork upgrades before the setup boundary',{skip},()=>{
  const r=prepared();for(const name of HELPER_ART_EXCLUSIONS)r.Game.Upgrades[name].earn();
  r.Game.cookies=r.Game.cookiesEarned=2**90;
  let m={},entered=false;
  for(let k=0;k<500;k++){
    const o=r.snapshot();
    if(entered && r.Game.resets===1 && !o.progression.onAscend && !o.progression.ascendTimer && !o.progression.reincarnateTimer)break;
    const d=decideAscensionAction(o,m,{allowReset:true,earlyCountResets:true,earlyResetCookieTarget:2**90,assignPermanentSlots:false});m=d.memory;
    assert(d.action,d.reason);if(d.action.type==='ascend')entered=true;r.act(d.action);
  }
  assert.equal(r.Game.resets,1);assert(HELPER_ART_EXCLUSIONS.every(name=>!r.Game.Has(name)));
  assert.equal(r.Game.Has('Season switcher'),1);assert.equal(plan(r).status,'needs-resources');
});

test('completion invokes the clean helper phase before its next early profitable reset',{skip},()=>{
  const r=prepared();boundary(r);r.Game.cookies=r.Game.cookiesEarned=2**90;
  const d=decidePolicy(completionPolicySource(),r.snapshot(),[],{restoreViewport:true});
  assert.equal(d.stage,'two-art-helper-setup');assert.deepEqual(d.action,{type:'buy-building',id:1,amount:1});
  const disabled=decidePolicy(completionPolicySource({helperSetup:false}),r.snapshot(),[],{restoreViewport:true});
  assert.deepEqual(disabled.action,{type:'ascend'});
});

test('the composed ascent selector does not preserve artwork in a permanent slot',{skip},()=>{
  const r=prepared(),o=r.snapshot();
  o.progression.onAscend=true;o.ascension.permanentSlots=[-1,-1,-1,-1,-1];
  for(const u of o.ascension.heavenlyUpgrades)u.bought=true;
  o.ascension.permanentCandidates=HELPER_ART_EXCLUSIONS.map(name=>({id:r.Game.Upgrades[name].id,name,price:1e30}));
  const d=decidePolicy(completionPolicySource(),o,[],{});
  assert.equal(d.action.type,'reincarnate');
  const without=decidePolicy(completionPolicySource({helperSetup:false}),o,[],{});
  assert.equal(without.action.type,'permanent-slot');
});

test('animation and the conservative source-profile clock bound are checked before a sweep',{skip},()=>{
  const r=prepared();boundary(r);
  let o=helperObservation(r);o.controls.preferences.animate=0;
  assert.equal(decidePolicy(source,o,[],{}).status,'blocked');
  o=helperObservation(r);delete o.controls.preferences.animate;
  assert.equal(decidePolicy(source,o,[],{}).status,'blocked');
  for(const elapsedMs of [-1,2**50+1,Infinity,NaN,0.5]) {
    o=helperObservation(r);o.elapsedMs=elapsedMs;
    assert.equal(decidePolicy(source,o,[],{}).status,'blocked');
  }
  o=helperObservation(r);o.elapsedMs=2**50;
  assert.notEqual(decidePolicy(source,o,[],{}).status,'blocked');
});

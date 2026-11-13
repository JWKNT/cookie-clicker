import test from 'node:test';
import assert from 'node:assert/strict';
import {createRuntime} from '../model/runtime.mjs';
import {hasGameSource} from '../model/game-source.mjs';
import {decideAscensionAction} from '../model/ascension-policy.mjs';
import {completionPolicySource} from '../model/completion-policy.mjs';
import {baselinePolicySource} from '../model/baseline-policy.mjs';
import {decidePolicy} from '../model/policy-runtime.mjs';
const skip=!hasGameSource();
const target=2**90;
const options={allowReset:true,earlyCountResets:true,earlyResetCookieTarget:target};
const activation=['Heavenly chip secret','Heavenly cookie stand','Heavenly bakery','Heavenly confectionery','Heavenly key'];
function prepared(){
  const r=createRuntime();
  for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press','Cookie-dunker','Hardcore','Neverclick','Just wrong'])r.Game.Win(n);
  return r;
}
const memory=()=>({restoreViewport:true,growth:{nextClick:100,nextPurchase:0}});

test('the purchase cadence is explicit and bounded while the default stays300ms', {skip},()=>{
  const r=prepared(),o=r.snapshot();
  for(const interval of [300,1000]){
    const d=decidePolicy(baselinePolicySource({clickRate:0,purchaseIntervalMilliseconds:interval}),o,[],null);
    assert.equal(d.memory.nextPurchase,o.elapsedMs+interval);
  }
  for(const interval of [0,-1,Infinity,1001])assert.throws(()=>baselinePolicySource({purchaseIntervalMilliseconds:interval}),/Invalid/);
});

test('the early count waits for its fixed earned target and positive native prestige', {skip},()=>{
  const r=prepared();r.Game.cookies=target;r.Game.cookiesEarned=target-2**38;
  let d=decideAscensionAction(r.snapshot(),{},options);
  assert.equal(d.status,'needs-resources');assert.equal(d.action,null);assert.equal(d.requiredCookiesEarned,target);
  r.Game.cookiesEarned=target;
  d=decideAscensionAction(r.snapshot(),{},options);assert.deepEqual(d.action,{type:'ascend'});
  assert.equal(d.goal,'Early profitable ascensions');
  r.Game.cookiesReset=1e90;r.Game.prestige=Math.floor(r.Game.HowMuchPrestige(r.Game.cookiesReset));
  assert.equal(r.snapshot().ascension.gainedIfAscend,0);
  d=decideAscensionAction(r.snapshot(),{},options);assert.equal(d.status,'needs-prestige');assert.equal(d.action,null);
});

test('challenge, reset-permission and normal-mode gates protect the early count', {skip},()=>{
  const r=prepared();r.Game.cookiesEarned=target;r.Game.cookies=target;
  r.Game.Achievements.Hardcore.won=0;
  assert.equal(decideAscensionAction(r.snapshot(),{},options).status,'needs-achievement');
  r.Game.Win('Hardcore');
  assert.equal(decideAscensionAction(r.snapshot(),{},{...options,allowReset:false}).status,'deferred');
  r.Game.ascensionMode=1;
  assert.equal(decideAscensionAction(r.snapshot(),{},options).status,'blocked');
});

test('activation offers are permitted by default; the old hold is an explicit diagnostic option', {skip},()=>{
  const r=prepared();r.Game.cookies=1e15;
  const o=r.snapshot();
  // Decision fixture: expose native activation offers to isolate admission.
  // It does not assert that this bank was reached from a new save.
  o.shop.upgrades=activation.map(name=>({id:r.Game.Upgrades[name].id,name,price:r.Game.Upgrades[name].getPrice(),canBuy:true,pool:''}));
  for(const name of activation){o.upgrades[name].unlocked=true;assert.equal(r.Game.Upgrades[name].noPerm,1);}
  const before=structuredClone(o), source=completionPolicySource();
  let d=decidePolicy(source,o,[],memory());
  assert.equal(d.action.type,'buy-upgrade');assert(o.shop.upgrades.some(u=>u.id===d.action.id));
  assert.equal(d.memory.ascension.config.earlyResetCookieTarget,target);
  assert.equal(d.memory.ascension.config.earlyCountResets,true);
  assert.equal(d.memory.ascension.config.assignPermanentSlots,true);
  assert.deepEqual(o,before);
  const held=completionPolicySource({withholdEarlyPrestigeActivation:true});
  d=decidePolicy(held,o,[],memory());
  assert(!o.shop.upgrades.some(u=>d.action.type==='buy-upgrade' && d.action.id===u.id));
  o.ascensions=100;
  d=decidePolicy(held,o,[],{...memory(),ascension:{config:{allowReset:false}}});
  assert.equal(d.action.type,'buy-upgrade');assert(o.shop.upgrades.some(u=>u.id===d.action.id));
});

test('removing the activation hold preserves the first-run Hardcore restriction', {skip},()=>{
  const r=prepared();r.Game.cookies=1e15;r.Game.Achievements.Hardcore.won=0;
  const o=r.snapshot();
  o.shop.upgrades=activation.map(name=>({id:r.Game.Upgrades[name].id,name,price:1,canBuy:true,pool:''}));
  const d=decidePolicy(completionPolicySource(),o,[],memory());
  assert.notEqual(d.action.type,'buy-upgrade');assert.equal(d.stage,'challenge-achievements');
  assert.equal(r.Game.UpgradesOwned,0);
});

test('the early policy permits a legal permanent upgrade assignment', {skip},()=>{
  const r=prepared();r.Game.Upgrades['Kitten helpers'].earn();
  const o=r.snapshot();o.progression.onAscend=true;
  for(const u of o.ascension.heavenlyUpgrades)u.bought=true;
  o.ascension.permanentSlots=[-1,-1,-1,-1,-1];
  o.ascension.permanentCandidates=o.ascension.permanentCandidates.filter(u=>u.name==='Kitten helpers');
  assert.equal(o.ascension.permanentCandidates.length,1);
  const d=decidePolicy(completionPolicySource(),o,[],memory());
  assert.deepEqual(d.action,{type:'permanent-slot',slot:0,id:r.Game.Upgrades['Kitten helpers'].id});
  assert.equal(d.memory.ascension.config.assignPermanentSlots,true);
});

test('the early phase defers unripe trials and funds Temple1 from a ripe lump', {skip},()=>{
  const r=prepared();const o=r.snapshot();
  o.lump={available:true,ageMs:600,matureAge:600,ripeAge:900,overripeAge:1200};
  const source=completionPolicySource();
  let d=decidePolicy(source,o,[],memory());assert.notEqual(d.action.type,'harvest-lump');
  o.lump.ageMs=900;d=decidePolicy(source,o,[],memory());assert.equal(d.action.type,'harvest-lump');
  o.lump.ageMs=0;o.lumps=1;
  const temple=o.shop.buildings.find(b=>b.name==='Temple');temple.amount=1;
  d=decidePolicy(source,o,[],memory());assert.deepEqual(d.action,{type:'level-building',id:temple.id});
  assert.equal(d.stage,'early-income-temple');
});

test('the early Temple upgrade owns only its immediate native lump confirmation', {skip},()=>{
  const r=prepared();r.Game.Objects.Temple.amount=r.Game.Objects.Temple.highest=1;r.Game.lumps=1;r.Game.cookiesEarned=1e9;r.Game.prefs.askLumps=1;
  const source=completionPolicySource();
  const d=decidePolicy(source,r.snapshot(),[],memory());assert.equal(d.action.type,'level-building');r.act(d.action);
  assert.equal(r.Game.promptOn,1);
  const confirm=decidePolicy(source,r.snapshot(),[],d.memory);assert.deepEqual(confirm.action,{type:'prompt',option:0});r.act(confirm.action);
  assert.equal(r.Game.Objects.Temple.level,1);assert.equal(r.Game.lumps,0);
  r.Game.Prompt('<h3>Unrelated prompt</h3>',['Close']);
  const stale=decidePolicy(source,r.snapshot(),[],{...memory(),confirmEarlyLevel:{elapsedMs:-1,level:1}});
  assert.equal(stale.stage,'unowned-prompt');assert.equal(stale.action.type,'wait');
});

test('a supplied100-run funding ledger produces100 actual profitable resets, not a new-save certificate', {skip},()=>{
  const r=prepared();let m={};const gained=[];
  for(let run=0;run<100;run++){
    // Explicit conditional ledger fixture: funding is supplied at each entry.
    // The separate new-save experiment supplies no such values.
    r.Game.cookies=r.Game.cookiesEarned=target;
    const old=r.Game.resets,gain=r.snapshot().ascension.gainedIfAscend;
    assert(gain>0);gained.push(gain);
    let entered=false,finished=false;
    for(let j=0;j<500;j++){
      const o=r.snapshot();
      if(entered && r.Game.resets===old+1 && !o.progression.onAscend && !o.progression.ascendTimer && !o.progression.reincarnateTimer){finished=true;break;}
      const d=decideAscensionAction(o,m,options);m=d.memory;
      assert(d.action,`${run}: ${d.status}: ${d.reason}`);
      if(d.action.type==='ascend')entered=true;
      r.act(d.action);
    }
    assert(finished,`cycle ${run}`);
    for(const n of activation)assert.equal(r.Game.Upgrades[n].bought,0,n);
  }
  assert.equal(r.Game.resets,100);assert.equal(r.Game.HasAchiev('Reincarnation'),1);
  assert.equal(r.Game.cookiesReset,100*target);assert.equal(gained.length,100);
  assert.equal(r.snapshot().ascension.gainedIfAscend,0);
});

test('Pantheon open observation follows the native minigame toggle', {skip},()=>{
  const r=prepared();r.Game.Objects.Temple.amount=1;r.Game.Objects.Temple.level=1;
  r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
  const b=r.Game.Objects.Temple;b.minigame.launch();b.minigameLoaded=true;
  const before=r.snapshot().controls.pantheon.open;
  assert.equal(before,!!b.onMinigame);
  r.act({type:'minigame-open',id:b.id});assert.equal(r.snapshot().controls.pantheon.open,!before);
  r.act({type:'minigame-open',id:b.id});assert.equal(r.snapshot().controls.pantheon.open,before);
});

test('an explicit reset prohibition releases other controllers instead of trapping the early phase', {skip},()=>{
  const r=prepared();r.Game.Objects.Grandma.amount=1;r.Game.Achievements['Just wrong'].won=0;
  const source=completionPolicySource({ascension:{allowReset:false}});
  const d=decidePolicy(source,r.snapshot(),[],memory());
  assert.equal(d.stage,'misc');assert.deepEqual(d.action,{type:'sell-building',id:1,amount:1});
  const byMemory=decidePolicy(completionPolicySource(),r.snapshot(),[],{...memory(),ascension:{config:{allowReset:false}}});
  assert.equal(byMemory.stage,'misc');assert.deepEqual(byMemory.action,d.action);
});

import test from 'node:test';import assert from 'node:assert/strict';
import{createRuntime}from'../model/runtime.mjs';import{hasGameSource}from'../model/game-source.mjs';
import{decidePolicy}from'../model/policy-runtime.mjs';
import{orderedNaturalPolicySource,orderedNaturalPlan}from'../model/ordered-natural-policy.mjs';
import{decideSaturationFunding,saturationFundingPolicySource}from'../model/saturation-funding-policy.mjs';
import{completionPolicySource}from'../model/completion-policy.mjs';
const skip=!hasGameSource()&&'Pinned source unavailable';
const source=orderedNaturalPolicySource({saturation:{targetMultiplier:5,batchCycles:2,clicks:2},targetBank:2**100});
function prepared(){
 const r=createRuntime({recordAudit:false});r.advance(200);const G=r.Game;
 // Explicit conditional handoff fixture. No new-save reachability claim.
 G.cookies=G.cookiesEarned=2**500;G.resets=100;G.prestige=2**83;G.dragonLevel=27;G.santaLevel=14;G.pledges=10;
 for(const a of Object.values(G.Achievements))a.won=1;G.AchievementsOwned=622;
 for(const u of Object.values(G.Upgrades)){u.unlocked=1;u.bought=Number(!['debug','unused','dungeon','shadow','toggle'].includes(u.pool));}
 for(const b of Object.values(G.Objects)){b.amount=b.highest=b.id===0?1000:700;b.level=1;}
 G.Objects.Cursor.level=12;G.Objects.Farm.level=10;
 for(const[name,file]of[['Farm','minigameGarden.js'],['Bank','minigameMarket.js'],['Temple','minigamePantheon.js'],['Wizard tower','minigameGrimoire.js']]){
 const b=G.Objects[name];if(!b.minigame)r.evaluate(r.source.sources[file],file);b.minigame.launch();b.minigameLoaded=true;b.switchMinigame(true);}
 G.Objects.Bank.minigame.officeLevel=4;G.Objects.Bank.minigame.brokers=50;
 const garden=G.Objects.Farm.minigame;garden.soil=0;garden.freeze=1;garden.convertTimes=1;garden.harvestsTotal=1000;for(const p of Object.values(garden.plants))p.unlocked=1;
 G.Objects.Temple.minigame.slot=[2,-1,-1];G.Objects.Temple.minigame.gods.ruin.slot=0;
 G.seasonT=0;G.recalculateGains=1;r.advance(200);return r;
}
function act(r,a){if(a.type==='sequence')for(const x of a.actions)act(r,x);else r.act(a);}
function step(r,m={},extra={}){const o=r.snapshot();const d=decidePolicy(source,o,[],m);if(d.action)act(r,d.action);return d;}

test('ordered candidate starts on a genuine fresh save and retains the daily schedule',{skip},()=>{
 const r=createRuntime({recordAudit:false});let m={};for(let n=0;n<8;n++){const d=step(r,m);m=d.memory;assert(d.action);assert.notEqual(d.action.type,'ascend');}
 assert.equal(m.phase,'resources');assert.equal(r.Game.resets,0);assert(r.Game.cookieClicks<=15);
 assert.deepEqual(orderedNaturalPlan().maintenanceReload,{firstMs:86400000,everyMs:86400000});
});

test('Farm10 is unconditional before research, while only ripe lumps are harvested',{skip},()=>{
 const r=prepared();const G=r.Game;G.Objects.Farm.level=9;G.lumps=10;G.Achievements['Green, aching thumb'].won=0;
 for(const n of ['Bingo center/Research facility','One mind'])G.Upgrades[n].bought=0;
 const o=r.snapshot();let d=decidePolicy(source,o,[],{});
 assert.equal(d.memory.phase,'resources');assert.deepEqual(d.action,{type:'level-building',id:2});act(r,d.action);assert.equal(G.Objects.Farm.level,10);
 // Isolate the source completion controller's new ripe-only decision rule.
 const lone=completionPolicySource({ripeLumpsOnly:true,gardenEnabled:false,allowFinalCollection:false,finalPreparation:false,deferVeil:true,
  earlyFunding:{enabled:false},season:{seasons:[],research:false,wrinklers:false,fortunes:false,dragonDrops:false,helperGrandma:false,eldeer:false},ascension:{allowReset:false}});
 const v=r.snapshot();v.achievements['Hand-picked']=false;v.lump={available:true,ageMs:20*3600000,matureAge:20*3600000,ripeAge:23*3600000,overripeAge:24*3600000};
 d=decidePolicy(lone,v,[],{restoreViewport:true});assert.notEqual(d.action.type,'harvest-lump');
 v.lump.ageMs=v.lump.ripeAge;d=decidePolicy(lone,v,[],{restoreViewport:true});assert.equal(d.action.type,'harvest-lump');
});

test('resources phase withholds native research even when the displayed shop offers One mind',{skip},()=>{
 const r=prepared(),G=r.Game;G.Objects.Farm.level=9;G.lumps=0;G.Upgrades['One mind'].bought=0;G.Upgrades['One mind'].unlocked=1;
 let d=decidePolicy(source,r.snapshot(),[],{nextFunding:1e12});assert.equal(d.memory.phase,'resources');
 assert.notEqual(d.action?.id,G.Upgrades['One mind'].id);assert.equal(d.memory.prefix.season.config.research,false);

});

test('the single final reset decision does not depend on an already-won veil or spell outcome',{skip},()=>{
 const r=prepared(),o=r.snapshot();
 const a=decidePolicy(source,o,[],{phase:'elder'});assert.equal(a.memory.phase,'final-reset');
 const b=decidePolicy(source,{...o,achievements:{...o.achievements,'Thick-skinned':false}},[],{phase:'elder'});
 assert.equal(b.memory.phase,'final-reset');assert.deepEqual(a.action,b.action);
 const reset=decidePolicy(source,o,[],a.memory);assert.equal(reset.action.type,'ascend');
 const same=decidePolicy(source,{...o,achievements:{...o.achievements,'Thick-skinned':false}},[],b.memory);assert.deepEqual(reset.action,same.action);
 // A missing wizard goal does not reuse or repeatedly retry a final boundary.
 const missing=decidePolicy(source,{...o,achievements:{...o.achievements,'A wizard is you':false}},[],{phase:'elder'});
 assert.notEqual(missing.memory.phase,'final-reset');
});

test('native finite saturation prefixes increase the actual buff, restore1000Cursors, and keep allocations/resources real',{skip},()=>{
 const r=prepared();const G=r.Game;G.buffs={};G.cookies=G.cookiesEarned=2**250;const options={targetMultiplier:5,batchCycles:2,clicks:2,restoreTarget:1000};let m={};let d;let controls=0;
 for(let n=0;n<30;n++){
 const o=r.snapshot();d=decideSaturationFunding(o,m,options);assert.deepEqual(decidePolicy(saturationFundingPolicySource(options),o,[],m),d);m=d.memory;
 if(d.status==='complete')break;assert(d.action,JSON.stringify(d));controls++;act(r,d.action);
 }
 assert.equal(d.status,'complete');assert(G.buffs.Devastation.multClick>=5);assert.equal(G.Objects.Cursor.amount,1000);assert(controls>4);
 assert.equal(m.observedClickCountChange,2);assert(G.cookies>m.bankBeforeClicks);
});

test('a native final reset and direct veil suffix is executed once without another reset after a failed veil click',{skip,timeout:30000},()=>{
 const r=prepared();let m={phase:'final-reset'};let resets=0;let enteredRebuild=false;
 for(let n=0;n<120;n++){
 const d=decidePolicy(source,r.snapshot(),[],m);m=d.memory;
 if(m.phase==='rebuild'){enteredRebuild=true;break;}
 assert(d.action,JSON.stringify(d));if(d.action.type==='ascend')resets++;act(r,d.action);
 }
 assert(enteredRebuild,JSON.stringify(m));assert.equal(resets,1);assert.equal(r.Game.resets,101);
 assert.equal(m.finalReset.reusedSpellBoundary,false);assert.equal(m.veil.phase,'complete');
});

test('a prepared native rebuild releases the frozen tail and its final office callback',{skip},()=>{
 const r=prepared();r.Game.Objects.Farm.minigame.freeze=0;r.Game.Achievements['Pyramid scheme'].won=0;let m={phase:'rebuild'};let released=false;
 for(let n=0;n<15;n++){
 const d=decidePolicy(source,r.snapshot(),[],m);m=d.memory;if(m.phase==='tail')released=true;
 if(d.status==='complete')break;assert(d.action,JSON.stringify(d));act(r,d.action);
 }
 assert(released);assert.equal(r.Game.Objects.Bank.minigame.officeLevel,5);
 const d=decidePolicy(source,r.snapshot(),[],m);assert.equal(d.status,'complete');
});


test('funding refuses a native click that rounds away at the current bank',{skip},()=>{
 const r=prepared(),o=r.snapshot();o.buffs.Devastation={multClick:5,time:300};o.cookiesPerClick=1;
 const d=decideSaturationFunding(o,{phase:'gains',run:o.ascensions},{targetMultiplier:5,clicks:2});
 assert.equal(d.status,'blocked');assert.equal(d.action,null);assert.match(d.reason,/rounding threshold/);
});

test('completion route restrictions reject invalid values without changing legacy defaults',()=>{
 assert.doesNotThrow(()=>completionPolicySource());
 for(const options of [{minimumFarmLevel:8},{minimumFarmLevel:13},{buildingAmountLimit:0},{gardenEnabled:'false'},{deferVeil:1}])
  assert.throws(()=>completionPolicySource(options),RangeError);
});

test('the prefix keeps source spell/reset gates but leaves aggregate current ownership to the tail',{skip},()=>{
 const r=prepared(),o=r.snapshot();
 let d=decidePolicy(source,{...o,achievements:{...o.achievements,"Oft we mar what's well":false}},[],{phase:'elder'});
 assert.equal(d.memory.phase,'final-reset');
 d=decidePolicy(source,{...o,achievements:{...o.achievements,'Bibbidi-bobbidi-boo':false}},[],{phase:'elder'});
 assert.notEqual(d.memory.phase,'final-reset');
});


test('a pre-Hardcore current-save reload cannot erase the retained opening progress',{skip},()=>{
 const r=createRuntime({recordAudit:false}),o=r.snapshot();
 const memory={phase:'resources',highestAscensions:0,hardcore:false,openingEarned:15};
 const d=decidePolicy(source,o,[],memory);
 assert.equal(d.stage,'opening-maintenance-restoration');assert.equal(d.action.type,'wait');
 assert.equal(d.memory.openingEarned,15);
 const restored=decidePolicy(source,{...o,cookiesEarned:15},[],d.memory);
 assert.notEqual(restored.stage,'opening-maintenance-restoration');
});

import assert from'node:assert/strict';import{writeFileSync}from'node:fs';
import{createRuntime}from'../../runtime.mjs';
const r=createRuntime({randomSeed:1,recordAudit:true}),G=r.Game;r.advance(1000);
// Conditional prior heavenly ownership and achievement milestones, not a new-save trace.
// The ordinary reset below is fixed independently of any veil outcome.
for(const name of ['Hardcore','Neverclick'])G.Win(name);
for(const name of ['Legacy','Starter kit','Starter kitchen','Shimmering veil','Reinforced membrane','Delicate touch','Steadfast murmur','Glittering edge'])G.Upgrades[name].earn();
r.act({type:'ascend'});r.act({type:'key',code:27,down:true});r.act({type:'key',code:27,down:false});r.advance(40);
assert(G.OnAscend);r.act({type:'reincarnate',mode:0});r.advance(6100);
assert.equal(G.cookieClicks,0);
const before=r.snapshot(),sales=[];
for(const b of before.shop.buildings)if(b.amount>0){r.act({type:'sell-building',id:b.id,amount:b.amount});sales.push([b.name,b.amount]);}
r.act({type:'wait',milliseconds:34});
assert.equal(G.BuildingsOwned,0);assert.equal(G.unbuffedCps,0);assert.equal(G.cookieClicks,0);
// The worst sufficient-index seed is a supplied diagnostic entry, never a
// policy read or a source reset. All35 subsequent clicks/purchases are native.
G.seed='awjiu';
const receipts=[];let purchases=0;
while(!G.HasAchiev('Thick-skinned')&&receipts.length<35){
 let o=r.snapshot();
 if(!o.upgrades['Shimmering veil [off]'].bought){
  const u=o.shop.upgrades.find(u=>u.name==='Shimmering veil [off]');assert(u);assert.equal(u.price,0);assert(u.canBuy);
  r.act({type:'buy-upgrade',id:u.id});purchases++;
 }
 r.act({type:'wait',milliseconds:34});o=r.snapshot();assert.equal(o.cookiesPs,0);
 const counter=o.cookieClicks;r.act({type:'click'});assert.equal(G.cookieClicks,counter+1);
 receipts.push({counter,afterCookieClicks:G.cookieClicks,won:!!G.HasAchiev('Thick-skinned'),elapsedMs:r.snapshot().elapsedMs,bank:G.cookies,unbuffedCps:G.unbuffedCps});
}
assert(G.HasAchiev('Thick-skinned'));assert.equal(receipts.length,35);assert.equal(purchases,34);assert.equal(G.BuildingsOwned,0);
const result={scope:'Conditional post-milestone entry, one independently fixed ordinary reset, then zero-building public sales/free veil rebuys and consecutive source clicks. Supplied worst seed is a diagnostic premise, not policy information. No all-goal new-save claim.',sales,startingCookieClicks:before.cookieClicks,defense:G.getVeilDefense(),purchases,receipts,sourceHashes:r.source.hashes,audit:r.auditCounts()};
writeFileSync('/tmp/cookie-audit/veil-seed-cover/free-veils-receipt.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({sales,clicks:receipts.length,purchases,elapsedMs:r.snapshot().elapsedMs,bank:G.cookies,unbuffedCps:G.unbuffedCps,won:!!G.HasAchiev('Thick-skinned')}));

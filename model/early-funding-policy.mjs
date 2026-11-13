/** A bounded, observation-only native Godzamok burst; no endpoint is assigned. */
function fundingDecision(o, memory, options) {
  const config={cycles:16384,batchCycles:128,clickRate:50,...options};
  config.clicks??=Math.min(400,Math.floor(config.clickRate*8));
  let m={...(memory || {})};
  const result=(status,reason,action=null)=>({status,reason,action,memory:m,exclusive:!!m.phase && !['complete','interrupted'].includes(m.phase),optimalityCertified:false});
  if(!Number.isSafeInteger(config.cycles)||config.cycles<1||config.cycles>65536
    || !Number.isSafeInteger(config.batchCycles)||config.batchCycles<1||config.batchCycles>249
    || !Number.isFinite(config.clickRate)||config.clickRate<=0||config.clickRate>50
    || !Number.isSafeInteger(config.clicks)||config.clicks<1||config.clicks>400||config.clicks/config.clickRate>8)
    return result('blocked','Use finite bounded cycle and native click batches.');
  const interrupted=reason=>{m.phase='interrupted';m.interruptionReason=reason;return result('interrupted',reason);};
  if(m.phase==='interrupted')return result('interrupted',m.interruptionReason);
  const p=o.progression,c=o.controls,b=o.shop?.buildings?.find(x=>x.name==='Cursor');
  const unavailable=reason=>m.phase?interrupted(reason):result('deferred',reason);
  if(!p||!c||!b||p.onAscend||p.ascendTimer||p.reincarnateTimer||p.ascensionMode!==0||c.promptOn||c.menu)
    return unavailable('An active normal run with visible store controls is required.');
  if(!o.achievements.Hardcore||!o.achievements.Neverclick)return unavailable('Finish the first-run challenges first.');
  if(!p.minigames.Temple||!o.shop.buildings.some(x=>x.name==='Temple'&&x.amount>0)||c.pantheon?.slots?.[0]!==2)return unavailable('The native diamond Godzamok slot must be active.');
  if(!o.upgrades?.['Plastic mouse']?.bought)return unavailable('Buy the ordinary CpS-based click upgrade before funding bursts.');
  if(o.buffs?.['Cursed finger'])return unavailable('Let Cursed finger finish before starting a funding burst.');
  if(o.buffs?.['Nasty goblins'])return unavailable('Wait for the temporary building-price penalty to end.');
  if(!Number.isFinite(o.cookies)||o.cookies<0||!Number.isFinite(o.cookiesPerClick)||o.cookiesPerClick<=0)
    return unavailable('Finite positive native income is required.');
  if(m.run!==undefined&&m.run!==o.ascensions)return interrupted('A reset interrupted the owned burst.');
  const bulk=id=>({type:'store-bulk',id}),product={type:'click-product',id:0};
  const sequence=actions=>({type:'sequence',actions});
  if(!m.phase){
    const otherCps=o.shop.buildings.filter(x=>x.id!==0).reduce((sum,x)=>sum+(x.productionCps||0),0);
    const stableBuffs=Object.values(o.buffs||{}).every(x=>!(x.multCpS>1)||x.time/o.fps>9);
    const amount=o.cookies>=2**50 && otherCps*.01*config.clicks>=2**34 && stableBuffs ? 100 : 1;
    const lossPerCycle=amount===100?2**32:16;
    if(o.cookies<lossPerCycle*config.cycles+100000)return result('deferred','Reserve every possible native purchase debit before the burst.');
    m={run:o.ascensions,phase:'setup',originalCursors:b.amount,completed:0,amount,lossPerCycle,bulkId:amount===100?4:2};
    if(b.amount!==m.amount){
      const actions=b.amount>0?[bulk(1),bulk(5),product]:[];
      actions.push(bulk(0),bulk(m.bulkId),product);
      return result('acting','Use native controls to retain the selected Cursor batch and all sale proceeds.',sequence(actions));
    }
  }
  if(b.amount!==m.amount)return result('blocked','Native setup did not leave the selected Cursor count.');
  if(b.price>(m.amount===100?20000000:18)||b.rebuyOnePrice>(m.amount===100?20000000:15)||!Number.isFinite(b.price)||!Number.isFinite(b.rebuyOnePrice))
    return result('blocked','The quoted Cursor price exceeds this burst profile.');
  if(m.phase==='setup'){
    // Native sales increase an existing multiplier but do not renew its time.
    // Allow one second beyond the clicks for the gains frame and the native
    // 33ms loop cadence (buff.time is measured in nominal 30fps ticks).
    const old=o.buffs.Devastation;
    if(old && old.time/o.fps<=config.clicks/config.clickRate+1){
      m.phase='expiry';m.waitUntil=o.elapsedMs+Math.ceil(old.time*1000/o.fps)+100;
      return result('acting','Let the short remaining buff expire before starting a complete burst.',{type:'wait',milliseconds:m.waitUntil-o.elapsedMs});
    }
    m.phase='cycles';m.startedAt=o.elapsedMs;m.startBank=o.cookies;m.startEarned=o.cookiesEarned;
  }
  if(m.phase==='expiry'){
    if(o.elapsedMs<m.waitUntil || o.buffs.Devastation)return result('blocked','The committed native expiry wait did not finish.');
    m.phase='cycles';m.startedAt=o.elapsedMs;m.startBank=o.cookies;m.startEarned=o.cookiesEarned;
  }
  if(m.phase==='cycles'){
    if(o.elapsedMs!==m.startedAt||o.cookiesEarned!==m.startEarned)return result('blocked','An automatic task or earned-cookie change interrupted the same-time prefix.');
    if(m.pending){m.completed+=m.pending;delete m.pending;}
    if(o.cookies<m.startBank-m.lossPerCycle*m.completed)return result('blocked','Native debit exceeded the reserved per-cycle loss.');
    if(m.completed<config.cycles){
      const count=Math.min(config.batchCycles,config.cycles-m.completed);
      if(o.cookies<m.lossPerCycle*count)return result('blocked','The next committed batch is not funded.');
      const actions=[bulk(m.bulkId)];for(let i=0;i<count;i++)actions.push(bulk(1),product,bulk(0),product);
      m.pending=count;
      return result('acting','Execute a finite native sell/rebuy batch without advancing time.',sequence(actions));
    }
    m.phase='gains';return result('acting','Allow a native gains update before the click burst.',{type:'wait',milliseconds:34});
  }
  if(m.phase==='gains'){
    if(!o.buffs.Devastation)return interrupted('The committed buff is absent before the clicks.');
    m.phase='clicks';m.clicksBefore=o.cookieClicks;
    const interval=1000/config.clickRate,actions=[];
    for(let i=0;i<config.clicks;i++)actions.push({type:'wait',milliseconds:interval},{type:'click'});
    return result('acting','Use the native click cadence while the completed buff remains active.',sequence(actions));
  }
  if(m.phase==='clicks'){
    m.phase='complete';m.acceptedClicks=o.cookieClicks-m.clicksBefore;m.afterBank=o.cookies;m.afterEarned=o.cookiesEarned;
    if(m.acceptedClicks!==config.clicks)return interrupted('The native click receipt differs from the committed batch; retain the observed result.');
  }
  return result('complete','The bounded native burst returned; later growth and resets use its actual result.');
}
export function earlyFundingPolicySource(options={}){
 return `(function(o,actions,memory){return (${fundingDecision.toString()})(o,memory,${JSON.stringify(options)});})`;
}
export function decideEarlyFunding(o,memory={},options={}){return fundingDecision(o,memory,options);}

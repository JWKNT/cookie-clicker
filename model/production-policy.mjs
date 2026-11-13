/** Final-run ownership and production baseline. It does not certify optimal growth. */
function productionDecision(o, actions, memory) {
  const config={finalCollection:false,preserveChallengeAchievements:true,buyOrdinaryUpgrades:true,clickRate:20,maxWaitMs:1000,...(memory?.config||{})};
  const m={...(memory||{}),config};
  const result=(status,goal,reason,action=null,extra={})=>({status,goal,reason,action,memory:m,...extra});
  const won=name=>!!o.achievements?.[name];
  if(!config.finalCollection)return result('deferred','Final-run collection','The scheduler must finish its planned resets before requesting final current ownership.');
  if(!Number.isFinite(config.clickRate)||config.clickRate<0||config.clickRate>50||!Number.isFinite(config.maxWaitMs)||config.maxWaitMs<=0)return result('blocked','Production configuration','Use a click rate from zero to fifty and a positive finite wait limit.');
  const p=o.progression;
  if(p.onAscend||p.ascendTimer||p.reincarnateTimer||p.ascensionMode!==0)return result('blocked','Final normal run','Production collection requires an active normal run.');
  if(o.controls.promptOn)return result('blocked','Production controls','Resolve the unrelated prompt before purchases.');
  if(config.preserveChallengeAchievements&&(!won('Hardcore')||!won('Neverclick')))return result('needs-achievement','First-run challenges','Preserve the no-upgrade and limited-click conditions until both achievements are won.');
  const buildings=o.shop?.buildings;
  const targets=o.production;
  if(buildings?.length!==20||!targets?.bankAchievements?.length||!targets.cpsAchievements?.length||targets.handmadeAchievements?.length!==15)return result('blocked','Production catalogue','The pinned native production thresholds are required.');
  const deficient=buildings.filter(b=>b.amount<b.goalAmount).sort((a,b)=>a.buy1price-b.buy1price||a.id-b.id);
  for(const b of deficient) {
    if(b.locked)continue;
    const amount=b.goalPurchase.amount;
    if(amount>0&&o.cookies>=b.goalPurchase.price)return result('acting','Final building counts','Buy the native batch needed for this current holding.',{type:'buy-building',id:b.id,amount},{building:b.name,targetAmount:b.goalAmount});
    if(o.cookies>=b.buy1price)return result('acting','Final building counts','Add one affordable building toward its current holding target.',{type:'buy-building',id:b.id,amount:1},{building:b.name,targetAmount:b.goalAmount});
  }
  if(config.buyOrdinaryUpgrades) {
    // One mind owns a confirmation workflow in the research controller.
    const u=o.shop.upgrades.filter(u=>!['toggle','prestige','debug','unused','dungeon','shadow'].includes(u.pool)&&u.name!=='One mind'&&u.canBuy&&u.price<=o.cookies)
      .sort((a,b)=>a.price-b.price||a.id-b.id)[0];
    if(u)return result('acting','Current ordinary upgrades','Buy an unlocked ordinary upgrade at its native displayed price.',{type:'buy-upgrade',id:u.id});
  }
  const handmadeMissing=targets.handmadeAchievements.filter(a=>!won(a.name));
  if(handmadeMissing.length&&config.clickRate>0&&o.elapsedMs>=(m.nextClickAt??100)) {
    m.nextClickAt=o.elapsedMs+1000/config.clickRate;
    return result('acting','Handmade production','Click without predicting a random outcome.',{type:'click'});
  }
  if(deficient.length) {
    const b=deficient[0];
    return result('needs-resources','Final building counts','Grow the bank before the next count purchase.',null,{building:b.name,buildingId:b.id,targetAmount:b.goalAmount,requiredCookies:b.buy1price,fullBatchCookies:b.goalPurchase.price});
  }
  const missingProduction=buildings.flatMap(b=>b.productionAchievements.filter(a=>!won(a.name)).map(a=>({building:b.name,buildingId:b.id,achievement:a.name,target:a.threshold,produced:b.totalCookies,
    secondsAtCurrentRate:b.productionCps>0?Math.max(0,(a.threshold-b.totalCookies)/b.productionCps):null})));
  const missingBank=targets.bankAchievements.filter(a=>!won(a.name));
  const missingCps=targets.cpsAchievements.filter(a=>!won(a.name));
  const countChecks=buildings.flatMap(b=>b.countAchievements).filter(a=>!won(a.name));
  const pending=missingProduction.length||missingBank.length||missingCps.length||handmadeMissing.length||countChecks.length||!won('Septcentennial');
  if(!pending)return result('complete','Final production and counts','All native production families and count achievements are won, and current building holdings meet their targets.');
  const nextClick=config.clickRate>0&&handmadeMissing.length?Math.max(1,(m.nextClickAt??100)-o.elapsedMs):config.maxWaitMs;
  return result('needs-production','Production milestones','Continue growth and native production; the rate estimates assume unchanged rates and are not completion-time bounds.',
    {type:'wait',milliseconds:Math.min(config.maxWaitMs,nextClick)},
    {requiredRawCps:missingCps.at(-1)?.threshold??null,requiredCookiesEarned:missingBank.at(-1)?.threshold??null,requiredHandmadeCookies:handmadeMissing.at(-1)?.threshold??null,
      missingProduction, pendingCountChecks:countChecks.map(a=>a.name)});
}

export function decideProductionAction(observation,memory={},options={}) {
  return productionDecision(observation,[],{...memory,config:{...(memory.config||{}),...options}});
}
export function productionPolicySource(options={}) {
  return `(function(observation,availableActions,memory){return (${productionDecision.toString()})(observation,availableActions,{...(memory||{}),config:{...${JSON.stringify(options)},...((memory||{}).config||{})}});})`;
}

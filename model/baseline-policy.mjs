/**
 * A reproducible growth baseline for full-engine experiments. It is not a
 * completing strategy: ascensions, the full achievement schedule, and most
 * minigames still need a controller. Evaluation always uses the full target.
 */
export function baselinePolicySource({ clickRate = 20, purchaseRule = 'exchange', upgradeShare = 0.5, inputBatchMilliseconds = 0, purchaseIntervalMilliseconds = 300 } = {}) {
  if (!Number.isFinite(clickRate) || clickRate < 0 || clickRate > 50
      || !['exchange', 'roi', 'cheapest'].includes(purchaseRule)
      || !Number.isFinite(upgradeShare) || upgradeShare < 0 || upgradeShare > 1
      || !Number.isFinite(purchaseIntervalMilliseconds) || purchaseIntervalMilliseconds < 1 || purchaseIntervalMilliseconds > 1000
      || !Number.isFinite(inputBatchMilliseconds) || inputBatchMilliseconds < 0 || inputBatchMilliseconds > 1000) {
    throw new Error('Invalid baseline parameters');
  }
  const configuration = JSON.stringify({ clickRate, purchaseRule, upgradeShare, inputBatchMilliseconds, purchaseIntervalMilliseconds });
  return `(function () {
    const config = ${configuration};
    return function (observation, actions, memory) {
      const m = memory ? { ...memory } : { nextClick: 100, nextPurchase: 0 };
      const t = observation.elapsedMs;
      const answer = action => ({ action, memory: m });
      if (observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer) return answer({type:'wait',milliseconds:100});
      const shimmer = observation.shimmers[0];
      if (shimmer) return answer({type:'click-shimmer',id:shimmer.id});
      if (config.clickRate > 0 && t >= m.nextClick) {
        m.nextClick = t + 1000 / config.clickRate;
        return answer({type:'click'});
      }
      if (t >= m.nextPurchase) {
        m.nextPurchase = t + config.purchaseIntervalMilliseconds;
        const upgrade = observation.shop.upgrades
          .filter(u => u.pool !== 'toggle' && u.pool !== 'prestige' && u.canBuy && u.price <= observation.cookies * config.upgradeShare)
          .sort((a,b) => a.price-b.price || a.id-b.id)[0];
        if (upgrade) return answer({type:'buy-upgrade',id:upgrade.id});
        const buildings = observation.shop.buildings.filter(b => !b.locked && b.storedCps > 0);
        const totalBase = observation.shop.buildings.reduce((sum,b) => sum+b.storedTotalCps,0);
        const multiplier = totalBase > 0 ? observation.cookiesPs / totalBase : 1;
        const income = Math.max(observation.cookiesPs,0.1);
        const score = b => config.purchaseRule === 'cheapest' ? b.buy1price
          : config.purchaseRule === 'roi' ? b.buy1price / Math.max(b.storedCps*multiplier,0.000001)
          : Math.max(b.buy1price-observation.cookies,0)/income + b.buy1price/Math.max(b.storedCps*multiplier,0.000001);
        buildings.sort((a,b) => score(a)-score(b) || a.id-b.id);
        const best = buildings[0];
        if (best && best.buy1price <= observation.cookies) return answer({type:'buy-building',id:best.id,amount:1});
      }
      if (config.clickRate>0 && config.inputBatchMilliseconds>0) {
        const end=Math.min(t+config.inputBatchMilliseconds,m.nextPurchase,t+(observation.decisionHorizonMs??1000));
        if(end>t && m.nextClick<=end) {
          const inputs=[];let at=t;
          while(m.nextClick<=end) {
            if(m.nextClick>at) inputs.push({type:'wait',milliseconds:m.nextClick-at});
            at=Math.max(at,m.nextClick);inputs.push({type:'click'});m.nextClick=at+1000/config.clickRate;
          }
          if(end>at) inputs.push({type:'wait',milliseconds:end-at});
          return answer({type:'sequence',actions:inputs});
        }
      }
      const wait = Math.min(1000, Math.max(1,m.nextPurchase-t), config.clickRate > 0 ? Math.max(1,m.nextClick-t) : 1000);
      return answer({type:'wait',milliseconds:wait});
    };
  })()`;
}

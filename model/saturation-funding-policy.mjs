/** Actual finite same-time controls; the multiplier is never assigned.
 * Default saturation can require an enormous finite number of decisions.
 * This is not a source-loop or funding-reachability theorem.
 */
function saturationDecision(o, memory, options) {
  const config = { targetMultiplier: 2 ** 53, batchCycles: 200, clickRate: 50, clicks: 400, restoreTarget: 100, ...options };
  const m = { ...(memory || {}) };
  const result = (status, reason, action = null) => ({ status, reason, action, memory: m, exclusive: !!m.phase && !['complete','interrupted'].includes(m.phase) });
  const interrupted = reason => { m.phase = 'interrupted'; return result('interrupted', reason); };
  const bulk = id => ({ type: 'store-bulk', id }), product = { type: 'click-product', id: 0 };
  const sequence = actions => ({ type: 'sequence', actions });
  const b = o.shop?.buildings?.find(b => b.id === 0), P = o.progression;
  if (!Number.isInteger(config.targetMultiplier) || config.targetMultiplier < 2 || config.targetMultiplier > 2 ** 53
    || !Number.isSafeInteger(config.batchCycles) || config.batchCycles < 1 || config.batchCycles > 249
    || !(config.clickRate > 0 && config.clickRate <= 50) || !Number.isInteger(config.clicks) || config.clicks < 1 || config.clicks > 400
    || config.clicks / config.clickRate > 8 || config.restoreTarget !== null && (!Number.isInteger(config.restoreTarget) || config.restoreTarget < 100 || config.restoreTarget > 1000 || config.restoreTarget % 100 !== 0)) return result('blocked','Invalid finite funding configuration.');
  if (m.phase === 'complete') return result('complete','The native funding burst returned.');
  if (m.phase === 'interrupted') return result('interrupted','Retain the interrupted native result.');
  if (!P || !b || P.onAscend || P.ascendTimer || P.reincarnateTimer || P.ascensionMode !== 0 || o.controls?.promptOn || o.controls?.menu
    || !P.minigames.Temple || o.controls.pantheon?.slots?.[0] !== 2 || !o.achievements.Hardcore || !o.achievements.Neverclick
    || !o.upgrades?.['Plastic mouse']?.bought || !Number.isFinite(o.cookies) || o.cookies < 2 ** 90
    || o.buffs?.['Cursed finger'] || o.buffs?.['Nasty goblins']) return m.phase ? interrupted('The owned native funding profile changed.') : result('deferred','Use the funded active Godzamok profile.');
  if (m.run !== undefined && m.run !== o.ascensions) return interrupted('The run changed.');
  if (!m.phase) {
    const untilMaintenance = 86400000 - o.elapsedMs % 86400000;
    if (untilMaintenance < 10000) return result('waiting','Wait across the precommitted daily maintenance boundary.',{type:'wait',milliseconds:untilMaintenance + 1000});
    const old = o.buffs.Devastation;
    if (old && old.time / o.fps <= config.clicks / config.clickRate + 1) return result('waiting','Allow the remaining native buff to expire.',
      {type:'wait',milliseconds:Math.ceil(old.time * 1000 / o.fps) + 100});
    m.phase = 'setup'; m.run = o.ascensions; m.restoreTarget = config.restoreTarget ?? Math.max(100,Math.min(1000,Math.floor(b.amount / 100) * 100));
    if (b.amount !== 100) return result('acting','Retain 100 Cursors through native Sell all and Buy 100 controls.',
      sequence([...(b.amount > 0 ? [bulk(1),bulk(5),product] : []),bulk(0),bulk(4),product]));
  }
  if (m.phase === 'setup') {
    if (b.amount !== 100 || b.buy1price > 2 ** 25 || b.rebuyOnePrice > 2 ** 25) return result('blocked','The native 100-Cursor setup is not in its price envelope.');
    m.phase = 'cycles'; m.startedAt = o.elapsedMs; m.bank = o.cookies; m.earned = o.cookiesEarned; m.observedBatches = 0;
  }
  if (m.phase === 'cycles') {
    if (b.amount !== 100 || o.elapsedMs !== m.startedAt || o.cookies !== m.bank || o.cookiesEarned !== m.earned) return interrupted('A source event changed the same-time income frame.');
    const multiplier = o.buffs.Devastation?.multClick ?? 1;
    if (!Number.isFinite(multiplier) || multiplier < 1) return result('blocked','A finite native click multiplier is required.');
    if (multiplier < config.targetMultiplier) {
      const count = Math.min(config.batchCycles, Math.ceil(config.targetMultiplier - multiplier));
      const inputs = [bulk(4)]; for (let i = 0; i < count; i++) inputs.push(bulk(1),product,bulk(0),product);
      m.observedBatches++; return result('acting','Increase the native multiplier with a finite same-time sale/rebuy batch.',sequence(inputs));
    }
    m.phase = 'restore';
  }
  if (m.phase === 'restore') {
    if (o.elapsedMs !== m.startedAt) return interrupted('A timed source task interrupted the owned prefix.');
    if (b.amount < m.restoreTarget) {
      // The public quote to the full1000-Cursor target is a conservative reserve
      // for every smaller restoration; no future bank is assigned.
      if (!(o.cookies >= b.goalPurchase.price)) return result('blocked','The original full-Cursor restoration is not funded.');
      return result('acting','Restore one native100-Cursor batch before recalculating income.',sequence([bulk(0),bulk(4),product]));
    }
    m.phase = 'gains'; return result('acting','Run the native gains frame.',{type:'wait',milliseconds:34});
  }
  if (m.phase === 'gains') {
    if (!(o.buffs.Devastation?.multClick >= config.targetMultiplier) || o.buffs.Devastation.time / o.fps <= config.clicks / config.clickRate + 0.5) return interrupted('The actual buff did not survive until the click interval.');
    if (!(o.cookies + o.cookiesPerClick > o.cookies)) return result('blocked','The actual click credit is below the current native bank rounding threshold.');
    m.phase = 'clicks'; m.bankBeforeClicks = o.cookies; m.clicksBefore = o.cookieClicks;
    const inputs = []; for (let i = 0; i < config.clicks; i++) inputs.push({type:'wait',milliseconds:1000/config.clickRate},{type:'click'});
    return result('acting','Use the native click cadence during this finite buff.',sequence(inputs));
  }
  if (m.phase === 'clicks') {
    m.phase = 'complete'; m.observedClickCountChange = o.cookieClicks - m.clicksBefore; m.bankAfterClicks = o.cookies;
    // The public click counter may saturate. Do not report a fictitious exact
    // accepted-click count from its rounded difference.
    return result('complete','Record the actual bank and rounded click counter after the burst.');
  }
  return result('blocked','Unknown owned funding phase.');
}
export function decideSaturationFunding(o,m={},options={}) { return saturationDecision(o,m,options); }
export function saturationFundingPolicySource(options={}) { return `(function(o,a,m){return (${saturationDecision.toString()})(o,m,${JSON.stringify(options)});})`; }

/** Constructive seasonal, research and wrinkler collection. No optimality claim. */
export const RESEARCH_UPGRADES = Object.freeze([
  'Bingo center/Research facility', 'Specialized chocolate chips', 'Designer cocoa beans',
  'Ritual rolling pins', 'Underworld ovens', 'One mind', 'Exotic nuts',
  'Communal brainsweep', 'Arcane sugar', 'Elder Pact',
]);
export const DRAGON_DROPS = Object.freeze(['Dragon scale', 'Dragon claw', 'Dragon fang', 'Dragon teddy bear']);
export const SEASON_ACHIEVEMENTS = Object.freeze([
  'Coming to town', 'All hail Santa', 'Let it snow', 'Oh deer', 'Sleigh of hand',
  'Reindeer sleigher', 'Eldeer', "Baby it's old outside", 'Lovely cookies',
  'Spooky cookies', 'The hunt is on', 'Egging on', 'Mass Easteria', 'Hide & seek champion',
  'O Fortuna', 'Grandmapocalypse', 'Itchscratcher', 'Wrinklesquisher', 'Moistburster',
  'Wrinkler poker', 'Elder nap', 'Elder slumber', 'Elder calm',
]);

function seasonDecision(o, actions, memory, researchNames, dragonDrops) {
  const config = { seasons: ['valentines', 'christmas', 'halloween', 'easter'],
    preserveChallengeAchievements: true, research: true, fortunes: true, dragonDrops: true, wrinklers: true,
    helperGrandma: true, eldeer: true, reindeerTarget: 200, pledgeTarget: 10,
    maxSeasonUses: 12, helperMaxWidth: 16384,
    maxWaitMs: 1000, petIntervalMs: 0, suppressWrathForCookieCount: false, ...(memory?.config || {}) };
  const m = { ...(memory || {}), config };
  const answer = (status, goal, reason, action = null, extra = {}) => ({ status, goal, reason, action, memory: m, ...extra });
  const now = o.wallTimeMs;
  const wait = (goal, reason, ms = config.maxWaitMs) => answer('waiting', goal, reason,
    { type: 'wait', milliseconds: Math.max(1, Math.min(config.maxWaitMs, ms)) }, { wakeAfterMs: ms });
  const act = (goal, reason, action) => answer('acting', goal, reason, action);
  const retry = (goal, reason, retryReason) => answer('needs-ascension', goal, reason, null,
    { retryReason, requiresOrdinaryReset: true });
  const has = name => !!o.upgrades?.[name]?.bought;
  const unlocked = name => has(name) || !!o.upgrades?.[name]?.unlocked;
  const won = name => !!o.achievements?.[name];
  const offer = name => o.shop?.upgrades?.find(u => u.name === name && u.unlocked && !u.bought);
  const buy = (name, goal = name) => {
    const u = offer(name);
    if (!u) return null;
    if (o.cookies < u.price || !u.canBuy) return answer('needs-resources', goal, 'The native upgrade price exceeds the available bank.', null, { requiredCookies: u.price, upgrade: name });
    if (name === 'One mind') m.confirm = { name, elapsedMs: o.elapsedMs };
    return act(goal, 'Buy the unlocked native upgrade.', { type: 'buy-upgrade', id: u.id });
  };
  const S = o.seasonal;
  if (!S || !Number.isFinite(now)) return answer('blocked', 'Season observation', 'The native seasonal observation is required.');
  if (!Array.isArray(config.seasons) || config.seasons.some(s => !['valentines','christmas','halloween','easter'].includes(s))
    || !(config.maxWaitMs > 0 && Number.isFinite(config.maxWaitMs)) || !(config.petIntervalMs >= 0 && Number.isFinite(config.petIntervalMs))
    || !Number.isSafeInteger(config.reindeerTarget) || config.reindeerTarget < 0
    || !Number.isSafeInteger(config.maxSeasonUses) || config.maxSeasonUses < 1
    || !Number.isSafeInteger(config.helperMaxWidth) || config.helperMaxWidth < 200 || config.helperMaxWidth > 16384
    || !Number.isSafeInteger(config.pledgeTarget) || config.pledgeTarget < 0) return answer('blocked', 'Season configuration', 'Use supported seasons and finite nonnegative goal limits.');
  if (o.progression.onAscend || o.progression.ascensionMode !== 0 || o.progression.ascendTimer || o.progression.reincarnateTimer) return answer('blocked', 'Active normal run', 'Season collection requires an active normal run.');
  if (config.preserveChallengeAchievements && !won('Hardcore')) return answer('needs-achievement', 'Hardcore', 'Keep the no-upgrade run intact until Hardcore is won.');
  if (m.confirm) {
    const pending = m.confirm; delete m.confirm;
    if (o.controls.promptOn && o.elapsedMs === pending.elapsedMs && unlocked(pending.name) && !has(pending.name)) return act('Research confirmation', 'Confirm only the One mind purchase requested by this controller.', { type: 'prompt', option: 0 });
    return answer('blocked', 'Research confirmation', 'The expected research prompt changed or is absent.');
  }
  if (o.controls.promptOn) return answer('blocked', 'Season controls', 'Resolve the unrelated prompt first.');
  if (m.helperReleaseAt != null) {
    if (now < m.helperReleaseAt) return wait('Santa helper', 'Allow the native draw callback to process the held pointer.', m.helperReleaseAt - now);
    delete m.helperReleaseAt;
    return act('Santa helper', 'Release the native pointer after the draw callback.', { type: 'building-press', id: 1, release: true });
  }
  if (m.helperPress) {
    delete m.helperPress; m.helperReleaseAt = now + 100;
    return act('Santa helper', 'Press on the visible helper grandma.', { type: 'building-press', id: 1, release: false });
  }
  if (S.fortuneVisible && config.fortunes) return act('Fortune upgrades', 'Click the currently visible fortune.', { type: 'click-news' });

  const seasonNames = config.seasons.flatMap(s => s === 'christmas' ? ['A festive hat', ...S.groups.santa, "Santa's dominion", ...S.groups.reindeer] : S.groups[s]);
  const collection = [...(config.research ? researchNames : []), ...seasonNames,
    ...(config.dragonDrops ? dragonDrops : []), ...(config.fortunes ? S.groups.fortunes : [])];
  // Unlocks are purchased before another drop opportunity; bought eggs reduce duplicates.
  for (const name of collection) if (!has(name)) {
    const purchase = buy(name); if (purchase?.action) return purchase;
  }

  // A missing purchase or display must not suppress time-limited rewards.
  // The scheduler removes any golden cookie owned by its Fading luck hold.
  const reindeer = o.shimmers?.find(s => s.type === 'reindeer');
  const golden = o.shimmers?.find(s => s.type === 'golden');
  if (reindeer && (won('Eldeer') || !config.eldeer || o.buffs?.['Elder frenzy'] || reindeer.lifeSeconds <= 1)) return act('Christmas reindeer', 'Click the visible reindeer; preserve time for Eldeer when needed.', { type: 'click-shimmer', id: reindeer.id });
  if (golden) return act('Seasonal random rewards', 'Click a visible golden or wrath cookie without predicting its outcome.', { type: 'click-shimmer', id: golden.id });

  const targetFor = season => {
    const names = season === 'christmas' ? ['A festive hat', ...S.groups.santa, "Santa's dominion", ...S.groups.reindeer] : S.groups[season];
    return names.some(name => !has(name)) || season === 'christmas' && (o.santa.level < 14 || S.reindeerClicked < config.reindeerTarget && !(config.reindeerTarget <= 200 && won('Reindeer sleigher'))
      || config.eldeer && !won('Eldeer') || config.helperGrandma && !won("Baby it's old outside"));
  };
  const target = config.seasons.find(targetFor);
  if (target && S.season !== target) {
    if (S.uses >= config.maxSeasonUses) return retry('Season renewal',
      'Start another ordinary run before exponential season-switch prices grow further.', 'season-switch-limit');
    const trigger = { valentines: 'Lovesick biscuit', christmas: 'Festive biscuit', halloween: 'Ghostly biscuit', easter: 'Bunny biscuit' }[target];
    return buy(trigger, `${target} collection`) || answer('needs-unlock', 'Season switcher', 'The target season requires its unlocked season switch.', null, { upgrade: 'Season switcher' });
  }
  if (target === 'christmas') {
    if (has('A festive hat') && o.santa.level < 14) {
      if (o.santa.canUpgrade) return act('Santa levels', 'Pay the native Santa level cost.', { type: 'upgrade-santa' });
      return answer('needs-resources', 'Santa levels', 'Santa requires a bank strictly greater than the level price.', null, { requiredCookies: o.santa.price + Math.max(1, o.santa.price * Number.EPSILON) });
    }
    if (config.helperGrandma && !won("Baby it's old outside")) {
      const amount = o.progression.buildingAmounts.Grandma || 0;
      const display = S.grandmaDisplay;
      if (display?.muted) {
        if (!o.controls.preferences?.extraButtons) return act('Santa helper display', 'Enable the native building display controls.', { type: 'preference', name: 'extraButtons' });
        return act('Santa helper display', 'Show the Grandma display.', { type: 'building-mute', id: 1, muted: false });
      }
      if (o.controls.menu) return act('Santa helper display', 'Close the menu so the native canvas can receive pointer input.', { type: 'open-menu', menu: '' });
      const helper = S.helperGrandmas?.[0];
      if (helper) { m.helperPress = true; return act('Santa helper', 'Move to the center of a visible Santa helper grandma.', { type: 'building-hover', id: 1, x: helper.x, y: helper.y }); }
      if (m.helperResizePending) {
        const pending = m.helperResizePending;
        if (display?.width <= pending.previousWidth && now < pending.deadline) return wait('Santa helper display',
          'Allow the native draw callback to expand the visible sprite area.', 100);
        delete m.helperResizePending;
        if (display?.width <= pending.previousWidth) return retry('Santa helper retry',
          'The requested viewport has not revealed more sprite space. Request an ordinary retry run.', 'helper-display-exhausted');
      }
      if (display && display.drawn < Math.min(amount, display.capacity)) return wait('Santa helper display', 'Allow the native draw callback to show the purchased grandma.', 100);
      if (display && amount >= display.capacity) {
        const width = o.viewport?.width ?? m.helperViewportWidth ?? display.width;
        if (width < config.helperMaxWidth) {
          const wider = Math.min(config.helperMaxWidth, Math.max(width + 1, width * 2));
          m.helperViewportWidth = wider;
          m.helperResizePending = { previousWidth: display.width, deadline: now + 1000 };
          return act('Santa helper display', 'Expand the viewport once to reveal additional seeded sprite indices.',
            { type: 'resize', width: wider, height: o.viewport?.height ?? 900 });
        }
        return retry('Santa helper retry',
          'This run has no helper in the available display. Request another ordinary run before final collection.', 'helper-display-exhausted');
      }
      return answer('needs-resources', 'Santa helper', 'Add a grandma so the native Christmas display can include a helper sprite.', null, { building: 'Grandma', amount: amount + 1 });
    }
  }

  // Each quarter-hour has one fixed, seed-dependent dragon drop. Learn only from
  // drops actually observed after petting; never inspect the seed or future RNG.
  if (config.dragonDrops && dragonDrops.some(name => !has(name)) && has('Pet the dragon') && o.dragon.level >= 8) {
    const quarter = Math.floor(now / 900000);
    const phase = quarter % 4;
    const seen = dragonDrops.filter(unlocked);
    const learned = { ...(m.dragonQuarterDrops || {}) };
    const newDrops = seen.filter(name => !m.knownDragonDrops?.includes(name));
    if (m.petAttemptQuarter !== undefined && newDrops.length === 1) {
      learned[m.petAttemptQuarter % 4] = newDrops[0];
      m.petQuarterComplete = m.petAttemptQuarter;
    }
    m.dragonQuarterDrops = learned;
    m.knownDragonDrops = seen;
    // The native shuffle is a fixed permutation for this run. A mapped phase
    // with an owned drop cannot produce anything new, regardless of retries.
    if (learned[phase] && unlocked(learned[phase])) m.petQuarterComplete = quarter;
    if (m.petQuarterComplete !== quarter && now >= (m.nextPetAt || 0)) {
      // If every existing drop has a known phase, any unknown phase contains a
      // missing drop. Geometric retries then finish at this same timestamp a.s.
      // A cold-start permanent drop has no observed phase; advance time between
      // attempts so a hidden duplicate quarter cannot create an endless loop.
      const missingDropCertain = seen.every(name => Object.values(learned).includes(name));
      m.nextPetAt = now + Math.max(config.petIntervalMs, missingDropCertain ? 0 : 100);
      m.petAttemptQuarter = quarter;
      return act('Dragon drops', 'Pet the dragon during this observed quarter-hour.', { type: 'pet-dragon' });
    }
  }

  const needPoker = config.wrinklers && !won('Wrinkler poker');
  const needPop = config.wrinklers && !won('Moistburster') && o.wrinklersPopped < 200 || target === 'halloween' || target === 'easter';
  const needWrath = needPoker || needPop || target === 'christmas' && config.eldeer && !won('Eldeer');
  if (needWrath && has('Elder Covenant')) return buy('Revoke Elder Covenant', 'Restore wrinkler access') || wait('Covenant', 'Wait for the native revoke control.');
  if (needWrath && S.pledgeRemainingMs > 0) return buy('Elder Covenant', 'Restore wrinkler access') || wait('Pledge', 'Wait for the pledge to expire.', S.pledgeRemainingMs);
  if ((needPoker || needPop) && S.elderWrath > 0) {
    const wrinklers = o.controls.wrinklers.filter(w => w.phase > 0);
    let w = wrinklers.find(w => w.id === m.wrinklerTarget) || wrinklers[0];
    if (w) {
      m.wrinklerTarget = w.id;
      if (!needPoker && (target === 'halloween' || target === 'easter') && w.sucked <= 0.5) return wait('Wrinkler drops', 'Wait for a positive stored payout before requesting a seasonal drop.');
      if (now < (m.nextPokeAt || 0)) return wait('Wrinkler recovery', 'Allow native recovery before the next poke.', m.nextPokeAt - now);
      if (!w.selected) {
        m.nextPokeAt = now + 200;
        return act('Wrinkler target', 'Hover the visible wrinkler and let native hit testing select it.', { type: 'wrinkler-hover', id: w.id });
      }
      m.nextPokeAt = now + (needPoker ? 1000 : 40);
      return act(needPoker ? 'Wrinkler poker' : 'Wrinkler drops', needPoker ? 'Poke once, then allow enough recovery to keep this wrinkler alive.' : 'Poke the selected wrinkler to request its native payout.', { type: 'wrinkler-poke', id: w.id });
    }
  }

  const dropsDone = !target && (!config.wrinklers || (o.wrinklersPopped >= 200 || won('Moistburster')) && won('Wrinkler poker'));
  if (config.research && has('Elder Pact') && dropsDone) {
    if (!won('Grandmapocalypse')) return wait('Grandmapocalypse', 'Allow the native maximum-wrath achievement check before pledging.');
    if (S.pledges < config.pledgeTarget || !won('Elder calm')) {
      if (has('Elder Covenant')) return buy('Revoke Elder Covenant', 'Restore pledge access') || wait('Covenant', 'Wait for the revoke control.');
      if (S.pledgeRemainingMs > 0) return buy('Elder Covenant', 'Pledge cycle') || wait('Pledge cycle', 'Wait for the covenant control.');
      return buy('Elder Pledge', 'Pledge count') || wait('Pledge count', 'Wait for the native pledge unlock.');
    }
    if (config.pledgeTarget >= 10 && !has('Sacrificial rolling pins')) {
      const purchase = buy('Sacrificial rolling pins'); if (purchase) return purchase;
      return wait('Sacrificial rolling pins', 'Wait for the native ten-pledge check.');
    }
  }

  for (const name of collection) if (!has(name)) {
    const purchase = buy(name); if (purchase) return purchase;
  }
  if (config.research && !has('Elder Pact')) {
    if (!has('Bingo center/Research facility') && !unlocked('Bingo center/Research facility')) return answer('needs-resources', 'Research facility', 'Own six grandmas and seven Grandma synergy upgrades to unlock the research facility.', null, { building: 'Grandma', amount: 6 });
    return wait('Research', 'Wait for the current native research timer.', S.researchRemainingMs > 0 ? S.researchRemainingMs : config.maxWaitMs);
  }
  if (target || !dropsDone) return wait(target || 'Wrinkler goals', 'Wait for visible native drops, spawns, or unlock checks.');
  if (config.dragonDrops && dragonDrops.some(name => !has(name))) {
    if (!has('Pet the dragon') || o.dragon.level < 8) return answer('needs-unlock', 'Dragon pet drops', 'Pet the dragon and dragon level 8 are required.', null, { upgrade: 'Pet the dragon', dragonLevel: 8 });
    return wait('Dragon pet drops', 'Wait for another pet attempt or quarter-hour.', m.petQuarterComplete === Math.floor(now / 900000) ? 900000 - now % 900000 : Math.max(1, (m.nextPetAt || now) - now));
  }
  if (config.fortunes && S.groups.fortunes.some(name => !has(name))) {
    if (!has('Fortune cookies')) return answer('needs-unlock', 'Fortunes', 'The Fortune cookies heavenly upgrade is required.', null, { upgrade: 'Fortune cookies' });
    return wait('Fortunes', 'Wait for a naturally generated fortune in the news ticker.');
  }
  const expected = [...(config.wrinklers ? ['Wrinkler poker','Itchscratcher','Wrinklesquisher','Moistburster'] : []),
    ...(config.research ? ['Grandmapocalypse','Elder nap','Elder calm',...(config.pledgeTarget >= 5 ? ['Elder slumber'] : [])] : []),
    ...(config.fortunes ? ['O Fortuna'] : []),
    ...(config.seasons.includes('halloween') ? ['Spooky cookies'] : []),
    ...(config.seasons.includes('valentines') ? ['Lovely cookies'] : []),
    ...(config.seasons.includes('easter') ? ['The hunt is on','Egging on','Mass Easteria','Hide & seek champion'] : []),
    ...(config.seasons.includes('christmas') ? ['Coming to town','All hail Santa','Let it snow',...(config.reindeerTarget >= 200 ? ['Reindeer sleigher'] : [])] : [])];
  const pendingAchievement = expected.find(name => !won(name));
  if (pendingAchievement) return wait(pendingAchievement, 'Allow the native achievement check to record the completed condition.');
  // Golden clover does not accelerate wrath-cookie timers. Once the required
  // wrath rewards and pledge goals are done, the final count crop uses normal
  // golden cookies. The ordinary Covenant purchase carries its native CpS cost.
  if (config.suppressWrathForCookieCount && !won("Black cat's paw") && has('Elder Pact') && !has('Elder Covenant')) {
    return buy('Elder Covenant', 'Natural golden-cookie count')
      || wait('Natural golden-cookie count', 'Wait for the native Covenant control.');
  }
  return answer('complete', 'Seasonal collection', 'The configured seasonal, research, wrinkler, dragon-drop, and fortune goals are complete.');
}

export function decideSeasonAction(observation, memory = {}, options = {}) {
  return seasonDecision(observation, [], { ...memory, config: { ...(memory.config || {}), ...options } }, RESEARCH_UPGRADES, DRAGON_DROPS);
}
export function seasonPolicySource(options = {}) {
  return `(function(observation, availableActions, memory) {
    return (${seasonDecision.toString()})(observation, availableActions, {...(memory || {}), config: {...${JSON.stringify(options)}, ...((memory || {}).config || {})}}, ${JSON.stringify(RESEARCH_UPGRADES)}, ${JSON.stringify(DRAGON_DROPS)});
  })`;
}

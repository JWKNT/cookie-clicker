/** Native controls for finite goals outside the four minigames. No optimum is claimed. */
export const MISC_ACHIEVEMENTS = Object.freeze([
  'Cookie-dunker', 'Just wrong', 'Early bird', 'Fading luck', 'Thick-skinned', 'No time like the present',
]);

function miscDecision(o, actions, memory) {
  const m = { ...(memory || {}) };
  let timing = { deferShimmerIds: [], wakeAfterMs: 1000 };
  const result = (status, goal, action = null, extra = {}) => ({ status, goal, action, memory: m, ...timing, ...extra });
  const act = (goal, action) => result('acting', goal, action);
  const resources = (goal, requiredCookies) => result('needs-resources', goal, null, { requiredCookies });
  const won = name => !!o.achievements[name];
  if (o.progression.onAscend || o.progression.ascendTimer || o.progression.reincarnateTimer) return result('blocked', 'Active run');

  // The send result is a code displayed by the native prompt, not save data.
  if (m.giftPending) {
    delete m.giftPending;
    if (o.controls.promptOn && o.giftCode) {
      m.giftCode = o.giftCode;
      return act('No time like the present', { type: 'close-prompt' });
    }
  }
  if (o.controls.promptOn) return result('blocked', 'Unrelated prompt');

  if (m.dunkViewport && won('Cookie-dunker')) {
    delete m.dunkViewport;
    return act('Restore viewport', { type: 'resize', width: 1200, height: 900 });
  }
  if (!won('Cookie-dunker') && Object.values(o.achievements).filter(Boolean).length >= 3) {
    if (!m.dunkViewport) {
      m.dunkViewport = true;
      return act('Cookie-dunker', { type: 'resize', width: 1200, height: 200 });
    }
  }
  // During the no-upgrade challenge the scheduler can preserve this income.
  // The required sale remains available immediately after Hardcore is won.
  if (!won('Just wrong') && o.progression.buildingAmounts.Grandma > 0
    && (!m.deferGrandmaSaleUntilHardcore || won('Hardcore'))) {
    return act('Just wrong', { type: 'sell-building', id: 1, amount: 1 });
  }

  // A golden cookie's remaining lifetime is measured in engine frames.
  // No hidden effect or random seed is inspected. A forced cookie may not
  // award these goals; the same rule will try a later natural spawn.
  const golden = o.shimmers.filter(s => s.type === 'golden');
  if (!won('Early bird') && golden.length) return act('Early bird', { type: 'click-shimmer', id: golden[0].id });
  let deferred = [];
  let wakeAfterMs = 1000;
  if (!won('Fading luck') && golden.length) {
    const target = golden.find(s => s.id === m.fadingId) || golden.reduce((a, b) => a.life < b.life ? a : b);
    m.fadingId = target.id;
    const fps = o.fps || 30;
    if (target.life < fps) return act('Fading luck', { type: 'click-shimmer', id: target.id });
    deferred = [target.id];
    wakeAfterMs = Math.max(1, (target.life - (fps - 1)) * 1000 / fps);
  } else delete m.fadingId;
  const extra = { deferShimmerIds: deferred, wakeAfterMs };
  timing = extra;

  if (m.restoreGoldenSwitch) {
    const restore = o.shop.upgrades.find(u => u.name === 'Golden switch [on]');
    if (restore?.canBuy && o.cookies >= restore.price) { delete m.restoreGoldenSwitch; return act('Restore golden-cookie spawns', { type: 'buy-upgrade', id: restore.id }); }
    if (!o.upgrades['Golden switch [off]']?.bought) delete m.restoreGoldenSwitch;
    else if (restore) return resources('Restore golden-cookie spawns', restore.price);
    else return result('needs-unlock', 'Restore golden-cookie spawns');
  }

  if (!won('No time like the present') && o.upgrades['Wrapping paper']?.bought
      && o.progression.ascensionMode === 0 && !o.buffs['Gifted out']) {
    if (o.cookies < 1e9) return resources('No time like the present', 1e9);
    if (m.giftCode) return act('No time like the present', { type: 'gift-redeem', code: m.giftCode });
    m.giftPending = true;
    return act('No time like the present', { type: 'gift-send', amount: 1, message: 'Completion gift' });
  }
  if (!won('Thick-skinned') && o.upgrades['Reinforced membrane']?.bought && won('Neverclick') && won('Hardcore')) {
    const restore = o.shop.upgrades.find(u => u.name === 'Shimmering veil [off]');
    if (restore?.canBuy && o.cookies >= restore.price) return act('Thick-skinned', { type: 'buy-upgrade', id: restore.id });
    if (restore) return resources('Thick-skinned', restore.price);
    if (o.upgrades['Shimmering veil [off]']?.bought && o.elapsedMs >= (m.veilClickAfter || 100)) {
      m.veilClickAfter = o.elapsedMs + 20;
      return act('Thick-skinned', { type: 'click' });
    }
  }
  const accessed = name => o.upgrades[name]?.unlocked || o.upgrades[name]?.bought || o.history.accessedUpgrades.includes(name);
  if (won('Black cat\'s paw') && !accessed('Golden switch [on]')) {
    const enable = o.shop.upgrades.find(u => u.name === 'Golden switch [off]');
    // This is a conservative reserve for the two native toggle prices. The
    // final bank can pay it without a period of disabled golden-cookie spawns.
    if (enable?.canBuy && o.cookies >= enable.price * 100) {
      m.restoreGoldenSwitch = true;
      return act('Golden switch access', { type: 'buy-upgrade', id: enable.id });
    }
    if (enable) return resources('Golden switch access', enable.price * 100);
  }
  return result(MISC_ACHIEVEMENTS_INTERNAL.every(won) && accessed('Golden switch [on]') && !m.restoreGoldenSwitch ? 'complete' : 'waiting', 'Miscellaneous goals', null, extra);
}

// Kept in the source expression for the restricted VM, which has no imports.
const MISC_ACHIEVEMENTS_INTERNAL = MISC_ACHIEVEMENTS;
export function decideMiscAction(observation, memory = {}) { return miscDecision(observation, [], memory); }
export function miscPolicySource() {
  return `(function () { const MISC_ACHIEVEMENTS_INTERNAL = ${JSON.stringify(MISC_ACHIEVEMENTS)}; return (${miscDecision.toString()}); })()`;
}

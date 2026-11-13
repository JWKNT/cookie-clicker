import { HELPER_ART_EXCLUSIONS, HELPER_GRANDMAS, helperSweepActions } from './helper-cover.mjs';

/** Elapsed bounds refer only to this pinned diagnostic profile: one initial
 * Game.Loop chain, the native Init draw, and fresh-realm maintenance startup.
 * No direct Game.Draw/Resume calls, external mods, or imported prior realm are
 * admitted. Init resets drawT; each later Loop timeout costs at least 1ms.
 * Thus drawT is at most elapsedMs+2 in the current realm. The 2^50 guard leaves
 * room for all 3350ms of the sweep before the binary64 counter reaches 2^53.
 * This is a source-profile premise, not an inference from arbitrary snapshots. */
export const HELPER_DRAW_PROFILE = 'pinned-init-loop-only-v1';

/** Fixed two-art setup. The seed certificate requires every premise below.
 * This controller does not request a new run after a failed sprite outcome. */
function helperSetupDecision(o, memory, excluded, count, sweep) {
  const m={...(memory || {})};
  const answer=(status,action=null,reason='')=>({status,action,reason,memory:m});
  if(o.achievements["Baby it's old outside"])return answer('complete');
  if(o.progression.onAscend || o.progression.ascendTimer || o.progression.reincarnateTimer
    || o.progression.ascensionMode!==0 || o.controls.promptOn)return answer('deferred',null,'An active normal run with no prompt is required.');
  if(o.ascensions<1 || !o.upgrades['Season switcher']?.bought)return answer('deferred',null,'Use an already scheduled profitable reset and its Season switcher purchase.');
  if(excluded.some(name=>o.upgrades[name]?.bought))return answer('deferred',null,'This run does not have the certified two-art pool. Keep its scheduled economic reset.');
  if(o.controls.preferences?.animate!==1)return answer('blocked',null,'The pinned helper draw profile requires building animation enabled.');
  if(!Number.isSafeInteger(o.elapsedMs) || o.elapsedMs<0 || o.elapsedMs>2**50)
    return answer('blocked',null,'The pinned Init/Loop-only draw profile does not certify remaining frames at this elapsed time.');
  if(m.attempted)return answer('blocked',null,'The fixed two-art sweep ended without the native achievement. Its display or draw premise is unresolved.');
  const grandma=o.shop.buildings.find(b=>b.name==='Grandma');
  if(!grandma)return answer('blocked',null,'The public Grandma offer is absent.');
  if(grandma.amount<count) {
    if(!grandma.locked && grandma.buy1price<=o.cookies)return answer('acting',{type:'buy-building',id:grandma.id,amount:1});
    return answer('needs-resources',null,'Fund the next of the 24 Grandmas through ordinary growth.');
  }
  if(o.seasonal.season!=='christmas') {
    const offer=o.shop.upgrades.find(u=>u.name==='Festive biscuit' && u.unlocked && !u.bought);
    if(!offer)return answer('blocked',null,'Season switcher has not exposed its native Christmas trigger.');
    if(offer.canBuy && offer.price<=o.cookies)return answer('acting',{type:'buy-upgrade',id:offer.id});
    return answer('needs-resources',null,'Fund the native Christmas trigger through ordinary growth.');
  }
  if(!o.controls.preferences.fancy)return answer('acting',{type:'preference',name:'fancy'});
  const display=o.seasonal.grandmaDisplay;
  if(display?.muted) {
    if(!o.controls.preferences.extraButtons)return answer('acting',{type:'preference',name:'extraButtons'});
    return answer('acting',{type:'building-mute',id:grandma.id,muted:false});
  }
  if(o.controls.menu)return answer('acting',{type:'open-menu',menu:''});
  if(!display || display.width<278 || display.height<89) {
    if(m.resized)return answer('blocked',null,'The configured viewport does not expose the certified 278x89 Grandma rectangle.');
    m.resized=true;
    return answer('acting',{type:'sequence',actions:[{type:'resize',width:1200,height:900},{type:'wait',milliseconds:134}]});
  }
  m.attempted=true;
  return answer('acting',{type:'sequence',actions:sweep});
}

export function helperSetupPolicySource() {
  return `(function(o,actions,memory){return (${helperSetupDecision.toString()})(o,memory,${JSON.stringify(HELPER_ART_EXCLUSIONS)},${HELPER_GRANDMAS},${JSON.stringify(helperSweepActions())});})`;
}

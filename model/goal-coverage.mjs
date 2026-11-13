import { GARDEN_DROP_CROPS } from './garden-policy.mjs';
import { MARKET_ACHIEVEMENTS } from './market-policy.mjs';
import { SEASON_ACHIEVEMENTS, RESEARCH_UPGRADES, DRAGON_DROPS } from './season-policy.mjs';
import { MISC_ACHIEVEMENTS } from './misc-policy.mjs';

/** Audit-time mapping of every terminal item to a native trigger family.
 * This consumes the inspected engine, never a policy observation. A mapped
 * trigger is not a proof that the composed policy reaches it or minimizes time.
 */
export function buildGoalCoverage(runtime, requirements) {
  const G = runtime.Game;
  const entries = new Map();
  const add = (name, controller, trigger, details = {}) => entries.set(name, { controller, trigger, ...details });
  for (const a of G.BankAchievements) add(a.name, 'production', 'current-run cookies baked', { threshold: a.threshold });
  for (const a of G.CpsAchievements) add(a.name, 'production', 'native cookies per second', { threshold: a.threshold });
  for (const b of Object.values(G.Objects)) {
    for (const a of Object.values(b.tieredAchievs)) add(a.name, 'production', 'building amount', { building: b.name, tier: a.tier });
    for (const p of b.productionAchievs) add(p.achiev.name, 'production', 'current-run building production', { building: b.name, threshold: p.pow });
  }
  for (const name of SEASON_ACHIEVEMENTS) add(name, 'season', 'native seasonal, research, fortune, or wrinkler callback');
  for (const name of MARKET_ACHIEVEMENTS) add(name, 'market', 'native trade or office callback');
  for (const name of MISC_ACHIEVEMENTS) add(name, 'misc', 'native interface or finite event callback');
  for (const name of ['Botany enthusiast', 'Green, aching thumb', 'In the garden of Eden (baby)', 'Keeper of the conservatory', 'Seedless to nay']) add(name, 'garden', 'native Garden harvest, log, or sacrifice callback');
  for (const name of ['Bibbidi-bobbidi-boo', "I'm the wiz", 'A wizard is you']) add(name, 'completion', 'completed native spell callbacks');
  for (const name of ['Dude, sweet', 'Sugar rush', 'Hand-picked']) add(name, 'completion', 'native sugar-lump harvest');
  for (const name of ['Hardcore', 'Neverclick']) add(name, 'completion', 'preserved first-run condition and native periodic check');
  for (const name of ["What's in a name", 'Tiny cookie', 'Here you go', 'Olden days', 'Tabloid addiction', 'Stifling the press']) add(name, 'completion', 'native interface action');
  for (const name of ['Rebirth', 'Resurrection', 'Reincarnation', 'All the stars in heaven', 'Debt evasion']) add(name, 'ascension', 'native reset or reincarnation callback');
  for (const name of ['Golden cookie', 'Lucky cookie', 'A stroke of luck', 'Fortune', 'Leprechaun', "Black cat's paw", 'Wrath cookie']) add(name, 'completion', 'click native counted golden or wrath cookies');
  for (const name of ['Wholesome', 'You win a cookie', 'Cookie Clicker']) add(name, 'production', 'native economic unlock check');
  add('Here be dragon', 'completion', 'complete native dragon training');
  add('Uncanny clicker', 'baseline', 'five accumulated fast-click detections; native click interval below 1/15 second');
  for (const { name } of requirements.requiredAchievements) {
    if (entries.has(name)) continue;
    const desc = G.Achievements[name].baseDesc.replace(/<[^>]*>/g, '');
    if (desc.startsWith('Ascend with ')) add(name, 'ascension', 'current-run cookies forfeited');
    else if (desc.includes('cookies from clicking')) add(name, 'baseline', 'current-run cookies from clicks');
    else if (/^Have .* cursor/.test(desc)) add(name, 'production', 'current cursor amount; final required threshold is 1000');
    else if (/^Have at least /.test(desc) || /^Own /.test(desc) || /^Purchase /.test(desc)) add(name, 'production', 'native aggregate building or upgrade ownership check');
  }
  const achievements = requirements.requiredAchievements.map(a => ({ ...a, ...(entries.get(a.name) || { controller: null, trigger: 'unmapped' }) }));

  const seasonal = new Set(Object.values(runtime.snapshot().seasonal.groups).flat());
  const earned = new Set(G.UnlockAt.map(x => x.name));
  const garden = new Set(GARDEN_DROP_CROPS.map(x => x.upgrade));
  const research = new Set([...RESEARCH_UPGRADES, 'Sacrificial rolling pins']);
  const grandma = new Set(G.GrandmaSynergies);
  const cursor = new Set(['Reinforced index finger', 'Carpal tunnel prevention cream', 'Ambidextrous',
    'Thousand fingers', 'Million fingers', 'Billion fingers', 'Trillion fingers', 'Quadrillion fingers',
    'Quintillion fingers', 'Sextillion fingers', 'Septillion fingers', 'Octillion fingers',
    'Nonillion fingers', 'Decillion fingers', 'Undecillion fingers']);
  const heavenlyPower = new Set(['Heavenly chip secret', 'Heavenly cookie stand', 'Heavenly bakery', 'Heavenly confectionery', 'Heavenly key']);
  const biscuit = new Set(['Milk chocolate butter biscuit','Dark chocolate butter biscuit','White chocolate butter biscuit','Ruby chocolate butter biscuit',
    'Lavender chocolate butter biscuit','Synthetic chocolate green honey butter biscuit','Royal raspberry chocolate butter biscuit',
    'Ultra-concentrated high-energy chocolate butter biscuit','Pure pitch-black chocolate butter biscuit','Cosmic chocolate butter biscuit',
    'Butter biscuit (with butter)','Everybutter biscuit','Personal biscuit']);
  const upgrades = requirements.ownedUpgrades.map(item => {
    const u = G.Upgrades[item.name];
    let controller = 'baseline'; let trigger = null;
    if (u.pool === 'prestige') { controller = 'ascension'; trigger = 'native heavenly parents, price, and visibility'; }
    else if (garden.has(u.name)) { controller = 'garden'; trigger = 'mature Garden harvest drop, then purchase'; }
    else if (research.has(u.name) || seasonal.has(u.name) || DRAGON_DROPS.includes(u.name)
      || ['A festive hat', "Santa's dominion"].includes(u.name)) { controller = 'season'; trigger = 'native research, season, fortune, or pet drop, then purchase'; }
    else if (cursor.has(u.name)) trigger = 'native cursor amount unlock, then purchase';
    else if (/ mouse$/.test(u.name)) trigger = 'native handmade-cookie threshold, then purchase';
    else if (biscuit.has(u.name)) trigger = 'native all-building amount threshold up to700, then purchase';
    else if (heavenlyPower.has(u.name)) trigger = 'positive prestige and preceding prestige-power upgrades';
    else if (['Lucky day','Serendipity','Get lucky'].includes(u.name)) trigger = 'native counted golden-cookie threshold, then purchase';
    else if (['A crumbly egg','Dragon cookie'].includes(u.name)) trigger = 'native dragon access or training, then purchase';
    else if (earned.has(u.name)) trigger = 'native UnlockAt cookie and prerequisite check, then purchase';
    else if (u.buildingTie || u.buildingTie1 || grandma.has(u.name)) trigger = 'native building, synergy, or Grandma unlock, then purchase';
    else if (u.kitten) trigger = 'native milk threshold, then purchase';
    return { ...item, controller: trigger ? controller : null, trigger: trigger || 'unmapped' };
  });
  const access = requirements.accessUpgrades.map(item => ({ ...item,
    controller: ['Golden switch [off]', 'Golden switch [on]'].includes(item.name) ? 'misc'
      : ['Elder Pledge','Elder Covenant','Revoke Elder Covenant'].includes(item.name) ? 'season' : 'native-unlock',
    trigger: ['Golden switch [off]', 'Golden switch [on]'].includes(item.name)
      ? 'switch on once, record access, then switch off to restore golden-cookie spawns'
      : 'record native unlocked or owned state; historical access persists across mutually exclusive choices',
  }));
  return {
    schemaVersion: 1, gameVersion: '2.053', edition: 'steam', sourceHashes: requirements.sourceHashes,
    evidenceScope: 'Exhaustive target-to-trigger inventory. This is not a reachability, termination, expectation, or optimality proof.',
    achievements, upgrades, access,
    finiteUnlocks: {
      sufficientBuildingTargets: Object.values(G.Objects).map(b => ({ name: b.name, amount: b.id === 0 ? 1000 : 700 })),
      buildingTargetScope: 'Sufficient construction targets, not extra terminal conditions. Their achievements remain won after buildings are sold.',
      minimumNormalAchievements: 600,
      deterministicMilkFallback: { building: 'Farm', level: 10, additionalLumpsFromLevel9: 10,
        condition: 'Use only if other normally won achievements do not already bring the count to600.' },
      grossLevelLumpCostWithFarm10: 136,
      otherCurrentGoals: ['all34GardenSeeds','all5soils','all4minigames','allspells','allgods','allmarketgoods','allloans','dragon27','Santa14','office5','normalrun'],
    },
    unmapped: [...achievements, ...upgrades].filter(x => !x.controller).map(x => ({ id: x.id, name: x.name })),
  };
}
